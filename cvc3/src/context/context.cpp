/*****************************************************************************/
/*!
 * \file context.cpp
 * 
 * Author: Clark Barrett
 * 
 * Created: Fri Jan 17 14:30:37 2003
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 * 
 */
/*****************************************************************************/


#include "context.h"


using namespace CVC3;
using namespace std;


vector<char*> ContextMemoryManager::s_freePages;


///////////////////////////////////////////////////////////////////////////////
// Scope methods                                                             //
///////////////////////////////////////////////////////////////////////////////


void Scope::finalize(void)
{
  ContextObjChain* obj = d_restoreChain;
  while (obj != NULL) {
    ContextObjChain* tmp = obj->d_restoreChainNext;
    // When called from ~ContextManager(), the master objects may
    // still point to this scope.  Disconnect them here.
    if (obj->d_master != NULL) {
      if (obj->d_master->d_scope == this)
        obj->d_master->d_scope = NULL;
      if (obj->d_master->d_restore == obj)
        obj->d_master->d_restore = NULL;
    }
    obj = tmp;
  }
}


void Scope::check(void)
{
  IF_DEBUG(
  ContextObjChain* obj = d_restoreChain;
  if (debugger.trace("memory") && obj != NULL) {
    ostream& os = debugger.getOS();
    int n(0);
    ContextObjChain* tmp = obj;
    while(tmp != NULL) {
      tmp = tmp->d_restoreChainNext;
      n++;
    }
    os << "*** Warning: ~Scope(): found "<< n << " leaked objects "
       << "in scope " << d_level << ":" << endl;
    if (debugger.flag("memory leaks")) {
      tmp = obj;
      while(tmp != NULL) {
        os << tmp->name() << "\n";
        tmp = tmp->d_restoreChainNext;
      }
    }
    os << flush;
  }
  )
}


unsigned long Scope::getMemory(int verbosity)
{
  unsigned long memSelf = 0; // scope is allocated in cmm
  unsigned long mem = 0;

  mem += getCMM()->getMemory(verbosity - 1);
  if (d_prevScope != NULL) {
    mem += d_prevScope->getMemory(verbosity - 1);
  }

  // TODO: d_restoreChain?

  if (verbosity > 0) {
    cout << "Scope " << d_level << ": " << memSelf << endl;
    cout << "  Children: " << mem << endl;
    cout << "  Total: " << mem+memSelf << endl;
  }

  return mem + memSelf;


}


///////////////////////////////////////////////////////////////////////////////
// ContextObjChain methods                                                   //
///////////////////////////////////////////////////////////////////////////////


ContextObjChain* ContextObjChain::restore(void)
{
  // Assign 'next' pointer only when the master object is restored,
  // since this may change our next pointer (master may have other
  // context objects removed).
  DebugAssert(d_master != NULL, "How did this happen");
  //  if (d_master == NULL) return d_restoreChainNext;
  ContextObjChain* next;
  DebugAssert(d_data != NULL, "Shouldn't happen");
//   if (d_data == NULL) {
//     d_master->setNull();
//     d_master->d_scope = d_master->d_scope->prevScope();
//     DebugAssert(d_restore==NULL,"Expected NULL");
//     next = d_restoreChainNext;
//     d_master->d_scope->addToChain(this);
//   }
//   else {
    d_master->restoreData(d_data);
    d_master->d_scope = d_data->d_scope;
    d_master->d_restore = d_restore;
    next = d_restoreChainNext;
    if (d_data != NULL) delete d_data;
    DebugAssert(d_master->d_restore != this, "points to self");
//   }
  return next;
}


#ifdef _CVC3_DEBUG_MODE
std::string ContextObjChain::name() const
{
  DebugAssert(d_master != NULL, "NULL master");
  return d_master->name();
}
#endif


///////////////////////////////////////////////////////////////////////////////
// ContextObj methods                                                        //
///////////////////////////////////////////////////////////////////////////////


void ContextObj::update(int scope)
{
  Scope* tmpScope = d_scope;
  DebugAssert(scope < 0 || d_scope->level() <= scope,
	      "ContextObj::update(scope="+int2string(scope)
	      +"): scope < d_scope->level() = "
	      +int2string(d_scope->level()));
  d_scope = d_scope->topScope();
  if (scope >= 0) {
    // Fetch the specified scope
    for(int i=level(); i>scope; --i) {
      d_scope = d_scope->prevScope();
      DebugAssert(d_scope != NULL, "ContextObj::update["
		  +name()+"]: d_scope == NULL");
    }
  }
  ContextObj* data = makeCopy(getCMM());
  data->d_scope = tmpScope;
  // The destructor of the copy should not destroy our older copies
  data->d_restore=NULL;
  IF_DEBUG(data->setName(name()+" [copy]");)
  d_restore = new(getCMM()) ContextObjChain(data, this, d_restore);
  d_scope->addToChain(d_restore);
}


ContextObj::~ContextObj()
{
  // Delete our restore copies
  IF_DEBUG(FatalAssert(d_active, "~ContextObj["+name()+"]");)
  IF_DEBUG(d_active=false);;
  for(ContextObjChain* obj = d_restore; obj != NULL; ) {
    ContextObjChain* tmp = obj->d_restore;
    // Remove the object from the restore chain
    if(obj->d_restoreChainNext != NULL)
      obj->d_restoreChainNext->d_restoreChainPrev = obj->d_restoreChainPrev;
    *(obj->d_restoreChainPrev) = obj->d_restoreChainNext;
    //    if (obj->d_data != NULL) delete obj->d_data;
    obj->d_master = NULL;
    if (tmp == NULL) {
      delete obj;
      free(obj);
      break;
    }
    obj = tmp;
  }
  //  TRACE("context verbose", "~ContextObj()[", this, "] }");
}


///////////////////////////////////////////////////////////////////////////////
// Context methods                                                           //
///////////////////////////////////////////////////////////////////////////////


Context::Context(ContextManager* cm, const string& name, int id)
  : d_cm(cm), d_name(name), d_id(id)
{
  ContextMemoryManager* cmm = new ContextMemoryManager();
  d_topScope = new(cmm) Scope(this, cmm);
  d_bottomScope = d_topScope;
  TRACE("context", "*** [context] Creating new context: name = "
	+ name + "id = ", id, "");
}


// Don't pop, just delete everything.  At this point, most of the
// system is already destroyed, popping may be dangerous.
Context::~Context()
{
  // popto(0);
  Scope* top = d_topScope;
  while(top != NULL) {
    top = d_topScope->prevScope();
    d_topScope->finalize();
    delete d_topScope->getCMM();
    d_topScope = top;
  }
  while (!d_cmmStack.empty()) {
    delete d_cmmStack.back();
    d_cmmStack.pop_back();
  }
  ContextMemoryManager::garbageCollect();
  // Erase ourselves from the notify objects, so they don't call us
  for(vector<ContextNotifyObj*>::iterator i=d_notifyObjList.begin(),
	iend=d_notifyObjList.end(); i!=iend; ++i) {
    (*i)->d_context = NULL;
  }
}


void Context::push()
{
  IF_DEBUG(
    string indentStr(level(), ' ');
    TRACE("pushpop", indentStr, "Push", " {");
  )
  ContextMemoryManager* cmm;
  if (!d_cmmStack.empty()) {
    cmm = d_cmmStack.back();
    d_cmmStack.pop_back();
  }
  else {
    cmm = new ContextMemoryManager();
  }
  cmm->push();
  d_topScope = new(cmm) Scope(this, cmm, d_topScope);
  //  TRACE("context", "*** [context] Pushing scope to level ", level(), " {");
  IF_DEBUG(DebugCounter maxLevel(debugger.counter("max scope level"));)
  IF_DEBUG(if(maxLevel<level()) maxLevel=level();)
}


void Context::pop()
{
  Scope* top = d_topScope;
  //  TRACE("context", "*** [context] Popping scope from level ", level(), "...");
  DebugAssert(top->prevScope() != NULL,
	      "Illegal to pop last scope off of stack.");
  // Notify before popping the scope
  for(vector<ContextNotifyObj*>::iterator i=d_notifyObjList.begin(),
	iend=d_notifyObjList.end(); i != iend; ++i)
    (*i)->notifyPre();
  // Pop the scope
  d_topScope = top->prevScope();
  top->restore();
  IF_DEBUG(top->check();)
  ContextMemoryManager* cmm = top->getCMM();
  cmm->pop();
  d_cmmStack.push_back(cmm);

  // Notify after the pop is done
  for(vector<ContextNotifyObj*>::iterator i=d_notifyObjList.begin(),
	iend=d_notifyObjList.end(); i != iend; ++i)
    (*i)->notify();
  //  TRACE("context", "*** [context] Popped scope to level ", level(), "}");
  IF_DEBUG(
    string indentStr(level(), ' ');
    TRACE("pushpop", indentStr, "}", " Pop");
  )
}


void Context::popto(int toLevel)
{
  while (toLevel < topScope()->level()) pop();
}


void Context::deleteNotifyObj(ContextNotifyObj* obj) {
  size_t i(0), iend(d_notifyObjList.size());
  for(; i<iend && d_notifyObjList[i]!=obj; ++i);
  if(i<iend) { // Found obj; delete it from the vector
    d_notifyObjList[i]=d_notifyObjList.back();
    d_notifyObjList.pop_back();
  }
}


unsigned long Context::getMemory(int verbosity)
{
  unsigned long memSelf = sizeof(Context);
  unsigned long mem = 0;
  mem += MemoryTracker::getString(verbosity - 1, d_name);
  mem += d_topScope->getMemory(verbosity - 1);
  mem += MemoryTracker::getVecAndDataP(verbosity - 1, d_notifyObjList);
  mem += MemoryTracker::getVecAndDataP(verbosity - 1, d_cmmStack);
  MemoryTracker::print("Context "+d_name, verbosity, memSelf, mem);
  return mem + memSelf;
}


///////////////////////////////////////////////////////////////////////////////
// ContextManager methods                                                    //
///////////////////////////////////////////////////////////////////////////////


ContextManager::ContextManager()
{
  d_curContext = createContext("default");
}


ContextManager::~ContextManager()
{
  while (d_contexts.size()) {
    delete d_contexts.back();
    d_contexts.pop_back();
  }
}


Context* ContextManager::createContext(const string& name)
{
  d_contexts.push_back(new Context(this, name, d_contexts.size()));
  return d_contexts.back();
}


Context* ContextManager::switchContext(Context* context)
{
  FatalAssert(false, "Multiple contexts not yet implemented");
  Context* old = d_curContext;
  DebugAssert(context && context == d_contexts[context->id()],
	      "Unknown context");
  d_curContext = context;
  // TODO: Fix up all Context Objects
  return old;
}


unsigned long ContextManager::getMemory(int verbosity)
{
  unsigned long memSelf = sizeof(ContextManager);
  unsigned long mem = 0;

  // free pages in the context memory manager need to be counted somewhere
  // this seems as good a place as any
  mem += ContextMemoryManager::getStaticMemory(verbosity - 1);

  for (unsigned i = 0; i < d_contexts.size(); ++i) {
    mem += d_contexts[i]->getMemory(verbosity - 1);
  }

  MemoryTracker::print("ContextManager", verbosity, memSelf, mem);

  return mem + memSelf;
}
