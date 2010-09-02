/*****************************************************************************/
/*!
 * \file expr_manager.cpp
 *
 * Author: Sergey Berezin
 *
 * Created: Wed Dec  4 14:20:56 2002
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

#include "expr_manager.h"
#include "command_line_flags.h"
#include "expr_stream.h"
#include "pretty_printer.h"
#include "memory_manager_malloc.h"
#include "memory_manager_chunks.h"

using namespace CVC3;

using namespace std;

// File-local function which registers all the commonly declared
// kinds (defined below)
static void registerKinds(ExprManager& em);

void ExprManager::installExprValue(ExprValue* p_ev)
{
  DebugAssert(isActive(), "ExprManager::installExprValue(ExprValue*)");
//   int maxHeight = 0;
//   p_ev->d_highestKid = 0;
//   for (unsigned i = 0; i < p_ev->arity(); i++)
//   {
//     int height = p_ev->getKids()[i].getHeight();
//     if (height > maxHeight)
//     {
//       maxHeight = height;
//       p_ev->d_highestKid = i;
//     }
//   }

//   if (p_ev->d_kind == ITE && p_ev->arity() == 3)
//   {
//     if (p_ev->getKids()[1].getHeight() > p_ev->getKids()[2].getHeight())
//       p_ev->d_highestKid = 1;
//     else
//       p_ev->d_highestKid = 2;
//   }

//   switch (p_ev->d_kind) {
//   case NOT: case AND: case OR: case ITE: case IFF: case IMPLIES:
//     maxHeight++;
//   }
//   p_ev->d_height = maxHeight;

  d_exprSet.insert(p_ev);
}


// Constructor
ExprManager::ExprManager(ContextManager* cm, const CLFlags& flags)
  // Initial number of buckets is 1024 (it's kinda arbitrary)
  : d_cm(cm), d_index(0), d_flagCounter(1), d_prettyPrinter(NULL),
    d_printDepth(&(flags["print-depth"].getInt())),
    d_withIndentation(&(flags["indent"].getBool())),
    d_indent(0), d_indentTransient(0),
    d_lineWidth(&(flags["width"].getInt())),
    d_inputLang(&(flags["lang"].getString())),
    d_outputLang(&(flags["output-lang"].getString())),
    d_dagPrinting(&(flags["dagify-exprs"].getBool())),
    d_mmFlag(flags["mm"].getString()),
    d_exprSet(1024, HashEV(this), EqEV()),
    d_mm(EXPR_VALUE_TYPE_LAST),
    d_simpCacheTagCurrent(1), d_disableGC(false), d_postponeGC(false),
    d_inGC(false), d_typeComputer(NULL)
{
  // Initialize the notifier
  d_notifyObj = new ExprManagerNotifyObj(this, d_cm->getCurrentContext());

  // Initialize core memory managers
  if(d_mmFlag == "chunks") {
    d_mm[EXPR_VALUE] = new MemoryManagerChunks(sizeof(ExprValue));
    d_mm[EXPR_NODE] = new MemoryManagerChunks(sizeof(ExprNode));
    d_mm[EXPR_APPLY] = new MemoryManagerChunks(sizeof(ExprApply));
    d_mm[EXPR_STRING] = new MemoryManagerChunks(sizeof(ExprString));
    d_mm[EXPR_RATIONAL] = new MemoryManagerChunks(sizeof(ExprRational));
    d_mm[EXPR_UCONST] = new MemoryManagerChunks(sizeof(ExprVar));
    d_mm[EXPR_SYMBOL] = new MemoryManagerChunks(sizeof(ExprSymbol));
    d_mm[EXPR_BOUND_VAR] = new MemoryManagerChunks(sizeof(ExprBoundVar));
    d_mm[EXPR_CLOSURE] = new MemoryManagerChunks(sizeof(ExprClosure));
    d_mm[EXPR_SKOLEM] = new MemoryManagerChunks(sizeof(ExprSkolem));
  } else {
    d_mm[EXPR_VALUE] = new MemoryManagerMalloc();
    d_mm[EXPR_NODE] = new MemoryManagerMalloc();
    d_mm[EXPR_APPLY] = new MemoryManagerMalloc();
    d_mm[EXPR_STRING] = new MemoryManagerMalloc();
    d_mm[EXPR_RATIONAL] = new MemoryManagerMalloc();
    d_mm[EXPR_UCONST] = new MemoryManagerMalloc();
    d_mm[EXPR_SYMBOL] = new MemoryManagerMalloc();
    d_mm[EXPR_BOUND_VAR] = new MemoryManagerMalloc();
    d_mm[EXPR_CLOSURE] = new MemoryManagerMalloc();
    d_mm[EXPR_SKOLEM] = new MemoryManagerMalloc();
  }
  registerKinds(*this);

  d_bool = newLeafExpr(BOOLEAN);
  d_false = newLeafExpr(FALSE_EXPR);
  d_false.setType(Type::typeBool(this));
  d_true = newLeafExpr(TRUE_EXPR);
  d_true.setType(Type::typeBool(this));

  IF_DEBUG(d_inRebuild = false;)
}

// Destructor
ExprManager::~ExprManager() {
  FatalAssert(d_emptyVec.size()==0, "~ExprManager()");
  delete d_notifyObj;
  // Make sure garbage collector doesn't get in the way
  d_disableGC = false;		//  clear() will assert this.
  clear();
  d_disableGC = true;
  // Destroy memory managers
  TRACE_MSG("delete", "~ExprManager: deleting d_mm's {");
  for(size_t i=0; i<d_mm.size(); ++i)
    delete d_mm[i];

  TRACE_MSG("delete", "~ExprManager: finished deleting d_mm's }");
}


void ExprManager::clear() {
  FatalAssert(isActive(), "ExprManager::clear()");
  // Make ExprManager inactive, but keep all the Exprs intact
  // Remove all internal expressions.
  d_disableGC = true;

  TRACE("delete", "clear: number of remaining Exprs: ",
	d_exprSet.size(), flush);

  FatalAssert(d_nullExpr.isNull(), "ExprManager::clear()");

  // Set class-local Exprs to Null
  d_bool = Expr();
  d_false = Expr();
  d_true = Expr();

  // Save all the pointers, clear the hash set, then free the
  // pointers.  Erasing one pointer at a time requires rehashing,
  // which will segfault if some pointers are already deleted.
  vector<ExprValue*> exprs;
  exprs.reserve(d_exprSet.size());
  TRACE_MSG("delete", "clear:() collecting exprs { ");
  IF_DEBUG(int n(0);)
  for(ExprValueSet::iterator i=d_exprSet.begin(), iend=d_exprSet.end();
      i!=iend; ++i) {
    TRACE("delete", "expr[", n++, "]");
    exprs.push_back(*i);
  }
  TRACE_MSG("delete", "clear(): finished collecting exprs }");
  d_exprSet.clear();
  TRACE_MSG("delete", "clear(): deleting exprs { ");
  for(vector<ExprValue*>::iterator i=exprs.begin(), iend=exprs.end();
      i!=iend; ++i) {
    ExprValue *pExpr= *i;
    size_t tp(pExpr->getMMIndex()); // which memory manager to use
    delete (pExpr);
    d_mm[tp]->deleteData(pExpr);
  }
  TRACE_MSG("delete", "clear(): finished deleting exprs }");

}


bool ExprManager::isActive() { return !d_disableGC; }


// Garbage collect the ExprValue pointer
void ExprManager::gc(ExprValue* ev) {
  if(!d_disableGC) {
    d_exprSet.erase(ev);
    if (d_inGC) d_pending.push_back(ev);
    else if (d_postponeGC) d_postponed.push_back(ev);
    else {
      IF_DEBUG(FatalAssert(d_pending.size() == 0, "Expected size 1");)
      d_inGC = true;
      size_t tp = ev->getMMIndex();
      delete ev;
      d_mm[tp]->deleteData(ev);
      while (d_pending.size() > 0) {
        ev = d_pending.front();
        d_pending.pop_front();
        tp = ev->getMMIndex();
        delete ev;
        d_mm[tp]->deleteData(ev);
      }
      d_inGC = false;
    }
  }
}

void
ExprManager::resumeGC() {
  d_postponeGC = false;
  while(d_postponed.size()>0) {
    ExprValue* ev = d_postponed.back();
    size_t tp(ev->getMMIndex());
    d_postponed.pop_back();
    delete ev;
    d_mm[tp]->deleteData(ev);
  }
}


// Rebuild the Expr with this ExprManager if it belongs to another
// ExprManager
Expr ExprManager::rebuild(const Expr& e) {
  //  TRACE("expr", "rebuild(", e, ") {");
  // Shouldn't rebuild a Null Expr (it's a bug)
  DebugAssert(!e.isNull(), "ExprManager::rebuild called on Null Expr");
  // Both ExprManagers must be active
  DebugAssert(isActive() && e.getEM()->isActive(),
	      "ExprManager::rebuild is called on inactive ExprManager");
  // If e has the same ExprManager, no rebuilding is necessary
  if(e.isNull() || (e.getEM() == this)) {
    //    TRACE_MSG("expr", "rebuild (same EM) => }");
    return e;
  }
  // Gotta rebuild
  DebugAssert(!d_inRebuild, "ExprManager::rebuild()");
  IF_DEBUG(ScopeWatcher sw(&d_inRebuild);)
  // First, clear the cache
  if(d_rebuildCache.size() > 0) d_rebuildCache.clear();
  Expr res = rebuildRec(e);
  // Leave no trail behind (free up Exprs)
  if(d_rebuildCache.size() > 0) d_rebuildCache.clear();
  //  TRACE("expr", "rebuild => ", e, " }");
  return res;
}


Expr ExprManager::rebuildRec(const Expr& e) {
  DebugAssert(d_inRebuild, "ExprManager::rebuildRec("+e.toString()+")");
  // Check cache
  ExprHashMap<Expr>::iterator j=d_rebuildCache.find(e),
    jend=d_rebuildCache.end();
  if(j!=jend) return (*j).second;

  ExprValue* ev = e.d_expr->rebuild(this);
  // Uniquify the pointer
  ExprValueSet::iterator i(d_exprSet.find(ev)), iend(d_exprSet.end());
  if(i != iend) {
    MemoryManager* mm = getMM(ev->getMMIndex());
    delete ev;
    mm->deleteData(ev);
    ev = *i;
  } else {
    ev->setIndex(nextIndex());
    d_exprSet.insert(ev);
  }
  // Use non-uniquifying Expr() constructor
  Expr res(ev);
  // Cache the result
  d_rebuildCache[e] = res;

  // Rebuild the type too
  Type t;
  if (!e.d_expr->d_type.isNull()) {
    t = Type(rebuildRec(e.d_expr->d_type.getExpr()));
    if (ev->d_type.isNull()) ev->d_type = t;
    if (ev->d_type != t) {
      throw Exception("Types don't match in rebuildRec");
    }
  }
  return res;
}


ExprValue* ExprManager::newExprValue(ExprValue* ev) {
  DebugAssert(isActive(), "ExprManager::newExprValue(ExprValue*)");
  ExprValueSet::iterator i(d_exprSet.find(ev)), iend(d_exprSet.end());
  if(i != iend) return (*i);
  // No such ExprValue.  Create a clean copy, insert it into the set
  // and return the new pointer.
  ExprValue* p_ev = ev->copy(this, nextIndex());
  d_exprSet.insert(p_ev);
  return p_ev;
}


// ExprValue* ExprManager::newExprValue(const Expr& op,
// 				     const vector<Expr>& kids) {
//   // Check if op and kids have the same ExprManager
//   DebugAssert(isActive(), "ExprManager::newExprValue(op, kids)");
//   DebugAssert(this == op.getEM(),
// 	      "ExprManager::newExprValue(op, kids): op is from a wrong "
// 	      "ExprManager/ValidityChecker, call importExpr() first:\n"
// 	      +op.toString());
//   IF_DEBUG(
//     for(vector<Expr>::const_iterator i=kids.begin(), iend=kids.end();
// 	i!=iend; ++i)
//       DebugAssert(!i->isNull() && (i->getEM() == this),
// 		  "ExprManager::newExprValue(op, kids): the child is"
// 		  " from a wrong instance of ExprManager/ValidityChecker,"
// 		  "call importExpr() first:\n"
// 		  +i->toString());
//     )
//   ExprValue* res = op.d_expr->copy(this, kids);
//   ExprValueSet::iterator i(d_exprSet.find(res)), iend(d_exprSet.end());
//   if(i != iend) {
//     MemoryManager* mm = getMM(res->getMMIndex());
//     delete res;
//     mm->deleteData(res);
//     return (*i);
//   } else {
//     res->setIndex(nextIndex());
//     installExprValue(res);
//     return res;
//   }
// }


//! Set initial indentation.  Returns the previous permanent value.
int
ExprManager::indent(int n, bool permanent) {
  int ret(d_indent);
  d_indentTransient = n;
  if(permanent) d_indent = n;
  return ret;
}

//! Increment the current transient indentation by n
/*! If the second argument is true, sets the result as permanent.
  \return previous permanent value. */
int
ExprManager::incIndent(int n, bool permanent) {
  int ret(d_indent);
  d_indentTransient += n;
  if(permanent) d_indent = d_indentTransient;
  return ret;
}

// Various options
InputLanguage
ExprManager::getInputLang() const {
  return getLanguage(*d_inputLang);
}


InputLanguage
ExprManager::getOutputLang() const {
  const std::string* langPtr
    = (*d_outputLang == "")? d_inputLang : d_outputLang;
  return getLanguage(*langPtr);
}


void ExprManager::newKind(int kind, const string &name, bool isType) {
  if(d_kindMap.count(kind) == 0) {
    d_kindMap[kind] = name;
    if(isType) d_typeKinds.insert(kind);
  }
  else if(d_kindMap[kind] != name) {
    DebugAssert(false, "CVC3::ExprManager::newKind(kind = "
		+ int2string(kind) + ", name = " + name
		+ "): \n" +
		"this kind is already registered with a different name: "
		+ d_kindMap[kind]);
  }
  if(d_kindMapByName.count(name) == 0)
    d_kindMapByName[name] = kind;
  else if(d_kindMapByName[name] != kind) {
    DebugAssert(false, "CVC3::ExprManager::newKind(kind = "
		+ int2string(kind) + ", name = " + name
		+ "): \n" +
		"this kind name is already registered with a different index: "
		+ int2string(d_kindMapByName[name]));
  }
}

// Register a printer
void ExprManager::registerPrettyPrinter(PrettyPrinter& printer) {
  DebugAssert(d_prettyPrinter==NULL, "ExprManager:registerPrettyPrinter():"
	      " printer is already registered");
  d_prettyPrinter = &printer;
}

// Unregister a printer
void ExprManager::unregisterPrettyPrinter() {
  FatalAssert(d_prettyPrinter!=NULL, "ExprManager:unregisterPrettyPrinter():"
	      " printer is not registered");
  d_prettyPrinter = NULL;
}


const string& ExprManager::getKindName(int kind) {
  DebugAssert(d_kindMap.count(kind) > 0,
	      ("CVC3::ExprManager::getKindName(kind = "
	       + int2string(kind) + "): kind is not registered.").c_str());
  return d_kindMap[kind];
}

int ExprManager::getKind(const string& name) {
  std::hash_map<std::string, int, HashString>::iterator
    i=d_kindMapByName.find(name),
    iend=d_kindMapByName.end();
  if(i==iend) return NULL_KIND;
  else return (*i).second;
}


size_t ExprManager::registerSubclass(size_t sizeOfSubclass) {
  size_t idx(d_mm.size());
  if(d_mmFlag == "chunks")
    d_mm.push_back(new MemoryManagerChunks(sizeOfSubclass));
  else
    d_mm.push_back(new MemoryManagerMalloc());

  FatalAssert(d_mm.back() != NULL, "Out of memory");
  return idx;
}


unsigned long ExprManager::getMemory(int verbosity)
{
  unsigned long memSelf = sizeof(ExprManager);
  unsigned long mem = 0;

  //  mem += MemoryTracker::getHashMap(verbosity - 1, d_kindMap);

//   mem += d_typeKinds.getMemory(verbosity - 1);
//   mem += d_kindMapByName.getMemory(verbosity - 1);
//   mem += d_prettyPrinter->getMemory(verbosity - 1);
  mem += MemoryTracker::getString(verbosity - 1, d_mmFlag);

//   mem += d_exprSet.getMemory(verbosity - 1);
//  mem += getMemoryVec(d_mm);
//   for (i = 0; i < d_mm.size(); ++i) {
//     mem += d_mm->getMemory(verbosity - 1);
//   }

//   mem += d_pointerHash.getMemory(verbosity - 1) - sizeof(hash<void*>);

//  mem += getMemoryVec(d_emptyVec);
  //  mem += getMemoryVec(d_postponed);
//   mem += d_rebuildCache.getMemory(verbosity - 1) - sizeof(ExprHashMap<Expr>);

//   mem += d_typecomputer->getMemory(verbosity - 1);

  MemoryTracker::print("ExprManager", verbosity, memSelf, mem);

  return mem + memSelf;
}


void ExprManager::computeType(const Expr& e) {
  DebugAssert(d_typeComputer, "No type computer installed");
  d_typeComputer->computeType(e);
  DebugAssert(!e.getType().getExpr().isNull(), "Type not set by computeType");
}


void ExprManager::checkType(const Expr& e) {
  DebugAssert(d_typeComputer, "No type computer installed");
  if (!e.isValidType()) d_typeComputer->checkType(e);
  DebugAssert(e.isValidType(), "Type not checked by checkType");
}


Cardinality ExprManager::finiteTypeInfo(Expr& e,
                                        Unsigned& n,
                                        bool enumerate,
                                        bool computeSize)
{
  DebugAssert(d_typeComputer, "No type computer installed");
  return d_typeComputer->finiteTypeInfo(e, n, enumerate, computeSize);
}


// Kind registration macro
#define REG(k) em.newKind(k, #k)
#define REG_TYPE(k) em.newKind(k, #k, true)

static void registerKinds(ExprManager& em) {
  // Register type kinds
  em.newKind(BOOLEAN, "_BOOLEAN", true);
  //  REG(TUPLE_TYPE);
  em.newKind(ANY_TYPE, "_ANY_TYPE", true);
  em.newKind(ARROW, "_ARROW", true);
  em.newKind(TYPE, "_TYPE", true);
  em.newKind(TYPEDECL, "_TYPEDECL", true);
  em.newKind(TYPEDEF, "_TYPEDEF", true);
  em.newKind(SUBTYPE, "_SUBTYPE", true);

  // Register expression (non-type) kinds
  em.newKind(NULL_KIND, "_NULL_KIND");

  em.newKind(RAW_LIST, "_RAW_LIST");
  em.newKind(STRING_EXPR, "_STRING_EXPR");
  em.newKind(RATIONAL_EXPR, "_RATIONAL_EXPR");
  em.newKind(TRUE_EXPR, "_TRUE_EXPR");
  em.newKind(FALSE_EXPR, "_FALSE_EXPR");

  em.newKind(EQ, "_EQ");
  em.newKind(NEQ, "_NEQ");
  em.newKind(DISTINCT, "_DISTINCT");

  em.newKind(NOT, "_NOT");
  em.newKind(AND, "_AND");
  em.newKind(OR, "_OR");
  em.newKind(XOR, "_XOR");
  em.newKind(IFF, "_IFF");
  em.newKind(IMPLIES, "_IMPLIES");

  em.newKind(AND_R, "_AND_R");
  em.newKind(IFF_R, "_IFF_R");
  em.newKind(ITE_R, "_ITE_R");

  em.newKind(ITE, "_ITE");

  em.newKind(FORALL, "_FORALL");
  em.newKind(EXISTS, "_EXISTS");

  em.newKind(UFUNC, "_UFUNC");
  em.newKind(APPLY, "_APPLY");

  em.newKind(ASSERT, "_ASSERT");
  em.newKind(QUERY, "_QUERY");
  em.newKind(CHECKSAT, "_CHECKSAT");
  em.newKind(CONTINUE, "_CONTINUE");
  em.newKind(RESTART, "_RESTART");
  em.newKind(DBG, "_DBG");
  em.newKind(TRACE, "_TRACE");
  em.newKind(UNTRACE, "_UNTRACE");
  em.newKind(OPTION, "_OPTION");
  em.newKind(HELP, "_HELP");
  em.newKind(TRANSFORM, "_TRANSFORM");
  em.newKind(PRINT, "_PRINT");
  em.newKind(CALL, "_CALL");
  em.newKind(ECHO, "_ECHO");
  em.newKind(INCLUDE, "_INCLUDE");
  em.newKind(DUMP_PROOF, "_DUMP_PROOF");
  em.newKind(DUMP_ASSUMPTIONS, "_DUMP_ASSUMPTIONS");
  em.newKind(DUMP_SIG, "_DUMP_SIG");
  em.newKind(DUMP_TCC, "_DUMP_TCC");
  em.newKind(DUMP_TCC_ASSUMPTIONS, "_DUMP_TCC_ASSUMPTIONS");
  em.newKind(DUMP_TCC_PROOF, "_DUMP_TCC_PROOF");
  em.newKind(DUMP_CLOSURE, "_DUMP_CLOSURE");
  em.newKind(DUMP_CLOSURE_PROOF, "_DUMP_CLOSURE_PROOF");
  em.newKind(WHERE, "_WHERE");
  em.newKind(ASSERTIONS, "_ASSERTIONS");
  em.newKind(ASSUMPTIONS, "_ASSUMPTIONS");
  em.newKind(COUNTEREXAMPLE, "_COUNTEREXAMPLE");
  em.newKind(COUNTERMODEL, "_COUNTERMODEL");
  em.newKind(PUSH, "_PUSH");
  em.newKind(POP, "_POP");
  em.newKind(POPTO, "_POPTO");
  em.newKind(PUSH_SCOPE, "_PUSH_SCOPE");
  em.newKind(POP_SCOPE, "_POP_SCOPE");
  em.newKind(POPTO_SCOPE, "_POPTO_SCOPE");
  em.newKind(RESET, "_RESET");
  em.newKind(CONTEXT, "_CONTEXT");
  em.newKind(FORGET, "_FORGET");
  em.newKind(GET_TYPE, "_GET_TYPE");
  em.newKind(CHECK_TYPE, "_CHECK_TYPE");
  em.newKind(GET_CHILD, "_GET_CHILD");
  em.newKind(SUBSTITUTE, "_SUBSTITUTE");
  em.newKind(SEQ, "_SEQ");
  em.newKind(ARITH_VAR_ORDER, "_ARITH_VAR_ORDER");
  em.newKind(ANNOTATION, "_ANNOTATION");

  // Kinds used mostly in the parser

  em.newKind(TCC, "_TCC");
  em.newKind(ID, "_ID");
  em.newKind(VARDECL, "_VARDECL");
  em.newKind(VARDECLS, "_VARDECLS");


  em.newKind(BOUND_VAR, "_BOUND_VAR");
  em.newKind(BOUND_ID, "_BOUND_ID");

  em.newKind(SKOLEM_VAR, "_SKOLEM_VAR");
  em.newKind(THEOREM_KIND, "_THEOREM_KIND");

//   em.newKind(UPDATE, "_UPDATE");
//   em.newKind(UPDATE_SELECT, "_UPDATE_SELECT");

//   em.newKind(RECORD_TYPE, "_RECORD_TYPE");
//   em.newKind(RECORD, "_RECORD");
//   em.newKind(RECORD_SELECT, "_RECORD_SELECT");
//   em.newKind(RECORD_UPDATE, "_RECORD_UPDATE");

//   em.newKind(TUPLE, "_TUPLE");
//   em.newKind(TUPLE_SELECT, "_TUPLE_SELECT");
//   em.newKind(TUPLE_UPDATE, "_TUPLE_UPDATE");

//   em.newKind(SUBRANGE, "_SUBRANGE");

//   em.newKind(SCALARTYPE, "_SCALARTYPE");
//   em.newKind(DATATYPE, "_DATATYPE");
//   em.newKind(THISTYPE, "_THISTYPE");
//   em.newKind(CONSTRUCTOR, "_CONSTRUCTOR");
//   em.newKind(SELECTOR, "_SELECTOR");
//   em.newKind(TESTER, "_TESTER");
  //  em.newKind(DATATYPE_UPDATE, "_DATATYPE_UPDATE");

  em.newKind(IF, "_IF");
  em.newKind(IFTHEN, "_IFTHEN");
  em.newKind(ELSE, "_ELSE");
  em.newKind(COND, "_COND");

  em.newKind(LET, "_LET");
  em.newKind(LETDECLS, "_LETDECLS");
  em.newKind(LETDECL, "_LETDECL");

  em.newKind(LAMBDA, "_LAMBDA");
  em.newKind(SIMULATE, "_SIMULATE");

  em.newKind(CONST, "_CONST");
  em.newKind(VARLIST, "_VARLIST");
  em.newKind(UCONST, "_UCONST");
  em.newKind(DEFUN, "_DEFUN");

  // Arithmetic types and operators
//   em.newKind(REAL, "_REAL");
//   em.newKind(INT, "_INT");

//   em.newKind(UMINUS, "_UMINUS");
//   em.newKind(PLUS, "_PLUS");
//   em.newKind(MINUS, "_MINUS");
//   em.newKind(MULT, "_MULT");
//   em.newKind(DIVIDE, "_DIVIDE");
//   em.newKind(POW, "_POW");
//   em.newKind(INTDIV, "_INTDIV");
//   em.newKind(MOD, "_MOD");
//   em.newKind(LT, "_LT");
//   em.newKind(LE, "_LE");
//   em.newKind(GT, "_GT");
//   em.newKind(GE, "_GE");
//   em.newKind(IS_INTEGER, "_IS_INTEGER");
//   em.newKind(NEGINF, "_NEGINF");
//   em.newKind(POSINF, "_POSINF");
//   em.newKind(FLOOR, "_FLOOR");
}


void ExprManagerNotifyObj::notifyPre() {
  d_em->postponeGC();
}


void ExprManagerNotifyObj::notify() {
  d_em->resumeGC();
}
