/*****************************************************************************/
/*!
 * \file expr.cpp
 * 
 * Author: Sergey Berezin
 * 
 * Created: Thu Dec  5 11:35:55 2002
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


#include <algorithm>


#include "expr.h"
#include "pretty_printer.h"
#include "expr_stream.h"
#include "notifylist.h"
#include "exception.h"


using namespace std;


namespace CVC3 {


Expr Expr::s_null;

///////////////////////////////////////////////////////////////////////
// Class Expr methods                                                //
///////////////////////////////////////////////////////////////////////

vector<vector<Expr> > Expr::substTriggers(const ExprHashMap<Expr> & subst,
      ExprHashMap<Expr> & visited) const {
    /* Do the substitution in triggers */
    vector<vector<Expr> > vvOldTriggers(getTriggers());
    vector<vector<Expr> > vvNewTriggers;
    vector<vector<Expr> >::const_iterator i, iEnd;
    for( i = vvOldTriggers.begin(), iEnd = vvOldTriggers.end(); i != iEnd; ++i ) {
      vector<Expr> vOldTriggers(*i);
      vector<Expr> vNewTriggers;
      vector<Expr>::const_iterator j, jEnd;
      for( j = vOldTriggers.begin(), jEnd = vOldTriggers.end(); j != jEnd; ++j ) {
        vNewTriggers.push_back((*j).recursiveSubst(subst, visited));
      }
      vvNewTriggers.push_back(vNewTriggers);
    }

    return vvNewTriggers;
}

Expr Expr::recursiveSubst(const ExprHashMap<Expr>& subst,
                          ExprHashMap<Expr>& visited) const {
  // Check the cache.
  // INVARIANT: visited contains all the flagged expressions, and only those
  if(getFlag()) return visited[*this];

  ExprIndex minIndex = 0;
  for(ExprHashMap<Expr>::const_iterator i = subst.begin(),iend=subst.end();i!=iend;++i) {
    if(minIndex > (i->first).getIndex())
      minIndex = (i->first).getIndex();
  }

  Expr replaced;

  if(isClosure()) {
    const vector<Expr> & vars = getVars();
    vector<Expr> common; // Bound vars which occur in subst

    for(vector<Expr>::const_iterator i = vars.begin(), iend=vars.end();
	i!=iend; ++i) {
      if(subst.count(*i) > 0) common.push_back(*i);
    }

    if(common.size() > 0) {
      IF_DEBUG(debugger.counter("substExpr: bound var clashes")++;)
      // Reduced substitution (without the common vars)
      ExprHashMap<Expr> newSubst(subst);
      // Remove variables in "common" from the substitution
      for(vector<Expr>::iterator i=common.begin(), iend=common.end();
	  i!=iend; ++i)
	newSubst.erase(*i);

      // Clear all the caches (important!)
      visited.clear();
      clearFlags();
      visited = newSubst;

      ExprHashMap<Expr>::iterator j = newSubst.begin();
      for (; j != newSubst.end(); ++j) { // old vars bound in e
	j->first.setFlag();
      }
    
      vector<vector<Expr> > vvNewTriggers = substTriggers(newSubst,visited);

      replaced = 
	getEM()->newClosureExpr(getKind(), vars,
                                getBody().recursiveSubst(newSubst, visited),
                                vvNewTriggers);

      // Clear the flags again, as we restore the substitution
      visited.clear();
      clearFlags();
      visited = subst;
      // Restore the flags on the original substitutions
      for (ExprHashMap<Expr>::const_iterator i = subst.begin(), iend=subst.end();
	   i != iend; ++i)
	i->first.setFlag();
    } else {
      vector<vector<Expr> > vvNewTriggers = substTriggers(subst,visited);
      replaced =
        getEM()->newClosureExpr(getKind(), vars,
                                getBody().recursiveSubst(subst, visited),
                                vvNewTriggers);
    }
  } else { // Not a Closure
    int changed=0;
    vector<Expr> children;      
    for(Expr::iterator i=begin(), iend=end(); i!=iend; ++i){	
      Expr repChild = *i;
      if(repChild.getIndex() >= minIndex)
        repChild = (*i).recursiveSubst(subst, visited);
      if(repChild != *i)
        changed++;
      children.push_back(repChild);
    }
    Expr opExpr;
    if (isApply()) {
      opExpr = getOpExpr().recursiveSubst(subst, visited);
      if (opExpr != getOpExpr()) ++changed;
    }
    if(changed > 0) {
      Op op = opExpr.isNull() ? getOp() : opExpr.mkOp();
      replaced = Expr(op, children);
    }
    else replaced = *this;
  }
  visited.insert(*this, replaced);
  setFlag();
  return replaced;
}


static bool subExprRec(const Expr& e1, const Expr& e2) {
  if(e1 == e2) return true;
  if(e2.getFlag()) return false;
  // e1 is created after e2, so e1 cannot be a subexpr of e2
  if(e1 > e2) return false;
  e2.setFlag();
  bool res(false);
  for(Expr::iterator i=e2.begin(), iend=e2.end(); !res && i!=iend; ++i)
    res = subExprRec(e1, *i);
  return res;
}


bool 
Expr::subExprOf(const Expr& e) const {
  if(*this == e) return true;
  // "this" is created after e, so it cannot be e's subexpression
  if(*this > e) return false;
  clearFlags();
  return subExprRec(*this, e);
}


Expr Expr::substExpr(const vector<Expr>& oldTerms,
                     const vector<Expr>& newTerms) const
{
  DebugAssert(oldTerms.size() == newTerms.size(), "substExpr: vectors"
	      "don't match in size");
  // Catch the vacuous case
  if(oldTerms.size() == 0) return *this;

  ExprHashMap<Expr> oldToNew(10);
  clearFlags();
  for(unsigned int i=0; i<oldTerms.size(); i++) {
    oldToNew.insert(oldTerms[i], newTerms[i]);
    oldTerms[i].setFlag();
  }
  // For cache, initialized by the substitution
  ExprHashMap<Expr> visited(oldToNew);
  return recursiveSubst(oldToNew, visited);

}


Expr Expr::substExpr(const ExprHashMap<Expr>& oldToNew) const
{
  // Catch the vacuous case
  if(oldToNew.size() == 0) return *this;
  // Rebuild the map: we'll be using it as a cache
  ExprHashMap<Expr> visited(oldToNew);
  clearFlags();
  // Flag all the LHS expressions in oldToNew map.  We'll be checking
  // all flagged expressions (and only those) for substitution.
  for(ExprHashMap<Expr>::const_iterator i=oldToNew.begin(), iend=oldToNew.end();
      i!=iend; ++i) {
    (*i).first.setFlag();
  }
  return recursiveSubst(oldToNew, visited);
}



Expr Expr::substExprQuant(const vector<Expr>& oldTerms,
			  const vector<Expr>& newTerms) const
{
  //let us disable this first yeting
  //  static ExprHashMap<Expr> substCache;
  //  Expr cacheIndex = Expr(RAW_LIST, *this, Expr(RAW_LIST, newTerms));

  //  ExprHashMap<Expr>::iterator i = substCache.find(cacheIndex);
  //  if (i != substCache.end()){
  //    return i->second;
  //  }

  DebugAssert(oldTerms.size() == newTerms.size(), "substExpr: vectors"
	      "don't match in size");
  // Catch the vacuous case
  
  if(oldTerms.size() == 0) return *this;

  ExprHashMap<Expr> oldToNew(oldTerms.size());

  //  clearFlags();
  for(unsigned int i=0; i<oldTerms.size(); i++) {
    oldToNew.insert(oldTerms[i], newTerms[i]);
    //     oldTerms[i].setFlag();
  }

  // For cache, initialized by the substitution
  ExprHashMap<Expr> visited(oldToNew);
  Expr returnExpr = recursiveQuantSubst(oldToNew, visited);;

  //  substCache[cacheIndex] = returnExpr;
  //  cout<<"pushed " << cacheIndex << endl << "RET " << returnExpr << endl;

  return returnExpr;

}

Expr Expr::substExprQuant(const ExprHashMap<Expr>& oldToNew) const
{
  ExprHashMap<Expr> visited(oldToNew);
  return recursiveQuantSubst(oldToNew,visited);
}

Expr Expr::recursiveQuantSubst(const ExprHashMap<Expr>& substMap,
			       ExprHashMap<Expr>& visited) const {
  /* [chris 12/3/2009] It appears that visited is never used. */

  if (!containsBoundVar()){
    //    std::cout <<"no bound var " << *this << std::endl;
    return *this;
  }

  // Check the cache.
  // INVARIANT: visited contains all the flagged expressions, and only those
  // the above invariant is no longer true.  yeting
  
   if(getKind() == BOUND_VAR ) {
     ExprHashMap<Expr>::const_iterator find = substMap.find(*this);
     if (find != substMap.end()) {
       return find->second;
     }
/*
     //     Expr ret  = visited[*this];
     const Expr ret  = substMap[*this];
     if (!ret.isNull()){
       return ret; 
     }
*/
   }
  
   //  if(getFlag()) return visited[*this];

  // why we need this.
//   ExprIndex minIndex = 0;
//   for(ExprHashMap<Expr>::iterator i = substMap.begin(),iend=substMap.end();i!=iend;++i) {
//     if(minIndex > (i->first).getIndex())
//       minIndex = (i->first).getIndex();
//   }

  Expr replaced;

  if(isClosure()) {
    // for safety, we can wrap the following lines by if debug
  
    const vector<Expr> & vars = getVars();
//     vector<Expr> common; // Bound vars which occur in subst

//     for(vector<Expr>::const_iterator i = vars.begin(), iend=vars.end();
// 	i!=iend; ++i) {
//       if(substMap.count(*i) > 0) common.push_back(*i);
//     }

//     if(common.size() > 0) {
//       cout<<"error in quant subst" << endl;
//     } else {

      /* Perform substition on the triggers */

      vector<vector<Expr> > vvNewTriggers = substTriggers(substMap,visited);
      replaced =
        getEM()->newClosureExpr(getKind(), vars,
                                getBody().recursiveQuantSubst(substMap, visited),
                                vvNewTriggers );
//     }
  } else { // Not a Closure
    int changed=0;
    vector<Expr> children;      
    for(Expr::iterator i=begin(), iend=end(); i!=iend; ++i){	
      Expr repChild ;
      repChild = (*i).recursiveQuantSubst(substMap, visited);
      if(repChild != *i)
	changed++;
      children.push_back(repChild);
    }
    if(changed > 0)
      replaced = Expr(getOp(), children);
    else
      replaced = *this;
  }
  //  visited.insert(*this, replaced);
  //  setFlag();
  return replaced;
}




string Expr::toString() const {
  return toString(PRESENTATION_LANG);
//   if(isNull()) return "Null";
//   ostringstream ss;
//   ss << (*this);
//   return ss.str();
}

string Expr::toString(InputLanguage lang) const {
  if(isNull()) return "Null";
  ostringstream ss;
  ExprStream os(getEM());
  os.lang(lang);
  os.os(ss);
  os << (*this);
  return ss.str();
}

void Expr::print(InputLanguage lang, bool dagify) const {
  if(isNull()) {
    cout << "Null" << endl; return;
  }
  ExprStream os(getEM());
  os.lang(lang);
  os.dagFlag(dagify);
  os << *this << endl;
}


void Expr::pprint() const
{
  if(isNull()) {
    cout << "Null" << endl; return;
  }
  ExprStream os(getEM());
  os << *this << endl;
}


void Expr::pprintnodag() const
{
  if(isNull()) {
    cout << "Null" << endl; return;
  }
  ExprStream os(getEM());
  os.dagFlag(false);
  os << *this << endl;
}


void Expr::printnodag() const
{
  print(AST_LANG, false);
}


ExprStream& Expr::printAST(ExprStream& os) const {
  if(isNull()) return os << "Null" << endl;
  bool isLetDecl(getKind() == LETDECL);
  os << "(" << push;
  os << getEM()->getKindName(getKind());
  if (isApply()) {
    os << space << "{" << getOp().getExpr() << push << "}";
  }
  else if (isSymbol()) {
    os << space << "{Symbol: " << getName() << "}";
  }
  else if (isClosure()) {
    os << space << "{" << space << "(" << push;
    const vector<Expr>& vars = getVars();
    vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
    if(i!=iend) { os << *i; ++i; }
    for(; i!=iend; ++i) os << space << *i;
    os << push << ") " << pop << pop;
    os << getBody() << push << "}";
  }
  else {
    switch(getKind()) {
      case STRING_EXPR:
        DebugAssert(isString(), "Expected String");
        os << space << "{" << '"'+ getString() + '"' << "}";
        break;
      case SKOLEM_VAR:
        getExistential();
        os << space << "{SKOLEM_" << (int)getIndex() << "}";
        break;
      case RATIONAL_EXPR:
        os << space << "{" << getRational() << "}";
        break;
      case UCONST: 
        DebugAssert(isVar(), "Expected Var");
        os << space << "{" << getName() << "}";
        break;
      case BOUND_VAR:
        DebugAssert(isVar(), "Expected Var");
        os << space << "{"+getName()+"_"+getUid()+"}";
        break;
      case THEOREM_KIND:
        DebugAssert(isTheorem(), "Expected Theorem");
        os << space << "{Theorem: " << getTheorem().toString() << "}";
      default: ; // Don't do anything
    }
  }

  for(Expr::iterator i=begin(), iend=end(); i!=iend; ++i) {
    if(isLetDecl) os << nodag;
    os << space << *i;
  }
  os << push << ")";
  os.resetIndent();
  return os;
}


ExprStream& Expr::print(ExprStream& os) const {
  if(isNull()) return os << "Null" << endl;
  if (isSymbol()) return os << getName();
  switch(getKind()) {
    case TRUE_EXPR: return os << "TRUE";
    case FALSE_EXPR: return os << "FALSE";
    case NULL_KIND: return os << "Null";
    case STRING_EXPR: return os << '"'+ getString() + '"';
    case RATIONAL_EXPR: return os << getRational();
    case SKOLEM_VAR: return os << "SKOLEM_" <<  hash();
    case UCONST: return os << getName();
    case BOUND_VAR: return os << "(BOUND_VAR "+getName()+"_"+getUid()+")";
    case RAW_LIST: {
      os << "(" << push;
      bool firstTime(true);
      for(Expr::iterator i=begin(), iend=end(); i!=iend; ++i) {
        if(firstTime) firstTime = false;
        else os << space;
        os << *i;
      }
      return os << push << ")";
    }
    case FORALL:
    case EXISTS: 
      if(isQuantifier()) {
        os << "(" << push << getEM()->getKindName(getKind())
           << space << "(" << push;
        const vector<Expr>& vars = getVars();
        vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
        if(i!=iend) { os << *i; ++i; }
        for(; i!=iend; ++i) os << space << *i;
        os << push << ") " << pop << pop;
        return os << getBody() << push << ")";
      }
      // If not an internal representation of quantifiers, it'll be
      // printed as "normal" Expr with a kind and children
    case RESTART: return os << "RESTART " << (*this)[0] << ";";
    default:
      //    os << "(" << push;
      os << getEM()->getKindName(getKind());
      //    os << push << ")";
  }
  os.resetIndent();
  return os;
}


//! Set initial indentation to n.
/*! The indentation will be reset to default unless the second
    argument is true.  This setting only takes effect when printing to
    std::ostream.  When printing to ExprStream, the indentation can be
    set directly in the ExprStream. */
Expr& Expr::indent(int n, bool permanent) {
  DebugAssert(!isNull(), "Expr::indent called on Null Expr");
  getEM()->indent(n, permanent);
  return *this;
}


void Expr::addToNotify(Theory* i, const Expr& e) const {
  DebugAssert(!isNull(), "Expr::addToNotify() on Null expr");
  if(getNotify() == NULL)
    d_expr->d_notifyList = new NotifyList(getEM()->getCurrentContext());
  getNotify()->add(i, e);
}


bool Expr::containsTermITE() const
{
  if (getType().isBool()) {

    // We overload the isAtomicFlag to mean !containsTermITE for exprs
    // of Boolean type
    if (validIsAtomicFlag()) {
      return !getIsAtomicFlag();
    }

    for (int k = 0; k < arity(); ++k) {
      if ((*this)[k].containsTermITE()) {
        setIsAtomicFlag(false);
        return true;
      }
    }

    setIsAtomicFlag(true);
    return false;

  }
  else return !isAtomic();
}


bool Expr::isAtomic() const
{
  if (getType().isBool()) {
    return isBoolConst();
  }

  if (validIsAtomicFlag()) {
    return getIsAtomicFlag();
  }

  for (int k = 0; k < arity(); ++k) {
    if (!(*this)[k].isAtomic()) {
      setIsAtomicFlag(false);
      return false;
    }
  }
  setIsAtomicFlag(true);
  return true;
}


bool Expr::isAtomicFormula() const
{
  //  TRACE("isAtomic", "isAtomicFormula(", *this, ") {");
  if (!getType().isBool()) {
    //    TRACE_MSG("isAtomic", "isAtomicFormula[kid] => false }");
    return false;
  }
  switch(getKind()) {
    case FORALL: case EXISTS: case XOR:
    case NOT: case AND: case OR: case ITE: case IFF: case IMPLIES:
      //      TRACE_MSG("isAtomic", "isAtomicFormula[connective] => false }");
      return false;
  }
  for (Expr::iterator k = begin(), kend=end(); k != kend; ++k) {
    if (!(*k).isAtomic()) {
      //      TRACE_MSG("isAtomic", "isAtomicFormula[kid] => false }");
      return false;
    }
  }
  //  TRACE_MSG("isAtomic", "isAtomicFormula => true }");
  return true;
}


  // This is one of the most friequently called routines.  Make it as
  // efficient as possible.
int compare(const Expr& e1, const Expr& e2) {
  // Quick equality check (operator== is implemented independently
  // and more efficiently)
  if(e1 == e2) return 0;
    
  if(e1.d_expr == NULL) return -1;
  if(e2.d_expr == NULL) return 1;

  // Both are non-Null.  Check for constant
  bool e1c = e1.isConstant();
  if (e1c != e2.isConstant()) {
    return e1c ? -1 : 1;
  }

  // Compare the indices
  return (e1.getIndex() < e2.getIndex())? -1 : 1;
}


///////////////////////////////////////////////////////////////////////
// Class Expr::iterator methods                                      //
///////////////////////////////////////////////////////////////////////


ostream& operator<<(ostream& os, const Expr& e) {
  if(e.isNull()) return os << "Null";
  ExprStream es(e.getEM());
  es.os(os);
  es << e;
  e.getEM()->restoreIndent();
  return os;
}


// Functions from class Type


Type::Type(Expr expr) : d_expr(expr)
{
  if (expr.isNull()) return;
  expr.getEM()->checkType(expr);
}


Type Type::funType(const std::vector<Type>& typeDom, const Type& typeRan) {
  vector<Expr> tmp;
  for(vector<Type>::const_iterator i=typeDom.begin(), iend=typeDom.end();
      i!=iend; ++i)
    tmp.push_back(i->getExpr());
  tmp.push_back(typeRan.getExpr());
  return Type(Expr(ARROW, tmp));
}


} // end of namespace CVC3
