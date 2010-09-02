/*****************************************************************************/
/*!
 * \file theory.cpp
 * 
 * Author: Clark Barrett
 * 
 * Created: Thu Jan 30 15:11:55 2003
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


#include "theory_core.h"
#include "common_proof_rules.h"
#include "typecheck_exception.h"
#include "theorem_manager.h"
#include "command_line_flags.h"


using namespace CVC3;
using namespace std;


Theory::Theory(void) : d_theoryCore(NULL) { }


Theory::Theory(TheoryCore* theoryCore, const string& name)
  : d_em(theoryCore->getEM()),
    d_theoryCore(theoryCore),
    d_commonRules(theoryCore->getTM()->getRules()),
    d_name(name), d_theoryUsed(false) {
}


Theory::~Theory(void) { }


void Theory::computeModelTerm(const Expr& e, vector<Expr>& v) {
  TRACE("model", "Theory::computeModelTerm(", e, "): is a variable");
  //  v.push_back(e);
}


Theorem Theory::simplifyOp(const Expr& e) {
  int ar = e.arity();
  if (ar > 0) {
    if (ar == 1) {
      Theorem res = d_theoryCore->simplify(e[0]);
      if (!res.isRefl()) {
        return d_commonRules->substitutivityRule(e, res);
      }
    }
    else {
      vector<Theorem> newChildrenThm;
      vector<unsigned> changed;
      for(int k = 0; k < ar; ++k) {
        // Recursively simplify the kids
        Theorem thm = d_theoryCore->simplify(e[k]);
        if (!thm.isRefl()) {
          newChildrenThm.push_back(thm);
          changed.push_back(k);
        }
      }
      if(changed.size() > 0)
        return d_commonRules->substitutivityRule(e, changed, newChildrenThm);
    }
  }
  return reflexivityRule(e);
}


Expr Theory::computeTCC(const Expr& e) {
  vector<Expr> kids;
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
    kids.push_back(getTCC(*i));
  return (kids.size() == 0) ? trueExpr() :
    (kids.size() == 1) ? kids[0] :
    d_commonRules->rewriteAnd(andExpr(kids)).getRHS();
}


void Theory::registerAtom(const Expr& e, const Theorem& thm)
{
  d_theoryCore->registerAtom(e, thm);
}


bool Theory::inconsistent()
{
  return d_theoryCore->inconsistent();
}


void Theory::setInconsistent(const Theorem& e)
{
  //  TRACE("facts assertFact", ("setInconsistent[" + getName() + "->]("), e, ")");
  //  TRACE("conflict", ("setInconsistent[" + getName() + "->]("), e, ")");
  IF_DEBUG(debugger.counter("conflicts from DPs")++;)
  d_theoryCore->setInconsistent(e);
}


void Theory::setIncomplete(const string& reason)
{
  //  TRACE("facts assertFact", "setIncomplete["+getName()+"](", reason, ")");
  d_theoryCore->setIncomplete(reason);
}


Theorem Theory::simplify(const Expr& e)
{
  //  TRACE("simplify", ("simplify[" + getName() + "->]("), e, ") {");
  Theorem res(d_theoryCore->simplify(e));
  //  TRACE("simplify", "simplify[" + getName() + "] => ", res, "}");
  return res;
}


void Theory::enqueueFact(const Theorem& e)
{
  //  TRACE("facts assertFact", ("enqueueFact[" + getName() + "->]("), e, ")");
  d_theoryCore->enqueueFact(e);
}

void Theory::enqueueSE(const Theorem& e)
{
  //  TRACE("facts assertFact", ("enqueueFact[" + getName() + "->]("), e, ")");
  d_theoryCore->enqueueSE(e);
}



void Theory::assertEqualities(const Theorem& e)
{
  d_theoryCore->assertEqualities(e);
}


void Theory::addSplitter(const Expr& e, int priority) {
  TRACE("facts assertFact", "addSplitter[" + getName() + "->](", e,
	", pri="+int2string(priority)+")");
  //  DebugAssert(simplifyExpr(e) == e, "Expected splitter to be simplified");
  DebugAssert(e.isAbsLiteral() && !e.isBoolConst(), "Expected literal");
  d_theoryCore->d_coreSatAPI->addSplitter(e, priority);
}


void Theory::addGlobalLemma(const Theorem& thm, int priority) {
  d_theoryCore->d_coreSatAPI->addLemma(thm, priority, true);
}


void Theory::assignValue(const Expr& t, const Expr& val) {
  TRACE("facts assertFact", "assignValue["+getName()+"](", t, ", "+
	val.toString()+") {");
  d_theoryCore->assignValue(t, val);
  TRACE("facts assertFact", "assignValue[", getName(), "] => }");
}


void Theory::assignValue(const Theorem& thm) {
  TRACE("facts assertFact", "assignValue["+getName()+"](", thm, ") {");
  d_theoryCore->assignValue(thm);
  TRACE("facts assertFact", "assignValue[", getName(), "] => }");
}


void Theory::registerKinds(Theory* theory, vector<int>& kinds)
{
  vector<int>::const_iterator k;
  vector<int>::const_iterator kEnd;
  for (k = kinds.begin(), kEnd = kinds.end(); k != kEnd; ++k) {
    DebugAssert(d_theoryCore->d_theoryMap.count(*k) == 0,
		"kind already registered: "+getEM()->getKindName(*k)
		+" = "+int2string(*k));
    d_theoryCore->d_theoryMap[*k] = theory;
  }
}


void Theory::unregisterKinds(Theory* theory, vector<int>& kinds)
{
  vector<int>::const_iterator k;
  vector<int>::const_iterator kEnd;
  for (k = kinds.begin(), kEnd = kinds.end(); k != kEnd; ++k) {
    DebugAssert(d_theoryCore->d_theoryMap[*k] == theory,
		"kind not registered: "+getEM()->getKindName(*k)
		+" = "+int2string(*k));
    d_theoryCore->d_theoryMap.erase(*k);
  }
}


void Theory::registerTheory(Theory* theory, vector<int>& kinds,
			    bool hasSolver)
{
  registerKinds(theory, kinds);
  unsigned i = 0;
  for (; i < d_theoryCore->d_theories.size(); ++i) {
    if (d_theoryCore->d_theories[i] == NULL) {
      d_theoryCore->d_theories[i] = theory;
      break;
    }
  }
  if (i == d_theoryCore->d_theories.size()) {
    d_theoryCore->d_theories.push_back(theory);
  }
  if (hasSolver) {
    DebugAssert(!d_theoryCore->d_solver,"Solver already registered");
    d_theoryCore->d_solver = theory;
  }
}


void Theory::unregisterTheory(Theory* theory, vector<int>& kinds,
                              bool hasSolver)
{
  unregisterKinds(theory, kinds);
  unsigned i = 0;
  for (; i < d_theoryCore->d_theories.size(); ++i) {
    if (d_theoryCore->d_theories[i] == theory) {
      d_theoryCore->d_theories[i] = NULL;
    }
  }
  if (hasSolver) {
    DebugAssert(d_theoryCore->d_solver == theory, "Solver not registered");
    d_theoryCore->d_solver = NULL;
  }
}


int Theory::getNumTheories()
{
  return d_theoryCore->d_theories.size();
}


bool Theory::hasTheory(int kind) {
  return (d_theoryCore->d_theoryMap.count(kind) > 0);
}


Theory* Theory::theoryOf(int kind)
{
  DebugAssert(d_theoryCore->d_theoryMap.count(kind) > 0,
	      "Unknown operator: " + getEM()->getKindName(kind));
  return d_theoryCore->d_theoryMap[kind];
}


Theory* Theory::theoryOf(const Type& e)
{
  const Expr& typeExpr = getBaseType(e).getExpr();
  DebugAssert(!typeExpr.isNull(),"Null type");
  int kind = typeExpr.getOpKind();
  DebugAssert(d_theoryCore->d_theoryMap.count(kind) > 0,
	      "Unknown operator: " + getEM()->getKindName(kind));
  return d_theoryCore->d_theoryMap[kind];
}


Theory* Theory::theoryOf(const Expr& e)
{
  Expr e2(e);
  while (e2.isNot() || e2.isEq()) {
    e2 = e2[0];
  }
  if (e2.isApply()) {
    return d_theoryCore->d_theoryMap[e2.getOpKind()];
  }
  if (!e2.isVar()) {
    return d_theoryCore->d_theoryMap[e2.getKind()];
  }
  // Theory of a var is determined by its *base* type, since SUBTYPE
  // may have different base types, but SUBTYPE itself belongs to
  // TheoryCore.
  const Expr& typeExpr = getBaseType(e2).getExpr();
  DebugAssert(!typeExpr.isNull(),"Null type");
  int kind = typeExpr.getOpKind();
  DebugAssert(d_theoryCore->d_theoryMap.count(kind) > 0,
	      "Unknown operator: " + getEM()->getKindName(kind));
  return d_theoryCore->d_theoryMap[kind];
}


const Theorem& Theory::findRef(const Expr& e)
{
  DebugAssert(e.hasFind(), "expected find");
  const Theorem& thm1 = e.getFind();
  if (thm1.isRefl()) return thm1;
  const Expr& e1 = thm1.getRHS();
  if (!e1.hasFind() || e1.getFind().getRHS() == e1) return thm1;
  const Theorem& thm2 = findRef(e1);
  DebugAssert(thm2.getLHS()==e1,"");
  DebugAssert(thm2.getLHS() != thm2.getRHS(),"");
  e.setFind(transitivityRule(thm1,thm2));
  return e.getFind();
}


Theorem Theory::find(const Expr& e)
{
  if (!e.hasFind()) return reflexivityRule(e);
  const Theorem& thm1 = e.getFind();
  if (thm1.isRefl()) return thm1;
  const Expr& e1 = thm1.getRHS();
  if (e1 == e || !e1.hasFind() ||
      e1.getFind().getRHS() == e1) return thm1;
  Theorem thm2 = find(e1);
  DebugAssert(thm2.getLHS()==e1,"");
  DebugAssert(thm2.getLHS() != thm2.getRHS(),"");
  thm2 = transitivityRule(thm1,thm2);
  e.setFind(thm2);
  return thm2;
}


Theorem Theory::findReduce(const Expr& e)
{
  if (e.hasFind()) return find(e);
  int ar = e.arity();
  if (ar > 0) {
    if (ar == 1) {
      Theorem res = findReduce(e[0]);
      if (!res.isRefl()) {
        return d_commonRules->substitutivityRule(e, res);
      }
    }
    else {
      vector<Theorem> newChildrenThm;
      vector<unsigned> changed;
      for(int k = 0; k < ar; ++k) {
        // Recursively reduce the kids
        Theorem thm = findReduce(e[k]);
        if (!thm.isRefl()) {
          newChildrenThm.push_back(thm);
          changed.push_back(k);
        }
      }
      if(changed.size() > 0)
        return d_commonRules->substitutivityRule(e, changed, newChildrenThm);
    }
  }
  return reflexivityRule(e);
}


bool Theory::findReduced(const Expr& e)
{
  if (e.hasFind())
    return e.getFind().getRHS() == e;
  for (Expr::iterator i = e.begin(), iend = e.end(); i != iend; ++i)
    if (!findReduced(*i)) return false;
  return true;
}


Expr Theory::getTCC(const Expr& e)
{
  if(e.isVar()) return trueExpr();
  ExprMap<Expr>::iterator itccCache = d_theoryCore->d_tccCache.find(e);
  if (itccCache != d_theoryCore->d_tccCache.end()) {
    return (*itccCache).second;
  }
  Theory* i = theoryOf(e.getKind());
  TRACE("tccs", "computeTCC["+i->getName()+"](", e, ") {");
  Expr tcc = i->computeTCC(e);
  d_theoryCore->d_tccCache[e] = tcc;
  TRACE("tccs", "computeTCC["+i->getName()+"] => ", tcc, " }");
  return tcc;
}


Type Theory::getBaseType(const Expr& e)
{
  return getBaseType(e.getType());
}


Type Theory::getBaseType(const Type& tp)
{
  const Expr& e = tp.getExpr();
  DebugAssert(!e.isNull(), "Theory::getBaseType(Type(Null))");
  // See if we have it cached
  Type res(e.lookupType());
  if(!res.isNull()) return res;

  DebugAssert(theoryOf(e) != NULL,
	      "Theory::getBaseType(): No theory for the type: "
	      +tp.toString());
  res= theoryOf(e)->computeBaseType(tp);
  e.setType(res);
  return res;
}


Expr Theory::getTypePred(const Type& t, const Expr& e)
{
  Expr pred;
  Theory *i = theoryOf(t.getExpr().getKind());
  //  TRACE("typePred", "computeTypePred["+i->getName()+"]("+t.toString()+", ", e, ") {");
  pred = i->computeTypePred(t, e);
  //  TRACE("typePred", "computeTypePred["+i->getName()+"] => ", pred, " }");
  return pred;
}


Theorem Theory::updateHelper(const Expr& e)
{
  int ar = e.arity();
  switch (ar) {
    case 0:
      break;
    case 1: {
      const Theorem& res = findRef(e[0]);
      if (res.getLHS() != res.getRHS()) {
        return d_commonRules->substitutivityRule(e, res);
      }
      break;
    }
    case 2: {
      const Theorem thm0 = findRef(e[0]);
      const Theorem thm1 = findRef(e[1]);
      if (thm0.getLHS() != thm0.getRHS() ||
          thm1.getLHS() != thm1.getRHS()) {
        return d_commonRules->substitutivityRule(e, thm0, thm1);
      }
      break;
    }
    default: {
      vector<Theorem> newChildrenThm;
      vector<unsigned> changed;
      for (int k = 0; k < ar; ++k) {
        const Theorem& thm = findRef(e[k]);
        if (thm.getLHS() != thm.getRHS()) {
          newChildrenThm.push_back(thm);
          changed.push_back(k);
        }
      }
      if (changed.size() > 0)
        return d_commonRules->substitutivityRule(e, changed, newChildrenThm);
      break;
    }
  }
  return reflexivityRule(e);
}


//! Setup a term for congruence closure (must have sig and rep attributes)
void Theory::setupCC(const Expr& e) {
  //  TRACE("facts setup", "setupCC["+getName()+"](", e, ") {");
  for (int k = 0; k < e.arity(); ++k) {
    e[k].addToNotify(this, e);
  }
  Theorem thm = reflexivityRule(e);
  e.setSig(thm);
  e.setRep(thm);
  e.setUsesCC();
  //  TRACE_MSG("facts setup", "setupCC["+getName()+"]() => }");
}


//! Update a term w.r.t. congruence closure (must be setup with setupCC())
void Theory::updateCC(const Theorem& e, const Expr& d) {
  //  TRACE("facts update", "updateCC["+getName()+"]("+e.getExpr().toString()+", ",
  //	d, ") {");
  int k, ar(d.arity());
  const Theorem& dEQdsig = d.getSig();
  if (!dEQdsig.isNull()) {
    const Expr& dsig = dEQdsig.getRHS();
    Theorem thm = updateHelper(d);
    const Expr& sigNew = thm.getRHS();
    if (sigNew == dsig) {
      //      TRACE_MSG("facts update", "updateCC["+getName()+"]() [no change] => }");
      return;
    }
    dsig.setRep(Theorem());
    const Theorem& repEQsigNew = sigNew.getRep();
    if (!repEQsigNew.isNull()) {
      d.setSig(Theorem());
      enqueueFact(transitivityRule(repEQsigNew, symmetryRule(thm)));
    }
    else if (d.getType().isBool()) {
      d.setSig(Theorem());
      enqueueFact(thm);
    }
    else {
      for (k = 0; k < ar; ++k) {
	if (sigNew[k] != dsig[k]) {
	  sigNew[k].addToNotify(this, d);
	}
      }
      d.setSig(thm);
      sigNew.setRep(thm);
      getEM()->invalidateSimpCache();
    }
  }
  //  TRACE_MSG("facts update", "updateCC["+getName()+"]() => }");
}


//! Rewrite a term w.r.t. congruence closure (must be setup with setupCC())
Theorem Theory::rewriteCC(const Expr& e) {
  const Theorem& rep = e.getRep();
  if (rep.isNull()) return reflexivityRule(e);
  else return symmetryRule(rep);
}


Expr Theory::parseExpr(const Expr& e) {
  //  TRACE("facts parseExpr", "parseExpr(", e, ") {");
  Expr res(d_theoryCore->parseExpr(e));
  //  TRACE("facts parseExpr", "parseExpr => ", res, " }");
  return res;
}


void Theory::getModelTerm(const Expr& e, vector<Expr>& v)
{
  Theory *i = theoryOf(getBaseType(e).getExpr());
  TRACE("model", "computeModelTerm["+i->getName()+"](", e, ") {");
  IF_DEBUG(unsigned size = v.size();)
  i->computeModelTerm(e, v);
  TRACE("model", "computeModelTerm[", i->getName(), "] => }");
  DebugAssert(v.size() <= size || v.back() != e, "Primitive var was pushed on "
	      "the stack in computeModelTerm["+i->getName()
	      +"]: "+e.toString());
  
}


Theorem Theory::getModelValue(const Expr& e) {
  return d_theoryCore->getModelValue(e);
}


bool Theory::isLeafIn(const Expr& e1, const Expr& e2)
{
  DebugAssert(isLeaf(e1),"Expected leaf");
  if (e1 == e2) return true;
  if (theoryOf(e2) != this) return false;
  for(Expr::iterator i=e2.begin(), iend=e2.end(); i != iend; ++i)
    if (isLeafIn(e1, *i)) return true;
  return false;
}


bool Theory::leavesAreSimp(const Expr& e)
{
  if (isLeaf(e)) {
    return !e.hasFind() || e.getFind().getRHS() == e;
  }
  for (int k = 0; k < e.arity(); ++k) {
    if (!leavesAreSimp(e[k])) return false;
  }
  return true;
}


Expr Theory::newVar(const string& name, const Type& type)
{
  DebugAssert(!type.isNull(), "Error: defining a variable of NULL type");
  Expr res = resolveID(name);
  Type t;
//   Expr res = lookupVar(name, &t);
  if (!res.isNull()) {
    t = res.getType();
    if (t != type) {
      throw TypecheckException
        ("incompatible redefinition of variable "+name+":\n "
         "already defined with type: "+t.toString()
         +"\n the new type is: "+type.toString());
    }
    return res;
  }
  // Replace TYPEDEF with its definition
  t = type;
  while(t.getExpr().getKind() == TYPEDEF) {
    DebugAssert(t.arity() == 2, "Bad TYPEDEF: "+t.toString());
    t = t[1];
  }
  if (type.isBool()) res = d_em->newSymbolExpr(name, UCONST);
  else res = getEM()->newVarExpr(name);

  // Add the variable for constructing a concrete model
  d_theoryCore->addToVarDB(res);
  // Add the new global declaration
  installID(name, res);

  if( type.isFunction() ) {
    throw Exception("newVar: expected non-function type");
  }
  if( !res.lookupType().isNull() ) {
    throw Exception("newVarExpr: redefining a variable " + name);
  }
  res.setType(type);
  return res;
}


Expr Theory::newVar(const string& name, const Type& type, const Expr& def)
{
  DebugAssert(!type.isNull(), "Error: defining a variable of NULL type");
  Type t;
  Expr res = resolveID(name);
  if (!res.isNull()) {
    throw TypecheckException
      ("Redefinition of variable "+name+":\n "
       "This variable is already defined.");
  }
  Expr v;

  // Replace TYPEDEF with its definition
  t = type;
  while(t.getExpr().getKind() == TYPEDEF) {
    DebugAssert(t.arity() == 2, "Bad TYPEDEF: "+t.toString());
    t = t[1];
  }

  // Typecheck
  if(getBaseType(def) != getBaseType(t)) {
    throw TypecheckException("Type mismatch in constant definition:\n"
			     "Constant "+name+
			     " is declared with type:\n  "
			     +t.toString()
			     +"\nBut the type of definition is\n  "
			     +def.getType().toString());
  }
  DebugAssert(t.getExpr().getKind() != ARROW,"");

  // Add the new global declaration
  installID(name, def);
  
  return def;
}


Op Theory::newFunction(const string& name, const Type& type,
                       bool computeTransClosure) {
  DebugAssert(!type.isNull(), "Error: defining a variable of NULL type");
  Expr res = resolveID(name);
  Type t;
  if (!res.isNull()) {
    t = res.getType();
    throw TypecheckException
      ("Redefinition of variable "+name+":\n "
       "already defined with type: "+t.toString()
       +"\n the new type is: "+type.toString());
  }
  res = getEM()->newSymbolExpr(name, UFUNC);
  // Replace TYPEDEF with its definition
  t = type;
  while(t.getExpr().getKind() == TYPEDEF) {
    DebugAssert(t.arity() == 2, "Bad TYPEDEF: "+t.toString());
    t = t[1];
  }
  res.setType(t);
  // Add it to the database of variables for concrete model generation
  d_theoryCore->addToVarDB(res);
  // Add the new global declaration
  installID(name, res);
  if (computeTransClosure &&
      t.isFunction() && t.arity() == 3 && t[2].isBool())
    res.setComputeTransClosure();
  return res.mkOp();
}


Op Theory::newFunction(const string& name, const Type& type,
                       const Expr& def) {
  DebugAssert(!type.isNull(), "Error: defining a variable of NULL type");
  Expr res = resolveID(name);
  Type t;
  if (!res.isNull()) {
    t = res.getType();
    throw TypecheckException
      ("Redefinition of name "+name+":\n "
       "already defined with type: "+t.toString()
       +"\n the new type is: "+type.toString());
  }

  // Add the new global declaration
  installID(name, def);
  return def.mkOp();
}


Op Theory::lookupFunction(const string& name, Type* type)
{
  Expr e = getEM()->newSymbolExpr(name, UFUNC);
  *type = e.lookupType();
  if ((*type).isNull()) return Op();
  return e.mkOp();
}


static int boundVarCount = 0;


Expr Theory::addBoundVar(const string& name, const Type& type) {
  ostringstream ss;
  ss << boundVarCount++;
  Expr v(getEM()->newBoundVarExpr(name, ss.str(), type));
  if (d_theoryCore->d_boundVarStack.size() == 0) {
    DebugAssert(d_theoryCore->d_parseCache == &d_theoryCore->d_parseCacheTop,
                "Parse cache invariant violated");
    d_theoryCore->d_parseCache = &d_theoryCore->d_parseCacheOther;
    DebugAssert(d_theoryCore->d_parseCache->empty(),
                "Expected empty cache");
  }
  else {
    DebugAssert(d_theoryCore->d_parseCache == &d_theoryCore->d_parseCacheOther,
                "Parse cache invariant violated 2");
    d_theoryCore->d_parseCache->clear();
  }
  d_theoryCore->d_boundVarStack.push_back(pair<string,Expr>(name,v));
  DebugAssert(v.getKind() != RAW_LIST, "Bound vars cannot be bound to RAW_LIST");
  hash_map<string, Expr>::iterator iBoundVarMap = d_theoryCore->d_boundVarMap.find(name);
  if (iBoundVarMap != d_theoryCore->d_boundVarMap.end()) {
    (*iBoundVarMap).second = Expr(RAW_LIST, v, (*iBoundVarMap).second);
  }
  else d_theoryCore->d_boundVarMap[name] = v;
  
  TRACE("vars", "addBoundVar("+name+", ", type, ") => "+v.toString());
  return v;
}


Expr Theory::addBoundVar(const string& name, const Type& type,
			 const Expr& def) {
  Expr res;
  // Without the type, just replace the bound variable with the definition
  if(type.isNull())
    res = def;
  else {
    // When type is given, construct (LETDECL var, def) for the typechecker
    ostringstream ss;
    ss << boundVarCount++;
    res = Expr(LETDECL,
               getEM()->newBoundVarExpr(name, ss.str(), type), def);
  }
  if (d_theoryCore->d_boundVarStack.size() == 0) {
    DebugAssert(d_theoryCore->d_parseCache == &d_theoryCore->d_parseCacheTop,
                "Parse cache invariant violated");
    d_theoryCore->d_parseCache = &d_theoryCore->d_parseCacheOther;
    DebugAssert(d_theoryCore->d_parseCache->empty(),
                "Expected empty cache");
  }
  else {
    DebugAssert(d_theoryCore->d_parseCache == &d_theoryCore->d_parseCacheOther,
                "Parse cache invariant violated 2");
    d_theoryCore->d_parseCache->clear();
  }
  d_theoryCore->d_boundVarStack.push_back(pair<string,Expr>(name,res));
  DebugAssert(res.getKind() != RAW_LIST, "Bound vars cannot be bound to RAW_LIST");
  hash_map<string,Expr>::iterator iBoundVarMap = d_theoryCore->d_boundVarMap.find(name);
  if (iBoundVarMap != d_theoryCore->d_boundVarMap.end()) {
    (*iBoundVarMap).second = Expr(RAW_LIST, res, (*iBoundVarMap).second);
  }
  else d_theoryCore->d_boundVarMap[name] = res;
  TRACE("vars", "addBoundVar("+name+", "+type.toString()+", ", def,
	") => "+res.toString());
  return res;
}


Expr Theory::lookupVar(const string& name, Type* type)
{
  Expr e = getEM()->newVarExpr(name);
  *type = e.lookupType();
//   if ((*type).isNull()) {
//     e = newApplyExpr(Op(UFUNC, e));
//     *type = e.lookupType();
    if ((*type).isNull()) return Expr();
//   }
  return e;
}


// TODO: reconcile this with parser-driven new type expressions
Type Theory::newTypeExpr(const string& name)
{
  Expr res = resolveID(name);
  if (!res.isNull()) {
    throw TypecheckException
      ("Redefinition of type variable "+name+":\n "
       "This variable is already defined.");
  }
  res = Expr(TYPEDECL, getEM()->newStringExpr(name));
  // Add the new global declaration
  installID(name, res);
  return Type(res);
}


Type Theory::lookupTypeExpr(const string& name)
{
  Expr res = resolveID(name);
  if (res.isNull() ||
      (res.getKind() != TYPEDECL && !res.isType())) {
    return Type();
  }
  return Type(res);
}


Type Theory::newSubtypeExpr(const Expr& pred, const Expr& witness)
{
  Type predTp(pred.getType());
  if(!predTp.isFunction() || predTp.arity() != 2)
    throw TypecheckException
      ("Expected unary predicate in the predicate subtype:\n\n  "
       +predTp.toString()
       +"\n\nThe predicate is:\n\n  "
       +pred.toString());
  if(!predTp[1].isBool())
    throw TypecheckException
      ("Range is not BOOLEAN in the predicate subtype:\n\n  "
       +predTp.toString()
       +"\n\nThe predicate is:\n\n  "
       +pred.toString());
  Expr p(simplifyExpr(pred));
  // Make sure that the supplied predicate is total: construct 
  // 
  //    FORALL (x: domType): getTCC(pred(x))
  //
  // This only needs to be done for LAMBDA-expressions, since
  // uninterpreted predicates are defined for all the arguments
  // of correct (exact) types.
  if (pred.isLambda() && d_theoryCore->getFlags()["tcc"].getBool()) {
    Expr quant = d_em->newClosureExpr(FORALL, p.getVars(),
                                      d_theoryCore->getTCC(p.getBody()));
    if (!d_theoryCore->d_coreSatAPI->check(quant)) {
      throw TypecheckException
        ("Subtype predicate could not be proved total in the following type:\n\n  "
         +Expr(SUBTYPE, p).toString()
         +"\n\nThe failed TCC is:\n\n  "
         +quant.toString());
    }
  }
  // We require that there exists an object of this type (otherwise there is an inherent inconsistency)
  Expr q;
  if (witness.isNull()) {
    vector<Expr> vec;
    vec.push_back(d_em->newBoundVarExpr(predTp[0]));
    q = d_em->newClosureExpr(EXISTS, vec, simplifyExpr(Expr(pred.mkOp(), vec.back())));
  }
  else {
    q = Expr(pred.mkOp(), witness);
  }
  if (!d_theoryCore->d_coreSatAPI->check(q)) {
    throw TypecheckException
      ("Unable to prove witness for subtype:\n\n  "
       +Expr(SUBTYPE, p).toString()
       +"\n\nThe failed condition is:\n\n  "
       +q.toString());
  }
  return Type(Expr(SUBTYPE, p));
}


//! Create a new type abbreviation with the given name 
Type Theory::newTypeExpr(const string& name, const Type& def)
{
  Expr res = resolveID(name);
  if (!res.isNull()) {
    throw TypecheckException
      ("Redefinition of type variable "+name+":\n "
       "This variable is already defined.");
  }
  res = def.getExpr();
  // Add the new global declaration
  installID(name, res);
  return Type(res);
}


Expr Theory::resolveID(const string& name) {
  //  TRACE("vars", "resolveID(", name, ") {");
  Expr res; // Result is Null by default
  // First, look up the bound variable stack
  hash_map<string,Expr>::iterator iBoundVarMap = d_theoryCore->d_boundVarMap.find(name);
  if (iBoundVarMap != d_theoryCore->d_boundVarMap.end()) {
    res = (*iBoundVarMap).second;
    if (res.getKind() == RAW_LIST) {
      res = res[0];
    }
  }
  else {
    // Next, check in the globals
    map<string,Expr>::iterator i=d_theoryCore->d_globals.find(name),
      iend=d_theoryCore->d_globals.end();
    if(i!=iend)
      res = i->second;
  }
  //  TRACE("vars", "resolveID => ", res, " }");
  return res;
}


void Theory::installID(const string& name, const Expr& e)
{
  DebugAssert(resolveID(name).isNull(),
              "installID called on existing identifier");
  d_theoryCore->d_globals[name] = e;
}


Theorem Theory::typePred(const Expr& e) {
  return d_theoryCore->typePred(e);
}


Theorem Theory::rewriteIte(const Expr& e)
{
  if (e[0].isTrue())
    return d_commonRules->rewriteIteTrue(e);
  if (e[0].isFalse())
    return d_commonRules->rewriteIteFalse(e);
  if (e[1] == e[2])
    return d_commonRules->rewriteIteSame(e);
  return reflexivityRule(e);
}


Theorem Theory::renameExpr(const Expr& e) {
  Theorem thm = d_commonRules->varIntroSkolem(e);
  DebugAssert(thm.isRewrite() && thm.getRHS().isSkolem(),
              "thm = "+thm.toString());
  d_theoryCore->addToVarDB(thm.getRHS());
  return thm;
}
