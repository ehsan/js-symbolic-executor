/*****************************************************************************/
/*!
 *\file datatype_theorem_producer.cpp
 *\brief TRUSTED implementation of recursive datatype rules
 *
 * Author: Clark Barrett
 *
 * Created: Mon Jan 10 15:43:39 2005
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


// This code is trusted
#define _CVC3_TRUSTED_


#include "datatype_theorem_producer.h"
#include "theory_datatype.h"
#include "theory_core.h"


using namespace std;
using namespace CVC3;


////////////////////////////////////////////////////////////////////
// TheoryDatatype: trusted method for creating DatatypeTheoremProducer
////////////////////////////////////////////////////////////////////


DatatypeProofRules*
TheoryDatatype::createProofRules() {
  return new DatatypeTheoremProducer(this);
}
  

////////////////////////////////////////////////////////////////////
// Proof rules
////////////////////////////////////////////////////////////////////


Theorem DatatypeTheoremProducer::dummyTheorem(const CDList<Theorem>& facts,
                                              const Expr& e) {
  vector<Theorem> thmVec;
  for (unsigned i = 0; i < facts.size(); ++i)
    thmVec.push_back(facts[i]);
  Assumptions a(thmVec);  
  Proof pf;
  return newTheorem(e, a, pf);
}


Theorem DatatypeTheoremProducer::rewriteSelCons(const CDList<Theorem>& facts,
                                                const Expr& e) {
  if (CHECK_PROOFS) {
    CHECK_SOUND(isSelector(e), "Selector expected");
    CHECK_SOUND(d_theoryDatatype->canCollapse(e), "Expected canCollapse");
  }
  Proof pf;
  Expr t;

  pair<Expr, unsigned> selectorInfo =
    d_theoryDatatype->getSelectorInfo(e.getOpExpr());
  if (isConstructor(e[0]) &&
      selectorInfo.first == getConstructor(e[0])) {
    t = e[0][selectorInfo.second];
  }
  else {
    Expr selTypeExpr = e.getOpExpr().getType().getExpr();
    Type type = Type(selTypeExpr[selTypeExpr.arity()-1]);
    t = d_theoryDatatype->getConstant(type);
  }

  if (withProof()) pf = newPf("rewriteSelCons", e, t);

  if (!isConstructor(e[0])) {
    vector<Theorem> thmVec;
    for (unsigned i = 0; i < facts.size(); ++i)
      thmVec.push_back(facts[i]);
    Assumptions a(thmVec);  
    return newRWTheorem(e, t, a, pf);
  }
  else {
    return newRWTheorem(e, t, Assumptions::emptyAssump(), pf);
  }
}


Theorem DatatypeTheoremProducer::rewriteTestCons(const Expr& e) {
  if (CHECK_PROOFS) {
    CHECK_SOUND(isTester(e), "Tester expected");
    CHECK_SOUND(isConstructor(e[0]), "Expected Test(Cons)");
  }
  Proof pf;
  Expr t;
  Expr cons = d_theoryDatatype->getConsForTester(e.getOpExpr());
  if (cons == getConstructor(e[0])) {
    t = d_theoryDatatype->trueExpr();
  }
  else {
    t = d_theoryDatatype->falseExpr();
  }
  if (withProof()) pf = newPf("rewriteTestCons", e, t);
  return newRWTheorem(e, t, Assumptions::emptyAssump(), pf);
}


Theorem DatatypeTheoremProducer::decompose(const Theorem& e) {
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.isRewrite(), "decompose: expected rewrite");
  }
  const Expr& lhs = e.getLHS();
  const Expr& rhs = e.getRHS();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isConstructor(lhs) && isConstructor(rhs) &&
                lhs.isApply() && rhs.isApply() &&
                lhs.getOpExpr() == rhs.getOpExpr() &&
                lhs.arity() > 0 && lhs.arity() == rhs.arity(),
                "decompose precondition violated");
  }
  Assumptions a(e);
  Proof pf;
  Expr res = lhs[0].eqExpr(rhs[0]);
  if (lhs.arity() > 1) {
    vector<Expr> args;
    args.push_back(res);
    for (int i = 1; i < lhs.arity(); ++i) {
      args.push_back(lhs[i].eqExpr(rhs[i]));
    }
    res = andExpr(args);
  }
  if (withProof()) pf = newPf("decompose", e.getProof());
  return newTheorem(res, a, pf);
}


Theorem DatatypeTheoremProducer::noCycle(const Expr& e) {
  if (CHECK_PROOFS) {
    CHECK_SOUND(isConstructor(e) && e.isApply() && e.arity() > 0,
                "noCycle: expected constructor with children");
  }
  Proof pf;

  Type t = e.getOpExpr().getType();
  t = t[t.arity()-1];
  const Op& reach = d_theoryDatatype->getReachablePredicate(t);

  vector<Expr> args;
  args.push_back(!Expr(reach, e, e));
  for (int i = 0; i < e.arity(); ++i) {
    if (isDatatype(e[i].getType()) &&
        d_theoryDatatype->getReachablePredicate(e[i].getType()) == reach)
      args.push_back(Expr(reach, e, e[i]));
  }

  if (withProof()) pf = newPf("noCycle", e);
  return newTheorem(andExpr(args), Assumptions::emptyAssump(), pf);
}
