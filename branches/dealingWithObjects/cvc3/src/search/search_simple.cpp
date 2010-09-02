/*****************************************************************************/
/*!
 * \file search_simple.cpp
 * 
 * Author: Clark Barrett
 * 
 * Created: Sat Mar 29 21:59:36 2003
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

#include "search_simple.h"
#include "theory_core.h"
#include "typecheck_exception.h"
#include "search_rules.h"

#include "decision_engine_dfs.h"
//#include "decision_engine_caching.h"
//#include "decision_engine_mbtf.h"
#include "expr_transform.h"
#include "command_line_flags.h"


using namespace std;
using namespace CVC3;


QueryResult SearchSimple::checkValidRec(Theorem& thm)
{
  if (d_core->outOfResources()) return ABORT;
  TRACE_MSG("search", "checkValidRec() {");
  if (d_core->inconsistent()) {
    TRACE("search", "checkValidRec => ", d_core->inconsistentThm(),
	  " (context inconsistent) }");
    d_decisionEngine->goalSatisfied();
    thm = d_core->inconsistentThm();
    return UNSATISFIABLE;
  }

  Theorem e = d_goal.get();
  bool workingOnGoal = true;
  if (d_goal.get().getExpr().isTrue()) {
    e = d_nonLiterals.get();
    workingOnGoal = false;
  }

  Theorem simp = simplify(e);
  Expr rhs = simp.getExpr();
  if (rhs.hasFind()) {
    simp = d_commonRules->iffMP(simp, d_core->find(rhs));
    rhs = simp.getExpr();
  }

  if (workingOnGoal) d_goal.set(simp);
  else d_nonLiterals.set(simp);

  if (rhs.isFalse()) {
    TRACE("search", "checkValidRec => ", simp, " (rhs=false) }");
    d_decisionEngine->goalSatisfied();
    thm = simp;
    return UNSATISFIABLE;
  }
  else if (rhs.isTrue()) {
    if (workingOnGoal || !d_core->checkSATCore()) {
      return checkValidRec(thm);
    }
    TRACE("search", "checkValidRec => ", "Null (true)", "}");
    thm = Theorem();
    return SATISFIABLE;
  }
  Expr splitter = d_decisionEngine->findSplitter(rhs);
  DebugAssert(!splitter.isNull(), "Expected splitter");
  d_decisionEngine->pushDecision(splitter);
  QueryResult qres = checkValidRec(thm);
  if (qres == UNSATISFIABLE) {
    d_decisionEngine->popDecision();
    d_decisionEngine->pushDecision(splitter, false);
    Theorem thm2;
    qres = checkValidRec(thm2);
    if (qres == UNSATISFIABLE) {
      d_decisionEngine->popDecision();
      thm = d_rules->caseSplit(splitter, thm, thm2);
      return qres;
    }
    thm = thm2;
    return qres;
  }
  return qres;
}


SearchSimple::SearchSimple(TheoryCore* core)
  : SearchImplBase(core),
    d_name("simple"),
    d_goal(core->getCM()->getCurrentContext()),
    d_nonLiterals(core->getCM()->getCurrentContext()),
    d_simplifiedThm(core->getCM()->getCurrentContext())
{
//   if (core->getFlags()["de"].getString() == "caching")
//     d_decisionEngine = new DecisionEngineCaching(core, this);
//   else if (core->getFlags()["de"].getString() == "mbtf")
//     d_decisionEngine = new DecisionEngineMBTF(core, this);
//   else
    d_decisionEngine = new DecisionEngineDFS(core, this);

  d_goal.set(d_commonRules->trueTheorem());
  d_nonLiterals.set(d_commonRules->trueTheorem());
}


SearchSimple::~SearchSimple()
{
  delete d_decisionEngine;
}


QueryResult SearchSimple::checkValidMain(const Expr& e2)
{
  Theorem thm;

  QueryResult qres = checkValidRec(thm);

  if (qres == SATISFIABLE && d_core->incomplete()) qres = UNKNOWN;

  if (qres == SATISFIABLE) {
    DebugAssert(d_goal.get().getExpr().isTrue(),
                "checkValid: Expected true goal");
    vector<Expr> a;
    d_goal.get().getLeafAssumptions(a);
    d_lastCounterExample.clear();
    for (vector<Expr>::iterator i=a.begin(), iend=a.end(); i != iend; ++i) {
      d_lastCounterExample[*i] = true;
    }
  }
  else if (qres != UNSATISFIABLE) return qres;

  processResult(thm, e2);

  if (qres == UNSATISFIABLE) {
    TRACE_MSG("search terse", "checkValid => true}");
    TRACE("search", "checkValid => true; theorem = ", d_lastValid, "}");

    Theorem e_iff_e2(d_commonRules->iffContrapositive(d_simplifiedThm));
    d_lastValid =
      d_commonRules->iffMP(d_lastValid, d_commonRules->symmetryRule(e_iff_e2));
    d_core->getCM()->pop();
  }
  else {
    TRACE_MSG("search terse", "checkValid => false}");
    TRACE_MSG("search", "checkValid => false; }");
  }
  return qres;
}


QueryResult SearchSimple::checkValidInternal(const Expr& e)
{
  DebugAssert(d_goal.get().getExpr().isTrue(),"checkValid: Expected true goal");
  DebugAssert(d_nonLiterals.get().getExpr().isTrue(),"checkValid: Expected true nonLiterals");

  TRACE("search", "checkValid(", e, ") {");
  TRACE_MSG("search terse", "checkValid() {");

  if (!e.getType().isBool()) {
    throw TypecheckException
      ("checking validity of a non-boolean expression:\n\n  "
       + e.toString()
       + "\n\nwhich has the following type:\n\n  "
       + e.getType().toString());
  }

  // A successful query should leave the context unchanged
  d_core->getCM()->push();
  d_bottomScope = scopeLevel();

  d_simplifiedThm.set(d_core->getExprTrans()->preprocess(e.negate()));
  TRACE("search", "checkValid: simplifiedThm = ", d_simplifiedThm, "");

  const Expr& not_e2 = d_simplifiedThm.get().getRHS();
  Expr e2 = not_e2.negate();

  // Assert not_e2 if it's not already asserted
  TRACE_MSG("search terse", "checkValid: Asserting !e: ");
  TRACE("search", "checkValid: Asserting !e: ", not_e2, "");
  Theorem not_e2_thm;
  if(d_assumptions.count(not_e2) == 0) {
    not_e2_thm = newUserAssumption(not_e2);
  } else {
    not_e2_thm = d_assumptions[not_e2];
  }
  d_core->addFact(not_e2_thm);
  d_goal.set(not_e2_thm);

  return checkValidMain(e2);
}


QueryResult SearchSimple::restartInternal(const Expr& e)
{
  TRACE("search", "restart(", e, ") {");
  TRACE_MSG("search terse", "restart() {");

  if (!e.getType().isBool()) {
    throw TypecheckException
      ("argument to restart is a non-boolean expression:\n\n  "
       + e.toString()
       + "\n\nwhich has the following type:\n\n  "
       + e.getType().toString());
  }

  if (d_bottomScope == 0) {
    throw Exception("Call to restart with no current query");
  }
  d_core->getCM()->popto(d_bottomScope);

  Expr e2 = d_simplifiedThm.get().getRHS().negate();

  TRACE_MSG("search terse", "restart: Asserting e: ");
  TRACE("search", "restart: Asserting e: ", e, "");
  if(d_assumptions.count(e) == 0) {
    d_core->addFact(newUserAssumption(e));
  }

  return checkValidMain(e2);
}


void SearchSimple::addNonLiteralFact(const Theorem& thm)
{
  d_nonLiterals.set(d_commonRules->andIntro(d_nonLiterals.get(), thm));
}
