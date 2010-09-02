/*****************************************************************************/
/*!
 * \file expr_transform.cpp
 * 
 * Author: Ying Hu, Clark Barrett
 * 
 * Created: Jun 05 2003
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


#include "expr_transform.h"
#include "theory_core.h"
#include "theory_arith.h"
#include "command_line_flags.h"
#include "core_proof_rules.h"
#include <set>


using namespace std;
using namespace CVC3;


ExprTransform::ExprTransform(TheoryCore* core)
  : d_core(core)
{
  d_commonRules = d_core->getCommonRules();  
  d_rules = d_core->getCoreRules();
}


Theorem ExprTransform::smartSimplify(const Expr& e, ExprMap<bool>& cache)
{
  ExprMap<bool>::iterator it;
  vector<Expr> operatorStack;
  vector<int> childStack;
  Expr e2;

  operatorStack.push_back(e);
  childStack.push_back(0);

  while (!operatorStack.empty()) {
    DebugAssert(operatorStack.size() == childStack.size(), "Invariant violated");
    if (childStack.back() < operatorStack.back().arity()) {
      e2 = operatorStack.back()[childStack.back()++];
      it = cache.find(e2);
      if (it != cache.end() || e2.hasFind() ||
          e2.validSimpCache() || e2.arity() == 0) continue;
      if (operatorStack.size() >= 5000) {
        smartSimplify(e2, cache);
        cache[e2] = true;
      }
      else {
        operatorStack.push_back(e2);
        childStack.push_back(0);
      }
    }
    else {
      cache[operatorStack.back()] = true;
      operatorStack.pop_back();
      childStack.pop_back();
    }
  }
  DebugAssert(childStack.empty(), "Invariant violated");
  return d_core->simplify(e);
}


Theorem ExprTransform::preprocess(const Expr& e)
{
  // Force simplifier to run
  d_core->getEM()->invalidateSimpCache();
  d_core->setInPP();
  Theorem res = d_commonRules->reflexivityRule(e);

  if (d_core->getFlags()["preprocess"].getBool()) {
    if (d_core->getFlags()["pp-pushneg"].getBool()) {
      res = pushNegation(e);
    }
    ExprMap<bool> cache;
    if (d_core->getFlags()["pp-bryant"].getBool()) {
      res = d_commonRules->transitivityRule(res, smartSimplify(res.getRHS(), cache));
      res = d_commonRules->transitivityRule(res, dobryant(res.getRHS()));
    }
    if (d_core->getFlags()["pp-care"].getBool()) {
      res = d_commonRules->transitivityRule(res, smartSimplify(res.getRHS(), cache));
      res = d_commonRules->transitivityRule(res, simplifyWithCare(res.getRHS()));
    }
    int budget = 0;
    d_budgetLimit = d_core->getFlags()["pp-budget"].getInt();
    while (budget < d_budgetLimit) {
      res = d_commonRules->transitivityRule(res, smartSimplify(res.getRHS(), cache));
      Theorem ppRes = newPP(res.getRHS(), budget);
      if (ppRes.isRefl()) break;
      res = d_commonRules->transitivityRule(res, ppRes);
      if (d_core->getFlags()["pp-care"].getBool()) {
        res = d_commonRules->transitivityRule(res, smartSimplify(res.getRHS(), cache));
        res = d_commonRules->transitivityRule(res, simplifyWithCare(res.getRHS()));
      }
    }
    res = d_commonRules->transitivityRule(res, smartSimplify(res.getRHS(), cache));
    // Make sure this call is last as it cleans up theory core
    res = d_commonRules->transitivityRule(res, d_core->callTheoryPreprocess(res.getRHS()));
  }
  d_core->clearInPP();
  return res;
}


Theorem ExprTransform::preprocess(const Theorem& thm)
{
  return d_commonRules->iffMP(thm, preprocess(thm.getExpr()));
}


// We assume that the cache is initially empty
Theorem ExprTransform::pushNegation(const Expr& e) {
  if(e.isTerm()) return d_commonRules->reflexivityRule(e);
  Theorem res(pushNegationRec(e, false));
  d_pushNegCache.clear();
  return res;
}


// Recursively descend into the expression e, keeping track of whether
// we are under even or odd number of negations ('neg' == true means
// odd, the context is "negative").

// Produce a proof of e <==> e' or !e <==> e', depending on whether
// neg is false or true, respectively.
Theorem ExprTransform::pushNegationRec(const Expr& e, bool neg) {
  TRACE("pushNegation", "pushNegationRec(", e,
	", neg=" + string(neg? "true":"false") + ") {");
  DebugAssert(!e.isTerm(), "pushNegationRec: not boolean e = "+e.toString());
  ExprMap<Theorem>::iterator i = d_pushNegCache.find(neg? !e : e);
  if(i != d_pushNegCache.end()) { // Found cached result
    TRACE("pushNegation", "pushNegationRec [cached] => ", (*i).second, "}");
    return (*i).second;
  }
  // By default, do not rewrite
  Theorem res(d_core->reflexivityRule((neg)? !e : e));
  if(neg) {
    switch(e.getKind()) {
      case TRUE_EXPR: res = d_commonRules->rewriteNotTrue(!e); break;
      case FALSE_EXPR: res = d_commonRules->rewriteNotFalse(!e); break;
      case NOT: 
        res = pushNegationRec(d_commonRules->rewriteNotNot(!e), false);
        break;
      case AND:
        res = pushNegationRec(d_rules->rewriteNotAnd(!e), false);
        break;
      case OR: 
        res = pushNegationRec(d_rules->rewriteNotOr(!e), false);
        break;
      case IMPLIES: {
        vector<Theorem> thms;
        thms.push_back(d_rules->rewriteImplies(e));
        res = pushNegationRec
          (d_commonRules->substitutivityRule(NOT, thms), true);
        break;
      }
//       case IFF:
// 	// Preserve equivalences to explore structural similarities
// 	if(e[0].getKind() == e[1].getKind())
// 	  res = d_commonRules->reflexivityRule(!e);
// 	else
// 	  res = pushNegationRec(d_commonRules->rewriteNotIff(!e), false);
//         break;
      case ITE:
        res = pushNegationRec(d_rules->rewriteNotIte(!e), false);
        break;

      // Replace LETDECL with its definition.  The
      // typechecker makes sure it's type-safe to do so.
      case LETDECL: {
        vector<Theorem> thms;
        thms.push_back(d_rules->rewriteLetDecl(e));
        res = pushNegationRec
          (d_commonRules->substitutivityRule(NOT, thms), true);
        break;
      }
      default:
        res = d_commonRules->reflexivityRule(!e);
    } // end of switch(e.getKind())
  } else { // if(!neg)
    switch(e.getKind()) {
      case NOT: res = pushNegationRec(e[0], true); break;
      case AND:
      case OR:
      case IFF:
      case ITE: {
        Op op = e.getOp();
        vector<Theorem> thms;
        for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
          thms.push_back(pushNegationRec(*i, false));
        res = d_commonRules->substitutivityRule(op, thms);
        break;
      }
      case IMPLIES:
        res = pushNegationRec(d_rules->rewriteImplies(e), false);
        break;
      case LETDECL:
        res = pushNegationRec(d_rules->rewriteLetDecl(e), false);
        break;
      default:
        res = d_commonRules->reflexivityRule(e);
    } // end of switch(e.getKind())
  }
  TRACE("pushNegation", "pushNegationRec => ", res, "}");
  d_pushNegCache[neg? !e : e] = res;
  return res;
}


Theorem ExprTransform::pushNegationRec(const Theorem& thm, bool neg) {
  DebugAssert(thm.isRewrite(), "pushNegationRec(Theorem): bad theorem: "
	      + thm.toString());
  Expr e(thm.getRHS());
  if(neg) {
    DebugAssert(e.isNot(), 
		"pushNegationRec(Theorem, neg = true): bad Theorem: "
		+ thm.toString());
    e = e[0];
  }
  return d_commonRules->transitivityRule(thm, pushNegationRec(e, neg));
}


Theorem ExprTransform::pushNegation1(const Expr& e) {
  TRACE("pushNegation1", "pushNegation1(", e, ") {");
  DebugAssert(e.isNot(), "pushNegation1("+e.toString()+")");
  Theorem res;
  switch(e[0].getKind()) {
    case TRUE_EXPR: res = d_commonRules->rewriteNotTrue(e); break;
    case FALSE_EXPR: res = d_commonRules->rewriteNotFalse(e); break;
    case NOT: 
      res = d_commonRules->rewriteNotNot(e);
      break;
    case AND:
      res = d_rules->rewriteNotAnd(e);
      break;
    case OR: 
      res = d_rules->rewriteNotOr(e);
      break;
    case IMPLIES: {
      vector<Theorem> thms;
      thms.push_back(d_rules->rewriteImplies(e[0]));
      res = d_commonRules->substitutivityRule(e.getOp(), thms);
      res = d_commonRules->transitivityRule(res, d_rules->rewriteNotOr(res.getRHS()));
      break;
    }
    case ITE:
      res = d_rules->rewriteNotIte(e);
      break;
      // Replace LETDECL with its definition.  The
      // typechecker makes sure it's type-safe to do so.
    case LETDECL: {
      vector<Theorem> thms;
      thms.push_back(d_rules->rewriteLetDecl(e[0]));
      res = d_commonRules->substitutivityRule(e.getOp(), thms);
      res = d_commonRules->transitivityRule(res, pushNegation1(res.getRHS()));
      break;
    }
    default:
      res = d_commonRules->reflexivityRule(e);
  }
  TRACE("pushNegation1", "pushNegation1 => ", res.getExpr(), " }");
  return res;
}


Theorem ExprTransform::newPP(const Expr& e, int& budget)
{
  if (!e.getType().isBool()) return d_commonRules->reflexivityRule(e);
  d_newPPCache.clear();
  Theorem thm = newPPrec(e, budget);
  //  cout << "budget = " << budget << endl;
  if (budget > d_budgetLimit ||
      thm.getRHS().getSize() > 2 * e.getSize()) {
    return d_commonRules->reflexivityRule(e);
  }
  return thm;
}


Theorem ExprTransform::specialSimplify(const Expr& e, ExprHashMap<Theorem>& cache)
{
  if (e.isAtomic()) return d_commonRules->reflexivityRule(e);

  ExprHashMap<Theorem>::iterator it = cache.find(e);
  if (it != cache.end()) return (*it).second;

  Theorem thm;
  if (e.getType().isBool()) {
    thm = d_core->simplify(e);
    if (thm.getRHS().isBoolConst()) {
      cache[e] = thm;
      return thm;
    }
  }

  thm = d_commonRules->reflexivityRule(e);

  vector<Theorem> newChildrenThm;
  vector<unsigned> changed;
  int ar = e.arity();
  for(int k = 0; k < ar; ++k) {
    // Recursively process the kids
    Theorem thm2 = specialSimplify(e[k], cache);
    if (!thm2.isRefl()) {
      newChildrenThm.push_back(thm2);
      changed.push_back(k);
    }
  }
  if(changed.size() > 0) {
    thm = d_commonRules->substitutivityRule(e, changed, newChildrenThm);
  }

  cache[e] = thm;
  return thm;
}


Theorem ExprTransform::newPPrec(const Expr& e, int& budget)
{
  DebugAssert(e.getType().isBool(), "Expected Boolean expression");
  Theorem res = d_commonRules->reflexivityRule(e);

  if (!e.containsTermITE()) return res;

  ExprMap<Theorem>::iterator i = d_newPPCache.find(e);
  if (i != d_newPPCache.end()) { // Found cached result
    res = (*i).second;
    return res;
  }

  Expr current = e;
  Expr newExpr;
  Theorem thm, thm2;

  do {

    if (budget > d_budgetLimit) break;

    ++budget;
    // Recursive case
    if (!current.isPropAtom()) {
      vector<Theorem> newChildrenThm;
      vector<unsigned> changed;
      int ar = current.arity();
      for(int k = 0; k < ar; ++k) {
        // Recursively process the kids
        thm = newPPrec(current[k], budget);
        if (!thm.isRefl()) {
          newChildrenThm.push_back(thm);
          changed.push_back(k);
        }
      }
      if(changed.size() > 0) {
        thm = d_commonRules->transitivityRule(res, d_commonRules->substitutivityRule(current, changed, newChildrenThm));
        newExpr = thm.getRHS();
        res = thm;
      }
      break;
    }

//     if (current.getSize() > 1000) {
//       break;
//     }

    // Contains Term ITEs

    thm = d_commonRules->transitivityRule(res, d_commonRules->liftOneITE(current));
    newExpr = thm.getRHS();

    if ((newExpr[0].isLiteral() || newExpr[0].isAnd())) {
      d_core->getCM()->push();
      d_core->addFact(d_commonRules->assumpRule(newExpr[0]));
      thm2 = d_core->simplify(newExpr[1]);
      thm = d_commonRules->transitivityRule(thm, d_rules->rewriteIteThen(newExpr, thm2));
      d_core->getCM()->pop();

      d_core->getCM()->push();
      d_core->addFact(d_commonRules->assumpRule(newExpr[0].negate()));

      thm2 = d_core->simplify(newExpr[2]);
      newExpr = thm.getRHS();
      thm = d_commonRules->transitivityRule(thm, d_rules->rewriteIteElse(newExpr, thm2));
      d_core->getCM()->pop();
      newExpr = thm.getRHS();
    }
    res = thm;
    current = newExpr;

  } while (current.containsTermITE());

  d_newPPCache[e] = res;
  return res;
  
}


void ExprTransform::updateQueue(ExprMap<set<Expr>* >& queue,
                                const Expr& e,
                                const set<Expr>& careSet)
{
  ExprMap<set<Expr>* >::iterator it = queue.find(e), iend = queue.end();

  if (it != iend) {

    set<Expr>* cs2 = (*it).second;
    set<Expr>* csNew = new set<Expr>;
    set_intersection(careSet.begin(), careSet.end(), cs2->begin(), cs2->end(),
                     inserter(*csNew, csNew->begin()));
    (*it).second = csNew;
    delete cs2;
  }
  else {
    queue[e] = new set<Expr>(careSet);
  }
}


Theorem ExprTransform::substitute(const Expr& e,
                                  ExprHashMap<Theorem>& substTable,
                                  ExprHashMap<Theorem>& cache)
{
  if (e.isAtomic()) return d_commonRules->reflexivityRule(e);

  // check cache

  ExprHashMap<Theorem>::iterator it = cache.find(e), iend = cache.end();
  if (it != iend) {
    return it->second;
  }

  // do substitution?

  it = substTable.find(e);
  iend = substTable.end();
  if (it != iend) {
    return d_commonRules->transitivityRule(it->second, substitute(it->second.getRHS(), substTable, cache));
  }

  Theorem res = d_commonRules->reflexivityRule(e);
  int ar = e.arity();
  if (ar > 0) {
    vector<Theorem> newChildrenThm;
    vector<unsigned> changed;
    for(int k = 0; k < ar; ++k) {
      Theorem thm = substitute(e[k], substTable, cache);
      if (!thm.isRefl()) {
        newChildrenThm.push_back(thm);
        changed.push_back(k);
      }
    }
    if(changed.size() > 0) {
      res = d_commonRules->substitutivityRule(e, changed, newChildrenThm);
    }
  }
  cache[e] = res;
  return res;
}


Theorem ExprTransform::simplifyWithCare(const Expr& e)
{
  ExprHashMap<Theorem> substTable;
  ExprMap<set<Expr>* > queue;
  ExprMap<set<Expr>* >::iterator it;
  set<Expr> cs;
  updateQueue(queue, e, cs);

  Expr v;
  bool done;
  Theorem thm;
  int i;

  while (!queue.empty()) {
    it = queue.end();
    --it;
    v = it->first;
    cs = *(it->second);
    delete it->second;
    queue.erase(v);

    if (v.isAtomic() || v.isAtomicFormula()) {

// Unfortunately, this can lead to incompleteness bugs

//       d_core->getCM()->push();
//       set<Expr>::iterator iCare = cs.begin(), iCareEnd = cs.end();
//       for (; iCare != iCareEnd; ++iCare) {
//         d_core->addFact(d_commonRules->assumpRule((*iCare)));
//       }
//       thm = d_core->simplify(v);
//       if (!thm.isRefl()) {
//         substTable[v] = d_rules->dummyTheorem(thm.getExpr());
//       }
//       d_core->getCM()->pop();
      continue;
    }

    if (false && v.isPropAtom() && d_core->theoryOf(v) == d_theoryArith &&
        d_theoryArith->leavesAreNumConst(v)) {
      Expr vNew = v;
      thm = d_commonRules->reflexivityRule(vNew);
      while (vNew.containsTermITE()) {
        thm = d_commonRules->transitivityRule(thm, d_commonRules->liftOneITE(vNew));
        DebugAssert(!thm.isRefl(), "Expected non-reflexive");
        thm = d_commonRules->transitivityRule(thm, d_rules->rewriteIteCond(thm.getRHS()));
        thm = d_commonRules->transitivityRule(thm, d_core->simplify(thm.getRHS()));
        vNew = thm.getRHS();
      }
      substTable[v] = thm;
      continue;
    }

    done = false;
    set<Expr>::iterator iCare, iCareEnd = cs.end();

    switch (v.getKind()) {
      case ITE: {
        iCare = cs.find(v[0]);
        if (iCare != iCareEnd) {
          Expr rewrite = v.getType().isBool() ? v.iffExpr(v[1]) : v.eqExpr(v[1]);
          substTable[v] = d_rules->dummyTheorem(rewrite);
          updateQueue(queue, v[1], cs);
          done = true;
          break;
        }
        else {
          iCare = cs.find(v[0].negate());
          if (iCare != iCareEnd) {
            Expr rewrite = v.getType().isBool() ? v.iffExpr(v[2]) : v.eqExpr(v[2]);
            substTable[v] = d_rules->dummyTheorem(rewrite);
            updateQueue(queue, v[2], cs);
            done = true;
            break;
          }
        }
        updateQueue(queue, v[0], cs);
        cs.insert(v[0]);
        updateQueue(queue, v[1], cs);
        cs.erase(v[0]);
        cs.insert(v[0].negate());
        updateQueue(queue, v[2], cs);
        done = true;
        break;
      }
      case AND: {
        for (i = 0; i < v.arity(); ++i) {
          iCare = cs.find(v[i].negate());
          if (iCare != iCareEnd) {
            Expr rewrite = v.iffExpr(d_core->getEM()->falseExpr());
            substTable[v] = d_rules->dummyTheorem(rewrite);
            done = true;
            break;
          }
        }
        if (done) break;

        DebugAssert(v.arity() > 1, "Expected arity > 1");
        cs.insert(v[1]);
        updateQueue(queue, v[0], cs);
        cs.erase(v[1]);
        cs.insert(v[0]);
        for (i = 1; i < v.arity(); ++i) {
          updateQueue(queue, v[i], cs);
        }
        done = true;
        break;
      }
      case OR: {
        for (i = 0; i < v.arity(); ++i) {
          iCare = cs.find(v[i]);
          if (iCare != iCareEnd) {
            Expr rewrite = v.iffExpr(d_core->getEM()->trueExpr());
            substTable[v] = d_rules->dummyTheorem(rewrite);
            done = true;
            break;
          }
        }
        if (done) break;
        DebugAssert(v.arity() > 1, "Expected arity > 1");
        cs.insert(v[1].negate());
        updateQueue(queue, v[0], cs);
        cs.erase(v[1].negate());
        cs.insert(v[0].negate());
        for (i = 1; i < v.arity(); ++i) {
          updateQueue(queue, v[i], cs);
        }
        done = true;
        break;
      }
      default:
        break;
    }

    if (done) continue;

    for (int i = 0; i < v.arity(); ++i) {
      updateQueue(queue, v[i], cs);
    }
  }
  ExprHashMap<Theorem> cache;
  return substitute(e, substTable, cache);
}

