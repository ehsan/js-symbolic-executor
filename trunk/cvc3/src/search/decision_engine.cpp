/*****************************************************************************/
/*!
 * \file decision_engine.cpp
 * \brief Decision Engine
 * 
 * Author: Clark Barrett
 * 
 * Created: Sun Jul 13 22:44:55 2003
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


#include "decision_engine.h"
#include "theory_core.h"
#include "search.h"


using namespace std;
using namespace CVC3;


DecisionEngine::DecisionEngine(TheoryCore* core, SearchImplBase* se)
  : d_core(core), d_se(se),
    d_splitters(core->getCM()->getCurrentContext()),
    d_splitterCount(core->getStatistics().counter("splitters"))
{
  IF_DEBUG(d_splitters.setName("CDList[SearchEngineDefault.d_splitters]");)
}

/*****************************************************************************/
/*!
 * Function: DecisionEngine::findSplitterRec
 *
 * Author: Clark Barrett
 *
 * Created: Sun Jul 13 22:47:06 2003
 *
 * Search the expression e (depth-first) for an atomic formula.  Note that in
 * order to support the "simplify in-place" option, each sub-expression is
 * checked to see if it has a find pointer, and if it does, the find is
 * followed instead of continuing to recurse on the given expression.
 * \return a NULL expr if no atomic formula is found.
 */
/*****************************************************************************/
Expr DecisionEngine::findSplitterRec(const Expr& e)
{
  Expr best;

  if(d_visited.count(e) > 0)
    return d_visited[e];

  if (e.isTrue() || e.isFalse() || e.isAtomic()
      || !d_se->isGoodSplitter(e)) {
    d_visited[e] = best;
    return best;
  }

  if (e.isAbsAtomicFormula()) {
    d_visited[e] = e;
    return e;
  }

  ExprMap<Expr>::iterator it = d_bestByExpr.find(e);
  if (it != d_bestByExpr.end()) {
    d_visited[e] = it->second;
    return it->second;
  }

  vector<int> order(e.arity());
  int i = 0;

  if (e.isITE())
  {
    order[i++] = 0;
    order[i++] = 1;//e.getHighestKid(); // always 1 or 2
    order[i++] = 2;//3 - e.getHighestKid();
  }

  else
  {
    if (e.arity() > 0)
    {
      order[i++] = 0;//e.getHighestKid();
      for (int k = 0; k < e.arity(); ++k)
	if (k != 0)//e.getHighestKid())
	  order[i++] = k;
    }
  }

  for (int k = 0; k < e.arity(); k++)
  {
    Expr splitter =
      findSplitterRec(d_core->findExpr(e[order[k]]));
    if (!splitter.isNull() && (best.isNull() || isBetter(splitter, best)))
      best = splitter;
  }

  d_bestByExpr[e] = best;
  d_visited[e] = best;
  return best;
}


/*****************************************************************************/
/*!
 * Function: DecisionEngine::pushDecision
 *
 * Author: Clark Barrett
 *
 * Created: Sun Jul 13 22:55:16 2003
 *
 * \param splitter 
 * \param whichCase If true, increment the splitter count and assert the
 * splitter.  If false, do NOT increment the splitter count and assert the
 * negation of the splitter.  Defaults to true.
 */
/*****************************************************************************/
void DecisionEngine::pushDecision(Expr splitter, bool whichCase)
{
  string stCase = whichCase ? "TRUE" : "FALSE";
  if (whichCase) d_splitterCount++;
  d_core->getCM()->push();
  TRACE("search trace", "Asserting splitter("+stCase+"): ", splitter, "");
  TRACE("search", "Asserting splitter("+stCase+"): ", splitter, "");
  d_splitters.push_back(splitter);
  if (!whichCase)
    splitter = splitter.negate();
  Theorem thm = d_se->newIntAssumption(splitter);
  d_core->addFact(thm);
  // Search engine needs to know what original facts it derived or
  // split on, so that we don't split on them twice.  addFact() may
  // simplify these facts before calling addLiteralFact() and lose
  // this information.  There is no reason to add non-literals though,
  // as we never split on them directly.
  if(thm.getExpr().isAbsLiteral())
    d_se->addLiteralFact(thm);
}


void DecisionEngine::popDecision()
{
  d_core->getCM()->pop();
  TRACE("search trace", "Pop: scope level =", d_core->getCM()->scopeLevel(), "");
}


void DecisionEngine::popTo(int dl)
{
  d_core->getCM()->popto(dl);
  TRACE("search trace", "Popto: scope level =", d_core->getCM()->scopeLevel(), "");
}


Expr DecisionEngine::lastSplitter()
{
  return d_splitters.back();
}
