///////////////////////////////////////////////////////////////////////////////
/*!
 * \file search_fast.cpp
 *
 * Author: Mark Zavislak <zavislak@stanford.edu>
 *         Undergraduate
 *         Stanford University          
 *
 * Created: Mon Jul 21 23:52:39 UTC 2003
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
*/
///////////////////////////////////////////////////////////////////////////////

#include "search_fast.h"
#include "typecheck_exception.h"
#include "search_rules.h"
#include "command_line_flags.h"
#include "cdmap.h"
#include "decision_engine_dfs.h"
//#include "decision_engine_caching.h"
//#include "decision_engine_mbtf.h"
#include "expr_transform.h"
#include "assumptions.h"


using namespace CVC3;
using namespace std;


//! When set to true, match Chaff behavior as close as possible
#define followChaff false


void SearchEngineFast::ConflictClauseManager::setRestorePoint()
{
  TRACE("conflict clauses",
	"ConflictClauseManager::setRestorePoint(): scope=",
	    d_se->scopeLevel(), "");
  d_se->d_conflictClauseStack.push_back(new deque<ClauseOwner>());
  d_se->d_conflictClauses = d_se->d_conflictClauseStack.back();
  d_restorePoints.push_back(d_se->scopeLevel());
}


void SearchEngineFast::ConflictClauseManager::notify()
{
  if (d_restorePoints.size() > 0) {
    int scope = d_restorePoints.back();
    if (scope > d_se->scopeLevel()) {
      TRACE("conflict clauses",
	    "ConflictClauseManager::notify(): restore to scope ", scope, "");
      d_restorePoints.pop_back();
      while (d_se->d_conflictClauses->size() > 0)
        d_se->d_conflictClauses->pop_back();
      delete d_se->d_conflictClauseStack.back();
      d_se->d_conflictClauseStack.pop_back();
      d_se->d_conflictClauses = d_se->d_conflictClauseStack.back();
    }
  }
}


//! Constructor
SearchEngineFast::SearchEngineFast(TheoryCore* core)
  : SearchImplBase(core),
    d_name("fast"),
    d_unitPropCount(core->getStatistics().counter("unit propagations")),
    d_circuitPropCount(core->getStatistics().counter("circuit propagations")),
    d_conflictCount(core->getStatistics().counter("conflicts")),
    d_conflictClauseCount(core->getStatistics().counter("conflict clauses")),
    d_clauses(core->getCM()->getCurrentContext()),
    d_unreportedLits(core->getCM()->getCurrentContext()),
    d_unreportedLitsHandled(core->getCM()->getCurrentContext()),
    d_nonLiterals(core->getCM()->getCurrentContext()),
    d_nonLiteralsSaved(core->getCM()->getCurrentContext()),
    d_simplifiedThm(core->getCM()->getCurrentContext()),
    d_nonlitQueryStart(core->getCM()->getCurrentContext()),
    d_nonlitQueryEnd(core->getCM()->getCurrentContext()),
    d_clausesQueryStart(core->getCM()->getCurrentContext()),
    d_clausesQueryEnd(core->getCM()->getCurrentContext()),
    d_conflictClauseManager(core->getCM()->getCurrentContext(), this),
    d_literalSet(core->getCM()->getCurrentContext()),
    d_useEnqueueFact(false),
    d_inCheckSAT(false),
    d_litsAlive(core->getCM()->getCurrentContext()),
    d_litsMaxScorePos(0),
    d_splitterCount(0),
    d_litSortCount(0),
    d_berkminFlag(false)
{
//   if (core->getFlags()["de"].getString() == "caching")
//     d_decisionEngine = new DecisionEngineCaching(core, this);
//   else if (core->getFlags()["de"].getString() == "mbtf")
//     d_decisionEngine = new DecisionEngineMBTF(core, this);
//   else
    d_decisionEngine = new DecisionEngineDFS(core, this);

  IF_DEBUG (
    d_nonLiterals.setName("CDList[SearchEngineDefault.d_nonLiterals]");
    d_clauses.setName("CDList[SearchEngineDefault.d_clauses]");
  )

  d_conflictClauseStack.push_back(new deque<ClauseOwner>());
  d_conflictClauses = d_conflictClauseStack.back();
}

//! Destructor
/*! We own the proof rules (d_rules) and the variable manager (d_vm);
  delete them. */
SearchEngineFast::~SearchEngineFast() {
  for (unsigned i=0; i < d_circuits.size(); i++)
    delete d_circuits[i];
  delete d_decisionEngine;
  for(size_t i=0, iend=d_conflictClauseStack.size(); i<iend; ++i)
    delete d_conflictClauseStack[i];
}


/*! @brief Return a ref to the vector of watched literals.  If no
  such vector exists, create it. */
/*!  This function is normally used when the value of 'literal'
 * becomes false.  The vector contains pointers to all clauses where
 * this literal occurs, and therefore, these clauses may cause unit
 * propagation.  In any case, the watch pointers in these clauses
 * need to be updated.
 */
vector<std::pair<Clause, int> >& 
SearchEngineFast::wp(const Literal& literal) {
  // return d_wp[literal.getExpr()];
  return literal.wp();
}

#ifdef _CVC3_DEBUG_MODE
static void checkAssump(const Theorem& t, const Theorem& orig,
		 const CDMap<Expr,Theorem>& assumptions) {
  const Assumptions& a(t.getAssumptionsRef());
  const Assumptions::iterator iend = a.end();
  if(!(!t.isAssump() || assumptions.count(t.getExpr()) > 0))
    orig.printDebug();
  DebugAssert((!t.isAssump() || assumptions.count(t.getExpr()) > 0), 
	      "checkAssump: found stray theorem:\n  "
	      + t.toString());
  if(t.isAssump()) return;
  for (Assumptions::iterator i = a.begin(); i != iend; ++i) {
    if (!i->isFlagged()) {
      i->setFlag();
      // comparing only TheoremValue pointers in .find()
      checkAssump(*i, orig, assumptions);
    }
  }
}


/*! @brief Check that assumptions in the result of checkValid() are a
  subset of assertions */
/*! Only defined in the debug build. 
 * \ingroup SE_Default
 */
static void
checkAssumpDebug(const Theorem& res,
		 const CDMap<Expr,Theorem>& assumptions) {
  // FIXME: (jimz) will need to traverse graph

  if(!res.withAssumptions()) return;
  res.clearAllFlags();
  checkAssump(res, res, assumptions);
}
#endif




////////////////////////////
// New Search Engine Code //
////////////////////////////


QueryResult SearchEngineFast::checkSAT()
{
  d_inCheckSAT=true;
  QueryResult result = UNSATISFIABLE;
  if (!bcp()) { // run an initial bcp
    DebugAssert(d_factQueue.empty(), "checkSAT()");
    if (!fixConflict()) goto checkSATfinalize;
  }
  while (!d_core->outOfResources()) {
    if (split()) {   // if we were able to split successfully
      // Run BCP
      while (!bcp()) {  // while bcp finds conflicts
	DebugAssert(d_factQueue.empty(), "checkSAT()");
	d_decisionEngine->goalSatisfied();

        // Try to fix those conflicts by rolling back contexts and
        // adding new conflict clauses to help in the future.
        if (!fixConflict()) goto checkSATfinalize;
      }
    }
    // Now we couldn't find a splitter.  This may have been caused by
    // other reasons, so we allow them to be processed here.
    else {
      result = SATISFIABLE;
      break;
    }
  }
 checkSATfinalize:
  d_inCheckSAT = false;
  if (d_core->outOfResources()) result = ABORT;
  else if (result == SATISFIABLE && d_core->incomplete()) result = UNKNOWN;
  return result;
}


/* There are different heurisitics for splitters available.  We would
 * normally try to use the new generic decision class, but initially
 * we want this just to work, and so we use a custom decision class
 * that knows about this particular search engine.  We can realize
 * this same behavior using the existing mechanism by having a
 * decision subclass dynamic_cast the received SearchEngine pointer as
 * a SearchEngineFast and work from there.  However, as of this time I
 * do not plan on supporting the nextClause() and nextNonClause()
 * functionality, as they don't make much sense in this kind of modern
 * solver.  It may make more sense to have the solver and it's literal
 * splitting heuristic tightly connected, but leaving the nonLiteral
 * splitting heurisitic separate, since it is generally independent of
 * the search mechanism.
 *
 * By this point we've already guaranteed that we need to split: no
 * unit clauses, and no conflicts.  The procedure is as follows.  Ask
 * the decision engine for an expression to split on.  The decision
 * engine dutifully returns an expression.  We craft an assumption out
 * of this and assert it to the core (after making sure d_assumptions
 * has a copy).
 *
 * If no splitters are available, we still have to let the decision
 * procedures have a final chance at showing the context is
 * inconsistent by calling checkSATcore().  If we get a false out of
 * this, we have to continue processing, so the context is left
 * unchanged, no splitter is chosen, and we return true to let the
 * bcp+conflict processing have another chance.  If we get true, then
 * the problem is SAT and we are done, so we return false.
 *
 * Otherwise, we obtain the splitter, then ship it back off to the
 * decision engine for processing.
 */

bool SearchEngineFast::split()
{
  TRACE_MSG("search basic", "Choosing splitter");
  Expr splitter = findSplitter();
  if (splitter.isNull()) {
    TRACE_MSG("search basic", "No splitter");
    bool res(d_core->inconsistent() || !d_core->checkSATCore());
    if(!res) {
      d_splitterCount = 0; // Force resorting splitters next time
      res = !bcp();
    }
    return res;
  }
  Literal l(newLiteral(splitter));
  Theorem simp;
  if(l.getValue() != 0) {
    // The literal is valid at a lower scope than it has been derived,
    // and therefore, it was lost after a scope pop.  Reassert it here.
    simp = l.deriveTheorem();
    d_literals.push_back((l.getValue() == 1)? l : !l);
    d_core->addFact(simp);
    return true;
  }
  else {
    simp = d_core->simplify(splitter);
    Expr e = simp.getRHS();
    if(e.isBoolConst()) {
      IF_DEBUG(debugger.counter("splitter simplified to TRUE or FALSE")++;)
      if(e.isTrue()) simp = d_commonRules->iffTrueElim(simp);
      else {
	if(splitter.isNot())
	  simp = d_commonRules->notNotElim(d_commonRules->iffFalseElim(simp));
	else
	  simp = d_commonRules->iffFalseElim(simp);
      }
      TRACE("search full", "Simplified candidate: ", splitter.toString(), "");
      TRACE("search full", "                  to: ",
	    simp.getExpr().toString(), "");
      // Send this literal to DPs and enqueue it for BCP
      d_core->addFact(simp);
      addLiteralFact(simp);
      DebugAssert(l.getValue()!=0, "SearchFast::split(): l = "+l.toString());
      return true;
    }
  }

  TRACE("search terse", "Asserting splitter: #"
	+int2string(d_core->getStatistics().counter("splitters"))+": ",
	splitter, "");
  d_decisionEngine->pushDecision(splitter);
  return true;
}

//! Total order on literals for the initial sort
/*! Used for debugging, to match Chaff's behavior as close as possible
  and track any discrepancies or inefficiencies. */
// static bool compareInitial(const Literal& l1, const Literal& l2) {
//   Expr lit1 = l1.getVar().getExpr();
//   Expr lit2 = l2.getVar().getExpr();
//   if(lit1.hasOp() && lit2.hasOp()) {
//     int i = atoi(&(lit1.getOp().getName().c_str()[2]));
//     int j = atoi(&(lit2.getOp().getName().c_str()[2]));
//     return (i < j);
//   }
//   else
//     return (l1.score() > l2.score());
// }

//! Ordering on literals, used to sort them by score
static inline bool compareLits(const Literal& l1, 
			       const Literal& l2) 
{
  return (l1.score() > l2.score());
}

IF_DEBUG(static string lits2str(const vector<Literal>& lits) {
  ostringstream ss;
  ss << "\n[";
  for(vector<Literal>::const_iterator i=lits.begin(), iend=lits.end();
      i!=iend; ++i)
    ss << *i << "\n ";
  ss << "\n]";
  return ss.str();
})


/*!
 * Recompute the scores for all known literals.  This is a relatively
 * expensive procedure, so it should not be called too often.
 * Currently, it is called once per 100 splitters.
 */
void SearchEngineFast::updateLitScores(bool firstTime)
{
  TRACE("search literals", "updateLitScores(size=", d_litsByScores.size(),
	") {");
  unsigned count, score;

  if (firstTime && followChaff) {
    ::stable_sort(d_litsByScores.begin(), d_litsByScores.end(), compareLits);
  }

  for(size_t i=0; i< d_litsByScores.size(); ++i) {
    // Reading by value, since we'll be modifying the attributes.
    Literal lit = d_litsByScores[i];
    // First, clean up the unused literals
    while(lit.count()==0 && i+1 < d_litsByScores.size()) {
      TRACE("search literals", "Removing lit["+int2string(i)+"] = ", lit,
	    " from d_litsByScores");
      // Remove this literal from the list
      lit.added()=false;
      lit = d_litsByScores.back();
      d_litsByScores[i] = lit;
      d_litsByScores.pop_back();
    }
    // Take care of the last literal in the vector
    if(lit.count()==0 && i+1 == d_litsByScores.size()) {
      TRACE("search literals", "Removing last lit["+int2string(i)+"] = ", lit,
	    " from d_litsByScores");
      lit.added()=false;
      d_litsByScores.pop_back();
      break; // Break out of the loop -- no more literals to process
    }

    TRACE("search literals", "Updating lit["+int2string(i)+"] = ", lit, " {");

    DebugAssert(lit == d_litsByScores[i], "lit = "+lit.toString());
    DebugAssert(lit.added(), "lit = "+lit.toString());
    DebugAssert(lit.count()>0, "lit = "+lit.toString());

    count = lit.count();
    unsigned& countPrev = lit.countPrev();
    int& scoreRef = lit.score();

    score = scoreRef/2 + count - countPrev;
    scoreRef = score;
    countPrev = count;

    TRACE("search literals", "Updated lit["+int2string(i)+"] = ", lit, " }");
//     Literal neglit(!lit);

//     count = neglit.count();
//     unsigned& negcountPrev = neglit.countPrev();
//     unsigned& negscoreRef = neglit.score();

//     negscore = negscoreRef/2 + count - negcountPrev;
//     negscoreRef = negscore;
//     negcountPrev = count;

//     if(negscore > score) d_litsByScores[i] = neglit;
  }
  ::stable_sort(d_litsByScores.begin(), d_litsByScores.end(), compareLits);
  d_litsMaxScorePos = 0;
  d_litSortCount=d_litsByScores.size();
  TRACE("search splitters","updateLitScores => ", lits2str(d_litsByScores),"");
  TRACE("search literals", "updateLitScores(size=", d_litsByScores.size(),
	") => }");
}

void SearchEngineFast::updateLitCounts(const Clause& c)
{
  TRACE("search literals", "updateLitCounts(", CompactClause(c), ") {");
  for(unsigned i=0; i<c.size(); ++i) {
    // Assign by value to modify the attributes
    Literal lit = c[i];
    DebugAssert(lit.getExpr().isAbsLiteral(),"Expected literal");
    // Only add the literal if it wasn't added before.  The literal
    // counts are taken care of in Clause constructors/destructors.
//     if(!lit.added() || lit.count() != lit.countPrev())
    d_litSortCount--;
    
    if(!lit.added()) {
      TRACE("search literals", "adding literal ", lit, " to d_litsByScores");
      d_litsByScores.push_back(lit);
      lit.added()=true;
    }
  }
  if(d_litSortCount < 0) {
    ::stable_sort(d_litsByScores.begin(), d_litsByScores.end(), compareLits);
    d_litSortCount=d_litsByScores.size();
  }
  TRACE("search splitters","updateLitCounts => ", lits2str(d_litsByScores),"");
  TRACE_MSG("search literals", "updateLitCounts => }");
}

Expr SearchEngineFast::findSplitter()
{
  TRACE_MSG("splitters", "SearchEngineFast::findSplitter() {");
  Expr splitter; // Null by default
  unsigned i;

  // if we have a conflict clause, pick the one inside with the
  // best ac(z) score (from the most recent conflict clause)
  //  if (d_berkminFlag && !d_conflictClauses.empty())
  if (d_berkminFlag && !d_conflictClauses->empty())
  {
    unsigned sCount = 0;
    std::deque<ClauseOwner>::reverse_iterator foundUnsat = d_conflictClauses->rend();
    for (std::deque<ClauseOwner>::reverse_iterator i = d_conflictClauses->rbegin();
         i != d_conflictClauses->rend();
         ++i) {
      ++sCount;
      if (!((Clause)*i).sat(true)) {
        foundUnsat = i;
        break;
      }
    }
    if (foundUnsat != d_conflictClauses->rend()) {
      Clause &topClause = *foundUnsat;
      int numLits = topClause.size();
      int bestScore = 0;
      int bestLit = -1;
      unsigned numChoices = 0;
      for (int i = 0; i < numLits; ++i) {
	const Literal& lit = topClause[i];
        if (lit.getValue() != 0) continue;
        if (bestLit == -1) bestLit = i;
        ++numChoices;
        int s = lit.score();
        if (s > bestScore) {
          bestLit = i;
          bestScore = s;
        }
      }
      if (bestLit != -1) {
	splitter = topClause[bestLit].getExpr();
        IF_DEBUG(debugger.counter("BerkMin heuristic")++;)
        TRACE("splitters", "SearchEngineFast::findSplitter()[berkmin] => ",
	      splitter, " }"); 
        return splitter;
      }
    }
  } 

  /*
  // Search for DP-specific splitters
  for(CDMapOrdered<Splitter,bool>::iterator i=d_dpSplitters.begin(),
	iend=d_dpSplitters.end(); i!=iend; ++i) {
    Expr e((*i).first.expr);
    if(e.isBoolConst() || d_core->find(e).getRHS().isBoolConst())
      continue;
    return e;
  }
  */

  for (int i = d_nonLiterals.size()-1; i >= 0; --i) {
    const Expr& e = d_nonLiterals[i].get().getExpr();
    if (e.isTrue()) continue;
    //    if (d_nonLiteralSimplified[thm.getExpr()]) continue;
    DebugAssert(!e.isBoolConst(), "Expected non-bool const");
    DebugAssert(d_core->simplifyExpr(e) == e,
    		"Expected non-literal to be simplified:\n e = "
		+e.toString()+"\n simplify(e) = "
		+d_core->simplifyExpr(e).toString());
    splitter = d_decisionEngine->findSplitter(e);
    //DebugAssert(!splitter.isNull(),
    //            "findSplitter: can't find splitter in non-literal: "
    //            + e.toString());
    if (splitter.isNull()) continue;
    IF_DEBUG(debugger.counter("splitters from non-literals")++;)          
    TRACE("splitters", "SearchEngineFast::findSplitter()[non-lit] => ",
	  splitter, " }"); 
    return splitter;
  }

  // Update the scores: we are about to choose a splitter based on them
  if (d_splitterCount <= 0) {
    updateLitScores(false);
//     d_splitterCount = d_litsByScores.size();
//     if(d_splitterCount > 100)
      d_splitterCount = 0x10;
  } else
    d_splitterCount--;
  // pick splitter based on score
  for (i=d_litsMaxScorePos; i<d_litsByScores.size(); ++i) {
    const Literal& splitterLit = d_litsByScores[i];
    TRACE("search splitters", "d_litsByScores["+int2string(i)+"] = ",
	  splitterLit,"");
    //if (d_core->simplifyExpr(splitter).isBoolConst()) continue;
    if(splitterLit.getValue() != 0) continue;
    splitter = splitterLit.getExpr();
    // Skip auxiliary CNF vars
    if(!isGoodSplitter(splitter)) continue;
    d_litsMaxScorePos = i+1;
    IF_DEBUG(debugger.counter("splitters from literals")++;)
    TRACE("splitters", "d_litsMaxScorePos: ", d_litsMaxScorePos, "");
    TRACE("splitters", "SearchEngineFast::findSplitter()[lit] => ",
	  splitter, " }"); 
    return splitter;
  }
  TRACE_MSG("splitters",
	    "SearchEngineFast::findSplitter()[not found] => Null }");
  return Expr();
}


void SearchEngineFast::recordFact(const Theorem& thm)
{
  Literal l(newLiteral(thm.getExpr()));
  if(l.getValue() == 0) {
    l.setValue(thm, thm.getScope());
    IF_DEBUG(debugger.counter("recordFact adds unreported lit")++;)
    d_unreportedLits.insert(l.getExpr(),thm,thm.getScope());
  } else if (l.getValue() == 1 && l.getScope() > thm.getScope()) {
    // Cannot do this, it will trigger DebugAssert
    // l.setValue(thm,thm.getScope());
    IF_DEBUG(debugger.counter("recordFact adds unreported lit")++;)
    d_unreportedLits.insert(l.getExpr(),thm,thm.getScope());
  } else if(l.getValue() < 0) { // Contradiction, bcp will die anyway
    if(l.isNegative())
      setInconsistent(d_commonRules->contradictionRule(l.deriveTheorem(), thm));
    else
      setInconsistent(d_commonRules->contradictionRule(thm, l.deriveTheorem()));
  }
  //else if (thm.getScope() < scopeLevel())
  //  d_unreportedLits.insert(l.getExpr(),l,thm.getScope());
  
}

#ifdef _CVC3_DEBUG_MODE
void SearchEngineFast::fullCheck()
{
  for (unsigned i = 0;
       i < d_clauses.size();
       ++i) {
    if (!((Clause)d_clauses[i]).sat()) {
      bool sat = false;
      const Clause &theClause = d_clauses[i];
      unsigned numLits = theClause.size();
      unsigned numChoices = 0;
      for (unsigned j = 0; !sat && j < numLits; ++j) {
        if (theClause[j].getValue() == 0)
          ++numChoices;
        else if (theClause[j].getValue() == 1)
          sat = true;
      }
      if (sat) continue;
      if (numChoices <= 1 || !theClause.wpCheck()) {
        CVC3::debugger.getOS() << CompactClause(theClause) << endl;
        CVC3::debugger.getOS() << theClause.toString() << endl;
      }
      DebugAssert(numChoices > 1, "BCP postcondition violated: unsat or unit clause(s)");
      DebugAssert(theClause.wpCheck(), "Watchpointers broken");
    }
  }

  if (!d_conflictClauses->empty())
  {
    for (std::deque<ClauseOwner>::reverse_iterator i = d_conflictClauses->rbegin();
         i != d_conflictClauses->rend();
         ++i) {
      if (!((Clause)*i).sat()) {
        bool sat = false;
        Clause &theClause = *i;
        unsigned numLits = theClause.size();
        unsigned numChoices = 0;
        for (unsigned j = 0; !sat && j < numLits; ++j) {
           if (theClause[j].getValue() == 0)
            ++numChoices; 
           else if (theClause[j].getValue() == 1)
             sat = true;
        }
        if (sat) continue;
        if (numChoices <= 1 || !theClause.wpCheck()) {
          CVC3::debugger.getOS() << CompactClause(theClause) << endl;
          CVC3::debugger.getOS() << theClause.toString() << endl;
        }
        
        DebugAssert(numChoices > 1, "BCP postcondition violated: unsat or unit conflict clause(s)");
        DebugAssert(theClause.wpCheck(), "Watchpointers broken");
      
      }
    }
  } 
}
#endif


void SearchEngineFast::clearLiterals() {
  TRACE_MSG("search literals", "clearLiterals()");
  d_literals.clear();
}


bool SearchEngineFast::bcp()
{
  TRACE("search bcp", "bcp@"+int2string(scopeLevel())+"(#lits=",
	d_literals.size(), ") {");
  IF_DEBUG(TRACE_MSG("search bcp", "literals=[\n");
	   for(size_t i=0,iend=d_literals.size(); i<iend; i++)
	   TRACE("search bcp", "          ", d_literals[i], ",");
	   TRACE_MSG("search bcp", "]");)
  DebugAssert(d_factQueue.empty(), "bcp(): start");
  bool newInfo = true;
  /*
  CDMap<Expr,Theorem>::iterator i = d_unreportedLits.begin(),
    iend = d_unreportedLits.end();
  for (; i != iend; ++i) {
    if (d_unreportedLitsHandled[(*i).first])
      continue;
    Theorem thm((*i).second);
    Literal l(newLiteral(thm.getExpr()));
    DebugAssert(l.getValue() != -1, "Bad unreported literal: "+l.toString());
    if(l.getValue() == 0) l.setValue(thm, scopeLevel());
    IF_DEBUG(debugger.counter("re-assert unreported lits")++;)
    DebugAssert(l.getExpr().isAbsLiteral(),
                "bcp(): pushing non-literal to d_literals:\n "
                +l.getExpr().toString());
    // The literal may be set to 1, but not on the list; push it here
    // explicitly
    d_literals.push_back(l);
    //recordFact((*i).second.getTheorem());
    enqueueFact(thm);
    d_unreportedLitsHandled[(*i).first] = true;
  }
  */
  while (newInfo) {
    IF_DEBUG(debugger.counter("BCP: while(newInfo)")++;)
    TRACE_MSG("search bcp", "while(newInfo) {");
    newInfo = false;
    while(!d_core->inconsistent() && d_literals.size() > 0) {
     for(unsigned i=0; !d_core->inconsistent() && i<d_literals.size(); ++i) {
      Literal l = d_literals[i];
      TRACE("search props", "Propagating literal: [", l.toString(), "]");
      DebugAssert(l.getValue() == 1, "Bad literal is d_literals: "
                  +l.toString());
      d_litsAlive.push_back(l);
      // Use the watch pointers to find more literals to assert.  Repeat
      // until conflict.  Once conflict found, call unsatClause() to
      // assert the contradiction.
      std::vector<std::pair<Clause, int> >& wps = wp(l);
      TRACE("search props", "Appears in ", wps.size(), " clauses.");
      for(unsigned j=0; j<wps.size(); ++j) {
        const Clause& c = wps[j].first;
        int k = wps[j].second;
        DebugAssert(c.watched(k).getExpr() == (!l).getExpr(),
                    "Bad watched literal:\n l = "+l.toString()
                    +"\n c[k] = "+c.watched(k).toString());
        if(c.deleted()) { // Remove the clause from the list
          if(wps.size() > 1) {
            wps[j] = wps.back();
            --j;
          }
          wps.pop_back();
        } else if(true || !c.sat()) {
          // Call BCP to update the watch pointer
          bool wpUpdated;
          bool conflict = !propagate(c, k, wpUpdated);
          // Delete the old watch pointer from the list
          if(wpUpdated) {
            if(wps.size() > 1) {
              wps[j] = wps.back();
              --j;
            }
            wps.pop_back();
          }
          if (conflict) {
	    clearFacts();
	    DebugAssert(d_factQueue.empty(), "bcp(): conflict");
	    TRACE_MSG("search bcp", "bcp[conflict] => false }}");
            return false;
	  }
        }
      }

      vector<Circuit*>& cps = d_circuitsByExpr[l.getExpr()];
      for (vector<Circuit*>::iterator it = cps.begin(), end = cps.end();
           it < end; it++)
      {
        if (!(*it)->propagate(this)) {
	  clearFacts();
	  DebugAssert(d_factQueue.empty(), "bcp(): conflict-2");
	  TRACE_MSG("search bcp", "bcp[circuit propagate] => false }}");
          return false;
	}
      }
     }
     // Finished with BCP* (without DPs).
     clearLiterals();
     // Now, propagate the facts to DPs and repeat ((BCP*); DP) step
     if(!d_core->inconsistent()) commitFacts();
    }
    if (d_core->inconsistent()) {
      d_conflictTheorem = d_core->inconsistentThm();
      clearFacts();
      TRACE_MSG("search bcp", "bcp[DP conflict] => false }}");
      return false;
    }
    else
      TRACE("search basic", "Processed ", d_literals.size(), " propagations");
    IF_DEBUG(fullCheck();)
    clearLiterals();

    bool dfs_heuristic = (d_core->getFlags()["de"].getString() == "dfs");
    TRACE("search dfs", "DFS is ", (dfs_heuristic? "on" : "off"),
	  " (de = "+d_core->getFlags()["de"].getString()+") {");
    // When DFS heuristic is used, simplify the nonliterals only until
    // there is a completely simplified one on top of the stack, or
    // all of the non-literals are gone.  Start from the end of the
    // list (top of the stack), since that's where the splitter is
    // most likely chosen.  This way we are likely to hit something
    // that simplifies very soon.

    size_t origSize = d_nonLiterals.size();
    bool done(false);
    for(int i=origSize-1; !done && !d_core->inconsistent() && i>=0; --i) {
      const Theorem& thm = d_nonLiterals[i].get();
      const Expr& e = thm.getExpr();
      TRACE("search dfs", "Simplifying non-literal", e, "");
      if (e.isTrue()) {
        //      if (d_nonLiteralSimplified[thm.getExpr()]) {
	IF_DEBUG(debugger.counter("BCP: simplified non-literals: skipped [stale]")++;)
	TRACE_MSG("search bcp", "}[continue]// end of while(newInfo)");
	continue;
      }
      IF_DEBUG(debugger.counter("BCP: simplified non-literals")++;)
      Theorem simpThm = simplify(thm);
      Expr simp = simpThm.getExpr();
      if(simp != e) {
	IF_DEBUG(debugger.counter("BCP: simplified non-literals: changed")++;)
        newInfo = true;
        //        d_nonLiteralSimplified[thm.getExpr()] = true;
        if (!simp.isFalse()) {
          while (simp.isExists()) {
            simpThm = d_commonRules->skolemize(simpThm);
            simp = simpThm.getExpr();
          }
          if (simp.isAbsLiteral()) {
            enqueueFact(simpThm);
            commitFacts();
          }
          d_nonLiterals[i] = simpThm;
	  if(dfs_heuristic) {
	    // Something has changed, time to stop this loop.  If we
	    // also get a new non-literal on top of the stack, and no
	    // new literals, then stop the entire BCP (since that
	    // non-literal is guaranteed to be fully simplified).
	    done = true;
	    if(d_nonLiterals.size() > origSize && d_literals.empty())
	      newInfo = false;
	  }
        } else
          setInconsistent(simpThm);
      } else if (dfs_heuristic) done = true;
    }
    TRACE("search dfs", "End of non-literal simplification: newInfo = ",
	  (newInfo? "true" : "false"), " }}");
    if (d_core->inconsistent()) {
      d_conflictTheorem = d_core->inconsistentThm();
      DebugAssert(d_factQueue.empty(), "bcp(): inconsistent (nonLits)");
      TRACE_MSG("search bcp", "bcp[nonCNF conflict] => false }}");
      return false;
    }
    TRACE_MSG("search bcp", "}// end of while(newInfo)");
  }
  IF_DEBUG(fullCheck();)
  DebugAssert(d_factQueue.empty(), "bcp(): end");
  TRACE_MSG("search bcp", "bcp => true }");
  return true;
}


// True if successfully propagated.  False if conflict.
bool SearchEngineFast::propagate(const Clause &c, int idx, bool& wpUpdated)
{
  TRACE("search propagate", "propagate(", CompactClause(c),
	", idx = "+int2string(idx)+") {");
  DebugAssert(idx==0 || idx==1, "propagate(): bad index = "+int2string(idx));
  // The current watched literal must be set to FALSE, unless the
  // clause is of size 1
  DebugAssert((c.size() == 1) ||  c.watched(idx).getValue() < 0,
	      "propagate(): this literal must be FALSE: c.watched("
	      +int2string(idx)+")\n c = "+c.toString());
  wpUpdated = false;
  int lit = c.wp(idx), otherLit = c.wp(1-idx);
  int dir = c.dir(idx);
  int size = c.size();
  while(true) {
    TRACE_MSG("search propagate", "propagate: lit="+int2string(lit)
	      +", otherLit="+int2string(otherLit)+", dir="+int2string(dir));
    lit += dir;
    if(lit < 0 || lit >= size) { // hit the edge
      if(dir == c.dir(idx)) {
	// Finished first half of the clause, do the other half
	lit = c.wp(idx);
	dir = -dir;
	continue;
      }
      // All literals are false, except for the other watched literal.
      // Check its value.
      Literal l(c[otherLit]);
      if(l.getValue() < 0) { // a conflict
	//Literal ff(newLiteral(d_vcl->getEM()->falseExpr()));
	//ff.setValue(1, c, -1);
        //d_lastBCPConflict = ff;
        vector<Theorem> thms;
        for (unsigned i = 0; i < c.size(); ++i)
          thms.push_back(c[i].getTheorem());
        d_conflictTheorem = d_rules->conflictRule(thms,c.getTheorem());
	TRACE("search propagate", "propagate[", CompactClause(c),
	      "] => false }");
        return false;
      }
      else if(l.getValue() == 0) {
        DebugAssert(c.size() > 1 && l.getExpr().isAbsLiteral(), "BCP: Expr should be literal");
        d_unitPropCount++;
        c.markSat();
        // Let's prove the new literal instead of playing assumption games
        unitPropagation(c,otherLit);
        //l.setValue(1, c, otherLit);
        //d_core->addFact(createAssumption(l));
	TRACE("search propagate", "propagate[", CompactClause(c),
	      "] => true }");
        return true;
      }
      else {
        c.markSat();
	TRACE("search propagate", "propagate[", CompactClause(c),
	      "] => true }");
        return true;
      }
    }
    // If it's the other watched literal, skip it
    if(lit == otherLit) continue;

    Literal l(c[lit]);
    int val(l.getValue());
    // if it is false, keep looking
    if(val < 0) continue;
    // OPTIMIZATION: if lit is TRUE, mark the clause SAT and give up.
    // FIXME: this is different from Chaff.  Make sure it doesn't harm
    // the performance.
     if(val > 0) {
       c.markSat();
//       return true;
     }

    // Now the value of 'lit' is unknown.  Set the watch pointer to
    // this literal, if it is indeed a literal (it may be any formula
    // in a pseudo-clause), and update the direction.
    c.wp(idx, lit);
    c.dir(idx, dir);
    DebugAssert(c.watched(idx).getValue() >= 0,
		"Bad watched literals in clause:\n"
		+CompactClause(c).toString());
    // Get the expression of the literal's inverse
    Literal inv(!c[lit]);
    // If it is indeed a literal, update the watch pointers
    DebugAssert(inv.getExpr().isAbsLiteral(), "Expr should be literal: inv = "
		+inv.getExpr().toString());
    // Add the new watched literal to the watch pointer list
    pair<Clause, int> p(c, idx);
    wp(inv).push_back(p);

    // Signal to remove the old watch pointer
    wpUpdated = true;
    TRACE("search propagate", "propagate[", CompactClause(c),
	  "] => true }");
    return true;
  }
}

void SearchEngineFast::unitPropagation(const Clause &c, unsigned idx)
{  
  vector<Theorem> thms;
  for (unsigned i = 0; i < c.size(); ++i)
    if (i != idx) {
      thms.push_back(c[i].getTheorem());
      DebugAssert(!thms.back().isNull(),
		  "unitPropagation(idx = "+int2string(idx)+", i = "
		  +int2string(i)+",\n"+c.toString()+")");
    }
  Theorem thm(d_rules->unitProp(thms,c.getTheorem(),idx));
  enqueueFact(thm); // d_core->addFact(thm);
  // recordFact(thm);

  DebugAssert(thm.isAbsLiteral(),
	      "unitPropagation(): pushing non-literal to d_literals:\n "
	      +thm.getExpr().toString());
  Literal l(newLiteral(thm.getExpr()));
  DebugAssert(l.getValue() == 1, "unitPropagation: bad literal: "
	      +l.toString());
  d_literals.push_back(l);
}


bool SearchEngineFast::fixConflict()
{
  TRACE_MSG("search basic", "FixConflict");
  Theorem res, conf;
  d_conflictCount++;
  TRACE("conflicts", "found conflict # ", d_conflictCount, "");
  IF_DEBUG(if(debugger.trace("impl graph verbose")) {
    d_conflictTheorem.printDebug();
  })

  if (scopeLevel() == d_bottomScope)
    return false;
  else if(d_conflictTheorem.getScope() <= d_bottomScope) {
    d_decisionEngine->popTo(d_bottomScope);
    d_litsMaxScorePos = 0; // from decision engine
    clearLiterals();
    return false;
  }

  traceConflict(d_conflictTheorem);
  
  if (d_lastConflictScope <= d_bottomScope)
    return false;

  // If we have unit conflict clauses, then we have to bounce back to
  // the original scope and assert them.
  if(d_unitConflictClauses.size() > 0) {
    TRACE_MSG("search basic", "Found unit conflict clause");
    d_decisionEngine->popTo(d_bottomScope);
    d_litsMaxScorePos = 0; // from decision engine
    clearLiterals();
    for (vector<Clause>::reverse_iterator i = d_unitConflictClauses.rbegin();
         i != d_unitConflictClauses.rend();
         ++i) {
      //IF_DEBUG(checkAssumpDebug(i->getTheorem(), d_assumptions);)
      // The theorem of *i is, most likely, (OR lit); rewrite it to just `lit'
      Theorem thm = i->getTheorem();
      if(thm.getExpr().isOr())
	thm = d_commonRules->iffMP(thm, d_commonRules->rewriteOr(thm.getExpr()));
      enqueueFact(thm);
      commitFacts(); // Make sure facts propagate to DPs
    }
    d_unitConflictClauses.clear();
    return true; // Let bcp take care of the rest.
  }

  // Otherwise, we need to make our failure driven assertion.
  DebugAssert(!d_lastConflictClause.isNull(), "");

  // We need to calculate the backtracking level.  We do this by
  // examining the decision levels of all the literals involved in the
  // last conflict clause.

  Clause &c = d_lastConflictClause;
  Literal unit_lit;
  unsigned idx=0;
  unsigned current_dl = d_lastConflictScope;
  unsigned back_dl = d_bottomScope;
  for (unsigned i = 0; i < c.size(); ++i) {
    unsigned dl = c[i].getVar().getScope();
    if (dl < current_dl) {
      if (dl > back_dl)
        back_dl = dl;
    }
    else {
      DebugAssert(unit_lit.getExpr().isNull(),
		  "Only one lit from the current decision level is allowed.\n"
		  "current_dl="
		  +int2string(current_dl)+", scopeLevel="
		  +int2string(scopeLevel())
		  +"\n l1 = "
		  +unit_lit.toString()
		  +"\n l2 = "+c[i].toString()
		  +"\nConflict clause: "+c.toString());
      unit_lit = c[i];
      idx = i;
    }
  }


  // Now we have the backtracking decision level.
  DebugAssert(!unit_lit.getExpr().isNull(),"Need to have an FDA in "
	      "conflict clause: "+c.toString());
  d_decisionEngine->popTo(back_dl);
  d_litsMaxScorePos = 0; // from decision engine
  clearLiterals();
  unitPropagation(c,idx);
  commitFacts(); // Make sure facts propagate to DPs
  return true;
}


void SearchEngineFast::enqueueFact(const Theorem& thm) {
  //  d_core->addFact(thm);
  TRACE("search props", "SearchEngineFast::enqueueFact(",
	thm.getExpr(), ") {");
  if(thm.isAbsLiteral()) {
    addLiteralFact(thm);
  }
  d_factQueue.push_back(thm);
  TRACE_MSG("search props", "SearchEngineFast::enqueueFact => }");
}


void SearchEngineFast::setInconsistent(const Theorem& thm) {
  TRACE_MSG("search props", "SearchEngineFast::setInconsistent()");
  d_factQueue.clear();
  IF_DEBUG(debugger.counter("conflicts from SAT solver")++;)
  d_core->setInconsistent(thm);
}

void SearchEngineFast::commitFacts() {
  for(vector<Theorem>::iterator i=d_factQueue.begin(), iend=d_factQueue.end();
      i!=iend; ++i) {
    TRACE("search props", "commitFacts(", i->getExpr(), ")");
    if(d_useEnqueueFact)
      d_core->enqueueFact(*i);
    else
      d_core->addFact(*i);
  }
  d_factQueue.clear();
}


void SearchEngineFast::clearFacts() {
  TRACE_MSG("search props", "clearFacts()");
  d_factQueue.clear();
}


void SearchEngineFast::addNewClause(Clause &c)
{
  DebugAssert(c.size() > 1, "New clauses should have size > 1");
  d_clauses.push_back(c);
  updateLitCounts(c);
  // Set up the watch pointers to this clause: find two unassigned
  // literals (otherwise we shouldn't even receive it as a clause)
  size_t i=0, iend=c.size();
  for(; i<iend && c[i].getValue() != 0; ++i);
  DebugAssert(i<iend, "SearchEngineFast::addNewClause:\n"
	      "no unassigned literals in the clause:\nc = "
	      +CompactClause(c).toString());
  c.wp(0,i); ++i;
  for(; i<iend && c[i].getValue() != 0; ++i);
  DebugAssert(i<iend, "SearchEngineFast::addNewClause:\n"
	      "Only one unassigned literal in the clause:\nc = "
	      +CompactClause(c).toString());
  c.wp(1,i);
  // Add the watched pointers to the appropriate lists
  for(int i=0; i<=1; i++) {
    Literal l(!c.watched(i));
    // Add the pointer to l's list
    pair<Clause, int> p(c, i);
    wp(l).push_back(p);
  }
}

inline bool TheoremEq(const Theorem& t1, const Theorem& t2) {
  DebugAssert(!t1.isNull() && !t2.isNull(),
	      "analyzeUIPs() Null Theorem found");
   return t1.getExpr() == t2.getExpr();
}


//! Auxiliary function used in analyzeUIPs()
/*! It processes a node and populates the relevant sets used in the
 * algorithm.
 * \sa analyzeUIPs() for more detail). 
 */
static void processNode(const Theorem& thm, 
			vector<Theorem>& lits,
			vector<Theorem>& gamma,
			vector<Theorem>& fringe,
			int& pending) {
  // Decrease the fan-out count
  int fanOutCount(thm.getCachedValue() - 1);
  thm.setCachedValue(fanOutCount);
  bool wasFlagged(thm.isFlagged());
  thm.setFlag();
  DebugAssert(fanOutCount >= 0, 
	      "analyzeUIPs(): node visited too many times: "
	      +thm.toString());
  if(fanOutCount == 0) {
    if(thm.getExpandFlag()) {
      if(wasFlagged) {
	TRACE("impl graph", "pending.erase(", thm.getExpr(), ")");
	DebugAssert(pending > 0, 
		    "analyzeUIPs(): pending set shouldn't be empty here");
	pending--;
      }
      TRACE("impl graph", "fringe.insert(", thm.getExpr(), ")");
      fringe.push_back(thm);
    } else if(thm.getLitFlag()) {
      DebugAssert(thm.isAbsLiteral(), "analyzeUIPs(): bad flag on "
		  +thm.toString());
      if(wasFlagged) {
	TRACE("impl graph", "pending.erase(", thm.getExpr(), ")");
	DebugAssert(pending > 0, 
		    "analyzeUIPs(): pending set shouldn't be empty here");
	pending--;
      }
      TRACE("impl graph", "lits.insert(", thm.getExpr(), ")");
      lits.push_back(thm);
    } else {
      if(!wasFlagged) {
	TRACE("impl graph", "gamma.insert(", thm.getExpr(), ")");
	gamma.push_back(thm);
      } else {
	TRACE("impl graph", "already in gamma: ", thm.getExpr(), "");
      }
    }
  } else { // Fan-out count is non-zero
    if(thm.getExpandFlag()) {
      // Too early to expand; stash in pending
      if(!wasFlagged) {
	pending++;
	TRACE("impl graph", "pending.insert(", thm.getExpr(), ")");
      } else {
	TRACE("impl graph", "already in pending: ", thm.getExpr(), "");
      }
    } else if(thm.getLitFlag()) {
      // It's a literal which goes into pending
      if(!wasFlagged) {
	pending++;
	TRACE("impl graph", "pending.insert(", thm.getExpr(), ")");
      } else {
	TRACE("impl graph", "already in pending: ", thm.getExpr(), "");
      }
    } else {
      if(!wasFlagged) {
	TRACE("impl graph", "gamma.insert(", thm.getExpr(), ")");
	gamma.push_back(thm);
      } else {
	TRACE("impl graph", "already in gamma: ", thm.getExpr(), "");
      }
    }
  }
  // FIXME: uniquify theorems in lits, gamma, and fringe by
  // expression; the smallest scope theorem should supersede all the
  // duplicates.  Question: can we do it safely, without breaking the
  // UIP algorithm?
}

/*! 
 <strong>Finding UIPs (Unique Implication Pointers)</strong>

 This is basically the same as finding hammocks of the subset of the
 implication graph composed of only the nodes from the current scope.
 A hammock is a portion of the graph which has a single source and/or
 sink such that removing that single node makes the graph
 disconnected.

 Conceptually, the algorithm maintains four sets of nodes: literals
 (named <em>lits</em>), gamma, fringe, and pending.  Literals are
 nodes whose expressions will become literals in the conflict clause
 of the current hammock, and the nodes in gamma are assumptions from
 which such conflict clause theorem is derived.  Nodes in fringe are
 intermediate nodes which are ready to be "expanded" (see the
 algorithm description below).  The pending nodes are those which are
 not yet ready to be processed (they later become literal or fringe
 nodes).

 These sets are maintained as vectors, and are updated in such a way
 that the nodes in the vectors never repeat.  The exception is the
 pending set, for which only a size counter is maintained.  A node
 belongs to the pending set if it has been visited (isFlagged()
 method), and its fan-out count is non-zero (stored in the cache,
 getCachedValue()).  In other words, pending nodes are those that have
 been visited, but not sufficient number of times.

 Also, fringe is maintained as a pair of vectors.  One vector is
 always the current fringe, and the other one is built when the
 current is processed.  When processing of the current fringe is
 finished, it is cleared, and the other vector becomes the current
 fringe (that is, they swap roles).

 A node is expanded if it is marked for expansion (getExpandFlag()).
 If its fan-out count is not yet zero, it is added to the set of
 pending nodes.

 If a node has a literal flag (getLitFlag()), it goes into literals
 when its fan-out count reaches zero.  Since this will be the last
 time the node is visited, it is added to the vector only once.

 A node neither marked for expansion nor with the literal flag goes
 into the gamma set.  It is added the first time the node is visited
 (isFlagged() returns false), and therefore, is added to the vector
 only once.  This is an important distinction from the other sets,
 since a gamma-node may be used by several conflict clauses.

 Clearing the gamma set after each UIP requires both clearing the
 vector and resetting all flags (clearAllFlags()).

 <strong>The algorithm</strong>

<ol>

<li> Initially, the fringe contains exactly the predecessors of
    falseThm from the current scope which are ready to be expanded
    (fan-out count is zero).  All the other predecessors of falseThm
    go to the appropriate sets of literals, gamma, and pending.

<li> If fringe.size() <= 1 and the set of pending nodes is empty, then
    the element in the fringe (if it's non-empty) is a UIP.  Generate
    a conflict clause from the UIP and the literals (using gamma as
    the set of assumptions), empty the sets, and continue with the
    next step.  Note, that the UIP remains in the fringe, and will be
    expanded in the next step.

    The important exception: if the only element in the fringe is
    marked for expansion, then this is a false UIP (the SAT solver
    doesn't know about this node), and it should not appear in the
    conflict clause.  In this case, simply proceed to step 3 as if
    nothing happened.

<li> If fringe.size()==0, stop (the set of pending nodes must also be
    empty at this point).  Otherwise, for *every* node in the fringe,
    decrement the fan-out for each of its predecessors, and empty the
    fringe.  Take the predecessors from the current scope, and add
    those to the fringe for which fan-out count is zero, and remove
    them from the set of pending nodes.  Add the other predecessors
    from the current scope to the set of pending nodes.  Add the
    remaining predecessors (not from the current scope) to the
    literals or gamma, as appropriate.  Continue with step 2.

</ol>
*/
void SearchEngineFast::analyzeUIPs(const Theorem &falseThm, int conflictScope)
{
  TRACE("impl graph", "analyzeUIPs(scope = ", conflictScope, ") {");
  vector<Theorem> fringe[2]; // 2-element array of vectors (new & curr. fringe)
  unsigned curr(0), next(1);

  int pending(0);
  vector<Theorem> lits;
  vector<Theorem> gamma;
  
  Theorem start = falseThm;
  d_lastConflictClause = Clause();
  d_lastConflictScope = conflictScope;
  start.clearAllFlags();

  TRACE("search full", "Analysing UIPs at level: ", conflictScope, "");

  // Initialize all the sets
  const Assumptions& a=start.getAssumptionsRef();
  for(Assumptions::iterator i=a.begin(), iend=a.end(); i!=iend; ++i) {
    processNode(*i, lits, gamma, fringe[curr], pending);
  }

  while (true) {
    TRACE_MSG("impl graph", "analyzeUIPs(): fringe size = "
	      +int2string(fringe[curr].size())
	      +", pending size = "+int2string(pending));
    // Wrap up a conflict clause if:
    // (1) There are no pending nodes
    // (2) The fringe has at most one element
    // (3) If fringe is not empty, its node should not be flagged for expansion
    if(fringe[curr].size() <= 1 && pending == 0
       && (fringe[curr].size() == 0
	   || !fringe[curr].back().getExpandFlag())) {
      // Found UIP or end of graph.  Generate conflict clause.
      if(fringe[curr].size() > 0)
	lits.push_back(fringe[curr].back());
      IF_DEBUG(if(debugger.trace("impl graph")) {
	ostream& os = debugger.getOS();
	os << "Creating conflict clause:"
	   << "\n  start: " << start.getExpr()
	   << "\n  Lits: [\n";
	for(size_t i=0; i<lits.size(); i++)
	  os << "    " << lits[i].getExpr() << "\n";
	os << "]\n  Gamma: [\n";
	for(size_t i=0; i<gamma.size(); i++)
	  os << "    " << gamma[i].getExpr() << "\n";
	os << "]" << endl;
      })
      // Derive a theorem for the conflict clause
      Theorem clause = d_rules->conflictClause(start, lits, gamma);
      d_conflictClauseCount++;
      // Generate the actual clause and set it up
      Clause c(d_core, d_vm, clause, d_bottomScope, __FILE__, __LINE__);
      updateLitCounts(c);
      if (c.size() > 1) {
	// Set the watched pointers to the two literals with the
	// highest scopes
        int firstLit = 0;
        int secondLit = 1;
        int firstDL = c[0].getScope();
        int secondDL = c[1].getScope();
	// Invariant: firstDL >= secondDL
	if(firstDL < secondDL) {
	  firstLit=1; secondLit=0;
	  int tmp(secondDL);
	  secondDL=firstDL; firstDL=tmp;
	}
	for(unsigned i = 2; i < c.size(); ++i) {
	  int cur = c[i].getScope();
	  if(cur >= firstDL) {
	    secondLit=firstLit; secondDL=firstDL;
	    firstLit=i; firstDL=cur;
	  } else if(cur > secondDL) {
	    secondLit=i; secondDL=cur;
	  }
	}

        c.wp(0, firstLit);
        c.wp(1, secondLit);
    
        // Add the watch pointers to the d_wp lists
        for(int i=0; i<=1; i++) {
          // Negated watched literal
          Literal l(!c.watched(i));
          // Add the pointer to l's list
          pair<Clause, int> p(c, i);
          wp(l).push_back(p);
        }
      }
      TRACE("conflict clauses",
	    "Conflict clause #"+int2string(d_conflictClauseCount)
	    +": ", CompactClause(c), "");
      if(c.size() == 1) {
        // Unit clause: stash it for later unit propagation
        TRACE("conflict clauses", "analyzeUIPs(): unit clause: ",
              CompactClause(c), "");
        d_unitConflictClauses.push_back(c);
      }
      else {
        TRACE("conflict clauses", "analyzeUIPs(): conflict clause ",
	      CompactClause(c), "");
        DebugAssert(c.getScope() <= d_bottomScope,
		    "Conflict clause should be at bottom scope.");
        d_conflictClauses->push_back(c);
        if (d_lastConflictClause.isNull()) {
          d_lastConflictClause = c;
// 	  IF_DEBUG(for(unsigned i=0; i<c.size(); ++i)
// 	    DebugAssert(c[i].getValue() == -1, "Bad conflict clause: "
// 			+c.toString());)
	}
      }
      if(fringe[curr].size() > 0) {
	// This was a UIP.  Leave it in the fringe for later expansion.
	IF_DEBUG(debugger.counter("UIPs")++;)
	start = fringe[curr].back();
	lits.clear();
	gamma.clear();
	start.clearAllFlags();
      } else {
	// No more conflict clauses, we are done.  This is the only
	// way this function can return.
	TRACE_MSG("impl graph", "analyzeUIPs => }");
	return;
      }
    }
    // Now expand all the nodes in the fringe
    for(vector<Theorem>::iterator i=fringe[curr].begin(),
	  iend=fringe[curr].end();
	i!=iend; ++i) {
      const Assumptions& a=i->getAssumptionsRef();
      for(Assumptions::iterator j=a.begin(), jend=a.end(); j!=jend; ++j) {
	processNode(*j, lits, gamma, fringe[next], pending);
      }
    }
    // Swap the current and next fringes
    fringe[curr].clear();
    curr = 1 - curr;
    next = 1 - next;
    IF_DEBUG(if(pending > 0 && fringe[curr].size()==0)
	     falseThm.printDebug();)
    DebugAssert(pending == 0 || fringe[curr].size() > 0,
		"analyzeUIPs(scope = "
		+int2string(conflictScope)+"): empty fringe");
  }
}


////////////////////////////////
// End New Search Engine Code //
////////////////////////////////


//! Redefine the counterexample generation.
/*! FIXME: for now, it just dumps all the assumptions (same as
 * getAssumptions()).  Eventually, it will simplify the related
 * formulas to TRUE, merge all the generated assumptions into
 * d_lastCounterExample, and call the parent's method. */
void SearchEngineFast::getCounterExample(std::vector<Expr>& assertions) {
  // This will not add anything, since the counterexample is empty,
  // but will check if we are allowed to be called
  SearchImplBase::getCounterExample(assertions);
  getAssumptions(assertions);
}


//! Notify the search engine about a new non-literal fact.
/*! It should be called by TheoryCore::assertFactCore().
 *
 * If the fact is an AND, we split it into individual conjuncts and
 * add them individually.
 *
 * If the fact is an OR, we check whether it's a CNF clause; that is,
 * whether all disjuncts are literals.  If they are, we add it as a
 * CNF clause.
 *
 * Otherwise add the fact to d_nonLiterals as it is.
 */
void
SearchEngineFast::addNonLiteralFact(const Theorem& thm) {
  TRACE("search", "addNonLiteralFact(", thm, ") {");
  TRACE("search", "d_nonLiteralsSaved.size()=",d_nonLiteralsSaved.size(),
	"@"+int2string(scopeLevel()));
  //IF_DEBUG(checkAssumpDebug(thm, d_assumptions);)
  const Expr& e(thm.getExpr());
  if(d_nonLiteralsSaved.count(e) > 0) {
    // We've seen this non-literal before.
    TRACE_MSG("search", "addNonLiteralFact[skipping] => }");
    IF_DEBUG(debugger.counter("skipped repeated non-literals")++;)
    return;
  }
  // Save the non-literal
  d_nonLiteralsSaved[e]=thm;
  bool isCNFclause(false);
  // Split conjunctions into individual assertions and add them to the
  // appropriate lists

  int k = e.getKind();
  if (k == AND_R || k == IFF_R || k == ITE_R)
  {
    d_circuits.push_back(new Circuit(this, thm));
  }

  else if(e.isAnd()) {
    for(int i=0, iend=e.arity(); i<iend; ++i) {
      Theorem t_i(d_commonRules->andElim(thm, i));
      // Call enqueueFact(), not addFact(), since we are called from
      // addFact() here
      if(e[i].isAbsLiteral()) {
	d_core->enqueueFact(t_i);
      }
      else addNonLiteralFact(t_i);
    }
  } else {
    int unsetLits(0); // Count the number of unset literals
    size_t unitLit(0); // If the #unsetLits==1, this is the only unset literal
    vector<Theorem> thms; // collect proofs of !l_i for unit prop.
    if(e.isOr()) {
      isCNFclause = true;
      for(int i=0; isCNFclause && i<e.arity(); ++i) {
	isCNFclause=e[i].isAbsLiteral();
	if(isCNFclause) {
	  // Check the value of the literal
	  Literal l(newLiteral(e[i]));
	  if(l.getValue() > 0) // The entire clause is true; ignore it
	    return;
	  if(l.getValue() == 0) { // Found unset literal
	    unsetLits++; unitLit = i;
	  } else // Literal is false, collect the theorem for it
	    thms.push_back(l.deriveTheorem());
	}
      }
    }
    if(isCNFclause) {
      DebugAssert(e.arity() > 1, "Clause should have more than one literal");
      // Check if clause is unit or unsat
      if(unsetLits==0) { // Contradiction
	TRACE("search", "contradictory clause:\n",
	      CompactClause(Clause(d_core, d_vm, thm, scopeLevel())),"");
	setInconsistent(d_rules->conflictRule(thms, thm));
      } else if(unsetLits==1) { // Unit clause: propagate literal
	TRACE("search", "unit clause, unitLit = "+int2string(unitLit)+":\n", 
	      CompactClause(Clause(d_core, d_vm, thm, scopeLevel())),"");
	d_core->enqueueFact(d_rules->unitProp(thms, thm, unitLit));
      } else { // Wrap up the clause
	Clause c(d_core, d_vm, thm, scopeLevel(), __FILE__, __LINE__);
	IF_DEBUG(debugger.counter("CNF clauses added")++;)
	TRACE("search", "addNonLiteralFact: adding CNF: ", c, "");
	addNewClause(c);
      }
    } else {
      TRACE("search", "addNonLiteralFact: adding non-literal: ", thm, "");
      IF_DEBUG(debugger.counter("added non-literals")++;)
      d_nonLiterals.push_back(SmartCDO<Theorem>(d_core->getCM()->getCurrentContext(), thm));
      //      d_nonLiteralSimplified[thm.getExpr()] = false;
    }
  }
  TRACE_MSG("search", "addNonLiteralFact => }");
}


//! Notify the search engine about a new literal fact.
/*! It should be called by TheoryCore::assertFactCore() */
void
SearchEngineFast::addLiteralFact(const Theorem& thm) {
  TRACE("search", "addLiteralFact(", thm, ")");
  // Save the value of the flag to restore it later
  bool useEF(d_useEnqueueFact);
  d_useEnqueueFact=true;

  DebugAssert(thm.isAbsLiteral(),
	      "addLiteralFact: not a literal: " + thm.toString());
  //IF_DEBUG(checkAssumpDebug(thm, d_assumptions);)
  Literal l(newLiteral(thm.getExpr()));
  TRACE("search", "addLiteralFact: literal = ", l, "");
  // Only add the literal if it doesn't have any value; otherwise it's
  // either a contradiction, or it must already be in the list
  // FIXME: why did we need thm.getScope() != 0 ???
  if ((l.getValue() == 0 /* && thm.getScope() != 0 */)
      /* || (l.getValue() == 1 && l.getScope() > thm.getScope()) */) {
    l.setValue(thm, scopeLevel());
    DebugAssert(l.getExpr().isAbsLiteral(),
		"addLiteralFact(): pushing non-literal to d_literals:\n "
		+l.getExpr().toString());
    DebugAssert(l.getValue() == 1, "addLiteralFact(): l = "+l.toString());
    d_literals.push_back(l);
    d_literalSet.insert(l.getExpr(),l);
    // Immediately propagate the literal with BCP, unless the SAT
    // solver is already running
    if(!d_inCheckSAT) bcp();

//     if (thm.getScope() != scopeLevel()) {
//       IF_DEBUG(debugger.counter("addLiteralFact adds unreported lit")++;)
//       d_unreportedLits.insert(l.getExpr(),thm,thm.getScope());
//     }
  } else if(l.getValue() < 0) { // Contradiction, bcp will die anyway
    if(l.isNegative())
      setInconsistent(d_commonRules->contradictionRule(l.deriveTheorem(), thm));
    else
      setInconsistent(d_commonRules->contradictionRule(thm, l.deriveTheorem()));
  }
  d_useEnqueueFact=useEF;
}

/*! @brief Redefine newIntAssumption(): we need to add the new theorem
 * to the appropriate Literal */
Theorem
SearchEngineFast::newIntAssumption(const Expr& e) {
  Theorem thm(SearchImplBase::newIntAssumption(e));
  DebugAssert(thm.isAssump(), "Splitter should be an assumption:" + thm.toString());
  TRACE("search full", "Splitter: ", thm.toString(), "");
  const Expr& expr = thm.getExpr();
  Literal l(newLiteral(expr));
  if(l.getValue() == 0) {
    l.setValue(thm, scopeLevel());
    if(l.getExpr().isAbsLiteral()) {
      DebugAssert(l.getValue() == 1, "newIntAssumption(): l = "+l.toString());
      d_literals.push_back(l);
    }
    else
      d_litsAlive.push_back(l);
  }

    
  return thm;
}

bool 
SearchEngineFast::isAssumption(const Expr& e) {
  return (SearchImplBase::isAssumption(e)
	  || (d_nonLiteralsSaved.count(e) > 0));
}


void
SearchEngineFast::addSplitter(const Expr& e, int priority) {
  // SearchEngine::addSplitter(e, priority);
  DebugAssert(e.isAbsLiteral(), "SearchEngineFast::addSplitter("+e.toString()+")");
  Literal lit(newLiteral(e));
  d_dpSplitters.push_back(Splitter(lit));
  if(priority != 0) {
    d_litSortCount--;
    lit.score() += priority*10;
  }
  if(!lit.added()) {
    TRACE("search literals", "addSplitter(): adding literal ", lit, " to d_litsByScores");
    d_litsByScores.push_back(lit);
    lit.added()=true;
    if(priority == 0) d_litSortCount--;
  }
  if(d_litSortCount < 0) {
    ::stable_sort(d_litsByScores.begin(), d_litsByScores.end(), compareLits);
    d_litSortCount=d_litsByScores.size();
  }
  TRACE("search splitters","addSplitter => ", lits2str(d_litsByScores),"");
}


QueryResult SearchEngineFast::checkValidMain(const Expr& e2)
{
  // Propagate the literals asserted before checkValid()
  for(CDMap<Expr,Literal>::iterator i=d_literalSet.begin(),
	iend=d_literalSet.end(); i!=iend; ++i)
    d_literals.push_back((*i).second);

  // Run the SAT solver
  QueryResult result = checkSAT();

  Theorem res;
  if (result == UNSATISFIABLE)
    res = d_conflictTheorem;
  else if (result == SATISFIABLE) {
    // Set counter-example
    vector<Expr> a;
    unsigned i;
    Theorem thm;

    d_lastCounterExample.clear();
    for (i=d_nonlitQueryStart; i < d_nonlitQueryEnd; ++i) {
      thm = d_nonLiterals[i].get();
      DebugAssert(thm.getExpr().isTrue(),
                  "original nonLiteral doesn't simplify to true");
      thm.getLeafAssumptions(a);
      for (vector<Expr>::iterator i=a.begin(), iend=a.end(); i != iend; ++i) {
        d_lastCounterExample[*i] = true;
      }
      a.clear();
    }
    for (i=d_clausesQueryStart; i < d_clausesQueryEnd; ++i) {
      thm = simplify(((Clause)d_clauses[i]).getTheorem());
      DebugAssert(thm.getExpr().isTrue(),
                  "original nonLiteral doesn't simplify to true");
      thm.getLeafAssumptions(a);
      for (vector<Expr>::iterator i=a.begin(), iend=a.end(); i != iend; ++i) {
        d_lastCounterExample[*i] = true;
      }
      a.clear();
    }
  }
  else return result;

  processResult(res, e2);

  if (result == UNSATISFIABLE) {
    d_core->getCM()->popto(d_bottomScope);
    d_litsMaxScorePos = 0; // from decision engine

    // Clear data structures
    d_unitConflictClauses.clear();
    clearLiterals();
    clearFacts();

    Theorem e_iff_e2(d_commonRules->iffContrapositive(d_simplifiedThm));
    d_lastValid =
      d_commonRules->iffMP(d_lastValid, d_commonRules->symmetryRule(e_iff_e2));
    IF_DEBUG(checkAssumpDebug(d_lastValid, d_assumptions);)
    TRACE_MSG("search terse", "checkValid => true}");
    TRACE("search", "checkValid => true; theorem = ", d_lastValid, "}");
    d_core->getCM()->pop();
  }
  else {
    TRACE_MSG("search terse", "checkValid => false}");
    TRACE_MSG("search", "checkValid => false; }");
    DebugAssert(d_unitConflictClauses.size() == 0, "checkValid(): d_unitConflictClauses postcondition violated");
    DebugAssert(d_literals.size() == 0, "checkValid(): d_literals postcondition violated");
    DebugAssert(d_factQueue.empty(), "checkValid(): d_factQueue postcondition violated");
  }
  return result;
}


QueryResult SearchEngineFast::checkValidInternal(const Expr& e)
{
  DebugAssert(d_unitConflictClauses.size() == 0, "checkValid(): d_unitConflitClauses precondition violated");
  DebugAssert(d_factQueue.empty(), "checkValid(): d_factQueue precondition violated");

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
  d_conflictClauseManager.setRestorePoint();
  d_bottomScope = scopeLevel();

  // First, simplify the NEGATION of the given expression: that's what
  // we'll assert
  d_simplifiedThm = d_core->getExprTrans()->preprocess(e.negate());
  TRACE("search", "checkValid: simplifiedThm = ", d_simplifiedThm, "");

  const Expr& not_e2 = d_simplifiedThm.get().getRHS();
  Expr e2 = not_e2.negate();

  // Assert not_e2 if it's not already asserted
  TRACE_MSG("search terse", "checkValid: Asserting !e: ");
  TRACE("search", "checkValid: Asserting !e: ", not_e2, "");
  Theorem not_e2_thm;
  d_nonlitQueryStart = d_nonLiterals.size();
  d_clausesQueryStart = d_clauses.size();
  if(d_assumptions.count(not_e2) == 0) {
    not_e2_thm = newUserAssumption(not_e2);
  } else {
    not_e2_thm = d_assumptions[not_e2];
  }
  //  d_core->addFact(not_e2_thm);
  d_nonlitQueryEnd = d_nonLiterals.size();
  d_clausesQueryEnd = d_clauses.size();

  // Reset the splitter counter.  This will force a call to
  // updateLitScores() the first time we need to find a splitter, and
  // clean out junk from the previous calls to checkValid().
  d_splitterCount=0;

  return checkValidMain(e2);
}


QueryResult SearchEngineFast::restartInternal(const Expr& e)
{
  DebugAssert(d_unitConflictClauses.size() == 0, "restart(): d_unitConflitClauses precondition violated");
  DebugAssert(d_factQueue.empty(), "restart(): d_factQueue precondition violated");

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

/*!
 * The purpose of this method is to mark up the assumption graph of
 * the FALSE Theorem (conflictThm) for the later UIP analysis.  The
 * required flags for each assumption in the graph are:
 *
 * <strong>ExpandFlag:</strong> whether to "expand" the node or not;
 * that is, whether to consider the current node as a final assumption
 * (either as a conflict clause literal, or a context assumption from
 * \f$\Gamma\f$)
 *
 * <strong>LitFlag:</strong> the node (actually, its inverse) is a
 * literal of the conflict clause
 *
 * <strong>CachedValue:</strong> the "fanout" count, how many nodes in
 * the assumption graph are derived from the current node.
 * 
 * INVARIANTS (after the method returns):
 *
 * -# The currect scope is the "true" conflict scope,
 *    i.e. scopeLevel() == conflictThm.getScope()
 * -# The literals marked with LitFlag (CC literals) are known to the
 *    SAT solver, i.e. their Literal class has a value == 1
 * -# The only CC literal from the current scope is the latest splitter
 *
 * ASSUMPTIONS: 
 * 
 * -# The Theorem scope of an assumption is the same as its Literal scope;
 *    i.e. if thm is a splitter, then 
 *    thm.getScope() == newLiteral(thm.getExpr()).getScope()
 *
 * Algorithm:
 * 
 * First, backtrack to the scope level of the conflict.  Then,
 * traverse the implication graph until we either hit a literal known
 * to the SAT solver at a lower scope:
 * newLiteral(e).getScope()<scopeLevel(), or a splitter (assumption), or a
 * fact from the bottom scope.  The literals from the first two
 * categories are marked with LitFlag (they'll comprise the conflict
 * clause), and the bottom scope facts will be the assumptions in the
 * conflict clause's theorem.
 *
 * The traversed nodes are cached by the .isFlagged() flag, and
 * subsequent hits only increase the fanout count of the node.
 *
 * Notice, that there can only be one literal in the conflict clause
 * from the current scope.  Also, even if some intermediate literals
 * were delayed by the DPs and reported to the SAT solver at or below
 * the conflict scope (which may be below their "true" Theorem scope),
 * they will be skipped, and their assumptions will be used.
 *
 * In other words, it is safe to backtrack to the "true" conflict
 * level, since, in the worst case, we traverse the graph all the way
 * to the splitters, and make a conflict clause out of those.  The
 * hope is, however, that this wouldn't happen too often.
 */
void SearchEngineFast::traceConflict(const Theorem& conflictThm) {
  TRACE("impl graph", "traceConflict(", conflictThm.getExpr(), ") {");
  
  // Always process conflict at its true scope or the bottom scope,
  // whichever is greater.
  DebugAssert(conflictThm.getScope() <= scopeLevel(),
	      "conflictThm.getScope()="+int2string(conflictThm.getScope())
	      +", scopeLevel()="+int2string(scopeLevel()));
  if(conflictThm.getScope() < scopeLevel()) {
    int scope(conflictThm.getScope());
    if(scope < d_bottomScope) scope = d_bottomScope;
    d_decisionEngine->popTo(scope);
  }

  if(scopeLevel() <= d_bottomScope) {
    // This is a top-level conflict, nothing to analyze.
    TRACE_MSG("impl graph", "traceConflict[bottom scope] => }");
    return;
  }

  // DFS stack
  vector<Theorem> stack;
  // Max assumption scope for the contradiction
  int maxScope(d_bottomScope);
  // Collect potential top-level splitters
  IF_DEBUG(vector<Theorem> splitters;)
  TRACE("impl graph", "traceConflict: maxScope = ", maxScope, "");

  conflictThm.clearAllFlags();
  conflictThm.setExpandFlag(true);
  conflictThm.setCachedValue(0);

  const Assumptions& assump = conflictThm.getAssumptionsRef();
  for(Assumptions::iterator i=assump.begin(),iend=assump.end();i!=iend;++i) {
    TRACE("impl graph", "traceConflict: adding ", *i, "");
    stack.push_back(*i);
  }

  // Do the non-recursive DFS, mark up the assumption graph
  IF_DEBUG(Literal maxScopeLit;)
  while(stack.size() > 0) {
    Theorem thm(stack.back());
    stack.pop_back();
    TRACE("impl graph", "traceConflict: while() { thm = ", thm, "");
    if (thm.isFlagged()) {
      // We've seen this theorem before.  Update fanout count.
      thm.setCachedValue(thm.getCachedValue() + 1);
      TRACE("impl graph", "Found again: ", thm.getExpr().toString(), "");
      TRACE("impl graph", "With fanout: ", thm.getCachedValue(), "");
    }
    else {
      // This is a new theorem.  Process it.
      thm.setCachedValue(1);
      thm.setFlag();
      thm.setLitFlag(false); // Clear this flag (it may be set later)
      bool expand(false);
      int scope = thm.getScope();
      bool isAssump = thm.isAssump();

      IF_DEBUG({
	int s = scope;
	if(thm.isAbsLiteral()) {
	  Literal l(newLiteral(thm.getExpr()));
	  if(l.getValue() == 1) s = l.getScope();
	}
	// maxScope will be reset: clear the splitters
	if(s > maxScope) splitters.clear();
      })

      if(thm.isAbsLiteral()) {
	Literal l(newLiteral(thm.getExpr()));
	bool isTrue(l.getValue()==1);
	if(isTrue) scope = l.getScope();
	if(!isAssump && (!isTrue || scope == scopeLevel()))
	  expand=true;
	else if(scope > d_bottomScope) {// Found a literal of a conflict clause
	  IF_DEBUG(if(scope >= maxScope) splitters.push_back(thm);)
	  thm.setLitFlag(true);
	}
      } else {
	DebugAssert(scope <= d_bottomScope || !isAssump,
		    "SearchEngineFast::traceConflict: thm = "
		    +thm.toString());
	if(!isAssump && scope > d_bottomScope)
	  expand=true;
      }

      if(scope > maxScope) {
	maxScope = scope;
	IF_DEBUG(maxScopeLit = newLiteral(thm.getExpr());)
	TRACE("impl graph", "traceConflict: maxScope = ", maxScope, "");
      }

      if(expand) {
	DebugAssert(!thm.isAssump(),
		    "traceConflict: thm = "+thm.toString());
	thm.setExpandFlag(true);
	const Assumptions& assump = thm.getAssumptionsRef();
	for(Assumptions::iterator i=assump.begin(),iend=assump.end();
	    i!=iend; ++i) {
	  TRACE("impl graph", "traceConflict: adding ", *i, "");
	  stack.push_back(*i);
	}
      } else
	thm.setExpandFlag(false);
    }
    TRACE_MSG("impl graph", "traceConflict: end of while() }");
  }
  IF_DEBUG(if(maxScope != scopeLevel()) conflictThm.printDebug();)
  DebugAssert(maxScope == scopeLevel(), "maxScope="+int2string(maxScope)
	      +", scopeLevel()="+int2string(scopeLevel())
	      +"\n maxScopeLit = "+maxScopeLit.toString());
  IF_DEBUG(
    if(!(maxScope == d_bottomScope || splitters.size() == 1)) {
      conflictThm.printDebug();
      ostream& os = debugger.getOS();
      os << "\n\nsplitters = [";
      for(size_t i=0; i<splitters.size(); ++i)
	os << splitters[i] << "\n";
      os << "]" << endl;
    }
    )
  DebugAssert(maxScope == d_bottomScope || splitters.size() == 1,
  	      "Wrong number of splitters found at maxScope="
  	      +int2string(maxScope)
  	      +": "+int2string(splitters.size())+" splitters.");
  d_lastConflictScope = maxScope;
  analyzeUIPs(conflictThm, maxScope);
  TRACE_MSG("impl graph", "traceConflict => }");
}
