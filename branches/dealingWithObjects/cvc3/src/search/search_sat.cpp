/*****************************************************************************/
/*!
 *\file search_sat.cpp
 *\brief Implementation of Search engine with generic external sat solver
 *
 * Author: Clark Barrett
 *
 * Created: Wed Dec  7 21:00:24 2005
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
/*****************************************************************************/


#include "search_sat.h"
#ifdef DPLL_BASIC
#include "dpllt_basic.h"
#endif
#include "dpllt_minisat.h"
#include "theory_core.h"
#include "eval_exception.h"
#include "typecheck_exception.h"
#include "expr_transform.h"
#include "search_rules.h"
#include "command_line_flags.h"
#include "theorem_manager.h"
#include "theory.h"
#include "debug.h"


using namespace std;
using namespace CVC3;
using namespace SAT;


namespace CVC3 {


class SearchSatCoreSatAPI :public TheoryCore::CoreSatAPI {
  SearchSat* d_ss;
public:
  SearchSatCoreSatAPI(SearchSat* ss) : d_ss(ss) {}
  ~SearchSatCoreSatAPI() {}
  void addLemma(const Theorem& thm, int priority, bool atBottomScope)
    { d_ss->addLemma(thm, priority, atBottomScope); }
  Theorem addAssumption(const Expr& assump)
  { return d_ss->newUserAssumption(assump); }
  void addSplitter(const Expr& e, int priority)
  { d_ss->addSplitter(e, priority); }
  bool check(const Expr& e);
  
};


bool SearchSatCoreSatAPI::check(const Expr& e)
{
  Theorem thm;
  d_ss->push();
  QueryResult res = d_ss->check(e, thm);
  d_ss->pop();
  return res == VALID;
}


class SearchSatTheoryAPI :public DPLLT::TheoryAPI {
  ContextManager* d_cm;
  SearchSat* d_ss;
public:
  SearchSatTheoryAPI(SearchSat* ss)
    : d_cm(ss->theoryCore()->getCM()), d_ss(ss) {}
  ~SearchSatTheoryAPI() {}
  void push() { return d_cm->push(); }
  void pop() { return d_cm->pop(); }
  void assertLit(Lit l) { d_ss->assertLit(l); }
  SAT::DPLLT::ConsistentResult checkConsistent(CNF_Formula& cnf, bool fullEffort)
    { return d_ss->checkConsistent(cnf, fullEffort); }
  bool outOfResources() { return d_ss->theoryCore()->outOfResources(); }
  Lit getImplication() { return d_ss->getImplication(); }
  void getExplanation(Lit l, CNF_Formula& cnf) { return d_ss->getExplanation(l, cnf); }
  bool getNewClauses(CNF_Formula& cnf) { return d_ss->getNewClauses(cnf); }
};


class SearchSatDecider :public DPLLT::Decider {
  SearchSat* d_ss;
public:
  SearchSatDecider(SearchSat* ss) : d_ss(ss) {}
  ~SearchSatDecider() {}

  Lit makeDecision() { return d_ss->makeDecision(); }
};


class SearchSatCNFCallback :public CNF_Manager::CNFCallback {
  SearchSat* d_ss;
public:
  SearchSatCNFCallback(SearchSat* ss) : d_ss(ss) {}
  ~SearchSatCNFCallback() {}

  void registerAtom(const Expr& e, const Theorem& thm)
  { d_ss->theoryCore()->theoryOf(e)->registerAtom(e, thm); }
};


}


void SearchSat::restorePre()
{
  if (d_core->getCM()->scopeLevel() == d_bottomScope) {
    DebugAssert(d_prioritySetBottomEntriesSizeStack.size() > 0, "Expected non-empty stack");
    d_prioritySetBottomEntriesSize = d_prioritySetBottomEntriesSizeStack.back();
    d_prioritySetBottomEntriesSizeStack.pop_back();
    while (d_prioritySetBottomEntriesSize < d_prioritySetBottomEntries.size()) {
      d_prioritySet.erase(d_prioritySetBottomEntries.back());
      d_prioritySetBottomEntries.pop_back();
    }
  }
}


void SearchSat::restore()
{
  while (d_prioritySetEntriesSize < d_prioritySetEntries.size()) {
    d_prioritySet.erase(d_prioritySetEntries.back());
    d_prioritySetEntries.pop_back();
  }
  while (d_pendingLemmasSize < d_pendingLemmas.size()) {
    d_pendingLemmas.pop_back();
    d_pendingScopes.pop_back();
  }
  while (d_varsUndoListSize < d_varsUndoList.size()) {
    d_vars[d_varsUndoList.back()] = SAT::Var::UNKNOWN;
    d_varsUndoList.pop_back();
  }
}


bool SearchSat::recordNewRootLit(Lit lit, int priority, bool atBottomScope)
{
  DebugAssert(d_prioritySetEntriesSize == d_prioritySetEntries.size() &&
              d_prioritySetBottomEntriesSize == d_prioritySetBottomEntries.size(),
              "Size mismatch");
  pair<set<LitPriorityPair>::iterator,bool> status =
    d_prioritySet.insert(LitPriorityPair(lit, priority));
  if (!status.second) return false;
  if (!atBottomScope || d_bottomScope == d_core->getCM()->scopeLevel()) {
    d_prioritySetEntries.push_back(status.first);
    d_prioritySetEntriesSize = d_prioritySetEntriesSize + 1;
  }
  else {
    d_prioritySetBottomEntries.push_back(status.first);
    ++d_prioritySetBottomEntriesSize;
  }
  
  if (d_prioritySetStart.get() == d_prioritySet.end() ||
      ((*status.first) < (*(d_prioritySetStart.get()))))
    d_prioritySetStart = status.first;
  return true;
}


void SearchSat::addLemma(const Theorem& thm, int priority, bool atBottomScope)
{
  IF_DEBUG(
  string indentStr(theoryCore()->getCM()->scopeLevel(), ' ');
  TRACE("addLemma", indentStr, "AddLemma: ", thm.getExpr().toString(PRESENTATION_LANG));
  )
    //  DebugAssert(!thm.getExpr().isAbsLiteral(), "Expected non-literal");
  DebugAssert(d_pendingLemmasSize == d_pendingLemmas.size(), "Size mismatch");
  DebugAssert(d_pendingLemmasSize == d_pendingScopes.size(), "Size mismatch");
  DebugAssert(d_pendingLemmasNext <= d_pendingLemmas.size(), "Size mismatch");
  d_pendingLemmas.push_back(pair<Theorem,int>(thm, priority));
  d_pendingScopes.push_back(atBottomScope);
  d_pendingLemmasSize = d_pendingLemmasSize + 1;
}


void SearchSat::addSplitter(const Expr& e, int priority)
{
  DebugAssert(!e.isEq() || e[0] != e[1], "Expected non-trivial splitter");
  addLemma(d_commonRules->excludedMiddle(e), priority);
}


void SearchSat::assertLit(Lit l)
{
  //  DebugAssert(d_inCheckSat, "Should only be used as a call-back");
  Expr e = d_cnfManager->concreteLit(l);

  IF_DEBUG(
  string indentStr(theoryCore()->getCM()->scopeLevel(), ' ');
  string val = " := ";
  
  std::stringstream ss;
  ss<<theoryCore()->getCM()->scopeLevel();
  std::string temp;
  ss>>temp;

  if (l.isPositive()) val += "1"; else val += "0";
  TRACE("assertLit", "", "", "");
  TRACE("assertLitScope", indentStr, "Scope level = ", temp);
  TRACE("assertLit", indentStr, l.getVar(), val+": "+e.toString());
  )

    //=======
    //  IF_DEBUG(
    //  string indentStr(theoryCore()->getCM()->scopeLevel(), ' ');
    //  string val = " := ";
    //  if (l.isPositive()) val += "1"; else val += "0";
    //  TRACE("assertLit", indentStr, l.getVar(), val);
    //  )

  // This can happen if the SAT solver propagates a learned unit clause from a p
  bool isSATLemma = false;
  if (e.isNull()) {
    e = d_cnfManager->concreteLit(l, false);
    DebugAssert(!e.isNull(), "Expected known expr");
    isSATLemma = true;
    TRACE("quant-level", "found null expr ",e, "");
  }

  DebugAssert(!e.isNull(), "Expected known expr");
  DebugAssert(!e.isIntAssumption() || getValue(l) == SAT::Var::TRUE_VAL,
              "internal assumptions should be true");
  // This happens if the SAT solver has been restarted--it re-asserts its old assumptions
  if (e.isIntAssumption()) return;
  if (getValue(l) == SAT::Var::UNKNOWN) {
    setValue(l.getVar(), l.isPositive() ? Var::TRUE_VAL : Var::FALSE_VAL);
  }
  else {
    DebugAssert(!e.isAbsLiteral(), "invariant violated");
    DebugAssert(getValue(l) == Var::TRUE_VAL, "invariant violated");
    return;
  }
  if (!e.isAbsLiteral()) return;
  e.setIntAssumption();

  Theorem thm = d_commonRules->assumpRule(e);
  if (isSATLemma) {
    CNF_Formula_Impl cnf;
    d_cnfManager->addAssumption(thm, cnf);
  }

  thm.setQuantLevel(theoryCore()->getQuantLevelForTerm(e.isNot() ? e[0] : e));
  d_intAssumptions.push_back(thm);
  d_core->addFact(thm);
}


SAT::DPLLT::ConsistentResult SearchSat::checkConsistent(SAT::CNF_Formula& cnf, bool fullEffort)
{
  DebugAssert(d_inCheckSat, "Should only be used as a call-back");
  if (d_core->inconsistent()) {
    d_cnfManager->convertLemma(d_core->inconsistentThm(), cnf);
    if (d_cnfManager->numVars() > d_vars.size()) {
      d_vars.resize(d_cnfManager->numVars(), SAT::Var::UNKNOWN);
    }
    return DPLLT::INCONSISTENT;
  }
  if (fullEffort) {
    if (d_core->checkSATCore() && d_pendingLemmasNext == d_pendingLemmas.size() && d_lemmasNext == d_lemmas.numClauses()) {
      if (d_core->inconsistent()) {
        d_cnfManager->convertLemma(d_core->inconsistentThm(), cnf);
        if (d_cnfManager->numVars() > d_vars.size()) {
          d_vars.resize(d_cnfManager->numVars(), SAT::Var::UNKNOWN);
        }
        return DPLLT::INCONSISTENT;
      }
      else return DPLLT::CONSISTENT;
    }
  }
  return DPLLT::MAYBE_CONSISTENT;
}


Lit SearchSat::getImplication()
{
  //  DebugAssert(d_inCheckSat, "Should only be used as a call-back");
  Lit l;
  Theorem imp = d_core->getImpliedLiteral();
  while (!imp.isNull()) {
    l = d_cnfManager->getCNFLit(imp.getExpr());
    DebugAssert(!l.isNull() || imp.getExpr().unnegate().isUserRegisteredAtom(),
                "implied literals should be registered by cnf or by user");
    if (!l.isNull() && getValue(l) != Var::TRUE_VAL) {
      d_theorems.insert(imp.getExpr(), imp);
      break;
    }
    l.reset();
    imp = d_core->getImpliedLiteral();
  }
  return l;
}


void SearchSat::getExplanation(Lit l, SAT::CNF_Formula& cnf)
{
  //  DebugAssert(d_inCheckSat, "Should only be used as a call-back");
  DebugAssert(cnf.empty(), "Expected empty cnf");
  Expr e = d_cnfManager->concreteLit(l);
  CDMap<Expr, Theorem>::iterator i = d_theorems.find(e);
  DebugAssert(i != d_theorems.end(), "getExplanation: no explanation found");
  d_cnfManager->convertLemma((*i).second, cnf);  
  if (d_cnfManager->numVars() > d_vars.size()) {
    d_vars.resize(d_cnfManager->numVars(), SAT::Var::UNKNOWN);
  }
}


bool SearchSat::getNewClauses(CNF_Formula& cnf)
{
  unsigned i;

  Lit l;
  for (i = d_pendingLemmasNext; i < d_pendingLemmas.size(); ++i) {
    l = d_cnfManager->addLemma(d_pendingLemmas[i].first, d_lemmas);
    if (!recordNewRootLit(l, d_pendingLemmas[i].second, d_pendingScopes[i])) {
      // Already have this lemma: delete it
      d_lemmas.deleteLast();
    }
  }
  d_pendingLemmasNext = d_pendingLemmas.size();

  if (d_cnfManager->numVars() > d_vars.size()) {
    d_vars.resize(d_cnfManager->numVars(), SAT::Var::UNKNOWN);
  }

  DebugAssert(d_lemmasNext <= d_lemmas.numClauses(), "");
  if (d_lemmasNext == d_lemmas.numClauses()) return false;
  do {
    cnf += d_lemmas[d_lemmasNext];
    d_lemmasNext = d_lemmasNext + 1;
  } while (d_lemmasNext < d_lemmas.numClauses());
  return true;
}


Lit SearchSat::makeDecision()
{
  DebugAssert(d_inCheckSat, "Should only be used as a call-back");
  Lit litDecision;

  set<LitPriorityPair>::const_iterator i, iend;
  Lit lit;
  for (i = d_prioritySetStart, iend = d_prioritySet.end(); i != iend; ++i) {
    lit = (*i).getLit();
    if (findSplitterRec(lit, getValue(lit), &litDecision)) {
      break;
    }
  }
  d_prioritySetStart = i;
  return litDecision;
}


bool SearchSat::findSplitterRec(Lit lit, Var::Val value, Lit* litDecision)
{
  if (lit.isFalse() || lit.isTrue()) return false;

  unsigned i, n;
  Lit litTmp;
  Var varTmp;
  bool ret;
  Var v = lit.getVar();

  DebugAssert(value != Var::UNKNOWN, "expected known value");
  DebugAssert(getValue(lit) == value || getValue(lit) == Var::UNKNOWN,
              "invariant violated");

  if (checkJustified(v)) return false;

  if (lit.isInverted()) {
    value = Var::invertValue(value);
  }

  if (d_cnfManager->numFanins(v) == 0) {
    if (getValue(v) != Var::UNKNOWN) {
      setJustified(v);
      return false;
    }
    else {
      *litDecision = Lit(v, value == Var::TRUE_VAL);
      return true;
    }
  }
  else if (d_cnfManager->concreteVar(v).isAbsAtomicFormula()) {
    // This node represents a predicate with embedded ITE's
    // We handle this case specially in order to catch the
    // corner case when a variable is in its own fanin.
    n = d_cnfManager->numFanins(v);
    for (i=0; i < n; ++i) {
      litTmp = d_cnfManager->getFanin(v, i);
      varTmp = litTmp.getVar();
      DebugAssert(!litTmp.isInverted(),"Expected positive fanin");
      if (checkJustified(varTmp)) continue;
      DebugAssert(d_cnfManager->concreteVar(varTmp).getKind() == ITE,
                  "Expected ITE");
      DebugAssert(getValue(varTmp) == Var::TRUE_VAL,"Expected TRUE");
      Lit cIf = d_cnfManager->getFanin(varTmp,0);
      Lit cThen = d_cnfManager->getFanin(varTmp,1);
      Lit cElse = d_cnfManager->getFanin(varTmp,2);
      if (getValue(cIf) == Var::UNKNOWN) {
	if (getValue(cElse) == Var::TRUE_VAL ||
            getValue(cThen) == Var::FALSE_VAL) {
	  ret = findSplitterRec(cIf, Var::FALSE_VAL, litDecision);
	}
	else {
	  ret = findSplitterRec(cIf, Var::TRUE_VAL, litDecision);
	}
	if (!ret) {
	  cout << d_cnfManager->concreteVar(cIf.getVar()) << endl;
	  DebugAssert(false,"No controlling input found (1)");
	}	  
	return true;
      }
      else if (getValue(cIf) == Var::TRUE_VAL) {
	if (findSplitterRec(cIf, Var::TRUE_VAL, litDecision)) {
	    return true;
	}
	if (cThen.getVar() != v &&
            (getValue(cThen) == Var::UNKNOWN ||
             getValue(cThen) == Var::TRUE_VAL) &&
	    findSplitterRec(cThen, Var::TRUE_VAL, litDecision)) {
	  return true;
	}
      }
      else {
	if (findSplitterRec(cIf, Var::FALSE_VAL, litDecision)) {
	  return true;
	}
	if (cElse.getVar() != v &&
            (getValue(cElse) == Var::UNKNOWN ||
             getValue(cElse) == Var::TRUE_VAL) &&
	    findSplitterRec(cElse, Var::TRUE_VAL, litDecision)) {
	  return true;
	}
      }
      setJustified(varTmp);
    }
    if (getValue(v) != Var::UNKNOWN) {
      setJustified(v);
      return false;
    }
    else {
      *litDecision = Lit(v, value == Var::TRUE_VAL);
      return true;
    }
  }

  int kind = d_cnfManager->concreteVar(v).getKind();
  Var::Val valHard = Var::FALSE_VAL;
  switch (kind) {
    case AND:
      valHard = Var::TRUE_VAL;
    case OR:
      if (value == valHard) {
        n = d_cnfManager->numFanins(v);
	for (i=0; i < n; ++i) {
          litTmp = d_cnfManager->getFanin(v, i);
	  if (findSplitterRec(litTmp, valHard, litDecision)) {
	    return true;
	  }
	}
	DebugAssert(getValue(v) == valHard, "Output should be justified");
	setJustified(v);
	return false;
      }
      else {
        Var::Val valEasy = Var::invertValue(valHard);
        n = d_cnfManager->numFanins(v);
	for (i=0; i < n; ++i) {
          litTmp = d_cnfManager->getFanin(v, i);
	  if (getValue(litTmp) != valHard) {
	    if (findSplitterRec(litTmp, valEasy, litDecision)) {
	      return true;
	    }
	    DebugAssert(getValue(v) == valEasy, "Output should be justified");
            setJustified(v);
	    return false;
	  }
	}
	DebugAssert(false, "No controlling input found (2)");
      }
      break;
    case IMPLIES:
      DebugAssert(d_cnfManager->numFanins(v) == 2, "Expected 2 fanins");
      if (value == Var::FALSE_VAL) {
        litTmp = d_cnfManager->getFanin(v, 0);
        if (findSplitterRec(litTmp, Var::TRUE_VAL, litDecision)) {
          return true;
        }
        litTmp = d_cnfManager->getFanin(v, 1);
        if (findSplitterRec(litTmp, Var::FALSE_VAL, litDecision)) {
          return true;
        }
	DebugAssert(getValue(v) == Var::FALSE_VAL, "Output should be justified");
	setJustified(v);
	return false;
      }
      else {
        litTmp = d_cnfManager->getFanin(v, 0);
        if (getValue(litTmp) != Var::TRUE_VAL) {
          if (findSplitterRec(litTmp, Var::FALSE_VAL, litDecision)) {
            return true;
          }
          DebugAssert(getValue(v) == Var::TRUE_VAL, "Output should be justified");
          setJustified(v);
          return false;
	}
        litTmp = d_cnfManager->getFanin(v, 1);
        if (getValue(litTmp) != Var::FALSE_VAL) {
          if (findSplitterRec(litTmp, Var::TRUE_VAL, litDecision)) {
            return true;
          }
          DebugAssert(getValue(v) == Var::TRUE_VAL, "Output should be justified");
          setJustified(v);
          return false;
	}
	DebugAssert(false, "No controlling input found (3)");
      }
      break;
    case IFF: {
      litTmp = d_cnfManager->getFanin(v, 0);
      Var::Val val = getValue(litTmp);
      if (val != Var::UNKNOWN) {
	if (findSplitterRec(litTmp, val, litDecision)) {
	  return true;
	}
	if (value == Var::FALSE_VAL) val = Var::invertValue(val);
        litTmp = d_cnfManager->getFanin(v, 1);

	if (findSplitterRec(litTmp, val, litDecision)) {
	  return true;
	}
	DebugAssert(getValue(v) == value, "Output should be justified");
	setJustified(v);
	return false;
      }
      else {
        val = getValue(d_cnfManager->getFanin(v, 1));
        if (val == Var::UNKNOWN) val = Var::FALSE_VAL;
	if (value == Var::FALSE_VAL) val = Var::invertValue(val);
	if (findSplitterRec(litTmp, val, litDecision)) {
	  return true;
	}
	DebugAssert(false, "Unable to find controlling input (4)");
      }
      break;
    }
    case XOR: {
      litTmp = d_cnfManager->getFanin(v, 0);
      Var::Val val = getValue(litTmp);
      if (val != Var::UNKNOWN) {
	if (findSplitterRec(litTmp, val, litDecision)) {
	  return true;
	}
	if (value == Var::TRUE_VAL) val = Var::invertValue(val);
        litTmp = d_cnfManager->getFanin(v, 1);
	if (findSplitterRec(litTmp, val, litDecision)) {
	  return true;
	}
	DebugAssert(getValue(v) == value, "Output should be justified");
	setJustified(v);
	return false;
      }
      else {
        val = getValue(d_cnfManager->getFanin(v, 1));
        if (val == Var::UNKNOWN) val = Var::FALSE_VAL;
	if (value == Var::TRUE_VAL) val = Var::invertValue(val);
	if (findSplitterRec(litTmp, val, litDecision)) {
	  return true;
	}
	DebugAssert(false, "Unable to find controlling input (5)");
      }
      break;
    }
    case ITE: {
      Lit cIf = d_cnfManager->getFanin(v, 0);
      Lit cThen = d_cnfManager->getFanin(v, 1);
      Lit cElse = d_cnfManager->getFanin(v, 2);
      if (getValue(cIf) == Var::UNKNOWN) {
	if (getValue(cElse) == value ||
            getValue(cThen) == Var::invertValue(value)) {
	  ret = findSplitterRec(cIf, Var::FALSE_VAL, litDecision);
	}
	else {
	  ret = findSplitterRec(cIf, Var::TRUE_VAL, litDecision);
	}
	if (!ret) {
	  cout << d_cnfManager->concreteVar(cIf.getVar()) << endl;
	  DebugAssert(false,"No controlling input found (6)");
	}	  
	return true;
      }
      else if (getValue(cIf) == Var::TRUE_VAL) {
	if (findSplitterRec(cIf, Var::TRUE_VAL, litDecision)) {
	    return true;
	}
	if (cThen.isVar() && cThen.getVar() != v &&
            (getValue(cThen) == Var::UNKNOWN ||
             getValue(cThen) == value) &&
	    findSplitterRec(cThen, value, litDecision)) {
	  return true;
	}
      }
      else {
	if (findSplitterRec(cIf, Var::FALSE_VAL, litDecision)) {
	  return true;
	}
	if (cElse.isVar() && cElse.getVar() != v &&
            (getValue(cElse) == Var::UNKNOWN ||
             getValue(cElse) == value) &&
	    findSplitterRec(cElse, value, litDecision)) {
	  return true;
	}
      }
      DebugAssert(getValue(v) == value, "Output should be justified");
      setJustified(v);
      return false;
    }
    default:
      DebugAssert(false, "Unexpected Boolean operator");
      break;
  }
  FatalAssert(false, "Should be unreachable");
  return false;
}


QueryResult SearchSat::check(const Expr& e, Theorem& result, bool isRestart)
{
  DebugAssert(d_dplltReady, "SAT solver is not ready");
  if (isRestart && d_lastCheck.get().isNull()) {
    throw Exception
      ("restart called without former call to checkValid");
  }

  DebugAssert(!d_inCheckSat, "checkValid should not be called recursively");
  TRACE("searchsat", "checkValid: ", e, "");

  if (!e.getType().isBool())
    throw TypecheckException
      ("checking validity of a non-Boolean expression:\n\n  "
       + e.toString()
       + "\n\nwhich has the following type:\n\n  "
       + e.getType().toString());

  Expr e2 = e;

  // Set up and quick exits
  if (isRestart) {
    while (e2.isNot() && e2[0].isNot()) e2 = e2[0][0];
    if (e2.isTrue() || (e2.isNot() && e2[0].isFalse())) {
      result = d_lastValid;
      return INVALID;
    }
    if (e2.isFalse() || (e2.isNot() && e2[0].isTrue())) {
      pop();
      //TODO: real theorem
      d_lastValid = d_commonRules->assumpRule(d_lastCheck);
      result = d_lastValid;
      return VALID;
    }
  }
  else {
    if (e.isTrue()) {
      d_lastValid = d_commonRules->trueTheorem();
      result = d_lastValid;
      return VALID;
    }
    push();
    d_bottomScope = d_core->getCM()->scopeLevel();
    d_prioritySetBottomEntriesSizeStack.push_back(d_prioritySetBottomEntriesSize);
    d_lastCheck = e;
    e2 = !e;
  }

  Theorem thm;
  CNF_Formula_Impl cnf;
  QueryResult qres;
  d_cnfManager->setBottomScope(d_bottomScope);
  d_dplltReady = false;

  newUserAssumptionInt(e2, cnf, true);

  d_inCheckSat = true;
  
  getNewClauses(cnf);

  if (!isRestart && d_core->inconsistent()) {
    qres = UNSATISFIABLE;
    thm = d_rules->proofByContradiction(e, d_core->inconsistentThm());
    pop();
    d_lastValid = thm;
    d_cnfManager->setBottomScope(-1);
    d_inCheckSat = false;
    result = d_lastValid;
    return qres;
  }
  else {
    // Run DPLLT engine
    qres = isRestart ? d_dpllt->continueCheck(cnf) : d_dpllt->checkSat(cnf);
  }

  if (qres == UNSATISFIABLE) {
     DebugAssert(d_core->getCM()->scopeLevel() == d_bottomScope,
                "Expected unchanged context after unsat");
    e2 = d_lastCheck;
    pop();
    if (d_core->getTM()->withProof()) {
      Proof pf = d_dpllt->getSatProof(d_cnfManager, d_core);
      //      std::cout<<"WITH PROOF:"<<pf<<std::endl;
      d_lastValid = d_rules->satProof(e2, pf);
    }
    else {
      d_lastValid = d_commonRules->assumpRule(d_lastCheck);
    }
  }
  else {
    DebugAssert(d_lemmasNext == d_lemmas.numClauses(),
                "Expected no lemmas after satisfiable check");
    d_dplltReady = true;
    d_lastValid = Theorem();
    if (qres == SATISFIABLE && d_core->incomplete()) qres = UNKNOWN;

#ifdef _CVC3_DEBUG_MODE

    if( CVC3::debugger.trace("quant debug")  ){
      d_core->theoryOf(FORALL)->debug(1);
    }


    if( CVC3::debugger.trace("sat model unknown")  ){
      std::vector<SAT::Lit> cur_assigns = d_dpllt->getCurAssignments();
      cout<<"Current assignments"<<endl;
      {
	for(size_t i = 0 ; i < cur_assigns.size(); i++){
	  Lit l = cur_assigns[i];
	  Expr e = d_cnfManager->concreteLit(l);
	  
	  string val = " := ";
	  
	  if (l.isPositive()) val += "1"; else val += "0";
	  cout<<l.getVar()<<val<<endl;
	  //	  cout<<e<<endl;
	  
	}
      }
      
      
      std::vector< std::vector<SAT::Lit> > cur_clauses = d_dpllt->getCurClauses();
      cout<<"Current Clauses"<<endl;
      {
	for(size_t i = 0 ; i < cur_clauses.size(); i++){
	  //	cout<<"clause "<<i<<"================="<<endl;
	  for(size_t j = 0; j < cur_clauses[i].size(); j++){
	    
	    Lit l = cur_clauses[i][j];
	    string val ;
	    if (l.isPositive()) val += "+"; else val += "-";
	    cout<<val<<l.getVar()<<" ";
	  }
	  cout<<endl;
	}
      }
    }
    
    if( CVC3::debugger.trace("model unknown")  ){
      const CDList<Expr>& allterms = d_core->getTerms();
      cout<<"===========terms begin=========="<<endl;
      
      for (size_t i=0; i<allterms.size(); i++){
	//	cout<<"i="<<i<<" :"<<allterms[i].getFindLevel()<<":"<<d_core->simplifyExpr(allterms[i])<<"|"<<allterms[i]<<endl;
	cout<<"i="<<i<<" :"<<allterms[i].getFindLevel()<<":"<<d_core->simplifyExpr(allterms[i])<<"|"<<allterms[i]<<endl;

	  //<<" and type is "<<allterms[i].getType() 
	  //	    << " and kind is" << allterms[i].getEM()->getKindName(allterms[i].getKind())<<endl;
      }
      cout<<"-----------term end ---------"<<endl;
      const CDList<Expr>& allpreds = d_core->getPredicates();
      cout<<"===========pred begin=========="<<endl;
      
      for (size_t i=0; i<allpreds.size(); i++){
	if(allpreds[i].hasFind()){
	  if( (d_core->findExpr(allpreds[i])).isTrue()){
	    cout<<"ASSERT "<< allpreds[i] <<";" <<endl;
	  }
	  else{
	    cout<<"ASSERT NOT("<< allpreds[i] <<");" <<endl;
	  }
	  //	  cout<<"i="<<i<<" :";
	  //	  cout<<allpreds[i].getFindLevel();
	  //	  cout<<":"<<d_core->findExpr(allpreds[i])<<"|"<<allpreds[i]<<endl;
	}
	//	else cout<<"U "<<endl;;


	//" and type is "<<allpreds[i].getType() 
	//	    << " and kind is" << allpreds[i].getEM()->getKindName(allpreds[i].getKind())<<endl;
      }
      cout<<"-----------end----------pred"<<endl;
    }

    if( CVC3::debugger.trace("model unknown quant")  ){
      cout<<"=========== quant pred begin=========="<<endl;
      const CDList<Expr>& allpreds = d_core->getPredicates();
      for (size_t i=0; i<allpreds.size(); i++){

	Expr cur = allpreds[i];
	if(cur.isForall() || cur.isExists() || (cur.isNot() && (cur[0].isForall()||cur[0].isExists()))){
	  if(allpreds[i].hasFind()) {
	    cout<<"i="<<i<<" :";
	    cout<<allpreds[i].getFindLevel();
	    cout<<":"<<d_core->findExpr(allpreds[i])<<"|"<<allpreds[i]<<endl;
	  }
	}
      }
      cout<<"-----------end----------pred"<<endl;
    }

    if( CVC3::debugger.trace("model unknown nonquant")  ){
      cout<<"=========== quant pred begin=========="<<endl;
      const CDList<Expr>& allpreds = d_core->getPredicates();
      for (size_t i=0; i<allpreds.size(); i++){

	Expr cur = allpreds[i];
	if(cur.isForall() || cur.isExists() || 
	   (cur.isNot() && (cur[0].isForall()||cur[0].isExists())) ||
	   cur.isEq() || 
	   (cur.isNot() && cur[0].isEq())){
	}
	else{
	  if(allpreds[i].hasFind()) {
	    cout<<"i="<<i<<" :";
	    cout<<allpreds[i].getFindLevel();
	    cout<<":"<<d_core->findExpr(allpreds[i])<<"|"<<allpreds[i]<<endl;
	  }
	}
      }
      cout<<"-----------end----------pred"<<endl;
    }

    if( CVC3::debugger.trace("unknown state")  ){
      const CDList<Expr>& allpreds = d_core->getPredicates();
      cout<<"===========pred begin=========="<<endl;
      
      for (size_t i=0; i<allpreds.size(); i++){
	if(allpreds[i].hasFind()){
	  // 	  Expr cur(allpreds[i]);
// 	  if(cur.isForall() || cur.isExists() || 
// 	     (cur.isNot() && (cur[0].isForall()||cur[0].isExists()))
// 	     ){
// 	    continue;
// 	  }
	  
	  if( (d_core->findExpr(allpreds[i])).isTrue()){
	    cout<<":assumption "<< allpreds[i] <<"" <<endl;
	  }
	  else{
	    cout<<":assumption(not "<< allpreds[i] <<")" <<endl;
	  }
	  //	  cout<<"i="<<i<<" :";
	  //	  cout<<allpreds[i].getFindLevel();
	  //	  cout<<":"<<d_core->findExpr(allpreds[i])<<"|"<<allpreds[i]<<endl;
	}
	//	else cout<<"U "<<endl;;
	

	//" and type is "<<allpreds[i].getType() 
	//	    << " and kind is" << allpreds[i].getEM()->getKindName(allpreds[i].getKind())<<endl;
      }
      cout<<"-----------end----------pred"<<endl;
    }

    if( CVC3::debugger.trace("unknown state noforall")  ){
      const CDList<Expr>& allpreds = d_core->getPredicates();
      cout<<"===========pred begin=========="<<endl;
      
      for (size_t i=0; i<allpreds.size(); i++){
	if(allpreds[i].hasFind()){
  	  Expr cur(allpreds[i]);
//    	  if(cur.isForall() || cur.isExists() || 
//    	     (cur.isNot() && (cur[0].isForall()||cur[0].isExists()))
//    	     ){
//    	    continue;
//   	  }

	  if( (d_core->findExpr(allpreds[i])).isTrue()){
// 	    if(cur.isExists()){
//  	      continue;
//  	    }
	    cout<<"ASSERT "<< allpreds[i] <<";" <<endl;
//	    cout<<":assumption "<< allpreds[i] <<"" <<endl;
	  }
	  else if ( (d_core->findExpr(allpreds[i])).isFalse()){
//  	    if (cur.isForall()){
//  	      continue;
//  	    }
	    cout<<"ASSERT (NOT "<< allpreds[i] <<");" <<endl;
//	    cout<<":assumption(not "<< allpreds[i] <<")" <<endl;
	  }
	  else{
	    cout<<"--ERROR"<<endl;
	  }
	  //	  cout<<"i="<<i<<" :";
	  //	  cout<<allpreds[i].getFindLevel();
	  //	  cout<<":"<<d_core->findExpr(allpreds[i])<<"|"<<allpreds[i]<<endl;
	}
	//	else cout<<"U "<<endl;;
	

	//" and type is "<<allpreds[i].getType() 
	//	    << " and kind is" << allpreds[i].getEM()->getKindName(allpreds[i].getKind())<<endl;
      }
      cout<<"-----------end----------pred"<<endl;
    }


#endif
  }
  d_cnfManager->setBottomScope(-1);
  d_inCheckSat = false;
  result = d_lastValid;
  return qres;
}


SearchSat::SearchSat(TheoryCore* core, const string& name)
  : SearchEngine(core),
    d_name(name),
    d_bottomScope(core->getCM()->getCurrentContext(), -1),
    d_lastCheck(core->getCM()->getCurrentContext()),
    d_lastValid(core->getCM()->getCurrentContext(),
                d_commonRules->trueTheorem()),
    d_userAssumptions(core->getCM()->getCurrentContext()),
    d_intAssumptions(core->getCM()->getCurrentContext()),
    d_idxUserAssump(core->getCM()->getCurrentContext(), 0),
    d_decider(NULL),
    d_theorems(core->getCM()->getCurrentContext()),
    d_inCheckSat(false),
    d_lemmas(core->getCM()->getCurrentContext()),
    d_pendingLemmasSize(core->getCM()->getCurrentContext(), 0),
    d_pendingLemmasNext(core->getCM()->getCurrentContext(), 0),
    d_lemmasNext(core->getCM()->getCurrentContext(), 0),
    d_varsUndoListSize(core->getCM()->getCurrentContext(), 0),
    d_prioritySetStart(core->getCM()->getCurrentContext()),
    d_prioritySetEntriesSize(core->getCM()->getCurrentContext(), 0),
    d_prioritySetBottomEntriesSize(0),
    d_lastRegisteredVar(core->getCM()->getCurrentContext(), 0),
    d_dplltReady(core->getCM()->getCurrentContext(), true),
    d_nextImpliedLiteral(core->getCM()->getCurrentContext(), 0),
    d_restorer(core->getCM()->getCurrentContext(), this)
{
  d_cnfManager = new CNF_Manager(core->getTM(), core->getStatistics(),
                                 core->getFlags());

  d_cnfCallback = new SearchSatCNFCallback(this);
  d_cnfManager->registerCNFCallback(d_cnfCallback);
  d_coreSatAPI = new SearchSatCoreSatAPI(this);
  core->registerCoreSatAPI(d_coreSatAPI);
  d_theoryAPI = new SearchSatTheoryAPI(this);
  if (core->getFlags()["de"].getString() == "dfs") d_decider = new SearchSatDecider(this);

  if (core->getFlags()["sat"].getString() == "sat") {
#ifdef DPLL_BASIC
    d_dpllt = new DPLLTBasic(d_theoryAPI, d_decider, core->getCM(),
                             core->getFlags()["stats"].getBool());
#else
    throw CLException("SAT solver 'sat' not supported in this build");
#endif
  } else if (core->getFlags()["sat"].getString() == "minisat") {
    d_dpllt = new DPLLTMiniSat(d_theoryAPI, d_decider,
                               core->getFlags()["stats"].getBool(),
                               core->getTM()->withProof());
  } else {
    throw CLException("Unrecognized SAT solver name: " + (core->getFlags()["sat"].getString()));
  }

  d_prioritySetStart = d_prioritySet.end();
}


SearchSat::~SearchSat()
{
  delete d_dpllt;
  delete d_decider;
  delete d_theoryAPI;
  delete d_coreSatAPI;
  delete d_cnfCallback;
  delete d_cnfManager;
}


void SearchSat::registerAtom(const Expr& e)
{
  e.setUserRegisteredAtom();
  if (!e.isRegisteredAtom())
    d_core->registerAtom(e, Theorem());
}


Theorem SearchSat::getImpliedLiteral(void)
{
  Theorem imp;
  while (d_nextImpliedLiteral < d_core->numImpliedLiterals()) {
    imp = d_core->getImpliedLiteralByIndex(d_nextImpliedLiteral);
    d_nextImpliedLiteral = d_nextImpliedLiteral + 1;
    if (imp.getExpr().unnegate().isUserRegisteredAtom()) return imp;
  }
  return Theorem();
}


void SearchSat::returnFromCheck()
{
  if (d_bottomScope < 0) {
    throw Exception
      ("returnFromCheck called with no previous invalid call to checkValid");
  }
  pop();
}


static void setRecursiveInUserAssumption(const Expr& e, int scope)
{
  if (e.inUserAssumption()) return;
  for (int i = 0; i < e.arity(); ++i) {
    setRecursiveInUserAssumption(e[i], scope);
  }
  e.setInUserAssumption(scope);
}


void SearchSat::newUserAssumptionIntHelper(const Theorem& thm, CNF_Formula_Impl& cnf, bool atBottomScope)
{
  Expr e = thm.getExpr();
  if (e.isAnd()) {
    for (int i = 0; i < e.arity(); ++i) {
      newUserAssumptionIntHelper(d_commonRules->andElim(thm, i), cnf, atBottomScope);
    }
  }
  else {
    if ( ! d_core->getFlags()["cnf-formula"].getBool()) {
      if (!recordNewRootLit(d_cnfManager->addAssumption(thm, cnf), 0, atBottomScope)) {
	cnf.deleteLast();
      }
    }
    else{
      d_cnfManager->addAssumption(thm, cnf);
    }
    // if cnf-formula is enabled,  d_cnfManager->addAssumption returns a random literal, not a RootLit.  A random lit can make recordNewRootLit return false, which in turn makes cnf.deleteLast() to delete the last clause, which is not correct. 
  }
}


Theorem SearchSat::newUserAssumptionInt(const Expr& e, CNF_Formula_Impl& cnf, bool atBottomScope)
{
  DebugAssert(!d_inCheckSat,
              "User assumptions should be added before calling checkSat");
  Theorem thm;
  int scope;
  if (atBottomScope) scope = d_bottomScope;
  else scope = -1;
  setRecursiveInUserAssumption(e, scope);
  if (!isAssumption(e)) {
    e.setUserAssumption(scope);
    thm = d_commonRules->assumpRule(e, scope);
    d_userAssumptions.push_back(thm, scope);

    if (atBottomScope && d_bottomScope != d_core->getCM()->scopeLevel()) {
      //TODO: run preprocessor without using context-dependent information
      //TODO: this will break if we have stuff like the BVDIV rewrite that needs to get enqueued during preprocessing
      newUserAssumptionIntHelper(thm, cnf, true);
    }
    else {
      Theorem thm2 = d_core->getExprTrans()->preprocess(thm);
      Expr e2 = thm2.getExpr(); 
      if (e2.isFalse()) {
        d_core->addFact(thm2);
        return thm;
      }
      else if (!e2.isTrue()) {
        newUserAssumptionIntHelper(thm2, cnf, false);
      }
    }
    if (d_cnfManager->numVars() > d_vars.size()) {
      d_vars.resize(d_cnfManager->numVars(), SAT::Var::UNKNOWN);
    }
  }
  return thm;
}


Theorem SearchSat::newUserAssumption(const Expr& e)
{
  CNF_Formula_Impl cnf;
  Theorem thm = newUserAssumptionInt(e, cnf, false);
  d_dpllt->addAssertion(cnf);
  return thm;
}


void SearchSat::getUserAssumptions(vector<Expr>& assumptions)
{
  for(CDList<Theorem>::const_iterator i=d_userAssumptions.begin(),
        iend=d_userAssumptions.end(); i!=iend; ++i)
    assumptions.push_back((*i).getExpr());
}


void SearchSat::getInternalAssumptions(vector<Expr>& assumptions)
{
  for(CDList<Theorem>::const_iterator i=d_intAssumptions.begin(),
        iend=d_intAssumptions.end(); i!=iend; ++i)
    assumptions.push_back((*i).getExpr());
}



void SearchSat::getAssumptions(vector<Expr>& assumptions)
{
  CDList<Theorem>::const_iterator iU=d_userAssumptions.begin(),
    iUend=d_userAssumptions.end(), iI = d_intAssumptions.begin(),
    iIend=d_intAssumptions.end();
  while (true) {
    if (iI == iIend) {
      if (iU == iUend) break;
      assumptions.push_back((*iU).getExpr());
      ++iU;
    }
    else if (iU == iUend) {
      Expr intAssump = (*iI).getExpr();
      if (!intAssump.isUserAssumption()) {
        assumptions.push_back(intAssump);
      }
      ++iI;
    }
    else {
      if ((*iI).getScope() <= (*iU).getScope()) {
        Expr intAssump = (*iI).getExpr();
        if (!intAssump.isUserAssumption()) {
          assumptions.push_back(intAssump);
        }
        ++iI;
      }
      else {
        assumptions.push_back((*iU).getExpr());
        ++iU;
      }
    }
  }
}


bool SearchSat::isAssumption(const Expr& e)
{
  return e.isUserAssumption() || e.isIntAssumption();
}


void SearchSat::getCounterExample(vector<Expr>& assumptions, bool inOrder)
{
  if (!d_lastValid.get().isNull()) {
    throw Exception("Expected last query to be invalid");
  }
  getInternalAssumptions(assumptions);
}


Proof SearchSat::getProof()
{
  if(!d_core->getTM()->withProof())
    throw EvalException
      ("getProof cannot be called without proofs activated");
  if(d_lastValid.get().isNull())
    throw EvalException
      ("getProof must be called only after a successful check");
  if(d_lastValid.get().isNull()) return Proof();
  else  return d_lastValid.get().getProof();
}
