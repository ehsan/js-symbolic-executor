/*****************************************************************************/
/*!
 *\file dpllt_basic.cpp
 *\brief Basic implementation of dpllt module using generic sat solver
 *
 * Author: Clark Barrett
 *
 * Created: Mon Dec 12 19:09:43 2005
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


#include "dpllt_basic.h"
#include "cnf.h"
#include "sat_api.h"
#include "exception.h"


using namespace std;
using namespace CVC3;
using namespace SAT;


//int level_ = 0;

static void SATDLevelHook(void *cookie, int change)
{
  //cout << "backtrack to: " << level_ << " " << change << endl;
  //level_ += change;
  //  cout<<"decision level called"<<endl;
  DPLLTBasic* db = static_cast<DPLLTBasic*>(cookie);
  for (; change > 0; change--) {
    db->theoryAPI()->push();
  }
  for (; change < 0; change++) {
    db->theoryAPI()->pop();
  }
}


static SatSolver::Lit SATDecisionHook(void *cookie, bool *done)
{
  // cout<<"sat decision called"<<endl;
  DPLLTBasic* db = static_cast<DPLLTBasic*>(cookie);

  if (db->theoryAPI()->outOfResources()) {
    // Tell SAT solver to exit with satisfiable result
    *done = true;
    return SatSolver::Lit();
  }

  if (!db->decider()) {
    // Tell SAT solver to make its own choice
    if (!*done) return SatSolver::Lit();
  }
  else {
    Lit lit = db->decider()->makeDecision();
    if (!lit.isNull()) {
      //cout << "Split: " << lit.getVar().getIndex() << endl;
      // Tell SAT solver which literal to split on
      *done = false;
      return db->cvc2SAT(lit);
    }
  }

  CNF_Formula_Impl cnf;
  DPLLT::ConsistentResult result;
  result = db->theoryAPI()->checkConsistent(cnf, true);

  if (result == DPLLT::MAYBE_CONSISTENT) {
    IF_DEBUG(bool added = ) db->theoryAPI()->getNewClauses(cnf);
    DebugAssert(added, "Expected new clauses");
    db->addNewClauses(cnf);
    *done = true;
    SatSolver::Lit l;
    l.id = 0;
    return l;
  }
  else if (result == DPLLT::INCONSISTENT) {
    db->addNewClauses(cnf);
  }

  // Tell SAT solver that we are done
  *done = true;
  return SatSolver::Lit();
}


static void SATAssignmentHook(void *cookie, SatSolver::Var var, int value)
{
  //  cout<<"assignment called"<<endl;
  DPLLTBasic* db = static_cast<DPLLTBasic*>(cookie);
  TRACE("DPLL Assign", var.id, " := ", value);
  if (value == 0)
    db->theoryAPI()->assertLit(Lit(db->satSolver()->GetVarIndex(var), false));
  else if (value == 1)
    db->theoryAPI()->assertLit(Lit(db->satSolver()->GetVarIndex(var), true));
  else return;
  CNF_Formula_Impl cnf;
  DPLLT::ConsistentResult result;
  result = db->theoryAPI()->checkConsistent(cnf, false);
  if (result == DPLLT::INCONSISTENT) {
    db->addNewClauses(cnf);
  }
}


static void SATDeductionHook(void *cookie)
{
  //  cout<<"deduction called"<<endl;;
  DPLLTBasic* db = static_cast<DPLLTBasic*>(cookie);
  Clause c;
  CNF_Formula_Impl cnf;
  if (db->theoryAPI()->getNewClauses(cnf)) {
    db->addNewClauses(cnf);
    cnf.reset();
  }
  Lit l = db->theoryAPI()->getImplication();
  while (!l.isNull()) {
    db->theoryAPI()->getExplanation(l, cnf);
    db->addNewClauses(cnf);
    cnf.reset();
    l = db->theoryAPI()->getImplication();
  }
}


void DPLLTBasic::createManager()
{
  d_mng = SatSolver::Create();
  d_mng->RegisterDLevelHook(SATDLevelHook, this);
  d_mng->RegisterDecisionHook(SATDecisionHook, this);
  d_mng->RegisterAssignmentHook(SATAssignmentHook, this);
  d_mng->RegisterDeductionHook(SATDeductionHook, this);
}


void DPLLTBasic::generate_CDB (CNF_Formula_Impl& cnf)
{
  CNF_Formula::const_iterator i, iend;
  Clause::const_iterator j, jend;
  vector<SatSolver::Lit> clause;
  if (cnf.numVars() > unsigned(d_mng->NumVariables())) {
    d_mng->AddVariables(cnf.numVars() - d_mng->NumVariables());
  }
  cnf.simplify();
  for (i = cnf.end()-1, iend = cnf.begin()-1; i != iend; --i) {
    //for (i = cnf.begin(), iend = cnf.end(); i != iend; i++) {
    if ((*i).isSatisfied()) continue;
    for (j = (*i).begin(), jend = (*i).end(); j != jend; ++j) {
      if (!(*j).isFalse()) clause.push_back(cvc2SAT(*j));
    }
    if (clause.size() != 0) {
      d_mng->AddClause(clause);
      clause.clear();
    }
  }
}


void DPLLTBasic::handle_result(SatSolver::SATStatus outcome)
{
  const char * result = "UNKNOWN";
  switch (outcome) {
    case SatSolver::SATISFIABLE:
//         if (d_printStats) {
//           cout << "Instance satisfiable" << endl;
//           for (int i=1, sz = d_mng->NumVariables(); i <= sz; ++i) {
//             switch(d_mng->GetVarAssignment(d_mng->GetVar(i))) {
//               case -1:
//                 cout <<"("<< i<<")"; break;
//               case 0:
//                 cout << "-" << i; break;
//               case 1:
//                 cout << i ; break;
//               default:
//                 throw Exception("Unknown variable value state");
// 	    }
//             cout << " ";
//           }
//           cout << endl;
//         }
	result = "SAT";
	break;
    case SatSolver::UNSATISFIABLE:
	result  = "UNSAT";
        if (d_printStats) cout << "Instance unsatisfiable" << endl;
	break;
    case SatSolver::BUDGET_EXCEEDED:
	result  = "ABORT : TIME OUT";
	cout << "Time out, unable to determine the satisfiablility of the instance";
	cout << endl;
	break;
    case SatSolver::OUT_OF_MEMORY:
	result  = "ABORT : MEM OUT";
	cout << "Memory out, unable to determing the satisfiablility of the instance";
	cout << endl;
	break;
    default:
      throw Exception("DPLTBasic::handle_result: Unknown outcome");
  }
  if (d_printStats) d_mng->PrintStatistics();
}


void DPLLTBasic::verify_solution()
{
  // Used to check that all clauses are true, but our decision maker
  // may ignore some clauses that are no longer relevant, so now we check to
  // make sure no clause is false.
  for (SatSolver::Clause cl = d_mng->GetFirstClause(); !cl.IsNull();
       cl = d_mng->GetNextClause(cl)) {
    vector<SatSolver::Lit> lits;
    d_mng->GetClauseLits(cl, &lits);
    for (; lits.size() != 0;) {
      SatSolver::Lit lit = lits.back();
      SatSolver::Var var = d_mng->GetVarFromLit(lit);
      int sign = d_mng->GetPhaseFromLit(lit);
      int var_value = d_mng->GetVarAssignment(var);
      if( (var_value == 1 && sign == 0) ||
	  (var_value == 0 && sign == 1) ||
          (var_value == -1) ) break;
      lits.pop_back();
    }
    DebugAssert(lits.size() != 0, "DPLLTBasic::verify_solution failed");
  }
}


DPLLTBasic::DPLLTBasic(TheoryAPI* theoryAPI, Decider* decider, ContextManager* cm,
                       bool printStats)
  : DPLLT(theoryAPI, decider), d_cm(cm), d_ready(true),
    d_printStats(printStats),
    d_pushLevel(cm->getCurrentContext(), 0),
    d_readyPrev(cm->getCurrentContext(), true),
    d_prevStackSize(cm->getCurrentContext(), 0),
    d_prevAStackSize(cm->getCurrentContext(), 0)
{
  createManager();
  d_cnf = new CNF_Formula_Impl();
  d_assertions = new CD_CNF_Formula(d_cm->getCurrentContext());
}


DPLLTBasic::~DPLLTBasic()
{
  if (d_assertions) delete d_assertions;
  if (d_cnf) delete d_cnf;
  if (d_mng) delete d_mng;
  while (d_assertionsStack.size() > 0) {
    d_assertions = d_assertionsStack.back();
    d_assertionsStack.pop_back();
    delete d_assertions;
  }
  while (d_mngStack.size() > 0) {
    d_mng = d_mngStack.back();
    d_mngStack.pop_back();
    delete d_mng;
    d_cnf = d_cnfStack.back();
    d_cnfStack.pop_back();
    delete d_cnf;
  }
}


void DPLLTBasic::addNewClause(const Clause& c)
{
  DebugAssert(c.size() > 0, "Expected non-empty clause");
  DebugAssert(c.getMaxVar() <= unsigned(d_mng->NumVariables()),
              "Expected no new variables");
  vector<SatSolver::Lit> lits;
  for (Clause::const_iterator i = c.begin(), iend = c.end(); i < iend; ++i) {
    if (!(*i).isFalse()) lits.push_back(cvc2SAT(*i));
  }
  satSolver()->AddClause(lits);
  (*d_cnf) += c;
}


void DPLLTBasic::addNewClauses(CNF_Formula_Impl& cnf)
{
  CNF_Formula::const_iterator i, iend;
  Clause::const_iterator j, jend;
  vector<SatSolver::Lit> clause;
  if (cnf.numVars() > unsigned(d_mng->NumVariables())) {
    d_mng->AddVariables(cnf.numVars() - d_mng->NumVariables());
  }
  cnf.simplify();
  for (i = cnf.end()-1, iend = cnf.begin()-1; i != iend; --i) {
    //for (i = cnf.begin(), iend = cnf.end(); i != iend; i++) {
    if ((*i).isSatisfied()) continue;
    for (j = (*i).begin(), jend = (*i).end(); j != jend; ++j) {
      if (!(*j).isFalse()) clause.push_back(cvc2SAT(*j));
    }
    if (clause.size() != 0) {
      d_mng->AddClause(clause);
      clause.clear();
    }
  }
  generate_CDB(cnf);
  (*d_cnf) += cnf;
}


void DPLLTBasic::push()
{
  d_theoryAPI->push();
  d_pushLevel = d_pushLevel + 1;
  d_prevStackSize = d_mngStack.size();
  d_prevAStackSize = d_assertionsStack.size();
  d_readyPrev = d_ready;
}


void DPLLTBasic::pop()
{
  unsigned pushLevel = d_pushLevel;
  unsigned prevStackSize = d_prevStackSize;
  unsigned prevAStackSize = d_prevAStackSize;
  bool readyPrev = d_readyPrev;

  while (d_assertionsStack.size() > prevAStackSize) {
    delete d_assertions;
    d_assertions = d_assertionsStack.back();
    d_assertionsStack.pop_back();
  }

  while (d_mngStack.size() > prevStackSize) {
    delete d_mng;
    delete d_cnf;
    d_mng = d_mngStack.back();
    d_mngStack.pop_back();
    d_cnf = d_cnfStack.back();
    d_cnfStack.pop_back();
    DebugAssert(d_mngStack.size() == d_cnfStack.size(), "size mismatch");
  }

  if (d_mngStack.size() == 0) {
    if (readyPrev && !d_ready) {
      delete d_mng;
      delete d_cnf;
      createManager();
      d_cnf = new CNF_Formula_Impl();
      d_ready = true;
    }
    else {
      DebugAssert(readyPrev == d_ready, "Unexpected ready values");
    }
  }
  else {
    DebugAssert(!d_ready, "Expected ready to be false");
  }

  while (d_pushLevel == pushLevel)
    d_theoryAPI->pop();

}

std::vector<SAT::Lit> DPLLTBasic::getCurAssignments(){
  std::vector<SAT::Lit> nothing;
  return nothing;
}

std::vector<std::vector<SAT::Lit> > DPLLTBasic::getCurClauses(){
  std::vector<std::vector<SAT::Lit> > nothing;
  return nothing;
}


void DPLLTBasic::addAssertion(const CNF_Formula& cnf)
{
  // Immediately assert unit clauses
  CNF_Formula::const_iterator i, iend;
  Clause::const_iterator j, jend;
  for (i = cnf.end()-1, iend = cnf.begin()-1; i != iend; --i) {
    if ((*i).isUnit()) {
      j = (*i).begin();
      d_theoryAPI->assertLit(*j);
    }
  }

  // Accumulate assertions in d_assertions
  (*d_assertions) += cnf;
}


QueryResult DPLLTBasic::checkSat(const CNF_Formula& cnf)
{
  SatSolver::SATStatus result;

  if (!d_ready) {
    // Copy current formula
    d_cnfStack.push_back(d_cnf);
    d_cnf = new CNF_Formula_Impl(*d_cnf);

    // make unit clauses for current assignment
    int value;
    for (int i = 1; i <= d_mng->NumVariables(); ++i) {
      value = d_mng->GetVarAssignment(d_mng->GetVar(i));
      if (value == 1) {
        d_cnf->newClause();
        d_cnf->addLiteral(Lit(i));
      }
      else if (value == 0) {
        d_cnf->newClause();
        d_cnf->addLiteral(Lit(i, false));
      }
    }

    // Create new manager
    d_mngStack.push_back(d_mng);
    DebugAssert(d_mngStack.size() == d_cnfStack.size(), "size mismatch");
    createManager();
  }
  d_ready = false;

  if (d_assertions) (*d_cnf) += (*d_assertions);

  (*d_cnf) += cnf;
  generate_CDB(*d_cnf);

  d_theoryAPI->push();

  result = d_mng->Satisfiable(true);
  if (result == SatSolver::SATISFIABLE && theoryAPI()->outOfResources())
    result = SatSolver::BUDGET_EXCEEDED;

  // Print result

  if (result == SatSolver::SATISFIABLE) {
    verify_solution();
    if (d_assertions->numClauses() > 0) {
      d_assertionsStack.push_back(d_assertions);
      d_assertions = new CD_CNF_Formula(d_cm->getCurrentContext());
    }
  }
  handle_result (result);

  if (result == SatSolver::UNSATISFIABLE) {
    d_theoryAPI->pop();
    delete d_mng;
    delete d_cnf;
    if (d_mngStack.size() == 0) {
      createManager();
      d_cnf = new CNF_Formula_Impl();
      d_ready = true;
    }
    else {
      d_mng = d_mngStack.back();
      d_mngStack.pop_back();
      d_cnf = d_cnfStack.back();
      d_cnfStack.pop_back();
      DebugAssert(d_mngStack.size() == d_cnfStack.size(), "size mismatch");
    }
  }

  return (result == SatSolver::UNSATISFIABLE ? UNSATISFIABLE :
          result == SatSolver::SATISFIABLE ? SATISFIABLE :
          ABORT);
}


QueryResult DPLLTBasic::continueCheck(const CNF_Formula& cnf)
{
  SatSolver::SATStatus result;

  if (d_ready) {
    throw Exception
      ("continueCheck should be called after a previous satisfiable result");
  }
  if (d_assertions->numClauses() > 0) {
    throw Exception
      ("a check cannot be continued if new assertions have been made");
  }
  CNF_Formula_Impl cnfImpl(cnf);

  generate_CDB(cnfImpl);
  (*d_cnf) += cnfImpl;

  result = d_mng->Continue();
  if (result == SatSolver::SATISFIABLE && theoryAPI()->outOfResources())
    result = SatSolver::BUDGET_EXCEEDED;

  // Print result

  if (result == SatSolver::SATISFIABLE)
    verify_solution();
  handle_result (result);

  if (result == SatSolver::UNSATISFIABLE) {
    d_theoryAPI->pop();
    delete d_mng;
    delete d_cnf;
    if (d_mngStack.size() == 0) {
      createManager();
      d_cnf = new CNF_Formula_Impl();
      d_ready = true;
    }
    else {
      d_mng = d_mngStack.back();
      d_mngStack.pop_back();
      d_cnf = d_cnfStack.back();
      d_cnfStack.pop_back();
      DebugAssert(d_mngStack.size() == d_cnfStack.size(), "size mismatch");
    }
  }

  return (result == SatSolver::UNSATISFIABLE ? UNSATISFIABLE :
          result == SatSolver::SATISFIABLE ? SATISFIABLE :
          ABORT);
}

CVC3::Proof  DPLLTBasic::getSatProof(CNF_Manager* cnfManager, CVC3::TheoryCore* core){
  CVC3::Proof temp;
  return temp;
}

