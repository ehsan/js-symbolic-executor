/*****************************************************************************/
/*!
 *\file dpllt_minisat.cpp
 *\brief Implementation of dpllt module using MiniSat
 *
 * Author: Alexander Fuchs
 *
 * Created: Fri Sep 08 11:04:00 2006
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
//we need this to use newPf
#define _CVC3_TRUSTED_ 

#include "dpllt_minisat.h"
#include "minisat_solver.h"
#include "sat_proof.h"
#include "theorem_producer.h"
#include "exception.h"

using namespace std;
using namespace CVC3;
using namespace SAT;


DPLLTMiniSat::DPLLTMiniSat(TheoryAPI* theoryAPI, Decider* decider,
			   bool printStats, bool createProof)
  : DPLLT(theoryAPI, decider), d_printStats(printStats),
    d_createProof(createProof), d_proof(NULL) {
  pushSolver();
}

DPLLTMiniSat::~DPLLTMiniSat() {
  while (!d_solvers.empty()) {
    // don't pop theories, this is not allowed when cvc shuts down.
    delete (d_solvers.top());
    d_solvers.pop();
  }
  delete d_proof;
}

MiniSat::Solver* DPLLTMiniSat::getActiveSolver() {
  DebugAssert(!d_solvers.empty(), "DPLLTMiniSat::getActiveSolver: no solver");
  return d_solvers.top();
}


void DPLLTMiniSat::pushSolver() {
  if (d_solvers.empty()) {
    d_solvers.push(new MiniSat::Solver(d_theoryAPI, d_decider, d_createProof));
  }
  else {
    d_solvers.push(MiniSat::Solver::createFrom(getActiveSolver()));
  }
}

QueryResult DPLLTMiniSat::search()
{
  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::search: no solver");
  DebugAssert(getActiveSolver()->inPush(), "DPLLTMiniSat::search: solver not pushed");

  // search
  MiniSat::Solver* solver = getActiveSolver();
  QueryResult result = solver->search();

  // print statistics
  if (d_printStats) {
    switch (result) {
    case SATISFIABLE:
      break;
    case UNSATISFIABLE:
      cout << "Instance unsatisfiable" << endl;
      break;
    case ABORT:
      cout << "aborted, unable to determine the satisfiablility of the instance" << endl;
      break;
    case UNKNOWN:
      cout << "unknown, unable to determing the satisfiablility of the instance" << endl;
      break;
    default:
      FatalAssert(false, "DPLTBasic::handle_result: Unknown outcome");
    }
    
    cout << "Number of Decisions\t\t\t" << solver->getStats().decisions << endl;
    cout << "Number of Propagations\t\t\t" << solver->getStats().propagations << endl;
    cout << "Number of Propositional Conflicts\t"
	 << (solver->getStats().conflicts - solver->getStats().theory_conflicts) << endl;
    cout << "Number of Theory Conflicts\t\t" << solver->getStats().theory_conflicts << endl;
    cout << "Number of Variables\t\t\t" << solver->nVars() << endl;
    cout << "Number of Literals\t\t\t"
	 << (solver->getStats().clauses_literals + solver->getStats().learnts_literals) << endl;
    cout << "Max. Number of Literals\t\t\t" << solver->getStats().max_literals << endl;
    cout << "Number of Clauses\t\t\t" << solver->getClauses().size() << endl;
    cout << "Number of Lemmas\t\t\t" << solver->getLemmas().size() << endl;
    cout << "Max. Decision Level\t\t\t" << solver->getStats().max_level << endl;
    cout << "Number of Deleted Clauses\t\t" << solver->getStats().del_clauses << endl;
    cout << "Number of Deleted Lemmas\t\t" << solver->getStats().del_lemmas << endl;
    cout << "Number of Database Simplifications\t" << solver->getStats().db_simpl << endl;
    cout << "Number of Lemma Cleanups\t\t" << solver->getStats().lm_simpl << endl;
    
    cout << "Debug\t\t\t\t\t" << solver->getStats().debug << endl;
  }

  // the dpllt interface requires that for an unsat result
  // all theory pops are undone right away.
  if (result == UNSATISFIABLE) {
    //    cout << "unsat" <<endl;
    //    return result;
    if (d_createProof ) {
      delete d_proof;
      //      cout<<"creating proof" << endl;
      DebugAssert(d_solvers.top()->getDerivation() != NULL, "DplltMiniSat::search: no proof");
      d_proof = d_solvers.top()->getDerivation()->createProof();
    }
    d_solvers.top()->popTheories();
    d_theoryAPI->pop();
  }

  return result;
}


QueryResult DPLLTMiniSat::checkSat(const CNF_Formula& cnf)
{
  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::checkSat: no solver");

  // perform any requested solver pops
  getActiveSolver()->doPops();

  DebugAssert(!getActiveSolver()->inSearch(), "DPLLTMiniSat::checkSat: solver already in search");

  // required by dpllt interface: theory push before search
  d_theoryAPI->push();
    
  // solver already in use, so create a new solver
  if (getActiveSolver()->inSearch()) {
    pushSolver();
  }

  // add new formula and search
  getActiveSolver()->addFormula(cnf, false);
  return search();
}


QueryResult DPLLTMiniSat::continueCheck(const CNF_Formula& cnf) 
{
  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::continueCheck: no solver");

  // if the current solver has no push, all its pushes have already been undone,
  // so remove it
  if (!getActiveSolver()->inPush()) {
    DebugAssert(!getActiveSolver()->inSearch(), "DPLLTMiniSat::continueCheck: solver without push in search");
    delete getActiveSolver();
    d_solvers.pop();
  }

  // perform any requested solver pops
  getActiveSolver()->doPops();

  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::continueCheck: no solver (2)");
  DebugAssert(getActiveSolver()->inPush(), "DPLLTMiniSat::continueCheck: solver not in push");
  DebugAssert(getActiveSolver()->inSearch(), "DPLLTMiniSat::continueCheck: solver not in search");

  // add new formula and search
  getActiveSolver()->addFormula(cnf, false);
  return search();
}


void DPLLTMiniSat::push() {
  // perform any requested solver pops
  getActiveSolver()->doPops();

  // if the current solver is already in a search, then create a new one
  if (getActiveSolver()->inSearch()) {
    pushSolver();
  }
  
  getActiveSolver()->push();
  d_theoryAPI->push();
}

void DPLLTMiniSat::pop() {
  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::pop: no solver");

  // if the current solver has no push, all its pushes have already been undone,
  // so remove it
  if (!getActiveSolver()->inPush()) {
    DebugAssert(!getActiveSolver()->inSearch(), "DPLLTMiniSat::pop: solver without push in search");
    delete getActiveSolver();
    d_solvers.pop();
  }

  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::pop: no solver 2");
  DebugAssert(getActiveSolver()->inPush(), "DPLLTMiniSat::pop: solver not in push");

  // undo checkSat theory push for an invalid query.
  // for a valid query this is done in search right away.
  if (getActiveSolver()->inSearch() && getActiveSolver()->isConsistent()) {
    d_theoryAPI->pop();  
  }
  getActiveSolver()->requestPop();
  d_theoryAPI->pop();
}

std::vector<SAT::Lit> DPLLTMiniSat::getCurAssignments(){
  return getActiveSolver()->curAssigns();
} 

std::vector<std::vector<SAT::Lit> > DPLLTMiniSat::getCurClauses(){
  return getActiveSolver()->curClauses();
}

void DPLLTMiniSat::addAssertion(const CNF_Formula& cnf) {
  // perform any requested solver pops
  getActiveSolver()->doPops();

  // if the current solver is already performing a search create a new solver
  if (getActiveSolver()->inSearch()) {
    pushSolver();
  }

  getActiveSolver()->addFormula(cnf, false);

  // Immediately assert unit clauses -
  // the intention is to make these immediately available for interactive use
  for (CNF_Formula::const_iterator i = cnf.begin(); i != cnf.end(); ++i) {
    if ((*i).isUnit() && getActiveSolver()->isConsistent()) {
      d_theoryAPI->assertLit(*(*i).begin());
    }
  }
}


Var::Val DPLLTMiniSat::getValue(Var var) {
  DebugAssert(d_solvers.size() > 0,
	      "DPLLTMiniSat::getValue: should be called after a previous satisfiable result");

  MiniSat::lbool value = getActiveSolver()->getValue(MiniSat::cvcToMiniSat(var));
  if (value == MiniSat::l_True)
    return Var::TRUE_VAL;
  else if (value == MiniSat::l_False)
    return Var::FALSE_VAL;
  else
    return Var::UNKNOWN;
}


CVC3::Proof generateSatProof(SAT::SatProofNode* node, CNF_Manager* cnfManager, TheoremProducer* thmProducer){
  if(node->hasNodeProof())    { 
    return node->getNodeProof();
  }
  if (node->isLeaf()){

    /*
//<<<<<<< dpllt_minisat.cpp

    SAT::Clause curClause =  *(node->getLeaf());

    DebugAssert(!curClause.isNull(), "Null clause found in generateSatProof");

    cout << "get leaf clause " << curClause.getId() << endl; 

    const CVC3::Theorem clauseThm = curClause.getClauseTheorem();
//=======
    */

    const CVC3::Theorem clauseThm = node->getLeaf();

    /*
//>>>>>>> 1.14
    */

    DebugAssert(!clauseThm.isNull(), "Null thm found in generateSatProof");
    node->setNodeProof(clauseThm.getProof());
//     cout<<"set proof " << clauseThm.getProof() << endl;
//     cout<<"set proof for theorem " << clauseThm << endl;
    return clauseThm.getProof();
  }
  else{
    CVC3::Proof leftProof = generateSatProof(node->getLeftParent(), cnfManager, thmProducer);
    CVC3::Proof rightProof = generateSatProof(node->getRightParent(), cnfManager, thmProducer);

    if(node->getLeftParent() == node->getRightParent() ) cout<<"***error ********"<<endl;
    vector<Proof> pfs;
    pfs.push_back(leftProof);
    pfs.push_back(rightProof);
    //    if(leftProof == rightProof) cout<<"***********"<<endl;

    Lit lit = node->getLit();
    Expr e = cnfManager->concreteLit(lit);
    Expr e_trans = cnfManager->concreteLit(lit,false);
//     cout<<"set lit "<<lit.getVar()<<endl << e_trans <<endl << e << endl;
//     cout<<"set lit "<<lit.getVar()<<endl << e_trans.getIndex() <<endl ;
     if(e != e_trans){
//         cout<<"-diff e "<<e<<endl<<flush;
//         cout<<"-diff e_trans " <<e_trans <<endl <<flush; 
     }
     //      {
     //        cout<<"Lit "<<lit.getID() << " " ;
     //        if (lit.isNull()) cout << "NULL";
     //        else if (lit.isFalse()) cout << "F";
     //        else if (lit.isTrue()) cout << "T";
     //        else {
     //  	if (!lit.isPositive()) cout << "-";
     //  	cout << lit.getVar();
     //        }
     //        cout<<endl;
     //      }
     
     //      cout<<"e "<<e<<endl<<flush;
    Proof pf;
    pf = thmProducer->newPf("bool_resolution", e_trans, pfs);
    node->setNodeProof(pf);
    return pf;

  }
  
}

void printSatProof(SAT::SatProofNode* node){
  if (node->isLeaf()){
    CVC3::Theorem theorem = node->getLeaf();
    
    if(theorem.isNull()){
      cout<<"theorem null"<<endl;
    }
    else{
      cout<<"====================" << endl;
      /*
//<<<<<<< dpllt_minisat.cpp
      clause.print();
      cout<<"--------------------" << endl;
      */
      /*      
      const CVC3::Theorem clauseThm = clause.getClauseTheorem();
      cout<<"====================" << endl;
      clause.print();
//=======
      theorem.print();
//>>>>>>> 1.14
      cout<<"--------------------" << endl;
//<<<<<<< dpllt_minisat.cpp
      if(clauseThm.isNull()){
	cout<<"leaf id " << clause.getId() << " # " <<  "NULL"  << endl;
      }
      else{
	cout<<"leaf id " << clause.getId() << " # " <<  clauseThm << endl;
	}
      */
      /*
//=======
//>>>>>>> 1.14
	  */
    }
  }
  else{
    SAT::SatProofNode * leftNode = node->getLeftParent();
    SAT::SatProofNode * rightNode = node->getRightParent();

    printSatProof(leftNode);
    printSatProof(rightNode);
  }

}



CVC3::Proof DPLLTMiniSat::getSatProof(CNF_Manager* cnfManager, CVC3::TheoryCore* core){
  SAT::SatProof* proof = getProof();
  SAT::SatProofNode * rootNode = proof->getRoot();
  
  //  printSatProof(rootNode);
  
  CVC3::TheoremProducer* thmProducer = new TheoremProducer(core->getTM());

  return generateSatProof(rootNode, cnfManager, thmProducer);
}

