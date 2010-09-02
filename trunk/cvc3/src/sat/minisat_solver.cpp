/*****************************************************************************/
/*!
 *\file minisat_solver.cpp
 *\brief Adaptation of MiniSat to DPLL(T)
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

/****************************************************************************************[Solver.C]
MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "minisat_solver.h"
#include "minisat_types.h"
#include <cmath>
#include <iostream>
#include <algorithm>

using namespace std;
using namespace MiniSat;


///
/// Constants
///


// if true do propositional propagation to exhaustion
// before asserting propagated literals to the theories.
// that is, a SAT propagation is not immediately asserted to the theories as well,
// but only when the SAT core has to do a decision.
//
// this way a branch may be closed propositionally only,
// which avoids work on the theory part,
// and introduction of new theory clauses and implications.
const bool defer_theory_propagation = true;


/// theory implications

// retrieve explanations of theory implications eagerly
// and store them right away as clauses
const bool eager_explanation = true;

// if explanations for theory implications are retrieved lazily
// during regressions, should they be added as clauses?
//
// only used if eager_explanation is false.
const bool keep_lazy_explanation = true;


/// pushes

// determines which theory operations are done,
// when unit propagation is done to exhaustion at the root level
// because a push is done.
 
// if true then assert propositional propagations to theories as well
// (this is done anyway when defer_theory_propagation is false)
const bool push_theory_propagation = true;

// if push_theory_propagation is also true,
// retrieve and propagate theory implications as well
const bool push_theory_implication = true;

// if push_theory_propagation is also true,
// retrieve and add theory clauses as well (and handle their propagations)
const bool push_theory_clause = true;




// the number of literals considered in propLookahead()
const vector<Var>::size_type prop_lookahead = 1;


// print the derivation
const bool protocol = false;
//const bool protocol = true;




// perform expensive assertion checks
const bool debug_full = false;




///
/// conversions between MiniSat and CVC data types:
///

bool MiniSat::cvcToMiniSat(const SAT::Clause& clause, std::vector<Lit>& literals) {
  // register all clause literals
  SAT::Clause::const_iterator j, jend;

  for (j = clause.begin(), jend = clause.end(); j != jend; ++j) {
    const SAT::Lit& literal = *j;

    // simplify based on true/false literals
    if (literal.isTrue())
      return false;

    if (!literal.isFalse())
      literals.push_back(cvcToMiniSat(literal));
  }
  
  return true;
}

Clause* Solver::cvcToMiniSat(const SAT::Clause& clause, int id) {
  vector<MiniSat::Lit> literals;
  if (MiniSat::cvcToMiniSat(clause, literals)) {
    if (getDerivation() != NULL)
      return Clause_new(literals, clause.getClauseTheorem(), id);
    else
      return Clause_new(literals, CVC3::Theorem(), id);
  }
  else {
    return NULL;
  }
}





/// Initialization

Solver::Solver(SAT::DPLLT::TheoryAPI* theoryAPI, SAT::DPLLT::Decider* decider,
	       bool logDerivation) :
  d_inSearch(false),
  d_ok(true),
  d_conflict(NULL),
  d_qhead            (0),
  d_thead            (0),
  d_registeredVars   (1),
  d_clauseIDCounter  (3), // -1 and -2 are used in Clause for special clauses,
                          // and negative ids are in general used for theory clauses,
                          // so avoid overlap by setting 3 as the possible first clause id.
  d_popRequests      (0),
  d_cla_inc          (1),
  d_cla_decay        (1),
  d_var_inc          (1),
  d_var_decay        (1),
  d_order            (d_assigns, d_activity),
  d_simpDB_assigns   (0),
  d_simpDB_props     (0),
  d_simpRD_learnts   (0),
  d_theoryAPI(theoryAPI),
  d_decider(decider),
  d_derivation(NULL),
  d_default_params(SearchParams(0.95, 0.999, 0.02)),
  d_expensive_ccmin(true)
{ 
  if (logDerivation) d_derivation = new Derivation();
}


// add a lemma which has not been computed just now (see push(), createFrom()),
// so it is not necessarily propagating
void Solver::insertLemma(const Clause* lemma, int clauseID, int pushID) {
  // need to add lemmas manually,
  // as addClause/insertClause assume that the lemma has just been computed and is propagating,
  // and as we want to keep the activity.
  vector<Lit> literals;
  lemma->toLit(literals);

  // If a lemma is based purely on theory lemmas (i.e. theory clauses),
  // then in backtracking those theory lemmas might be retracted,
  // and literals occurring in the lemma might not occur in any remaining clauses.
  // When creating a new solver based on an existing instance
  // (i.e. in continuing the search after finding a model),
  // then those literals have to be registered here.
  for (vector<Lit>::const_iterator i = literals.begin(); i != literals.end(); ++i) {
    registerVar(i->var());
  }

  // While lemma simplification might be nice to have,
  // this poses a problem with derivation recording,
  // as we would also have to modify the derivation of the original
  // lemma towards a derivation of the new lemma.
  // In the case of a new solver inheriting the lemmas of the previous solver 
  // the lemma is registered for the first time in the derivation.
  // In the case where the lemma was kept over a push the old lemma
  // is registered with the derivation, but about to be removed from memory (xfree).
  // So the simplest thing is to just replace any previous registration of the
  // lemma with a new identical lemma, and not do any simplification at all.
  //if (!simplifyClause(literals, clauseID)) {
    // ensure that order is appropriate for watched literals
    orderClause(literals);
   
    Clause* newLemma = Lemma_new(literals, clauseID, pushID);
    if (getDerivation() != NULL) getDerivation()->registerClause(newLemma);

    newLemma->setActivity(lemma->activity());
    
    // add to watches and lemmas
    if (newLemma->size() >= 2) {
      addWatch(~(*newLemma)[0], newLemma);
      addWatch(~(*newLemma)[1], newLemma);
    }
    d_learnts.push_back(newLemma);
    d_stats.learnts_literals += newLemma->size();
    
    // unsatisfiable
    if (newLemma->size() == 0 || getValue((*newLemma)[0]) == l_False) {
      updateConflict(newLemma);
    }
    // propagate
    if (newLemma->size() == 1 || getValue((*newLemma)[1]) == l_False) {
      if (!enqueue((*newLemma)[0], d_rootLevel, newLemma)) {
	DebugAssert(false, "MiniSat::Solver::insertLemma: conflicting/implying lemma");
      }
    }
    //}
}


Solver* Solver::createFrom(const Solver* oldSolver) {
  Solver* solver = new MiniSat::Solver(oldSolver->d_theoryAPI,
				       oldSolver->d_decider, oldSolver->d_derivation != NULL);
    
  // reuse literal activity
  // assigning d_activity before the clauses are added
  // will automatically rebuild d_order in the right way.
  solver->d_cla_inc = oldSolver->d_cla_inc;
  solver->d_var_inc = oldSolver->d_var_inc;
  solver->d_activity = oldSolver->d_activity;


  // build the current formula
  
  // add the formula and assignment from the previous solver
  // first assignment, as this contains only unit clauses, then clauses,
  // as these are immediately simplified by the assigned unit clauses
      
  // get the old assignment
  const vector<MiniSat::Lit>& trail = oldSolver->getTrail();
  for (vector<MiniSat::Lit>::const_iterator i = trail.begin(); i != trail.end(); ++i) {
    //:TODO: use special clause as reason instead of NULL
    solver->addClause(*i, CVC3::Theorem());
  }
      
  // get the old clause set
  const vector<MiniSat::Clause*>& clauses = oldSolver->getClauses();
  for (vector<MiniSat::Clause*>::const_iterator i = clauses.begin(); i != clauses.end(); ++i) {
    solver->addClause(**i, false);
  }

  // get the old lemmas
  const vector<MiniSat::Clause*>& lemmas = oldSolver->getLemmas();
  for (vector<MiniSat::Clause*>::const_iterator i = lemmas.begin();
       !solver->isConflicting() && i != lemmas.end(); ++i) {
    // can use clauseID for clause id as well as push id -
    // after all this is the root level, so all lemmas are ok in any push level anyway
    int clauseID = solver->nextClauseID();
    solver->insertLemma(*i, clauseID, clauseID);
  }

  return solver;
}

Solver::~Solver() {
  for (vector<Clause*>::const_iterator i = d_learnts.begin(); i != d_learnts.end(); ++i)
    remove(*i, true);

  for (vector<Clause*>::const_iterator i = d_clauses.begin(); i != d_clauses.end(); ++i)
    remove(*i, true);

  while (!d_pendingClauses.empty()) {
    xfree(d_pendingClauses.front());
    d_pendingClauses.pop();
  }

  while (!d_theoryExplanations.empty()) {
    xfree(d_theoryExplanations.top().second);
    d_theoryExplanations.pop();
  }

  delete d_derivation;
}




///
/// String representation
//

std::string Solver::toString(Lit literal, bool showAssignment) const {
  ostringstream buffer;
  buffer << literal.toString();

  if (showAssignment) {
    if (getValue(literal) == l_True)
      buffer << "(+)";
    else if (getValue(literal) == l_False)
      buffer << "(-)";
  }

  return buffer.str();
}


std::string Solver::toString(const std::vector<Lit>& clause, bool showAssignment) const {
  ostringstream buffer;
  for (size_type j = 0; j < clause.size(); ++j) {
    buffer << toString(clause[j], showAssignment) << " ";
  }
  buffer << endl;

  return buffer.str();
}

std::string Solver::toString(const Clause& clause, bool showAssignment) const {
  std::vector<Lit> literals;
  clause.toLit(literals);
  return toString(literals, showAssignment);
}


std::vector<SAT::Lit> Solver::curAssigns(){
  vector<SAT::Lit> res;
  cout << "current Assignment: " << endl;
  for (size_type i = 0; i < d_trail.size(); ++i) {
    res.push_back(miniSatToCVC(d_trail[i]));
  }
  return res;
}
 
std::vector<std::vector<SAT::Lit> > Solver::curClauses(){
  std::vector<std::vector< SAT::Lit> > res;
  cout << "current Clauses: " << endl;
  for (size_t i = 0; i < d_clauses.size(); ++i) {
    std::vector<SAT::Lit> oneClause;
    oneClause.clear();
    for (int j = 0; j < (*d_clauses[i]).size(); ++j) {
      oneClause.push_back(miniSatToCVC((*d_clauses[i])[j]));
    }
    res.push_back(oneClause);
  }
  return res;
}


void Solver::printState() const {
  cout << "Lemmas: " << endl;
  for (size_type i = 0; i < d_learnts.size(); ++i) {
    cout << toString(*(d_learnts[i]), true);
  }

  cout << endl;

  cout << "Clauses: " << endl;
  for (size_type i = 0; i < d_clauses.size(); ++i) {
    cout << toString(*(d_clauses[i]), true);
  }

  cout << endl;

  cout << "Assignment: " << endl;
  //  for (size_type i = 0; i < d_qhead; ++i) {
  for (size_type i = 0; i < d_trail.size(); ++i) {
    string split = "";
    if (getReason(d_trail[i].var()) == Clause::Decision()) {
      split = "(S)";
    }
    cout << toString(d_trail[i], false) << split << " ";
  }
  cout << endl;
}




void Solver::printDIMACS() const {
  int max_id = nVars();
  int num_clauses = d_clauses.size() + d_trail.size();// + learnts.size() ;

  // header
  cout << "c minisat test" << endl;
  cout << "p cnf " << max_id << " " << num_clauses << endl;

  // clauses
  for (size_type i = 0; i < d_clauses.size(); ++i) {
    Clause& clause = *d_clauses[i];
    for (int j = 0; j < clause.size(); ++j) {
      Lit lit = clause[j];
      cout << toString(lit, false) << " ";
    }
    cout << "0" << endl;
  }

  // lemmas
  //for (int i = 0; i < learnts.size(); ++i) {
  //  Clause& clause = *learnts[i];
  //  for (int j = 0; j < clause.size(); ++j) {
  //    Lit lit = clause[j];
  //    cout << toString(lit, false) << " ";
  //  }
  //  cout << "0" << endl;
  //}

  // context
  for (vector<Lit>::const_iterator i = d_trail.begin(); i != d_trail.end(); ++i) {
    Lit lit(*i);
    if (getReason(lit.var()) == Clause::Decision())
      cout << toString(lit, false) << " 0" << endl;
    else
      cout << toString(lit, false) << " 0" << endl;
  }
}



/// Operations on clauses:


bool Solver::isRegistered(Var var) {
  for (vector<Hash::hash_set<Var> >::const_iterator i = d_registeredVars.begin();
       i != d_registeredVars.end(); ++i) {
    if ((*i).count(var) > 0) return true;
  }
  return false;
}

// registers var with given index to all data structures
void Solver::registerVar(Var index) {
  if (isRegistered(index)) return;

  // register variables to all data structures
  if (nVars() <= index) {
    // 2 * index + 1 will be accessed for neg. literal,
    // so we need + 1 fiels for 0 field
    d_watches     .resize(2 * index + 2);
    d_reason      .resize(index + 1, NULL);
    d_assigns     .resize(index + 1, toInt(l_Undef));
    d_level       .resize(index + 1, -1);
    d_activity    .resize(index + 1, 0);
    d_analyze_seen.resize(index + 1, 0);
    d_pushIDs     .resize(index + 1, -1);
    if (d_derivation != NULL) d_trail_pos.resize(index + 1, d_trail.max_size());
  }

  // register with internal variable selection heuristics
  d_order       .newVar(index);

  // marks as registered
  DebugAssert(!d_registeredVars.empty(), "MiniSat::Solver::registerVar: d_registeredVars is empty");
  d_registeredVars.back().insert(index);
}

void Solver::addClause(Lit p, CVC3::Theorem theorem) {
  vector<Lit> literals;
  literals.push_back(p);
  addClause(literals, theorem, nextClauseID());
}

void Solver::addClause(const SAT::Clause& clause, bool isTheoryClause) {
  vector<MiniSat::Lit> literals;
  if (MiniSat::cvcToMiniSat(clause, literals)) {
    int clauseID = nextClauseID();
    // theory clauses have negative ids:
    if (isTheoryClause) clauseID = -clauseID;
    CVC3::Theorem theorem;
    if (getDerivation() != NULL) {
      getDerivation()->registerInputClause(clauseID);
      theorem = clause.getClauseTheorem();
    }
    addClause(literals, theorem, clauseID);
  }
  else {
    // ignore tautologies
    return;
  }
}

void Solver::addClause(const Clause& clause, bool keepClauseID) {
  vector<Lit> literals;
  for (int i = 0; i < clause.size(); ++i) {
    literals.push_back(clause[i]);
  }
  if (keepClauseID) {
    addClause(literals, clause.getTheorem(), clause.id());
  } else {
    addClause(literals, clause.getTheorem(), nextClauseID());
  }
}

// Note:
// tried to improve efficiency by asserting unit clauses first,
// then clauses of size 2, and so on,
// in the hope to immediately simplify or remove clauses.
//
// didn't work well with the theories, though,
// lead to significant overhead, even when the derivation did not change much.
// presumably as this interleaves clauses belonging to different 'groups',
// which describe different concepts and are better handled in sequence
// without interleaving them.
void Solver::addFormula(const SAT::CNF_Formula& cnf, bool isTheoryClause) {
  SAT::CNF_Formula::const_iterator i, iend;
  // for comparison: this is the order used by -sat sat
  //for (i = cnf.end()-1, iend = cnf.begin()-1; i != iend; --i) {
  for (i = cnf.begin(), iend = cnf.end(); i != iend; i++) {
//     if(i->d_reason.isNull()){
//       cout<<"found null thm in Solver::addFormula"<<endl<<flush;
//     }
    addClause(*i, isTheoryClause);
  }
}



// based on root level assignment removes all permanently falsified literals.
// return true if clause is permanently satisfied.
bool Solver::simplifyClause(vector<Lit>& literals, int clausePushID) const {
  // Check if clause is a tautology: p \/ -p \/ C:
  for (size_type i = 1; i < literals.size(); i++){
    if (literals[i-1] == ~literals[i]){
      return true;
    }
  }

  // Remove permanently satisfied clauses and falsified literals:
  size_type i, j;
  for (i = j = 0; i < literals.size(); i++) {
    bool rootAssign = (
      getLevel(literals[i]) == d_rootLevel
      && isImpliedAt(literals[i], clausePushID) );
    
    if (rootAssign && (getValue(literals[i]) == l_True)){
      return true;
    }
    else if (rootAssign && (getValue(literals[i]) == l_False)){

      ;
    }
    else{
      literals[j++] = literals[i];
    }
  }
  literals.resize(j);
  return false;
}


 
// need the invariant, that
// a) either two undefined literals are chosen as watched literals,
// or b) that after backtracking either a) kicks in
//    or the clause is still satisfied/unit 
//
// so either:
// - find two literals which are undefined or satisfied
// - or find a literal that is satisfied or unsatisfied
//   and the most recently falsified literal
// - or the two most recently falsified literals
// and put these two literals at the first two positions
void Solver::orderClause(vector<Lit>& literals) const {
  if (literals.size() >= 2) {
    int first = 0;
    int levelFirst = getLevel(literals[first]);
    lbool valueFirst = getValue(literals[first]);
    int second = 1;
    int levelSecond = getLevel(literals[second]);
    lbool valueSecond = getValue(literals[second]);
    for (size_type i = 2; i < literals.size(); i++) {
      // found two watched or satisfied literals
      if (!(valueFirst == l_False) && !(valueSecond == l_False))
	break;
      
      // check if new literal is better than the currently picked ones
      int levelNew = getLevel(literals[i]);
      lbool valueNew = getValue(literals[i]);
      
      // usable, take instead of previously chosen literal
      if (!(valueNew == l_False)) {
	if ((valueFirst == l_False) && (valueSecond == l_False)) {
	  if (levelFirst > levelSecond) {
	    second = i; levelSecond = levelNew; valueSecond = valueNew;
	  } else {
	    first = i; levelFirst = levelNew; valueFirst = valueNew;
	  }
	}
	else if (valueFirst == l_False) {
	  first = i; levelFirst = levelNew; valueFirst = valueNew;
	}
	else {
	  second = i; levelSecond = levelNew; valueSecond = valueNew;
	}
      }
      // check if new pick was falsified more recently than the others
      else {
	if ((valueFirst == l_False) && (valueSecond == l_False)) {
	  if ((levelNew > levelFirst) && (levelNew > levelSecond)) {
	    if (levelSecond > levelFirst) {
	      first = i; levelFirst = levelNew; valueFirst = valueNew;
		  }
	    else {
	      second = i; levelSecond = levelNew; valueSecond = valueNew;
	    }
	  }
	  else if (levelNew > levelFirst) {
	    first = i; levelFirst = levelNew; valueFirst = valueNew;
	  }
	  else if (levelNew > levelSecond) {
	    second = i; levelSecond = levelNew; valueSecond = valueNew;
	  }
	}
	else if (valueFirst == l_False) {
	  if (levelNew > levelFirst) {
	    first = i; levelFirst = levelNew; valueFirst = valueNew;
	  }
	}
	else { // valueSecond == l_false
	  if (levelNew > levelSecond) {
	    second = i; levelSecond = levelNew; valueSecond = valueNew;
	  }
	}
      }
    }
    
    Lit swap = literals[0]; literals[0] = literals[first]; literals[first] = swap;
    swap = literals[1]; literals[1] = literals[second]; literals[second] = swap;
    
    // if a literal is satisfied, the first literal is satisfied,
    // otherwise if a literal is falsified, the second literal is falsified.
    if (
	// satisfied literal at first position
	((getValue(literals[0]) != l_True) && (getValue(literals[1]) == l_True))
	||
	// falsified literal at second position
	(getValue(literals[0]) == l_False)
	)
      {
	Lit swap = literals[0]; literals[0] = literals[1]; literals[1] = swap;
      }
  }
}


void Solver::addClause(vector<Lit>& literals, CVC3::Theorem theorem, int clauseID) {
  // sort clause
  std::sort(literals.begin(), literals.end());

  // remove duplicates
  vector<Lit>::iterator end = std::unique(literals.begin(), literals.end());
  literals.erase(end, literals.end());

  // register var for each clause literal
  for (vector<Lit>::const_iterator i = literals.begin(); i != literals.end(); ++i){
    registerVar(i->var());
  }

  // simplify clause
  vector<Lit> simplified(literals);

  bool replaceReason = false;
  if (simplifyClause(simplified, clauseID)) {
    // it can happen that a unit clause was contradictory when it was added (in a non-root state).
    // then it was first added to list of pending clauses,
    // and the conflict analyzed and retracted:
    // this lead to the computation of a lemma which was used as a reason for the literal
    // instead of the unit clause itself.
    // so fix this here
    if (literals.size() == 1 && getReason(literals[0].var())->learnt()) {
      replaceReason = true;
    }
    else {
      // permanently satisfied clause
      return;
    }
  }

  // record derivation for a simplified clause
  if (getDerivation() != NULL && simplified.size() < literals.size()) {
    // register original clause as start of simplification
    Clause* c = Clause_new(literals, theorem, clauseID);
    getDerivation()->registerClause(c);
    getDerivation()->removedClause(c);

    // register simplification steps
    Inference* inference = new Inference(clauseID);
    size_type j = 0;
    for (size_type i = 0; i < literals.size(); ++i) {
      // literal removed in simplification
      if (j >= simplified.size() || literals[i] != simplified[j]) {
	inference->add(literals[i], getDerivation()->computeRootReason(~literals[i], this));
      }
      // keep literal
      else {
	++j;
      }
    }

    // register resolution leading to simplified clause
    clauseID = nextClauseID();
    getDerivation()->registerInference(clauseID, inference);
  }

  // insert simplified clause
  orderClause(simplified);
  Clause* c;
  if (simplified.size() < literals.size()) {
    c = Clause_new(simplified, CVC3::Theorem(), clauseID);
  } else {
    c = Clause_new(simplified, theorem, clauseID);
  }
  
  //  cout<<"clause size" << c->size() << endl << flush;

  insertClause(c);
  //  cout<<"after clause size" << c->size() << endl << flush;
  if (replaceReason) {
    d_reason[literals[0].var()] = c;
  }
//  cout<<"after after clause size" << c->size() << endl << flush;
}


void Solver::insertClause(Clause* c) {
  // clause set is unsatisfiable
  if (!d_ok) {
    remove(c, true);
    return;
  }

  if (getDerivation() != NULL) getDerivation()->registerClause(c);

  if (c->size() == 0){
    d_conflict = c;

    // for garbage collection: need to put clause somewhere
    if (!c->learnt()) {
      d_clauses.push_back(c);
    } else {
      d_learnts.push_back(c);
    }

    d_ok = false;
    return;
  }

  // process clause -
  // if clause is conflicting add it to pending clause and return

  // unit clause
  if (c->size() == 1) {
    if (!enqueue((*c)[0], d_rootLevel, c)) {
      // this backtracks to d_rootLevel, as reason c is just one literal,
      // which is immediately UIP, so c will be learned as a lemma as well.
      updateConflict(c);
      d_pendingClauses.push(c);
      return;
    }
  }
  // non-unit clause
  else {
    // ensure that for a lemma the second literal has the highest decision level
    if (c->learnt()){
      DebugAssert(getValue((*c)[0]) == l_Undef, 
		"MiniSat::Solver::insertClause: first literal of new lemma not undefined");
      IF_DEBUG (
        for (int i = 1; i < c->size(); ++i) {
	  DebugAssert(getValue((*c)[i]) == l_False,
		      "MiniSat::Solver::insertClause: lemma literal not false");
	}
      )

      // Put the second watch on the literal with highest decision level:	  
      int     max_i = 1;
      int     max   = getLevel((*c)[1]);
      for (int i = 2; i < c->size(); i++) {
	if (getLevel((*c)[i]) > max) {
	  max   = getLevel((*c)[i]);
	  max_i = i;
	}
      }
      Lit swap((*c)[1]);
      (*c)[1]     = (*c)[max_i];
      (*c)[max_i] = swap;
      
      // (newly learnt clauses should be considered active)
      claBumpActivity(c);
    }

    // satisfied
    if (getValue((*c)[0]) == l_True) {
      ;
    }
    // conflicting
    else if (getValue((*c)[0]) == l_False) {
      IF_DEBUG (
	for (int i = 1; i < c->size(); ++i) {
	  DebugAssert(getValue((*c)[i]) == l_False,
		      "MiniSat::Solver::insertClause: bogus conflicting clause");
	}
      )

      updateConflict(c);
      d_pendingClauses.push(c);
      return;
    }
    // propagation
    else if (getValue((*c)[1]) == l_False) {
      DebugAssert(getValue((*c)[0]) == l_Undef,
		  "MiniSat::Solver::insertClause: bogus propagating clause");
      IF_DEBUG (
        for (int i = 1; i < c->size(); ++i) {
	  DebugAssert(getValue((*c)[i]) == l_False,
		      "MiniSat::Solver::insertClause: bogus propagating clause");
	}
      )
      if (!enqueue((*c)[0], getImplicationLevel(*c), c)) {
	DebugAssert(false, "MiniSat::Solver::insertClause: conflicting/implying clause");
      }
    }

    // Watch clause:
    addWatch(~(*c)[0], c);
    addWatch(~(*c)[1], c);
  }

  // clause is not conflicting, so insert it into the clause list.
  d_stats.max_literals += c->size();
  if (!c->learnt()) {
    d_clauses.push_back(c);
    d_stats.clauses_literals += c->size();
  } else {
    d_learnts.push_back(c);
    d_stats.learnts_literals += c->size();
  }
}




// Disposes a clauses and removes it from watcher lists.
// NOTE! Low-level; does NOT change the 'clauses' and 'learnts' vector.
void Solver::remove(Clause* c, bool just_dealloc) {
  // no watches added for clauses of size < 2
  if (!just_dealloc && c->size() >= 2){
    removeWatch(getWatches(~(*c)[0]), c);
    removeWatch(getWatches(~(*c)[1]), c);
  }
  
  if (c->learnt()) d_stats.learnts_literals -= c->size();
  else             d_stats.clauses_literals -= c->size();
  
  if (getDerivation() == NULL) xfree(c);
  else getDerivation()->removedClause(c);
}




/// Conflict handling

// Pre-condition: 'elem' must exists in 'ws' OR 'ws' must be empty.
void Solver::removeWatch(std::vector<Clause*>& ws, Clause* elem) {
  if (ws.size() == 0) return;     // (skip lists that are already cleared)
  size_type j = 0;
  for (; ws[j] != elem; j++) {
    // want to find the right j, so the loop should be executed
    // and not wrapped in a debug guard
    DebugAssert(j < ws.size(), "MiniSat::Solver::removeWatch: elem not in watched list");
  }

  ws[j] = ws.back();
  ws.pop_back();
}


// for a clause, of which the first literal is implied,
// get the highest decision level of the implying literals,
// i.e. the decision level from which on the literal is implied
//
// as theory clauses can be added at any time,
// this is not necessarily the level of the second literal.
// thus, all literals have to be checked.
int Solver::getImplicationLevel(const Clause& clause) const {
  int currentLevel = decisionLevel();
  int maxLevel = d_rootLevel;

  for (int i = 1; i < clause.size(); ++i) {
    DebugAssert(getValue(clause[i]) == l_False,
		"MiniSat::Solver::getImplicationLevelFull: literal not false");

    int newLevel = getLevel(clause[i]);

    // highest possible level
    if (newLevel == currentLevel)
      return currentLevel;

    // highest level up to now
    if (newLevel > maxLevel)
      maxLevel = newLevel;
  }

  return maxLevel;
}


// like getImplicationLevel, but for all literals,
// i.e. for conflicting instead of propagating clause
int Solver::getConflictLevel(const Clause& clause) const {
  int decisionLevel = d_rootLevel;
  
  for (int i = 0; i < clause.size(); ++i) {
    DebugAssert(getValue(clause[i]) == l_False, "MiniSat::Solver::getConflictLevel: literal not false");

    int newLevel = getLevel(clause[i]);
    if (newLevel > decisionLevel)
      decisionLevel = newLevel;
  }

  return decisionLevel;
}


Clause* Solver::getReason(Lit literal, bool _resolveTheoryImplication) {
  Var var = literal.var();
  Clause* reason = d_reason[var];

  if (!_resolveTheoryImplication)
    return reason;

  DebugAssert(reason != NULL, "MiniSat::getReason: reason[var] == NULL.");

  if (reason == Clause::TheoryImplication()) {
    if (getValue(literal) == l_True)
      resolveTheoryImplication(literal);
    else
      resolveTheoryImplication(~literal);
    reason = d_reason[var];
  }

  DebugAssert(d_reason[var] != Clause::TheoryImplication(),
	      "MiniSat::getReason: reason[var] == TheoryImplication.");

  return reason;
}

bool Solver::isConflicting() const {
  return (d_conflict != NULL);
}

void Solver::updateConflict(Clause* clause) {
  DebugAssert(clause != NULL, "MiniSat::updateConflict: clause == NULL.");
  IF_DEBUG (
    for (int i = 0; i < clause->size(); ++i) {
      DebugAssert(getValue((*clause)[i]) == l_False, "MiniSat::Solver::updateConflict: literal not false");
    }
  )

  if (
      (d_conflict == NULL)
      ||
      (clause->size() < d_conflict->size())
      ) {
      d_conflict = clause;
  }
}



// retrieve the explanation and update the implication level of a theory implied literal.
// if necessary, do this recursively (bottom up) for the literals in the explanation.
// assumes that the literal is true in the current context
void Solver::resolveTheoryImplication(Lit literal) {
  if (eager_explanation) return;

  if (d_reason[literal.var()] == Clause::TheoryImplication()) {
    // instead of recursion put the theory implications to check in toRegress,
    // and the theory implications depending on them in toComplete
    stack<Lit> toRegress;
    stack<Clause*> toComplete;
    toRegress.push(literal);

    SAT::Clause clauseCVC;
    while (!toRegress.empty()) {
      // get the explanation for the first theory implication
      literal = toRegress.top();
      DebugAssert(getValue(literal) == l_True,
		  "MiniSat::Solver::resolveTheoryImplication: literal is not true");
      toRegress.pop();
      FatalAssert(false, "Not implemented yet");
      //      d_theoryAPI->getExplanation(miniSatToCVC(literal), clauseCVC);
      Clause* explanation = cvcToMiniSat(clauseCVC, nextClauseID());

      // must ensure that propagated literal is at first position
      for (int i = 0; i < (*explanation).size(); ++i) {
	if ((*explanation)[i] == literal) {
	  MiniSat::Lit swap = (*explanation)[0];
	  (*explanation)[0] = (*explanation)[i];
	  (*explanation)[i] = swap;
	  break;
	}
      }      
      // assert that clause is implying the first literal
      IF_DEBUG(
        DebugAssert((*explanation)[0] == literal,
		    "MiniSat::Solver::resolveTheoryImplication: literal not implied by clause 1");
        DebugAssert(getValue((*explanation)[0]) == l_True,
		    "MiniSat::Solver::resolveTheoryImplication: literal not implied by clause 2");
        for (int i = 1; i < (*explanation).size(); ++i) {
	  DebugAssert(getValue((*explanation)[i]) == l_False,
		    "MiniSat::Solver::resolveTheoryImplication: literal not implied by clause 3");
        }
	)
	d_reason[literal.var()] = explanation;

      // if any of the reasons is also a theory implication,
      // then need to know its level first, so add it to toRegress
      for (int i = 1; i < (*explanation).size(); ++i) {
	if (d_reason[(*explanation)[i].var()] == Clause::TheoryImplication()) {
	  toRegress.push((*explanation)[i]);
	}
      }
      // set literal and its explanation aside for later processing
      toComplete.push(explanation);
    }

    // now set the real implication levels after they have been resolved
    //    std::pair<Lit, Clause*> pair;
    while (!toComplete.empty()) {
      Clause* explanation = toComplete.top();
      toComplete.pop();

      IF_DEBUG (
        for (int i = 1; i < explanation->size(); ++i) {
	  DebugAssert (d_reason[(*explanation)[i].var()] != Clause::TheoryImplication(),
		       "MiniSat::Solver::resolveTheoryImplication: not done to completion");
	}
      )

      // update propagation information
      int level = getImplicationLevel(*explanation);
      setLevel((*explanation)[0], level);
      setPushID((*explanation)[0].var(), explanation);      

      if (keep_lazy_explanation) {
	// the reason can be added to the clause set without any effect,
	// as the explanation implies the first literal, which is currently true
	// so neither propagation nor conflict are triggered,
	// only the correct literals are registered as watched literals.
	addClause(*explanation, true);
	xfree(explanation);
      } else {
	// store explanation for later deallocation
	d_theoryExplanations.push(std::make_pair(level, explanation));
      }
    }
  }

}



/// Conflict handling

Clause* Solver::analyze(int& out_btlevel) {
  DebugAssert(d_conflict != NULL, "MiniSat::Solver::analyze called when no conflict was detected");

  // compute the correct decision level for theory propagated literals
  //
  // need to find the most recent implication level of any of the literals in d_conflict,
  // after updating conflict levels due to lazy retrieval of theory implications.
  //
  // that is, really need to do:
  // 1) assume that the currently highest known level is the UIP Level,
  //    initially this is the decision level
  // 2) find a literal in the conflict clause whose real implication level is the UIP Level
  // 3) if their is no such literal, pick the new UIP level as the highest of their implication levels,
  //    and repeat
  //
  // unfortunately, 2) is not that easy:
  // - if the literals' level is smaller than the UIP level the literal can be ignored
  // - otherwise, it might depend on theory implications,
  //   who have just been assumed to be of the UIP level, but which in reality are of lower levels.
  //   So, must check all literals the literal depends on,
  //   until the real level of all of them is determined,
  //   and thus also of the literal we are really interested in.
  //   this can be stopped if the level must be lower than the (currently assumed) UIP level,
  //   or if it is sure that the literal really has the UIP level.
  //   but this is only the case if it depends on the decision literal of the UIP level.
  //
  //   but how to find this out efficiently?
  //
  // so, this is done as an approximation instead:
  // 1) if the explanation of a (conflict clause) literal is known, stop and take the literal's level
  // 2) otherwise, retrieve its explanation,
  //    and do 1) and 2) on each literal in the explanation.
  //    then set the original literal's level to the highest level of its explanation.
  //
  // as an example, if we have:
  // - theory implication A in level n
  // - propositional implication B depending on A and literals below level n
  // - propositional implication C depending on B and literals below level n
  // then A, B, C will all be assumed to be of level n,
  // and if C is in a conflict it will be assumed to be of level n
  // in the conflict analysis
  //
  // this is fast to compute,
  // but it is not clear if starting from the real UIP level
  // would lead to a significantly better lemma
  for (int j = 0; j < d_conflict->size(); j++){
    resolveTheoryImplication(~((*d_conflict)[j]));
  }
  int UIPLevel = getConflictLevel(*d_conflict);

  // clause literals to regress are marked by setting analyze_d_seen[var]
  // seen should be false for all variables
  IF_DEBUG (
    for (size_type i = 0; i < d_analyze_seen.size(); ++i) {
      DebugAssert (d_analyze_seen[i] == 0, "MiniSat::Solver::analyze: analyze_seen is not clear at: " /*+ i*/);
    }
  )
  // index into trail, regression is done chronologically (in combination with analyze_seen)
  int index = d_trail.size() - 1;
  // lemma is generated here;
  vector<Lit> out_learnt;
  // number of literals to regress in current decision level
  int            pathC = 0;
  // highest level below UIP level, i.e. the level to backtrack to
  out_btlevel = 0;
  // current literal to regress
  Lit            p     = lit_Undef;
  
  // derivation logging
  Inference* inference = NULL;
  if (getDerivation() != NULL) inference = new Inference(d_conflict->id());

  // conflict clause is the initial clause to regress
  Clause* confl = d_conflict;
  d_conflict = NULL;

  // compute pushID as max pushID of all regressed clauses
  int pushID = confl->pushID();

  // do until pathC == 1, i.e. UIP found
  if (confl->size() == 1) {
    out_learnt.push_back((*confl)[0]);
  } else {
    // leave room for the asserting literal -
    // we might get an empty lemma if a new clause is conflicting at the root level.
    if (UIPLevel != d_rootLevel) out_learnt.push_back(lit_Undef);

    do {
    DebugAssert (confl != Clause::Decision(), "MiniSat::Solver::analyze: no reason for conflict");
    DebugAssert (confl != Clause::TheoryImplication(), "MiniSat::Solver::analyze: theory implication not resolved");

    if (confl->learnt()) claBumpActivity(confl);

    // regress p
    for (int j = (p == lit_Undef) ? 0 : 1; j < confl->size(); j++){
      Lit q = (*confl)[j];
      DebugAssert(getValue(q) == l_False, "MiniSat::Solver::analyze: literal to regress is not false");
      DebugAssert(getLevel(q) <= UIPLevel, "MiniSat::Solver::analyze: literal above UIP level");

      // get explanation and compute implication level for theory implication
      resolveTheoryImplication(~q);
      
      // first time that q is in a reason, so process it
      if (!d_analyze_seen[q.var()]) {
	// q is falsified at root level, so it can be dropped
	if (getLevel(q) == d_rootLevel) {
	  d_analyze_redundant.push_back(q);
	  d_analyze_seen[q.var()] = 1;
	}
	else {
	  varBumpActivity(q);
	  d_analyze_seen[q.var()] = 1;
	  // mark q to regress
	  if (getLevel(q) == UIPLevel)
	    pathC++;
	  // add q to lemma
	  else{
	    out_learnt.push_back(q);
	    out_btlevel = max(out_btlevel, getLevel(q));
	  }
	}
      }
    }

    // for clause conflicting at root level pathC can be 0 right away
    if (pathC == 0) break;

    // pick next literal in UIP level to regress.
    // as trail is not ordered wrt. implication level (theory clause/ implications),
    // check also if the next literal is really from the UIP level.
    while (!d_analyze_seen[d_trail[index].var()] || (getLevel(d_trail[index])) != UIPLevel) {
      --index;
    }
    --index;
    // this could theoretically happen if UIP Level is 0,
    // but should be catched as then the conflict clause
    // is simplified to the empty clause.
    DebugAssert(index >= -1, "MiniSat::Solver::analyze: index out of bound");
    
    // set up p to be regressed
    p     = d_trail[index+1];
    d_analyze_seen[p.var()] = 0;
    pathC--;

    confl = getReason(p);
    pushID = max(pushID, confl->pushID());
    if (getDerivation() != NULL && pathC > 0) inference->add(~p, confl);
  } while (pathC > 0);
    // add the UIP - except in root level, here all literals have been resolved.
    if (UIPLevel != d_rootLevel) out_learnt[0] = ~p;
  }

  // check that the UIP has been found
  IF_DEBUG (
    DebugAssert ((out_learnt.size() == 0 && UIPLevel == d_rootLevel)
		 || getLevel(out_learnt[0]) == UIPLevel,
		 "MiniSat::Solver::analyze: backtracked past UIP level.");
    for (size_type i = 1; i < out_learnt.size(); ++i) {
      DebugAssert (getLevel(out_learnt[i]) < UIPLevel,
		   "MiniSat::Solver::analyze: conflict clause contains literal from UIP level or higher.");
    }
  )

  analyze_minimize(out_learnt, inference, pushID);

  // clear seen for lemma
  for (vector<Lit>::const_iterator j = out_learnt.begin(); j != out_learnt.end(); ++j) {
    d_analyze_seen[j->var()] = 0;
  }

  // finish logging of conflict clause generation
  int clauseID = nextClauseID();
  if (getDerivation() != NULL) getDerivation()->registerInference(clauseID, inference);

  return Lemma_new(out_learnt, clauseID, pushID);
}

class lastToFirst_lt {  // Helper class to 'analyze' -- order literals from last to first occurance in 'trail[]'.
  const vector<MiniSat::size_type>& d_trail_pos;
public:
  lastToFirst_lt(const vector<MiniSat::size_type>& trail_pos) : d_trail_pos(trail_pos) {}

  bool operator () (Lit p, Lit q) {
    return d_trail_pos[p.var()] > d_trail_pos[q.var()];
  }
};

void Solver::analyze_minimize(vector<Lit>& out_learnt, Inference* inference, int& pushID) {
  // for empty clause current analyze_minimize will actually do something wrong
  if (out_learnt.size() > 1) {

  // literals removed from out_learnt in conflict clause minimization,
  // including reason literals which had to be removed as well
  // (except for literals implied at root level).
  size_type i, j;
  // 1) Simplify conflict clause (a lot):
  // drop a literal if it is implied by the remaining lemma literals:
  // that is, as in 2), but also recursively taking the reasons
  // for the implying clause, and their reasone, and so on into consideration.
  if (d_expensive_ccmin){
    // (maintain an abstraction of levels involved in conflict)
    unsigned int min_level = 0;
    for (i = 1; i < out_learnt.size(); i++)
      min_level |= 1 << (getLevel(out_learnt[i]) & 31);
    
    for (i = j = 1; i < out_learnt.size(); i++) {
      Lit lit(out_learnt[i]);
      if (getReason(lit) == Clause::Decision() || !analyze_removable(lit, min_level, pushID))
	out_learnt[j++] = lit;
    }
  }
  // 2) Simplify conflict clause (a little):
  // drop a literal if it is implied by the remaining lemma literals:
  // that is, if the other literals of its implying clause
  // are falsified by the other lemma literals.
  else {
    for (i = j = 1; i < out_learnt.size(); i++) {
      Lit lit(out_learnt[i]);
      Clause& c = *getReason(lit);
      if (&c == Clause::Decision()) {
	out_learnt[j++] = lit;
      } else {
	bool keep = false;
	// all literals of the implying clause must be:
	for (int k = 1; !keep && k < c.size(); k++) {
	  if (
	      // already part of the lemma
	      !d_analyze_seen[c[k].var()]
	      &&
	      // or falsified in the root level
	      getLevel(c[k]) != d_rootLevel
	      ) {
	    // failed, can't remove lit
	    out_learnt[j++] = lit;
	    keep = true;
	  }
	}
	if (!keep) {
	  d_analyze_redundant.push_back(lit);
	}
      }
    }
  }

  out_learnt.resize(j);
  }

  // clean seen for simplification and log derivation
  // do this in reverse chronological order of variable assignment
  // in combination with removing duplication literals after each resolution step
  // this allows to resolve on each literal only once,
  // as it depends only on literals (its clause contains only literals)
  // which were assigned earlier.
  if (getDerivation() != NULL) {
    std::sort(d_analyze_redundant.begin(), d_analyze_redundant.end(), lastToFirst_lt(d_trail_pos));
  }
  for (vector<Lit>::const_iterator i = d_analyze_redundant.begin(); i != d_analyze_redundant.end(); ++i) {
    Lit lit(*i);
    d_analyze_seen[lit.var()] = 0;

    // if this literal is falsified in the root level,
    // but not implied in the current push level,
    // and the lemma is currently valid in levels lower than the current push level,
    // then don't remove the literal.
    // instead move it to the end of the lemma,
    // so that it won't hurt performance.
    if (out_learnt.size() > 0 // found the empty clause, so remove all literals
	&&
	getLevel(lit) == d_rootLevel
	&&
	getPushID(lit) > pushID
	&&
	!d_pushes.empty()
	&&
	getPushID(lit) > d_pushes.front().d_clauseID
	) {
      out_learnt.push_back(lit);
      continue;
    }

    // update the push level and the derivation wrt. the removed literal

    pushID = max(pushID, getPushID(lit));
    
    if (getDerivation() != NULL) {
      // resolve on each removed literal with its reason
      if (getLevel(lit) == d_rootLevel) {
	inference->add(lit, getDerivation()->computeRootReason(~lit, this));
      }
      else {
	Clause* reason = getReason(lit);
	inference->add(lit, reason);
      }
    }
  }

  d_analyze_redundant.clear();
}


// Check if 'p' can be removed. 'min_level' is used to abort early if visiting literals at a level that cannot be removed.
//
// 'p' can be removed if it depends only on literals
// on which they other conflict clause literals do depend as well.
bool Solver::analyze_removable(Lit p, unsigned int min_level, int pushID) {
  DebugAssert(getReason(p) != Clause::Decision(), "MiniSat::Solver::analyze_removable: p is a decision.");

  d_analyze_stack.clear();
  d_analyze_stack.push_back(p);
  int top = d_analyze_redundant.size();

  while (d_analyze_stack.size() > 0){
    DebugAssert(getReason(d_analyze_stack.back()) != Clause::Decision(),
		"MiniSat::Solver::analyze_removable: stack var is a decision.");
    DebugAssert(getReason(d_analyze_stack.back()) != Clause::TheoryImplication(),
		"MiniSat::Solver::analyze_removable: stack var is an unresolved theory implication.");
    Clause& c = *getReason(d_analyze_stack.back()); d_analyze_stack.pop_back();
    for (int i = 1; i < c.size(); i++) {
      Lit p = c[i];
      // ignore literals already considered or implied at root level
      if (!d_analyze_seen[p.var()]) {
	if (getLevel(p) == d_rootLevel) {
	  d_analyze_redundant.push_back(p);
	  d_analyze_seen[p.var()] = 1;
	}
	else {
	  // min_level is a precheck,
	  // only try to remove literals which might be implied,
	  // at least wrt. to the abstraction min_level
	  if (getReason(p) != Clause::Decision() && ((1 << (getLevel(p) & 31)) & min_level) != 0){
	    d_analyze_seen[p.var()] = 1;
	    d_analyze_stack.push_back(p);
	    d_analyze_redundant.push_back(p);
	  } else {
	    // failed, so undo changes to seen literals/redundant and return
	  for (size_type j = top; j < d_analyze_redundant.size(); ++j) {
	    d_analyze_seen[d_analyze_redundant[j].var()] = 0;
	  }
	  d_analyze_redundant.resize(top);
	  return false;
	  }
	}
      }
    }
  }
  
  d_analyze_redundant.push_back(p);
  return true;
}



bool Solver::isImpliedAt(Lit lit, int clausePushID) const {
  return
    // literal asserted before first push
    (d_pushes.empty() || getPushID(lit) <= d_pushes.front().d_clauseID)
    ||
    // or literal depends only on clauses added before given clause
    getPushID(lit) < clausePushID;
  
}


// Can assume everything has been propagated! (esp. the first two literals are != l_False, unless
// the clause is binary and satisfied, in which case the first literal is true)
// Returns True if clause is satisfied (will be removed), False otherwise.
//
bool Solver::isPermSatisfied(Clause* c) const {
  for (int i = 0; i < c->size(); i++){
    Lit lit((*c)[i]);
    if (getValue(lit) == l_True
	&& getLevel(lit) == d_rootLevel
	&& isImpliedAt(lit, c->pushID())
	)
      return true;
  }
  return false;
}



// a split decision, returns FALSE if immediate conflict.
bool Solver::assume(Lit p) {
  d_trail_lim.push_back(d_trail.size());
  d_stats.max_level = std::max(d_trail_lim.size(), size_type(d_stats.max_level));
  return enqueue(p, decisionLevel(), Clause::Decision());
}


// Revert to the state at given level, assert conflict clause and pending clauses
void Solver::backtrack(int toLevel, Clause* learnt_clause) {
  DebugAssert (decisionLevel() > toLevel, "MiniSat::Solver::backtrack: backtrack not to previous level");

  // backtrack theories
  DebugAssert(toLevel >= d_rootLevel, "MiniSat::Solver::backtrack: backtrack beyond root level");
  for (int i = toLevel; i < decisionLevel(); ++i) {
    d_theoryAPI->pop();
  }

  // backtrack trail
  int trail_size = d_trail.size();
  int trail_jump = d_trail_lim[toLevel];
  int first_invalid = d_trail_lim[toLevel];
  for (int c = first_invalid; c < trail_size; ++c) {
    Var x  = d_trail[c].var();    
    // only remove enqueued elements which are not still implied after backtracking
    if (getLevel(x) > toLevel) {
      //setLevel(x, -1);
      d_assigns[x] = toInt(l_Undef);
      d_reason [x] = NULL;
      //d_pushIDs[x] = -1;
      d_order.undo(x);
    }
    else {
      d_trail[first_invalid] = d_trail[c];
      if (d_derivation != NULL) d_trail_pos[x] = first_invalid;
      ++first_invalid;
    }
  }
  // shrink queue
  d_trail.resize(first_invalid);
  d_trail_lim.resize(toLevel);
  d_qhead = trail_jump;
  d_thead = d_qhead;

  // insert lemma
  // we want to insert the lemma before the original conflicting clause,
  // so that propagation is done on the lemma instead of that clause.
  // as that clause might be a theory clause in d_pendingClauses,
  // the lemma has to be inserted before the pending clauses are added.
  insertClause(learnt_clause);


  // enqueue clauses which were conflicting in previous assignment
  while (!isConflicting() && !d_pendingClauses.empty()) {
    Clause* c = d_pendingClauses.front();
    d_pendingClauses.pop();
    addClause(*c, true);
    xfree(c);
  }


  // deallocate explanations for theory implications
  // which have been retracted and are thus not needed anymore.
  //
  // not necessarily ordered by level,
  // so stackwise deallocation by level does not necessarily remove
  // all possible explanations as soon as possible.
  // still, should be a good enough compromise between speed and completeness.
  bool done = false;
  while (!done && !d_theoryExplanations.empty()) {
    std::pair<int, Clause*> pair = d_theoryExplanations.top();
    if (pair.first > toLevel) {
      d_theoryExplanations.pop();
      remove(pair.second, true);
    }
    else {
      done = true;
    }
  }
}


/*_________________________________________________________________________________________________
|
|  enqueue : (p : Lit) (from : Clause*)  ->  [bool]
|  
|  Description:
|    Puts a new fact on the propagation queue as well as immediately updating the variable's value.
|    Should a conflict arise, FALSE is returned.
|  
|  Input:
|    p    - The fact to enqueue
|    decisionLevel - The level from which on this propagation/decision holds.
|           if a clause is added in a non-root level, there might be propagations
|           which are not only valid in the current, but also earlier levels.
|    from - [Optional] Fact propagated from this (currently) unit clause. Stored in 'reason[]'.
|           Default value is NULL (no reason).
|           GClause::s_theoryImplication means theory implication where explanation
|           has not been retrieved yet.
|  
|  Output:
|    TRUE if fact was enqueued without conflict, FALSE otherwise.
|________________________________________________________________________________________________@*/
bool Solver::enqueue(Lit p, int decisionLevel, Clause* from) {
  lbool value(getValue(p));
  if (value != l_Undef) {
    return value != l_False;
  }
  else {
    Var var(p.var());
    d_assigns[var] = toInt(lbool(p.sign()));
    setLevel(var, decisionLevel);
    d_reason [var] = from;
    setPushID(var, from);
    d_trail.push_back(p);
    if (d_derivation != NULL) d_trail_pos[var] = d_trail.size();
    return true;
  }
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates one enqueued fact. If a conflict arises, updateConflict is called.
|________________________________________________________________________________________________@*/

// None:
//
// due to theory clauses and lazy retrieval of theory implications we get propagations
// out of any chronological order.
// therefore it is not guaranteed that in a propagating clause
// the first two literals (the watched literals) have the highest decision level.
//
// this doesn't matter, though, it suffices to ensure that
// if there are less than two undefined literals in a clause,
// than these are at the first two positions?
//
// Reasoning, for eager retrieval of explanations for theory implications:
// case analysis for first two positions:
// 1) TRUE, TRUE
// then the clause is satisfied until after backtracking
// the first two literals are undefined, or we get case 2) TRUE, FALSE
//
// 2) TRUE, FALSE
// if TRUE is true because it is a theory implication of FALSE,
// this is fine, as TRUE and FALSE will be backtracked at the same time,
// and then both literals will be undefined.
//
// this holds in general if TRUE was set before FALSE was set,
// so this case is fine.
//
// and TRUE can't be set after FALSE was set,
// as this would imply that all other literals are falsified as well
// (otherwise the FALSE literal would be replace by an undefined/satisfied literal),
// and then TRUE would be implied at the same level as FALSE
//
// 3) FALSE, TRUE
// can not happen, falsifying the first literal will reorder this to TRUE, FALSE
//
// 4) FALSE, FALSE
// Both literals must be falsified at the current level,
// as falsifying one triggers unit propagation on the other in the same level.
// so after backtracking both are undefined.
//
//
// now, if explanations for theory implications are retrieved lazily,
// then the level in which a literal was set might change later on.
// i.e. first it is assumed to be of the level in which the theory implication happened,
// but later on, when checking its explanation,
// the real level might be calculated to be an earlier level.
//
// this means, when the original level was L and the real level is K,
// that this literal is going to be undefined when backtracking before L,
// but is immediately propagated again if the new level is >= K.
// this is done until level K is reached,
// then this literal behaves like any ordinary literal.
// (ensured by backtrack)
//
// case analysis for first two positions:
// 1) TRUE, TRUE
// same as before
//
// 2) TRUE, FALSE
// the new case is that TRUE was initially of level <= FALSE,
// but now FALSE is set to a level < TRUE.
//
// then when on backtracking TRUE is unset,
// FALSE will also be unset, but then right away be set to FALSE again,
// so they work fine as watched literals.
//
// 3) FALSE, TRUE
// same as before
//
// 4) FALSE, FALSE
// if the level of both literals is unchanged,
// changes in other literals don't matter,
// as after backtracking both are undefined (same as before)
//
// if for one of the two (or both) the level is changed,
// after backtracking it will be falsified again immediately,
// and the watched literal works as expected:
// either the other literal is propagated,
// or there is now an undefined literal in the rest of the clause
// which becomes the new watched literal.
//
// changes in the rest of the clause are of no consequence,
// as they are assumed to be false in the conflict level,
// changes in their level do not change this,
// and after backtracking they are again taken into consideration
// for finding a new watched literal.
//
// so, even for lazy retrieval of theory implication explanations
// there is no need to explicitly set the 2nd watched literal
// to the most recently falsified one.
void Solver::propagate() {
  Lit            p   = d_trail[d_qhead++];     // 'p' is enqueued fact to propagate.
  vector<Clause*>&  ws  = getWatches(p);

  d_stats.propagations++;
  --d_simpDB_props;
  if (getLevel(p) == d_rootLevel) ++d_simpDB_assigns;

  // propagate p to theories
  if (!defer_theory_propagation) {
    d_theoryAPI->assertLit(miniSatToCVC(p));
    ++d_thead;
  }
  
  vector<Clause*>::iterator j = ws.begin();
  vector<Clause*>::iterator i = ws.begin();
  vector<Clause*>::iterator end = ws.end();
  while (i != end) {
    Clause& c = **i;
    ++i;
    
    // Make sure the false literal is data[1]:
    Lit false_lit = ~p;
    if (c[0] == false_lit) {
      c[0] = c[1];
      c[1] = false_lit;
    }
    
    Lit   first = c[0];
    lbool val   = getValue(first);
    
    // If 0th watch is true, then clause is already satisfied.
    if (val == l_True) {
      DebugAssert(getValue(c[0]) == l_True && getValue(c[1]) == l_False,
		  "MiniSat::Solver:::propagate: True/False");
      *j = &c; ++j;
    }
    // Look for new watch:
    else {
      for (int k = 2; k < c.size(); k++) {
	if (getValue(c[k]) != l_False) {
	  c[1] = c[k];
	  c[k] = false_lit;
	  addWatch(~c[1], &c);
	  goto FoundWatch;
	}
      }

      // Did not find watch -- clause is unit under assignment:

      // check that all other literals are false
      IF_DEBUG(
        for (int z = 1; z < c.size(); ++z) {
	  DebugAssert(getValue(c[z]) == l_False,
		      "MiniSat::Solver:::propagate: Unit Propagation");
	}
      )

      *j = &c; ++j;
      if (!enqueue(first, getImplicationLevel(c), &c)){
	// clause is conflicting
	updateConflict(&c);
	d_qhead = d_trail.size();

	// remove gap created by watches for which a new watch has been picked
	if (i != j) ws.erase(j, i);
	return;
      }

      FoundWatch:;
    }
  }
 
  // remove gap created by watches for which a new watch has been picked
  ws.erase(j, ws.end());
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt {
  bool operator () (Clause* x, Clause* y) {
    return x->size() > 2 && (y->size() == 2 || x->activity() < y->activity());
  }
};

void Solver::reduceDB() {
  d_stats.lm_simpl++;
  
  size_type     i, j;
  double  extra_lim = d_cla_inc / d_learnts.size();    // Remove any clause below this activity
  
  std::sort(d_learnts.begin(), d_learnts.end(), reduceDB_lt());
  for (i = j = 0; i < d_learnts.size() / 2; i++){
    if (d_learnts[i]->size() > 2 && !isReason(d_learnts[i]))
      remove(d_learnts[i]);
    else
      d_learnts[j++] = d_learnts[i];
  }
  for (; i < d_learnts.size(); i++){
    if (d_learnts[i]->size() > 2 && !isReason(d_learnts[i]) && d_learnts[i]->activity() < extra_lim)
      remove(d_learnts[i]);
    else
      d_learnts[j++] = d_learnts[i];
  }

  d_learnts.resize(d_learnts.size() - (i - j), NULL);
  d_stats.del_lemmas += (i - j);
  
  d_simpRD_learnts = d_learnts.size();
}


/*_________________________________________________________________________________________________
|
|  simplifyDB : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
void Solver::simplifyDB() {
  // clause set is unsatisfiable
  if (isConflicting()) return;

  // need to do propagation to exhaustion before watches can be removed below.
  // e.g. in a <- b, c, where b an c are satisfied by unit clauses,
  // and b and c have been added to the propagation queue,
  // but not propagated yet: then the watches are not evaluated yet,
  // and a has not been propapagated.
  // thus by removing the watches on b and c,
  // the propagation of a would be lost.
  DebugAssert(d_qhead == d_trail.size(),
	      "MiniSat::Solver::simplifyDB: called while propagation queue was not empty");

  d_stats.db_simpl++;

  // Clear watcher lists:
  // could do that only for literals which are implied permanently,
  // but we don't know that anymore with the push/pop interface:
  // even if the push id of a literal is less than the first push clause id,
  // it might depend on theory clauses,
  // which will be retracted after a pop,
  // so that the literal is not implied anymore.
  // thus, this faster way of cleaning watches can not be used,
  // instead they have to removed per clause below
  /*
  Lit lit;
  for (vector<Lit>::const_iterator i = d_trail.begin(); i != d_trail.end(); ++i) {
    lit = *i;
    if (getLevel(lit) == d_rootLevel
	&&
	// must be in the root push
	(d_pushes.empty() || getPushID(lit) <= d_pushes.front().d_clauseID)
	) {
      getWatches(lit).clear();
      getWatches(~(lit)).clear();
    }
  }
  */

  // Remove satisfied clauses:
  for (int type = 0; type < 2; type++){
    vector<Clause*>& cs = type ? d_learnts : d_clauses;
    size_type j = 0;
    bool satisfied = false;
    for (vector<Clause*>::const_iterator i = cs.begin(); i != cs.end(); ++i) {
      Clause* clause = *i;
    
      
      if (isReason(clause)) {
	cs[j++] = clause;
      }
      else {
	satisfied = false;
	//	falsified = 0;
	int k = 0;
	int end = clause->size() - 1;
	// skip the already permanently falsified tail
	// clause should not be permanently falsified,
	// as simplifyDB should only be called in a consistent state.
	while (
	  (getLevel((*clause)[end]) == d_rootLevel)
	  &&
	  (getValue((*clause)[end]) == l_False)) {
	  DebugAssert(end > 0,
		      "MiniSat::Solver::simplifyDB: permanently falsified clause found");
	  --end;
	}

	while (k < end) {
	  Lit lit((*clause)[k]);
	  if (getLevel(lit) != d_rootLevel) {
	    ++k;
	  }
	  else if (getValue(lit) == l_True) {
	    if (isImpliedAt(lit, clause->pushID())) {
	      satisfied = true;
	      break;
	    }
	    else {
	      ++k;
	    }
	  }
	  else if (k > 1 && getValue(lit) == l_False) {
	    --end;
	    (*clause)[k] = (*clause)[end];
	    (*clause)[end] = lit;
	  } else {
	    ++k;
	  }
	}
	
	if (satisfied) {
	  d_stats.del_clauses++;
	  remove(clause);
	}
	else {
	  cs[j++] = clause;
	}
      }
      

      // isReason also ensures that unit clauses are kept
	/*
      if (!isReason(clause) && isPermSatisfied(clause)) {
	d_stats.del_clauses++;
	remove(clause);
      }
      else {
	cs[j++] = clause;
	}*/
      
    }
    cs.resize(j);
  }

  d_simpDB_assigns = 0;
  d_simpDB_props   = d_stats.clauses_literals + d_stats.learnts_literals;
}


void Solver::protocolPropagation() const {
  if (protocol) {
    Lit lit(d_trail[d_qhead]);
    cout << "propagate: " << decisionLevel() << " : " << lit.index() << endl;
    cout << "propagate: " << decisionLevel() << " : " << toString(lit, true)
	 << " at: " << getLevel(lit);
    if (getReason(lit.var()) != Clause::Decision())
      cout <<  " from: "  << toString(*getReason(lit.var()), true);
    cout << endl;
  }
}


void Solver::propLookahead(const SearchParams& params) {
  // retrieve the best vars according to the heuristic
  vector<Var> nextVars(prop_lookahead);
  vector<Var>::size_type fetchedVars = 0;
  while (fetchedVars < nextVars.size()) {
    Var nextVar = d_order.select(params.random_var_freq);
    if (isRegistered(nextVar) || nextVar == var_Undef) {
      nextVars[fetchedVars] = nextVar;
      ++fetchedVars;
    }
  }
  // and immediately put the variables back
  for (vector<Var>::size_type i = 0; i < nextVars.size(); ++i) {
    if (nextVars[i] != var_Undef) d_order.undo(nextVars[i]);
  }

  
  // propagate on these vars
  int level = decisionLevel();
  int first_invalid = d_trail.size();

  for (vector<Var>::size_type i = 0; i < nextVars.size(); ++i) {
    Var nextVar = nextVars[i];
    if (nextVar == var_Undef) continue;

    for (int sign = 0; sign < 2; ++sign) {
      // first propagate on +var, then on -var
      if (sign == 0) {
	assume(Lit(nextVar, true));
      } else {
	assume(Lit(nextVar, false));
      }

      while (d_qhead < d_trail.size() && !isConflicting()) {
	protocolPropagation();
	propagate();
      }
      // propagation found a conflict
      if (isConflicting()) return;
      
      // otherwise remove assumption and backtrack
      for (int i = d_trail.size() - 1; i >= first_invalid; --i) {
	Var x  = d_trail[i].var();    
	d_assigns[x] = toInt(l_Undef);
	d_reason [x] = NULL;
	d_order.undo(x);
      }
      d_trail.resize(first_invalid);
      d_trail_lim.resize(level);
      d_qhead = first_invalid;
    }
  }
}


CVC3::QueryResult Solver::search() {
  DebugAssert(d_popRequests == 0, "MiniSat::Solver::search: pop requests pending");
  DebugAssert(!d_pushes.empty(), "MiniSat::Solver::search: no push before search");

  d_inSearch = true;

  SearchParams params(d_default_params);
  d_stats.starts++;
  d_var_decay = 1 / params.var_decay;
  d_cla_decay = 1 / params.clause_decay;

  if (protocol) printState();

  // initial unit propagation has been done in push -
  // already unsatisfiable without search
  if (!d_ok) {
    if (getDerivation() != NULL) getDerivation()->finish(d_conflict, this);
    return CVC3::UNSATISFIABLE;
  }

  // main search loop
  SAT::Lit literal;
  SAT::CNF_Formula_Impl clauses;
  for (;;){
    //    if (d_learnts.size() == 1 && decisionLevel() == 3) printState();
    // -1 needed if the current 'propagation' is a split
    DebugAssert(d_thead <= d_qhead, "MiniSat::Solver::search: thead <= qhead");
    DebugAssert(d_trail_lim.size() == 0 || d_qhead >= (size_type)d_trail_lim[decisionLevel() - 1],
		"MiniSat::Solver::search: qhead >= trail_lim[decisionLevel()");
    DebugAssert(d_trail_lim.size() == 0 || d_thead >= (size_type)d_trail_lim[decisionLevel() - 1],
		"MiniSat::Solver::search: thead >= trail_lim[decisionLevel()");

    // 1. clause set detected to be unsatisfiable
    if (!d_ok) {
      d_stats.conflicts++;
      if (getDerivation() != NULL) getDerivation()->finish(d_conflict, this);
      return CVC3::UNSATISFIABLE;
    }

    // 2. out of resources, e.g. quantifier instantiation aborted
    if (d_theoryAPI->outOfResources()) {
      return CVC3::ABORT;
    }

    // 3. boolean conflict, backtrack
    if (d_conflict != NULL){
      d_stats.conflicts++;

      // unsatisfiability detected
      if (decisionLevel() == d_rootLevel){
	d_ok = false;
	if (getDerivation() != NULL) getDerivation()->finish(d_conflict, this);
	return CVC3::UNSATISFIABLE;
      }

      int backtrack_level;
      Clause* learnt_clause = analyze(backtrack_level);
      backtrack(backtrack_level, learnt_clause);
      if (protocol) {
	cout << "conflict clause: " << toString(*learnt_clause, true);
	clauses.print();
      }
      varDecayActivity();
      claDecayActivity();	

      if (protocol) {
	cout << "backtrack to: " << backtrack_level << endl;
      }
    }

    // 4. theory conflict - cheap theory consistency check
    else if (d_theoryAPI->checkConsistent(clauses, false) == SAT::DPLLT::INCONSISTENT) {
      if (protocol) {
	cout << "theory inconsistency: " << endl;
	clauses.print();
      }      
      d_stats.theory_conflicts++;
      addFormula(clauses, true);
      clauses.reset();
      while (!isConflicting() && d_ok && d_qhead < d_trail.size() && !isConflicting()) {
        protocolPropagation();
        propagate();
      }
      DebugAssert(isConflicting(), "expected conflict");
    }
    
    // 5. boolean propagation
    else if (d_qhead < d_trail.size()) {
      // do boolean propagation to exhaustion
      // before telling the theories about propagated literals
      if (defer_theory_propagation) {
	while (d_ok && d_qhead < d_trail.size() && !isConflicting()) {
	  protocolPropagation();
	  propagate();
	}
      }
      // immediately tell theories about boolean propagations
      else {
	protocolPropagation();
	propagate();
      }
    }

    // :TODO: move to 8. tell theories about new boolean propagations
    // problem: can lead to worse performance,
    // apparently then to many theory clauses are learnt,
    // so need to forget them (database cleanup), or limit them (subsumption test)
    else if (defer_theory_propagation && d_thead < d_qhead) {
      while (d_thead < d_qhead) {
	d_theoryAPI->assertLit(miniSatToCVC(d_trail[d_thead]));
	++d_thead;
      }
    }

    // everything else
    else {
      DebugAssert(d_qhead == d_thead, "MiniSat::Solver::search: d_qhead != d_thead");

      // 6. theory clauses
      if (d_theoryAPI->getNewClauses(clauses)) {
	if (protocol) {
	  cout << "theory clauses: " << endl;
	  clauses.print();
	  printState();   
	}
	
	addFormula(clauses, true);
	clauses.reset();
	continue;
      }

      // 7. theory implication
      literal = d_theoryAPI->getImplication();
      if (!literal.isNull()) {
	Lit lit = MiniSat::cvcToMiniSat(literal);
	if (protocol) {
	  cout << "theory implication: " << lit.index() << endl;
	}
	if (
	    // get explanation now
	    eager_explanation
	    ||
	    // enqueue, and retrieve explanation (as a conflict clause)
	    // only if this implication is responsible for a conflict.
	    !enqueue(lit, decisionLevel(), Clause::TheoryImplication())
	    ) {
	  d_theoryAPI->getExplanation(literal, clauses);
	  if (protocol) {
	    cout << "theory implication reason: " << endl;
	    clauses.print();
	  }
	  addFormula(clauses, true);
	  clauses.reset();
	}
	continue;
      }

//       // 8. tell theories about new boolean propagations
//       if (defer_theory_propagation && d_thead < d_qhead) {
// 	d_theoryAPI->assertLit(miniSatToCVC(d_trail[d_thead]));
// 	++d_thead;
// 	continue;
//       }
//       DebugAssert(d_qhead == d_thead, "MiniSat::Solver::search: d_qhead != d_thead");

      // 9. boolean split
      Lit next = lit_Undef;

      
      // use CVC decider
      if (d_decider != NULL) {
	literal = d_decider->makeDecision();
	if (!literal.isNull()) {
	  next = MiniSat::cvcToMiniSat(literal);
	}
      }
      // use MiniSat's decision heuristic
      else {
	Var nextVar = d_order.select(params.random_var_freq);
	if (nextVar != var_Undef){
	  next = ~Lit(nextVar, false);
	}
      }
      if (next != lit_Undef) {
	// Simplify the set of problem clauses:
	// there must have been enough propagations in root level,
	// and no simplification too recently
	if (false && d_simpDB_props <= 0 && d_simpDB_assigns > (nAssigns() / 10)) {
	  simplifyDB();
	  DebugAssert(d_ok, "MiniSat::Solver::search: simplifyDB resulted in conflict");
	}
	  
	// Reduce the set of learnt clauses:
	//if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts)
	//if (learnts.size()-nAssigns() >= nClauses() / 3)
	// don't remove lemmas unless there are a significant number
	//if (d_learnts.size() - nAssigns() < nClauses() / 3)
	//return;
	// don't remove lemmas unless there are lots of new ones
	//	if (d_learnts.size() - nAssigns() < 3 * d_simpRD_learnts)
	//    return;
	// :TODO:
	//reduceDB();
	
	d_stats.decisions++;
	d_theoryAPI->push();
	
	DebugAssert(getValue(next) == l_Undef,
		    "MiniSat::Solver::search not undefined split variable chosen.");

	if (protocol) {
	  cout << "Split: " << next.index() << endl;
	}

	// do lookahead based on MiniSat's decision heuristic
	if (d_decider != NULL) propLookahead(params);
	if (isConflicting()) {
	  ++d_stats.debug;
	  continue;
	}

	
	if (!assume(next)) {
	  DebugAssert(false, "MiniSat::Solver::search contradictory split variable chosen.");
	}
	continue;	
      }

      // 10. full theory consistency check
      SAT::DPLLT::ConsistentResult result = d_theoryAPI->checkConsistent(clauses, true);
      // inconsistency detected
      if (result == SAT::DPLLT::INCONSISTENT) {
	if (protocol) {
	  cout << "theory conflict (FULL): " << endl;
	  clauses.print();
	  printState();
	}
	d_stats.theory_conflicts++;
	addFormula(clauses, true);
	clauses.reset();
        while (!isConflicting() && d_ok && d_qhead < d_trail.size() && !isConflicting()) {
          protocolPropagation();
          propagate();
        }
        DebugAssert(isConflicting(), "expected conflict");
	continue;
      }
      // perhaps consistent, new clauses added by theory propagation
      if (result == SAT::DPLLT::MAYBE_CONSISTENT) {
	if (d_theoryAPI->getNewClauses(clauses)) {
	  if (protocol) {
	    cout << "theory clauses: " << endl;
	    clauses.print();
	  }
	  addFormula(clauses, true);
	  clauses.reset();
	}
	// it can happen that after doing a full consistency check
	// there are actually no new theory clauses,
	// but then there will be new decisions in the next round.
	continue;
      }
      // consistent
      if (result == SAT::DPLLT::CONSISTENT) {
	DebugAssert(d_decider == NULL || d_decider->makeDecision().isNull(),
		    "DPLLTMiniSat::search: consistent result, but decider not done yet.");
	DebugAssert(allClausesSatisfied(),
		    "DPLLTMiniSat::search: consistent result, but not all clauses satisfied.");
	return CVC3::SATISFIABLE;
      }

      FatalAssert(false, "DPLLTMiniSat::search: unreachable");    
      return CVC3::SATISFIABLE;
    }
  }
}




/// Activity


// Divide all variable activities by 1e100.
//
void Solver::varRescaleActivity() {
  for (int i = 0; i < nVars(); i++)
    d_activity[i] *= 1e-100;
  d_var_inc *= 1e-100;
}


// Divide all constraint activities by 1e100.
//
void Solver::claRescaleActivity() {
  for (vector<Clause*>::const_iterator i = d_learnts.begin(); i != d_learnts.end(); i++) {
    (*i)->setActivity((*i)->activity() * (float)1e-20);
  }
  d_cla_inc *= 1e-20;
}




///
/// expensive debug checks
///

bool Solver::allClausesSatisfied() {
  if (!debug_full) return true;

  for (size_type i = 0; i < d_clauses.size(); ++i) {
    Clause& clause = *d_clauses[i];
    int size = clause.size();
    bool satisfied = false;
    for (int j = 0; j < size; ++j) {
      if (getValue(clause[j]) == l_True) {
	satisfied = true;
	break;
      }
    }
    if (!satisfied) {
      cout << "Clause not satisfied:" << endl;
      cout << toString(clause, true);

      for (int j = 0; j < size; ++j) {
	Lit lit = clause[j];
	bool found = false;
	const vector<Clause*>& ws  = getWatches(~lit);
	if (getLevel(lit) == d_rootLevel) {
	  found = true;
	} else {
	  for (size_type j = 0; !found && j < ws.size(); ++j) {
	    if (ws[j] == &clause) {
	      found = true;
	      break;
	    }
	  }
	}

	if (found) {
	  cout << "    watched: " << toString(lit, true) << endl;
	} else {
	  cout << "not watched: " << toString(lit, true) << endl;
	}
      }

      return false;
    }
  }
  return true;
}


void Solver::checkWatched(const Clause& clause) const {
  // unary clauses are not watched
  if (clause.size() < 2) return;

  for (int i = 0; i < 2; ++i) {
    Lit lit = clause[i];
    bool found = false;
    const vector<Clause*>& ws  = getWatches(~lit);
    
    // simplifyDB removes watches on permanently set literals
    if (getLevel(lit) == d_rootLevel) found = true;
    
    // search for clause in watches
    for (size_type j = 0; !found && j < ws.size(); ++j) {
      if (ws[j] == &clause) found = true;
    }

    if (!found) {
      printState();
      cout << toString(clause, true) << " : " << toString(clause[i], false) << endl;
      FatalAssert(false, "MiniSat::Solver::checkWatched");
    }
  }
}

void Solver::checkWatched() const {
  if (!debug_full) return;
  
  for (size_type i = 0; i < d_clauses.size(); ++i) {
    checkWatched(*d_clauses[i]);
  }
  
  for (size_type i = 0; i < d_learnts.size(); ++i) {
    checkWatched(*d_learnts[i]);
  }
}



void Solver::checkClause(const Clause& clause) const {
  // unary clauses are true anyway
  if (clause.size() < 2) return;

  // 1) the first two literals are undefined
  if (getValue(clause[0]) == l_Undef && getValue(clause[1]) == l_Undef)
    return;
  
  // 2) one of the first two literals is satisfied
  else if (getValue(clause[0]) == l_True || getValue(clause[1]) == l_True)
    return;

  // 3) the first literal is undefined and all other literals are falsified
  // 4) all literals are falsified
  else {
    bool ok = true;
    if (getValue(clause[0]) == l_True)
      ok = false;

    for (int j = 1; ok && j < clause.size(); ++j) {
      if (getValue(clause[j]) != l_False) {
	ok = false;
      }
    }
    
    if (ok) return;
  }
  
  printState();
  cout << endl;
  cout << toString(clause, true) << endl;
  FatalAssert(false, "MiniSat::Solver::checkClause");
}

void Solver::checkClauses() const {
  if (!debug_full) return;

  for (size_type i = 0; i < d_clauses.size(); ++i) {
    checkClause(*d_clauses[i]);
  }

  for (size_type i = 0; i < d_learnts.size(); ++i) {
    checkClause(*d_learnts[i]);
  }
}



void Solver::checkTrail() const {
  if (!debug_full) return;

  for (size_type i = 0; i < d_trail.size(); ++i) {
    Lit lit = d_trail[i];
    Var var = lit.var();
    Clause* reason = d_reason[var];

    if (reason == Clause::Decision()
	||
	reason == Clause::TheoryImplication()) {
    }

    else {
      const Clause& clause = *reason;

      // check that the first clause literal is the implied literal
      FatalAssert(clause.size() > 0, "MiniSat::Solver::checkTrail: empty clause as reason for " /*+ var*/);
      FatalAssert(lit == clause[0], "MiniSat::Solver::checkTrail: incorrect reason for " /*+ var*/);
      FatalAssert(d_assigns[var] == toInt(lbool(lit.sign())), "MiniSat::Solver::checkTrail: incorrect value for " /*+ var*/);
      
      // check that other literals are in the trail before this literal and this literal's level
      for (int j = 1; j < clause.size(); ++j) {
	Lit clauseLit = clause[j];
	Var clauseVar = clauseLit.var();
	FatalAssert(getLevel(var) >= getLevel(clauseVar),
		    "MiniSat::Solver::checkTrail: depends on later asserted literal " /*+ var*/);
	
	bool found = false;
	for (size_type k = 0; k < i; ++k) {
	  if (d_trail[k] == ~clauseLit) {
	    found = true;
	    break;
	  }
	}
	FatalAssert(found, "MiniSat::Solver::checkTrail: depends on literal not in context " /*+ var*/);
      }
    }
  }
}










void Solver::setPushID(Var var, Clause* from) {
  // check that var is implied by from
  DebugAssert(getReason(var) == from, "MiniSat::Solver::setPushID: wrong reason given");
  int pushID = std::numeric_limits<int>::max();
  if (from != Clause::Decision() && from != Clause::TheoryImplication()) {
    pushID = from->pushID();
    for (int i = 1; i < from->size(); ++i) {
      pushID = std::max(pushID, getPushID((*from)[i]));
    }
  }
  d_pushIDs[var] = pushID;
}


void Solver::push() {
  DebugAssert(!inSearch(), "MiniSat::Solver::push: already in search");

  // inconsistency before this push, so nothing can happen after it,
  // so just mark this push as useless.
  // (can happen if before checkSat initial unit propagation finds an inconsistency)
  if (!d_ok) {
    d_pushes.push_back(PushEntry(-1, 0, 0, 0, true));
    return;
  }

  d_registeredVars.resize(d_registeredVars.size() + 1);

  // reinsert lemmas kept over the last pop
  for (vector<Clause*>::const_iterator i = d_popLemmas.begin(); i != d_popLemmas.end(); ++i) {
    Clause* lemma = *i;
    insertLemma(lemma, lemma->id(), lemma->pushID());
    d_stats.learnts_literals -= lemma->size();
    remove(lemma, true);
  }
  d_popLemmas.clear();

  // do propositional propagation to exhaustion, including the theory
  if (push_theory_propagation) {
    SAT::Lit literal;
    SAT::Clause clause;
    SAT::CNF_Formula_Impl clauses;
    // while more can be propagated
    while (!isConflicting() && (d_qhead < d_trail.size() || d_thead < d_qhead)) {
      // do propositional propagation to exhaustion
      while (!isConflicting() && d_qhead < d_trail.size()) {
	protocolPropagation();
	propagate();
      }
      
      // also propagate to theories right away
      if (defer_theory_propagation) {
	while (!isConflicting() && d_thead < d_qhead) {
	  d_theoryAPI->assertLit(miniSatToCVC(d_trail[d_thead]));
	  ++d_thead;
	}
      }

      // propagate a theory implication
      if (push_theory_implication) {
	literal = d_theoryAPI->getImplication();
	if (!literal.isNull()) {
	  Lit lit = MiniSat::cvcToMiniSat(literal);
	  if (protocol) {
	    cout << "theory implication: " << lit.index() << endl;
	  }
	  if (
	      // get explanation now
	      eager_explanation
	      ||
	      // enqueue, and retrieve explanation (as a conflict clause)
	      // only if this implication is responsible for a conflict.
	      !enqueue(lit, decisionLevel(), Clause::TheoryImplication())
	    ) {
	    d_theoryAPI->getExplanation(literal, clauses);
	    if (protocol) {
	      cout << "theory implication reason: " << endl;
	      clauses.print();
	    }
	    addFormula(clauses, false);
	    clauses.reset();
	  }
	  continue;
	}
      }

      // add a theory clause

      //      if (push_theory_clause && d_theoryAPI->getNewClauses(clauses)) {
      if (push_theory_clause ) {
	bool hasNewClauses = d_theoryAPI->getNewClauses(clauses);
	if(hasNewClauses){
	  if (protocol) {
	    cout << "theory clauses: " << endl;
	    clauses.print();
	    printState();
	  }
	  addFormula(clauses, false);
	  clauses.reset();
	  continue;
	}
      }
    }
  }
  // do propositional propagation to exhaustion, but only on the propositional level
  else {
    while (!isConflicting() && d_qhead < d_trail.size()) {
      protocolPropagation();
      propagate();
    }
  }

    
  simplifyDB();
  
  // can happen that conflict is detected in propagate
  // but d_ok is not immediately set to false

  if (isConflicting()) d_ok = false;

  if (d_derivation != NULL) d_derivation->push(d_clauseIDCounter - 1);
  d_pushes.push_back(PushEntry(d_clauseIDCounter - 1, d_trail.size(), d_qhead, d_thead, d_ok));
}



void Solver::requestPop() {
  DebugAssert(inPush(), "MiniSat::Solver::requestPop: no more pushes");

  // pop theories on first pop of consistent solver,
  // for inconsistent solver this is done in dpllt_minisat before the pop
  if (d_popRequests == 0 && isConsistent()) popTheories();
  ++d_popRequests;
}

void Solver::doPops() {
  if (d_popRequests == 0) return;

  while (d_popRequests > 1) {
    --d_popRequests;
    d_pushes.pop_back();
  }

  pop();
}

void Solver::popTheories() {
  for (int i = d_rootLevel; i < decisionLevel(); ++i) {
    d_theoryAPI->pop();
  }
}

void Solver::popClauses(const PushEntry& pushEntry, vector<Clause*>& clauses) {
  size_type i = 0;
  while (i != clauses.size()) {
    // keep clause
    if (clauses[i]->pushID() >= 0
	&&
	clauses[i]->pushID() <= pushEntry.d_clauseID) {
      //      cout << "solver keep : " << clauses[i]->id() << endl;
      //      cout << "solver keep2 : " << clauses[i]->pushID() << endl;
      ++i;
    }
    // remove clause
    else {
      //      cout << "solver pop : " << clauses[i]->id() << endl;
      remove(clauses[i]);
      clauses[i] = clauses.back();
      clauses.pop_back();
    }
  }
}

void Solver::pop() {
  DebugAssert(d_popRequests == 1, "Minisat::Solver::pop: d_popRequests != 1");

  --d_popRequests;
  PushEntry pushEntry = d_pushes.back();
  d_pushes.pop_back();

  // solver was already inconsistent before the push
  if (pushEntry.d_clauseID == -1) {
    DebugAssert(!d_ok, "Minisat::Solver::pop: inconsistent push, but d_ok == true");
    return;
  }

  // backtrack trail
  //
  // Note:
  // the entries that were added to the trail after the push,
  // and are kept over the pop,
  // are all based on propagating clauses/lemmas also kept after the push.
  // as they are not yet propagated yet, but only in the propagation queue,
  // watched literals will work fine.
  size_type first_invalid = pushEntry.d_trailSize;
  for (size_type i = pushEntry.d_trailSize; i != d_trail.size(); ++i) {
    Var x = d_trail[i].var();    
    //setLevel(x, -1);
    d_assigns[x] = toInt(l_Undef);
    d_reason [x] = NULL;
    //d_pushIDs[x] = -1;
    d_order.undo(x);
  }
  d_trail.resize(first_invalid);
  d_trail_lim.resize(0);
  d_qhead = pushEntry.d_qhead;
  d_thead = pushEntry.d_thead;

  // remove clauses added after push
  popClauses(pushEntry, d_clauses);


  // move all lemmas that are not already the reason for an implication
  // to pending lemmas - these are to be added when the next push is done.
  size_type i = 0;
  while (i != d_popLemmas.size()) {
    if (d_popLemmas[i]->pushID() <= pushEntry.d_clauseID) {
      ++i;
    } else {
      remove(d_popLemmas[i], true);
      d_popLemmas[i] = d_popLemmas.back();
      d_popLemmas.pop_back();
    }
  }

  i = 0;
  while (i != d_learnts.size()) {
    Clause* lemma = d_learnts[i];
    // lemma is propagating, so it was already present before the push
    if (isReason(lemma)) {
      //      cout << "solver keep lemma reason : " << lemma->id() << endl;
      //      cout << "solver keep lemma reason2 : " << lemma->pushID() << endl;
      ++i;
    }
    // keep lemma?
    else {
      d_stats.learnts_literals -= lemma->size();
      // lemma ok after push, mark it for reinsertion in the next push
      if (lemma->pushID() <= pushEntry.d_clauseID) {
	//      cout << "solver keep lemma : " << lemma->id() << endl;
      //      cout << "solver keep lemma2 : " << lemma->pushID() << endl;
	if (lemma->size() >= 2) {
	  removeWatch(getWatches(~(*lemma)[0]), lemma);
	  removeWatch(getWatches(~(*lemma)[1]), lemma);
	}
	d_popLemmas.push_back(lemma);
      }
      // lemma needs to be removed
      else {
	//      cout << "solver pop lemma : " << lemma->id() << endl;
	remove(lemma);
      }

      d_learnts[i] = d_learnts.back();
      d_learnts.pop_back();
    }
  }
  d_stats.debug += d_popLemmas.size();


  // remove all pending clauses and explanations
  while (!d_pendingClauses.empty()) {
    remove(d_pendingClauses.front(), true);
    d_pendingClauses.pop();
  }
  while (!d_theoryExplanations.empty()) {
    remove(d_theoryExplanations.top().second, true);
    d_theoryExplanations.pop();
  }


  // backtrack registered variables
  d_registeredVars.resize(d_pushes.size() + 1);

  if (pushEntry.d_ok) {
    // this needs to be done _after_ clauses have been removed above,
    // as it might deallocate removed clauses
    if (d_derivation != NULL) d_derivation->pop(pushEntry.d_clauseID);
    
    // not conflicting or in search anymore
    d_conflict = NULL;
    d_ok = true;
    d_inSearch = false;
  } else {
    DebugAssert(d_conflict != NULL, "MiniSat::Solver::pop: not in conflict 1");
    DebugAssert(!d_ok, "MiniSat::Solver::pop: not in conflict 2");
  }
}
