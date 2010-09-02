/*****************************************************************************/
/*!
 *\file minisat_solver.h
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

/****************************************************************************************[Solver.h]
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

#ifndef _cvc3__minisat_h_
#define _cvc3__minisat_h_

#include "minisat_types.h"
#include "minisat_varorder.h"
#include "minisat_derivation.h"
#include "dpllt.h"
#include <queue>
#include <stack>
#include <vector>
#include <limits>
#include "hash_set.h"


// changes to MiniSat for CVC integration:
// 1) Decision heuristics
// 2) Theory clauses
// 3) Theory conflicts
// 4) Theory implications
// 5) binary clause trick
//
// in more detail:
// 1) Decision heuristics
// if a CVC decider is given (d_decider),
// it is used instead of MiniSat's decision heuristics
// to choose the next decision literal.
//
// 2) Theory clauses
// any number of clauses can be added at any decision level.
// see explanations for d_conflict and d_pendingClauses
//
// 3) Theory conflicts
// theory conflicts are just treated as conflicting theory clauses
//
// 4) Theory implications
// can be treated just as theory clauses if their explanation is retrieved immediately.
// otherwise, Clause::TheoryImplication() is used as a reason
// and the computation level is assumed to be the decision level,
// until the explanation is retrieved (see d_theoryExplanations).


// other changes:
// - binary clause trick
// MiniSat sometimes (watched literal, implication reason)
// used a pointer to a clause to represent a unary clause.
// the lowest bit was used to distinguish between a pointer,
// and the integer representing the literal of the unit clause.
// this saved memory and a pointer derefence.
// while this is reported to increase the performance by about 10%-20%,
// it also complicated the code. removing it didn't show any
// worse performance, so this trick was dropped.
//
// - store all clauses
// MiniSat stored unit and binary clauses only implicitly,
// in the context and the watched literal data.
// without the binary clause trick binary clauses have to be stored explicitly in d_clauses anyway.
// mostly for consistency and simplicity unary clauses are stored expicitly as well.
// not-so-convincing reasons are that this makes it also simpler to handle conflicting
// theory unit clauses (see insertClause()) by giving the reason
// (although one could use NULL instead,
//  but this would then complicate proof logging which is based on clause ids),
// and that it helps to retrieve the clause set independently of the assignment.
// (currently this is neither needed for DPLLT::checkSat nor DPLLT::continueCheck,
// the two operations in DPLLTMiniSat which use MiniSat)
// trying this out didn't show too much of an improvement, so it's not done.

namespace MiniSat {

// assume that all stl containers use the same size type
// and define it here once and for all
typedef std::vector<int>::size_type size_type;

  //
  /// conversions between MiniSat and CVC data types:
  ///

  // both MiniSat and CVC use integers for variables and literals.
  // CVC uses the integer's sign as the literals sign,
  // while MiniSat doubles the id and uses only positive numbers
  // (to be able to use them as array indizes).
  // e.g, for the variable p with the number 2,
  // CVC represents +p as 3 and -p as -3,
  // while MiniSat represents +p as 5 and -p as 4.
  //
  // unifying this representation is probably not worth doing,
  // as, first, conversion happens only at the interface level,
  // and second, no memory can be saved as a literal is just an integer.
  
  inline Var cvcToMiniSat(const SAT::Var& var) {
    return var.getIndex();  
  }

  inline SAT::Var miniSatToCVC(Var var) {
    return SAT::Var(var);
  }


  inline Lit cvcToMiniSat(const SAT::Lit& literal) {
    return MiniSat::Lit(cvcToMiniSat(literal.getVar()), literal.isPositive());  
  }

  inline SAT::Lit miniSatToCVC(Lit literal) {
    return SAT::Lit(miniSatToCVC(literal.var()), literal.sign());
  }
  
  // converts cvc clause into MiniSat literal list
  // returns true on permanently satisfied clause, i.e. clause containing 'true'
  bool cvcToMiniSat(const SAT::Clause& clause, std::vector<Lit>& literals);










//=================================================================================================
// MiniSat -- the main class:


struct SolverStats {
  int64_t   starts, decisions, propagations, conflicts, theory_conflicts, max_level;
  int64_t   clauses_literals, learnts_literals, max_literals,
    del_clauses, del_lemmas, db_simpl, lm_simpl,
    debug;
  SolverStats() : starts(0), decisions(0), propagations(0), conflicts(0), theory_conflicts(0), max_level(0),
		  clauses_literals(0), learnts_literals(0), max_literals(0),
		  del_clauses(0), del_lemmas(0), db_simpl(0), lm_simpl(0), debug(0) { }
};


// solver state at a push, needed so that a pop can revert to that state
struct PushEntry {
  // the highest id of all clauses known -
  // clauses with higher id must have been added after the push
  int d_clauseID;
  // size of d_trail
  size_type d_trailSize;
  size_type d_qhead;
  size_type d_thead;
  // conflict detected in initial propagation phase of push
  bool d_ok;

PushEntry(int clauseID, size_type trailSize, size_type qhead, size_type thead, bool ok) :
  d_clauseID(clauseID),
  d_trailSize(trailSize), d_qhead(qhead), d_thead(thead),
  d_ok(ok)
  {}
};


struct SearchParams {
    double var_decay, clause_decay, random_var_freq;    // (reasonable values are: 0.95, 0.999, 0.02)    
    SearchParams(double v = 1, double c = 1, double r = 0) : var_decay(v), clause_decay(c), random_var_freq(r) { }
};



class Solver {

  /// variables
protected:
  // level before first decision
  static const int d_rootLevel = 0;       

  /// status
  
  // a search() has been started
  bool d_inSearch;

  // if false, then the clause set is unsatisfiable.
  bool d_ok;       

  // this clause is conflicting with the current context
  //
  // it is not necessary to store more than one conflicting clause.
  // if there are several conflicting clauses,
  // they must all have been become conflicting at the same decision level,
  // as in a conflicting state no decision is made.
  //
  // after backtracking on any of these conflicting clauses,
  // the others are also not conflicting anymore,
  // if the conflict really was due to the current decision level.
  //
  // this is only not the case if theory clauses are involved.
  // i) a conflicting theory clause is added to d_pendingClauses instead of the clause set.
  // it will be only moved to the clause set if it is not conflicting,
  // otherwise it (or some other conflicting clause) will be used for backtracking.
  // ii) progapations based on new theory clauses may actually be already valid
  // in a previous level, not only in the current decision level.
  // on backtracking this will be kept in the part of the trail which has to be propagated,
  // and be propagated again after backtracking,
  // thus the conflict will be computed again.
  //
  // this scheme also allows to stop the propagation as soon as one conflict clause is found,
  // and backtrack only in this one, instead of searching for all conflicting clauses.
  //
  // the only attempt at picking a good conflict clause is to pick the shortest one.
  // looking at the lowest backjumping level is probably(?) too expensive.
  Clause* d_conflict;


  /// variable assignments, and pending propagations

  // mapping from literals to clauses in which a literal is watched,
  // literal.index() is used as the index
  std::vector<std::vector<Clause*> > d_watches;

  // The current assignments (lbool:s stored as char:s), indexed by var
  std::vector<signed char> d_assigns;

  // Assignment stack; stores all assigments made in the order they were made.
  // as theory clause and theory implications can add propagations
  // which are valid at earlier levels this list is _not_ necessarily ordered by level.
  std::vector<Lit> d_trail;

  // Separator indices for different decision levels in 'trail',
  // i.e. d_trail[trail_lim[i]] is the i.th decision
  std::vector<int> d_trail_lim;

  // 'd_trail_pos[var]' is the variable's position in 'trail[]'
  // used for proof logging
  std::vector<size_type> d_trail_pos;

  // head of propagation queue as index into the trail:
  // the context is the trail up to trail[qhead - 1],
  // the propagation queue is trail[qhead] to its end.
  size_type d_qhead;

  // like d_qhead for theories:
  // only the literals up to trail[thead - 1] have been asserted to the theories.
  size_type d_thead;

  // 'reason[var]' is the clause that implied the variables current value,
  // or Clause::Decision() for a decision ,
  // resp. (Clause::TheoryImplication()) for a theory implication with lazy explanation retrieval
  std::vector<Clause*> d_reason;

  // 'level[var]' is the decision level at which assignment was made.
  // except when the literal is a theory implication and the explanation
  // has not been retrieved yet. Then, this is the level of the literal's
  // assertion, and its real level will be computed during conflict analysis.
  std::vector<int> d_level;


  // Variables

  // the variables registered before the first push
  // and at each push level (with registerVar),
  // i.e. the variables occurring in the clauses at each push level.
  // cumulative, i.e. the variables registered in a push level
  // are the union of the variables registered at it and any previous level.
  std::vector<Hash::hash_set<Var> > d_registeredVars;


  /// Clauses

  // clause id counter
  int d_clauseIDCounter;

  // problem clauses (input clauses, theory clauses, explanations of theory implications).
  std::vector<Clause*> d_clauses;

  // learnt clauses (conflict clauses)
  std::vector<Clause*> d_learnts;


  /// Temporary clauses

  // these are clauses which were already conflicting when added.
  // so, first the solver has to backtrack,
  // then they can be added in a consistent state.
  std::queue<Clause*> d_pendingClauses;

  // these clauses are explanations for theory propagations which have been
  // retrieved to regress a conflict. they are gathered for the regression
  // in analyze, and then deleted on backtracking in backtrack.
  std::stack<std::pair<int, Clause*> > d_theoryExplanations;


  /// Push / Pop

  // pushes
  std::vector<PushEntry> d_pushes;

  // lemmas kept after a pop, to add with the next push
  std::vector<Clause*> d_popLemmas;

  // for each variable the highest pushID of the clauses used for its implication.
  // for a decision or theory implication with unknown explanation this is max_int,
  // for a unit clause as the reason it is the clauses pushID,
  // for any other reason it is the max of the d_pushIDs of the literals
  // falsifying the literals of the reason clause
  //
  // thus, an approximation for checking if a clause literal is permanently
  // falsified/satisfied even after pops (as long as the clause is not popped itself),
  // is that the implication level of the literal it the root level,
  // and that clauses' pushID is <= the d_pushIDs value of the literal.
  //
  // this can be used for simplifcation of clauses, lemma minimization,
  // and keeping propagated literals after a pop.
  std::vector<int> d_pushIDs;

  // :TODO: unify var -> x arrays into one with a varInfo data structure:
  // d_assigns, d_reason, d_level, d_pushIDs, d_activity
  // probably not: d_trail_pos, d_analyze_seen

  // number of queued pop requests
  unsigned int d_popRequests;



  /// heuristics

  // heuristics for keeping lemmas

  // Amount to bump next clause with.
  double d_cla_inc;
  // INVERSE decay factor for clause activity: stores 1/decay.
  double d_cla_decay;

  // heuristics for variable decisions

  // A heuristic measurement of the activity of a variable.
  std::vector<double> d_activity;
  // Amount to bump next variable with.
  double d_var_inc;
  // INVERSE decay factor for variable activity: stores 1/decay.
  // Use negative value for static variable order.
  double d_var_decay;
  // Keeps track of the decision variable order.
  VarOrder d_order;

  // heuristics for clause/lemma database cleanup

  // Number of top-level assignments since last execution of 'simplifyDB()'.
  int d_simpDB_assigns;
  // Remaining number of propagations that must be made before next execution of 'simplifyDB()'.
  int64_t d_simpDB_props;
  // Number of lemmas after last execution of 'reduceDB()'.
  int d_simpRD_learnts;


  /// CVC interface

  // CVC theory API
  SAT::DPLLT::TheoryAPI* d_theoryAPI;

  // CVC decision heuristic
  SAT::DPLLT::Decider* d_decider;


  /// proof logging

  // log derivation, to create a resolution proof from a closed derivation tree proof
  Derivation* d_derivation;
  

  /// Mode of operation:
  
  // Restart frequency etc.
  SearchParams d_default_params;

  // Controls conflict clause minimization. true by default.
  bool d_expensive_ccmin;


  /// Temporaries (to reduce allocation overhead).
  // Each variable is prefixed by the method in which is used:

  std::vector<char> d_analyze_seen;
  std::vector<Lit> d_analyze_stack;
  std::vector<Lit> d_analyze_redundant;

  // solver statistics
  SolverStats d_stats;


protected:
  /// Search:

  // the current decision level
  int decisionLevel() const { return (int)d_trail_lim.size(); }

  // decision on p
  bool assume(Lit p);

  // queue a literal for propagation, at decisionLevel implied by reason
  bool enqueue(Lit fact, int decisionLevel, Clause* reason);

  // propagate a literal (the head of the propagation queue)
  void propagate();

  // perform a lookahead on the best split literals.
  // this is done on the propositional level only, without involving theories.
  void propLookahead(const SearchParams& params);

  /// Conflict handling

  // conflict analysis: returns conflict clause and level to backtrack to
  // clause implies its first literal in level out_btlevel
  Clause* analyze(int& out_btlevel);

  // conflict analysis: conflict clause minimization (helper method for 'analyze()')
  void analyze_minimize(std::vector<Lit>& out_learnt, Inference* inference, int& pushID);

  // conflict analysis: conflict clause minimization (helper method for 'analyze()')
  bool analyze_removable(Lit p, unsigned int min_level, int pushID);

  // backtrack to level, add conflict clause
  void backtrack(int level, Clause* clause);

  // is the current state conflicting, i.e. is there a conflicting clause?
  bool isConflicting() const;

  // mark this clause as conflicting
  void updateConflict(Clause* clause);

  // returns the level in which this clause implies its first literal.
  // precondition: all clause literals except for the first must be falsified.
  int getImplicationLevel(const Clause& clause) const;

  // returns the level in which this clause became falsified
  // (or at least fully assigned).
  // precondition: no clause literal is undefined.
  int getConflictLevel(const Clause& clause) const;

  // if this literal is a theory implied literal and its explanation has not been retrieved,
  // then this is done now and the literal's reason is updated.
  // precondition: literal must be a propagated literal
  void resolveTheoryImplication(Lit literal);


  /// unit propagation

  // return the watched clauses for a literal
  std::vector<Clause*>& getWatches(Lit literal) { return d_watches[literal.index()]; };

  // return the watched clauses for a literal
  const std::vector<Clause*>& getWatches(Lit literal) const { return d_watches[literal.index()]; };

  // adds a watch to a clause literal
  // precondition: literal must be one of the first two literals in clause
  void addWatch(Lit literal, Clause* clause) { getWatches(literal).push_back(clause); };

  // removes the clause from the list of watched clauses
  void removeWatch(std::vector<Clause*>& ws, Clause* elem);


  /// Operations on clauses:

  // registers a variable - any variable has to be registered before it is used in the search.
  void registerVar(Var var);

  // checks if a variable is already registered (pop can remove a variable)
  bool isRegistered(Var var);

  // creates/adds a clause or a lemma and returns it; registers all variables,
  // used by all other addClause methods
  void addClause(std::vector<Lit>& literals, CVC3::Theorem theorem, int clauseID);

  // adds a clause or a lemma to the solver, watched lists, and checks if it is unit/conflicting
  // clause activity heuristics are updated.
  // precondition: all variables are registered
  // precondition: a lemma is propagating its first literal
  void insertClause(Clause* clause);

  // add a lemma which has not been computed just now (see push(), createFrom()),
  // so it is not necessary propagating (which is assumed by insertClause())
  void insertLemma(const Clause* lemma, int clauseID, int pushID);

  // simplify clause based on root level assignment
  // precondition: all variables are registered
  bool simplifyClause(std::vector<Lit>& literals, int clausePushID) const;

  // order a clause such that it is consistent with the current assignment,
  // i.e. the two first literals can be taken as the watched literals.
  // precondition: all variables are registered
  void orderClause(std::vector<Lit>& literals) const;

  // deallocate a clause, and removes it from watches if just_dealloc is false
  void remove(Clause* c, bool just_dealloc = false);

  // assuming that the literal is implied at the root level:
  // will the literal be assigned as long as the clause exists, even over pops?
  bool isImpliedAt(Lit lit, int clausePushID) const;

  // is this clause permanently satisfied?
  bool isPermSatisfied(Clause* c) const;


  // Push / Pop

  // sets the d_pushIDs entry of var implied by from
  void setPushID(Var var, Clause* from);

  // returns the d_pushIDs entry of a var
  // makes only sense for a var with a defined value
  int getPushID(Var var) const { return d_pushIDs[var]; }
  int getPushID(Lit lit) const { return getPushID(lit.var()); }

  // pop the most recent push
  void pop();
  void popClauses(const PushEntry& pushEntry, std::vector<Clause*>& clauses);

  
  /// Activity:
  
  void varBumpActivity(Lit p) {
    if (d_var_decay < 0) return;     // (negative decay means static variable order -- don't bump)
    if ( (d_activity[p.var()] += d_var_inc) > 1e100 ) varRescaleActivity();
    d_order.update(p.var()); }
  void varDecayActivity () { if (d_var_decay >= 0) d_var_inc *= d_var_decay; }
  void varRescaleActivity();
  void claDecayActivity() { d_cla_inc *= d_cla_decay; }
  void claRescaleActivity() ;
  void claBumpActivity (Clause* c) {
    float act = c->activity() + (float)d_cla_inc;
    c->setActivity(act);
    if (act > 1e20) claRescaleActivity();
  }
  


  /// debugging

  // are all clauses (excluding lemmas) satisfied?
  bool allClausesSatisfied();

  // checks that the first two literals of a clause are watched
  void checkWatched(const Clause& clause) const;
  void checkWatched() const;

  // checks that for each clause one of these holds:
  // 1) the first two literals are undefined
  // 2) one of the first two literals is satisfied
  // 3) the first literal is undefined and all other literals are falsified
  // 4) all literals are falsified
  void checkClause(const Clause& clause) const;
  void checkClauses() const;

  // checks that each literal in the context(trail) is either
  // 1) a decision
  // 2) or implied by previous context literals
  void checkTrail() const;

  // print the current propagation step
  void protocolPropagation() const;


public:
  /// Initialization

  // assumes that this is the SAT solver in control of CVC theories,
  // so it immediately pushs a new theory context.
  //
  // uses MiniSat's internal decision heuristics if decider is NULL
  //
  // if logDerivation then the derivation will be logged in getDerivation(),
  // which provides a prove if the empty clause is derived.
  Solver(SAT::DPLLT::TheoryAPI* theoryAPI, SAT::DPLLT::Decider* decider,
	 bool logDerivation);

  // copies clauses, assignment as unit clauses, and lemmas
  // will be in root level
  static Solver* createFrom(const Solver* solver);

  // releases all memory, but does not pop theories.
  // this is according to the semantics expected by CVC:
  // is the solver detects unsatisfiability, it pops all theory levels.
  // otherwise the caller is responsible for resetting the theory levels.
  ~Solver();


  /// problem specification

  // converts cvc clause into MiniSat clause with the given id.
  // returns NULL on permanently satisfied clause, i.e. clause containing 'true'
  Clause* cvcToMiniSat(const SAT::Clause& clause, int id);

  // adds a unit clause given as a literal
  void addClause(Lit p, CVC3::Theorem theorem);

  // adds a (copy of) clause, uses original clause id if wished
  void addClause(const Clause& clause, bool keepClauseID);

  // adds a CVC clause
  void addClause(const SAT::Clause& clause, bool isTheoryClause);

  // adds a CVC formula
  void addFormula(const SAT::CNF_Formula& cnf, bool isTheoryClause);

  // returns a unique id for a new clause
  // (addClause will then use the negation for theory clauses)
  int nextClauseID() {
    FatalAssert(d_clauseIDCounter >= 0, "MiniSat::Solver::nextClauseID: overflow");
    return d_clauseIDCounter++;
  };

  // removes permanently satisfied clauses
  void simplifyDB();

  // removes 'bad' lemmas
  void reduceDB();


  /// search

  // (continue) search with current clause set and context
  // until model is found (in d_trail), or unsatisfiability detected.
  // 
  // between two calls clauses may be added,
  // but everything else (including the theories) should remain untouched.
  //
  // the prover becomes essentially unusable if unsatisfiability is detected,
  // only data may be retrieved (clauses, statistics, proof, ...)
  CVC3::QueryResult search();

  // returns a resolution proof for unsatisfiability if
  // - createProof was true in the call to the constructor
  // - the last call to search returned status UNSATISFIABLE
  // returns NULL otherwise
  Derivation* getProof();

  // is the solver currently in a search state?
  // i.e. search() has been called and not been undone by a pop request.
  bool inSearch() const { return d_inSearch && d_popRequests == 0; }

  // is the solver in a consistent state?
  bool isConsistent() const { return !isConflicting(); }



  /// Push / Pop

  // push the current solver state
  // can only be done when solver is not already in a search (inSearch()).
  void push();

  // pop all theory levels pushed by the solver,
  // i.e. all (current) decision levels of the solver.
  void popTheories();

  // request to pop theories - all request are done when doPops is called
  void requestPop();

  // perform all pop requests (calls to requestPop)
  void doPops();

  // has there been a push which hasn't been (requested to be) undone yet?
  bool inPush() const { return d_pushes.size() > d_popRequests; }



  /// clauses / assignment

  // get the current value of a variable/literal
  lbool getValue(Var x) const { return toLbool(d_assigns[x]); }
  lbool getValue(Lit p) const { return p.sign() ? getValue(p.var()) : ~getValue(p.var()); }

  // get the assignment level of a variable/literal (which should have a value)
  int getLevel(Var var) const { return d_level[var]; };
  int getLevel(Lit lit) const { return getLevel(lit.var()); };

  // set the assignment level of a variable/literal
  void setLevel(Var var, int level) { d_level[var] = level; };
  void setLevel(Lit lit, int level) { setLevel(lit.var(), level); };

  // this clause is the reason for a propagation and thus can't be removed
  // precondition: the first literal of the reason clause must be the propagated literal
  bool isReason(const Clause* c) const { return c->size() > 0 && d_reason[((*c)[0]).var()] == c; }

  // returns the implication reason of a variable (its value must be defined)
  Clause* getReason(Var var) const { return d_reason[var]; };

  // like getReason, but if resolveTheoryImplication is true,
  // then additionaly if literal is a theory implication resolveTheoryImplication() is called.
  Clause* getReason(Lit literal, bool resolveTheoryImplication = true);

  // the current clause set
  const std::vector<Clause*>& getClauses() const { return d_clauses; }

  // the current lemma set
  const std::vector<Clause*>& getLemmas() const { return d_learnts; }

  // the current variable assignments
  const std::vector<Lit>& getTrail() const { return d_trail; }

  // the derivation, logged if != NULL
  Derivation* getDerivation() { return d_derivation; }

  /// Statistics

  // derivation statistics
  const SolverStats& getStats() const { return d_stats; }

  // number of assigned variabels (context size)
  int nAssigns() const { return d_trail.size(); }

  // number of stored clauses (does not include clauses removed by simplifyDB)
  int nClauses() const { return d_clauses.size(); }

  // number of stored lemmas (forgotten lemmas are not counted)
  int nLearnts() const { return d_learnts.size(); }

  // variable with the highest id + 1
  // not necessaribly the number of variables, if they are not enumerated without gap
  int nVars() const { return d_assigns.size(); }


  /// String representation:

  // literal id, sign, current assignment as string
  std::string toString(Lit literal, bool showAssignment) const;

  // clause as string, showAssignment true -> show current assignment of each literal
  std::string toString(const std::vector<Lit>& clause, bool showAssignment) const;

  // clause as string, showAssignment true -> show current assignment of each literal
  std::string toString(const Clause& clause, bool showAssignment) const;

  // prints lemmas, clauses, assignment to cout
  void printState() const;

  // output the clause set and context in DIMACS format
  void printDIMACS() const;

  std::vector<SAT::Lit> curAssigns() ;
  std::vector<std::vector<SAT::Lit> > curClauses();
};

}




//=================================================================================================
#endif
