/*****************************************************************************/
/*!
 *\file minisat_derivation.cpp
 *\brief MiniSat proof logging
 *
 * Author: Alexander Fuchs
 *
 * Created: Sun Dec 07 11:09:00 2007
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


#include "minisat_derivation.h"
#include "minisat_solver.h"
#include "sat_proof.h"
#include <set>
#include <iostream>

using namespace MiniSat;
using namespace std;

std::string Inference::toString() const {
  ostringstream buffer;
  buffer << getStart();
  for (Inference::TSteps::const_iterator step = d_steps.begin(); step != d_steps.end(); ++step) {
    buffer << " " << step->first.toString() << " " << step->second;
  }
  return buffer.str();
}





Derivation::~Derivation() {
  // deallocate generated unit clauses
  for (TClauses::iterator i = d_unitClauses.begin(); i != d_unitClauses.end(); ++i) {
    xfree(i->second);
  }
  
  // deallocate removed clauses
  for (std::deque<Clause*>::iterator i = d_removedClauses.begin(); i != d_removedClauses.end(); ++i) {
    xfree(*i);
  }
  
  // deallocate inferences
  for (TInferences::iterator i = d_inferences.begin(); i != d_inferences.end(); ++i) {
    delete i->second;
  }
}


int Derivation::computeRootReason(Lit implied, Solver* solver) {
  Clause* reason = solver->getReason(implied);
  //  cout << "computeRootReason " << reason->id() << endl;
  FatalAssert(d_clauses.find(reason->id()) != d_clauses.end(),
	      "MiniSat::Derivation::computeRootReason: implied reason not registered");
  FatalAssert(reason == d_clauses.find(reason->id())->second,
	      "MiniSat::Derivation::computeRootReason: implied reason not same as registered");
  FatalAssert(reason != NULL, "MiniSat::Derivation::computeRootReason: implied reason is NULL");
  FatalAssert(reason != Clause::Decision(), "MiniSat::Derivation::computeRootReason: implied is a decision");
  FatalAssert((*reason)[0] == implied, "MiniSat::Derivation::computeRootReason: implied is not in its reason");
  IF_DEBUG (
    FatalAssert(solver->getValue((*reason)[0]) == l_True,
		"MiniSat::Derivation::computeRootReason: literal not implied (TRUE)");
    for (int i = 1; i < reason->size(); ++i) {
      FatalAssert(solver->getValue((*reason)[i]) == l_False,
		  "MiniSat::Derivation::computeRootReason: literal not implied (FALSE)");
    }
  )

  // already a unit clause, so done
  if (reason->size() == 1) {
    return reason->id();
  }

  // already derived the unit clause internally
  TClauses::const_iterator iter = d_unitClauses.find(implied.index());
  if (iter != d_unitClauses.end()) {
    return iter->second->id();
  }


  // otherwise resolve the reason ...
  Inference* inference = new Inference(reason->id());
  for (int i = 1; i < reason->size(); ++i) {
    Lit lit((*reason)[i]);
    inference->add(lit, computeRootReason(~lit, solver));
  }

  // and create the new unit clause
  // (after resolve, so that clause ids are chronological wrt. inference)
  vector<Lit> literals;
  literals.push_back(implied);
  Clause* unit = Clause_new(literals, CVC3::Theorem(), solver->nextClauseID());

  d_unitClauses[implied.index()] = unit;
  //    cout << "compute root reason : " << unit->id() << endl;
  registerClause(unit);
  registerInference(unit->id(), inference);

  return unit->id();
}


void Derivation::finish(Clause* clause, Solver* solver) {
  FatalAssert(clause != NULL, "MiniSat::derivation:finish:");

  // already the empty clause
  if (clause->size() == 0) {
    d_emptyClause = clause;
  }
  // derive the empty clause
  else {
    Inference* inference = new Inference(clause->id());
    for (int i = 0; i < clause->size(); ++i) {
      Lit lit((*clause)[i]);
      inference->add(lit, computeRootReason(~lit, solver));
    }
    vector<Lit> literals;
    Clause* empty = Clause_new(literals, CVC3::Theorem(), solver->nextClauseID());
    removedClause(empty);
    d_emptyClause = empty;
    registerClause(empty);
    registerInference(empty->id(), inference);
  }

  checkDerivation(clause);
  IF_DEBUG (checkDerivation(clause));

//   cout << "PROOF_START" << endl;
//   printDerivation();
//   cout << "PROOF_END" << endl;

}



void Derivation::checkDerivation(Clause* clause) {
  // find all relevant clauses

  // - relevant: set clauses used in derivation
  // - regress: relevant clauses whose antecedents have to be checked
  std::set<int> relevant;
  std::set<int> regress;

  regress.insert(clause->id());
  while (!regress.empty()) {
    // pick next clause to derive - start from bottom, i.e. latest derived clause
    int clauseID = *(regress.rbegin());
    regress.erase(clauseID);

    // move to clauses relevant for the derivation
    FatalAssert(relevant.count(clauseID) == 0, "Solver::printProof: already in relevant");
    relevant.insert(clauseID);

    // process antecedents
    TInferences::const_iterator iter = d_inferences.find(clauseID);
    // input clause
    if (iter == d_inferences.end()) {
      FatalAssert(d_inputClauses.contains(clauseID),
		  "Solver::printProof: clause without antecedents is not marked as input clause");
    }

    else {
      Inference* inference = iter->second;
      regress.insert(inference->getStart());
      const Inference::TSteps& steps = inference->getSteps();
      for (Inference::TSteps::const_iterator step = steps.begin(); step != steps.end(); ++step) {
	regress.insert(step->second);
      }
    }
  }


  // check derivation
  for (std::set<int>::iterator i = relevant.begin(); i != relevant.end(); ++i) {
    int clauseID = *i;
    FatalAssert(d_clauses.contains(clauseID),
		"MiniSat::Derivation::printProof: clause id in proof is not in clauses");
    Clause* clause = d_clauses.find(clauseID)->second;

    Inference* inference = NULL;
    TInferences::const_iterator j = d_inferences.find(clauseID);
    if (j != d_inferences.end()) {
      inference = j->second;
    }

    FatalAssert(inference != NULL || d_inputClauses.contains(clauseID),
		"MiniSat::Derivation::printProof: derivation of input clause");
    FatalAssert(inference == NULL || !d_inputClauses.contains(clauseID),
		"MiniSat::Derivation::printProof: no derivation for derived clause");

    if (inference != NULL) {
      //      cout << "Regress: " << clause->id() << " : " << clause->toString() << endl;
      FatalAssert(d_clauses.find(inference->getStart()) != d_clauses.end(),
        "MiniSat::Derivation::printProof: first not in clauses");

      Clause* first = d_clauses.find(inference->getStart())->second;
      //      cout << "Derived from : " << first->id() << " : " << first->toString() << endl;

      set<Lit> derived;
      for (int i = 0; i < first->size(); ++i) {
	derived.insert((*first)[i]);
      }

      // retrace derivation
      for (Inference::TSteps::const_iterator step = inference->getSteps().begin();
	   step != inference->getSteps().end(); ++step) {
	Lit lit = step->first;
	//	cout << " over " << lit.toString() << endl;
	//	cout << "Derived from ... : " << step->second << " : " << d_clauses.find(step->second)->second->toString() << endl;

        FatalAssert(d_clauses.find(step->second) != d_clauses.end(),
		    "MiniSat::Derivation::printProof: next not in clauses");
	Clause* next = d_clauses.find(step->second)->second;

	FatalAssert(derived.find(lit) != derived.end(),
		    "MiniSat::Derivation::printProof: lit not in derived");
	FatalAssert(next->contains(~lit),
		    "MiniSat::Derivation::printProof: ~lit not in next");

	derived.erase(lit);
	for (int i = 0; i < next->size(); ++i) {
	  if ((*next)[i] != ~lit) {
	    derived.insert((*next)[i]);
	  }
	}
      }

      // check that we got the expected clause
      for (int i = 0; i < clause->size(); ++i) {
	FatalAssert(derived.find((*clause)[i]) != derived.end(),
		    "MiniSat::Derivation::printProof: didn't derive expected clause");
	derived.erase((*clause)[i]);
      }
      FatalAssert(derived.empty(),
		  "MiniSat::Derivation::printProof: didn't derive expected clause 2");
    };
  }
}


SAT::SatProof* Derivation::createProof() {
  FatalAssert(d_emptyClause != NULL, "MiniSat::Derivation:createProof: no empty clause");
  FatalAssert(d_emptyClause->size() == 0,
	      "MiniSat::Derivation:createProof: empty clause is not empty");
  return createProof(d_emptyClause);
}

SAT::SatProof* Derivation::createProof(Clause* clause) {
  checkDerivation(clause);
  //  IF_DEBUG (checkDerivation(clause));

  // find all relevant clauses

  // - relevant: set clauses used in derivation
  // - regress: relevant clauses whose antecedents have to be checked
  std::set<int> relevant;
  std::set<int> regress;
  regress.insert(clause->id());
  while (!regress.empty()) {
    // pick next clause to derive - start from bottom, i.e. latest derived clause
    int clauseID = *(regress.rbegin());
    regress.erase(clauseID);
    relevant.insert(clauseID);

    // process antecedents
    TInferences::const_iterator iter = d_inferences.find(clauseID);
    // input clause
    if (iter != d_inferences.end()) {
      Inference* inference = iter->second;
      regress.insert(inference->getStart());
      const Inference::TSteps& steps = inference->getSteps();
      for (Inference::TSteps::const_iterator step = steps.begin(); step != steps.end(); ++step) {
	regress.insert(step->second);
      }
    }
  }

  // create proof
  SAT::SatProof* proof = new SAT::SatProof();
  std::hash_map<int, SAT::SatProofNode*> proofNodes;

  for (std::set<int>::iterator i = relevant.begin(); i != relevant.end(); ++i) {
    int clauseID = *i;
    Clause* clause = d_clauses.find(clauseID)->second;

    Inference* inference = NULL;
    TInferences::const_iterator j = d_inferences.find(clauseID);
    if (j == d_inferences.end()) {
      /*
<<<<<<< minisat_derivation.cpp
      FatalAssert(clause->getCvcClause() != NULL, "createProof: leaf without clause");
      FatalAssert(clause->getCvcClause() != NULL, "createProof: leaf without clause");
      proofNodes[clause->id()] = proof->registerLeaf(clause->getCvcClause());
      //      cout<<"cluase with :"  << clause->id() << " ---> " ;
      //      clause->getCvcClause()->print();
      //      cout << endl;
=======
      */
      FatalAssert(!clause->getTheorem().isNull(), "createProof: leaf without clause");
      proofNodes[clause->id()] = proof->registerLeaf(clause->getTheorem());
      /*
>>>>>>> 1.9
      */
    }

    else {
      inference = j->second;
      FatalAssert(proofNodes.contains(inference->getStart()), "createProof: contains inference start");
      SAT::SatProofNode* left = proofNodes.find(inference->getStart())->second;
      const Inference::TSteps& steps = inference->getSteps();
      for (Inference::TSteps::const_iterator step = steps.begin(); step != steps.end(); ++step) {
	FatalAssert(proofNodes.contains(step->second), "createProof: contains inference start");
	SAT::SatProofNode* right = proofNodes.find(step->second)->second;
	left = proof->registerNode(left, right, miniSatToCVC(step->first));
      }
      proofNodes[clause->id()] = left;
    }
  }
  proof->setRoot(proofNodes[clause->id()]);
  return proof;
}


void Derivation::printDerivation() {
  FatalAssert(d_emptyClause != NULL, "MiniSat::Derivation:printDerivation: no empty clause");
  FatalAssert(d_emptyClause->size() == 0,
	      "MiniSat::Derivation:printDerivation: empty clause is not empty");
  printDerivation(d_emptyClause);
}

void Derivation::printDerivation(Clause* clause) {
  IF_DEBUG (checkDerivation(clause));

  // find all relevant clauses

  // - relevant: set clauses used in derivation
  // - regress: relevant clauses whose antecedents have to be checked
  std::set<int> relevant;
  std::set<int> regress;

  regress.insert(clause->id());
  while (!regress.empty()) {
    // pick next clause to derive - start from bottom, i.e. latest derived clause
    int clauseID = *(regress.rbegin());
    regress.erase(clauseID);

    // move to clauses relevant for the derivation
    relevant.insert(clauseID);

    // process antecedents
    TInferences::const_iterator iter = d_inferences.find(clauseID);
    // input clause
    if (iter != d_inferences.end()) {
      Inference* inference = iter->second;
      regress.insert(inference->getStart());
      const Inference::TSteps& steps = inference->getSteps();
      for (Inference::TSteps::const_iterator step = steps.begin(); step != steps.end(); ++step) {
	regress.insert(step->second);
      }
    }
  }


  // print proof
  for (std::set<int>::iterator i = relevant.begin(); i != relevant.end(); ++i) {
    int clauseID = *i;
    Clause* clause = d_clauses.find(clauseID)->second;

    Inference* inference = NULL;
    TInferences::const_iterator j = d_inferences.find(clauseID);
    if (j != d_inferences.end()) {
      inference = j->second;
    }

    // ID D : L1 ... Ln : C1 K1 C2 K2 ... Cm
    cout << clauseID;
    // input clause or derived clause?
    if (d_inputClauses.contains(clauseID)) {
      cout << " I ";
    } else {
      cout << " D ";
    }
    cout << ": " << clause->toString() << " : ";
    if (inference != NULL) cout << inference->toString();
    cout << endl;    
  }
}


void Derivation::push(int clauseID) {
  //  cout << "derivation push: " << clauseID << endl;
}

void Derivation::pop(int clauseID) {
  //  cout << "derivation pop: " << clauseID << endl;
  // remove all popped clauses
  TClauses::const_iterator i = d_clauses.begin();
  while (i != d_clauses.end()) {
    Clause* clause = (*i).second;
    if (
	// Warning: clause removal needs to be done
	// exactly the same way in minisat_solver!!!

	// remove theory lemmas
	// :TODO: can't do that: kept lemmas might depend on them	
	//	(!clause->learnt() && clause->pushID() < 0)
	//	||
	// remove clauses added after the last push
	clause->pushID() > clauseID) {
      int id = clause->id();
      //      cout << "derivation pop now: " << id << endl;
      d_inputClauses.erase(id);
      d_inferences.erase(id);

      if (clause->size() == 1) {
	int index = (*clause)[0].index();
	if (d_unitClauses.contains(index) && d_unitClauses[index] == clause) {
	  d_unitClauses.erase(index);
	  FatalAssert(!d_unitClauses.contains(index), "AHA");
	}
      }

      i = d_clauses.erase(i);
    }
    else {
      ++i;
    }
  }

  // undo conflicting clause
  if (d_emptyClause != NULL && d_emptyClause->pushID() > clauseID)
    d_emptyClause = NULL;

  // delete popped and removed clauses
  std::deque<Clause*>::iterator j = d_removedClauses.begin();
  while (j != d_removedClauses.end()) {
    if ((*j)->pushID() > clauseID) {
      xfree(*j);
      j = d_removedClauses.erase(j);
    } else {
      ++j;
    }
  }
}
