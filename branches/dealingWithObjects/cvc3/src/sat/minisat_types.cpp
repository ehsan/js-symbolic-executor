/*****************************************************************************/
/*!
 *\file minisat_types.cpp
 *\brief MiniSat internal types
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



#include "minisat_types.h"

using namespace std;

namespace MiniSat {

  // static class members
  Clause* Clause::s_decision = NULL;
  Clause* Clause::s_theoryImplication = NULL;

  const int clause_mem_base =
    sizeof(unsigned int)
    + 2 * sizeof(int)
    + sizeof(float)
    + sizeof (CVC3::Theorem);

  void* malloc_clause(const vector<Lit>& ps) {
    return xmalloc<char>
      (clause_mem_base + sizeof(Lit) * (max(size_t(1), ps.size())));
  }

  Clause* Clause_new(const vector<Lit>& ps, CVC3::Theorem theorem, int id) {
    void* mem = malloc_clause(ps);
    return new (mem) Clause(false, ps, theorem, id, id);
  }

  Clause* Lemma_new(const vector<Lit>& ps, int id, int pushID) {
    void* mem = malloc_clause(ps);
    return new (mem) Clause(true, ps, CVC3::Theorem(), id, pushID);
  }

  Clause* Clause::Decision() {
    if (s_decision == NULL) {
      vector<Lit> lits;
      s_decision = Clause_new(lits, CVC3::Theorem(), -1);
    }
    
    return s_decision;
  }
  
  Clause* Clause::TheoryImplication() {
    if (s_theoryImplication == NULL) {
      vector<Lit> lits;
      s_theoryImplication = Clause_new(lits, CVC3::Theorem(), -2);
    }
    
    return s_theoryImplication;
  }

  void Clause::toLit(vector<Lit>& literals) const {
    for (int i = 0; i < size(); ++i) {
      literals.push_back(d_data[i]);
    }
  }

}
