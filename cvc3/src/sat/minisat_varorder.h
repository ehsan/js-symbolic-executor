/*****************************************************************************/
/*!
 *\file minisat_varorder.h
 *\brief MiniSat decision heuristics
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

/**************************************************************************************[VarOrder.h]
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

#ifndef _cvc3__minisat__varorder_h_
#define _cvc3__minisat__varorder_h_

//=================================================================================================

#include "minisat_types.h"
#include "minisat_heap.h"
#include <iostream>
#include <vector>

// implements the decision heuristics by using a heap over variable ids (which are ints)

namespace MiniSat {

struct VarOrder_lt {
  const std::vector<double>&  activity;
  bool operator () (Var x, Var y) { return activity[x] > activity[y]; }
  VarOrder_lt(const std::vector<double>&  act) : activity(act) { }
};

class VarOrder {
  const std::vector<signed char>&    assigns;     // var->val. Pointer to external assignment table.
  const std::vector<double>&  activity;    // var->act. Pointer to external activity table.
  Heap<VarOrder_lt>   heap;
  double              random_seed; // For the internal random number generator

public:
  VarOrder(const std::vector<signed char>& ass, const std::vector<double>& act) :
    assigns(ass), activity(act), heap(VarOrder_lt(act)), random_seed(91648253)
  { }

    inline void newVar(void);
    inline void newVar(int varIndex);
    inline void update(Var x);                  // Called when variable increased in activity.
    inline void undo(Var x);                    // Called when variable is unassigned and may be selected again.
    inline Var  select(double random_freq =.0); // Selects a new, unassigned variable (or 'var_Undef' if none exists).
};


void VarOrder::newVar(void)
{
    heap.setBounds(assigns.size());
    heap.insert(assigns.size()-1);
}

void VarOrder::newVar(int varIndex)
{
    heap.setBounds(assigns.size());
    heap.insert(varIndex);
}

void VarOrder::update(Var x)
{
    if (heap.inHeap(x))
        heap.increase(x);
}

void VarOrder::undo(Var x)
{
    if (!heap.inHeap(x))
        heap.insert(x);
}


Var VarOrder::select(double random_var_freq)
{
  // Random decision:
  /*
    if (drand(random_seed) < random_var_freq && !heap.empty()){
    Var next = irand(random_seed,assigns.size());
    
    // find var which is not undefined or in the heap
    while (toLbool(assigns[next]) == l_Undef && !heap.inHeap(next)) {
    next = irand(random_seed,assigns.size());
    }
    if (toLbool(assigns[next]) == l_Undef) {
    return next;
    }

    // cvc does not necessarily use all variable ids without gaps,
    // so need to check if the picked id is a valid variable.
    //if (toLbool(assigns[next]) == l_Undef && heap.inHeap(next)) {
    //    return next;
    //}
    }
  */
  
  // Activity based decision:
  while (!heap.empty()){
    Var next = heap.getMin();
    if (toLbool(assigns[next]) == l_Undef)
      return next;
  }
  
  return var_Undef;
}

}

//=================================================================================================
#endif
