/*****************************************************************************/
/*!
 *\file simulate_theorem_producer.cpp
 *\brief Trusted implementation of the proof rules for symbolic simulator
 *
 * Author: Sergey Berezin
 *
 * Created: Tue Oct  7 10:55:24 2003
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

// This code is trusted
#define _CVC3_TRUSTED_

#include <algorithm>

#include "simulate_theorem_producer.h"
#include "theory_simulate.h"
#include "theory_core.h"

using namespace std;
using namespace CVC3;

////////////////////////////////////////////////////////////////////
// TheoryArith: trusted method for creating ArithTheoremProducer
////////////////////////////////////////////////////////////////////

SimulateProofRules* TheorySimulate::createProofRules() {
  return new SimulateTheoremProducer(theoryCore()->getTM());
}
  
////////////////////////////////////////////////////////////////////
// Proof rules
////////////////////////////////////////////////////////////////////

Theorem SimulateTheoremProducer::expandSimulate(const Expr& e) {
  const int arity = e.arity();
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == SIMULATE, 
		"SimulateTheoremProducer::expandSimulate: "
		"expected SIMULATE expression: "
		+e.toString());
    CHECK_SOUND(arity >= 3 && e[arity - 1].isRational() && 
		e[arity - 1].getRational().isInteger(), 
		"SimulateTheoremProducer::expandSimulate: "
		"incorrect children in SIMULATE: " + e.toString());
  }

  int n = e[arity - 1].getRational().getInt();

  if(CHECK_PROOFS) {
    CHECK_SOUND(n >= 0, "SimulateTheoremProducer::expandSimulate: "
		"Requested negative number of iterations: "+int2string(n));
  }
 
  // Compute f(f(...f(f(s0, I1(0), I2(0), ...), I1(1), ...), ... ),
  //           I1(n-1), ...)
  //
  // We do this by accumulating the expression in 'res':
  // res_{i+1} = func(res_i, I1(i), ..., Ik(i))
  Expr res(e[1]);
  for(int i=0; i<n; ++i) {
    vector<Expr> args;
    args.push_back(res);
    Expr ri(d_em->newRatExpr(i));
    for(int j=2; j<arity-1; ++j)
      args.push_back(Expr(e[j].mkOp(), ri));
    res = Expr(e[0].mkOp(), args);
  }

  Proof pf;
  if(withProof())
    pf = newPf("expand_simulate", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}
