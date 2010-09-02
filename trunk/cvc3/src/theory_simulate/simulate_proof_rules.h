/*****************************************************************************/
/*!
 *\file simulate_proof_rules.h
 *\brief Abstract interface to the symbolic simulator proof rules 
 *
 * Author: Sergey Berezin
 *
 * Created: Tue Oct  7 10:44:42 2003
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

#ifndef _cvc3__theory_simulate__simulate_proof_rules_h_
#define _cvc3__theory_simulate__simulate_proof_rules_h_

namespace CVC3 {

  class Expr;
  class Theorem;

class SimulateProofRules {
public:
  //! Destructor
  virtual ~SimulateProofRules() { }

  //! SIMULATE(f, s_0, i_1, ..., i_k, N) <=> f(...f(f(s_0, i_1), i_2), ... i_k)
  virtual Theorem expandSimulate(const Expr& e) = 0;

}; // end of class SimulateProofRules

} // end of namespace CVC3

#endif
