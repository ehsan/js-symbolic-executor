/*****************************************************************************/
/*!
 *\file simulate_theorem_producer.h
 *\brief Implementation of the symbolic simulator proof rules
 *
 * Author: Sergey Berezin
 *
 * Created: Tue Oct  7 10:49:14 2003
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

#ifndef _cvc3__theory_simulate__simulate_theorem_producer_h_
#define _cvc3__theory_simulate__simulate_theorem_producer_h_

#include "theorem_producer.h"
#include "simulate_proof_rules.h"

namespace CVC3 {

class SimulateTheoremProducer:
    public SimulateProofRules, public TheoremProducer {
public:
  //! Constructor
  SimulateTheoremProducer(TheoremManager* tm): TheoremProducer(tm) { }
  virtual ~SimulateTheoremProducer() { }

  virtual Theorem expandSimulate(const Expr& e);

  /*
private:
  Expr substFreeTerm(const Expr& e, const Expr& oldE, const Expr& newE);
  Expr recursiveSubst(const Expr& e, const Expr& oldE, const Expr& newE,
		      ExprMap<Expr>& visited);
  */

}; // end of class SimulateTheoremProducer

} // end of namespace CVC3 

#endif
