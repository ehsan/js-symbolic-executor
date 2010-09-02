/*****************************************************************************/
/*!
 *\file uf_proof_rules.h
 *\brief Abstract interface for uninterpreted function/predicate proof rules
 *
 * Author: Clark Barrett
 *
 * Created: Tue Aug 31 23:12:01 2004
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
 * CLASS: UFProofRules
 * 
 */
/*****************************************************************************/

#ifndef _cvc3__theory_uf__uf_proof_rules_h_
#define _cvc3__theory_uf__uf_proof_rules_h_

namespace CVC3 {

  class Expr;
  class Theorem;

  class UFProofRules {
  public:
    // Destructor
    virtual ~UFProofRules() { }

    ////////////////////////////////////////////////////////////////////
    // Proof rules
    ////////////////////////////////////////////////////////////////////

    virtual Theorem relToClosure(const Theorem& rel) = 0;
    virtual Theorem relTrans(const Theorem& t1, const Theorem& t2) = 0;

    //! Beta reduction: |- (lambda x. f(x))(arg) = f(arg)
    virtual Theorem applyLambda(const Expr& e) = 0;
    //! Replace LETDECL in the operator with the definition
    virtual Theorem rewriteOpDef(const Expr& e) = 0;

  }; // end of class UFProofRules

} // end of namespace CVC3

#endif
