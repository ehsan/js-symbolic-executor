/*****************************************************************************/
/*!
 *\file datatype_proof_rules.h
 *\brief Abstract interface for recursive datatype proof rules
 *
 * Author: Clark Barrett
 *
 * Created: Mon Jan 10 15:40:24 2005
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
 * CLASS: DatatypeProofRules
 * 
 */
/*****************************************************************************/

#ifndef _cvc3__theory_datatype__datatype_proof_rules_h_
#define _cvc3__theory_datatype__datatype_proof_rules_h_

namespace CVC3 {

  class Expr;
  class Theorem;
  template<class T> class CDList;

  class DatatypeProofRules {
  public:
    // Destructor
    virtual ~DatatypeProofRules() { }

    ////////////////////////////////////////////////////////////////////
    // Proof rules
    ////////////////////////////////////////////////////////////////////

    virtual Theorem dummyTheorem(const CDList<Theorem>& facts,
                                 const Expr& e) = 0;
    virtual Theorem rewriteSelCons(const CDList<Theorem>& facts, const Expr& e) = 0;
    virtual Theorem rewriteTestCons(const Expr& e) = 0;
    virtual Theorem decompose(const Theorem& e) = 0;
    virtual Theorem noCycle(const Expr& e) = 0;

  }; // end of class DatatypeProofRules

} // end of namespace CVC3

#endif
