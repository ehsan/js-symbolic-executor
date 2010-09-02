/*****************************************************************************/
/*!
 *\file uf_theorem_producer.h
 *\brief TRUSTED implementation of uninterpreted function/predicate proof rules
 *
 * Author: Clark Barrett
 *
 * Created: Tue Aug 31 23:14:54 2004
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
 * CLASS: UFTheoremProducer
 * 
 */
/*****************************************************************************/
#ifndef _cvc3__theory_uf__uf_theorem_producer_h_
#define _cvc3__theory_uf__uf_theorem_producer_h_

#include "uf_proof_rules.h"
#include "theorem_producer.h"

namespace CVC3 {

  class TheoryUF;

class UFTheoremProducer: public UFProofRules, public TheoremProducer {
    TheoryUF* d_theoryUF;
  private:
  public:
    //! Constructor
    UFTheoremProducer(TheoremManager* tm, TheoryUF* theoryUF) :
      TheoremProducer(tm), d_theoryUF(theoryUF) { }

    Theorem relToClosure(const Theorem& rel);
    Theorem relTrans(const Theorem& t1, const Theorem& t2);
    Theorem applyLambda(const Expr& e);
    Theorem rewriteOpDef(const Expr& e);
    
  }; // end of class UFTheoremProducer
} // end of namespace CVC3

#endif

