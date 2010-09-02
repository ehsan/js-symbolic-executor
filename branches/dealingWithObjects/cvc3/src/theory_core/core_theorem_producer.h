/*****************************************************************************/
/*!
 * \file core_theorem_producer.h
 * 
 * Author: Sergey Berezin
 * 
 * Created: Feb 05 03:40:36 GMT 2003
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
// CLASS: CoreTheoremProducer
//
// AUTHOR: Sergey Berezin, 12/09/2002
//
// Description: Implementation of the proof rules for ground
// equational logic (reflexivity, symmetry, transitivity, and
// substitutivity).
//
///////////////////////////////////////////////////////////////////////////////

#ifndef _cvc3__core_theorem_producer_h_
#define _cvc3__core_theorem_producer_h_

#include "core_proof_rules.h"
#include "theorem_producer.h"

namespace CVC3 {

  class TheoryCore;

  class CoreTheoremProducer: public CoreProofRules, public TheoremProducer {
  private:
    //! pointer to theory core
    TheoryCore* d_core;

  public:
    CoreTheoremProducer(TheoremManager* tm, TheoryCore* core)
      : TheoremProducer(tm), d_core(core) { }
    virtual ~CoreTheoremProducer() { }

    Theorem typePred(const Expr& e);
    Theorem rewriteLetDecl(const Expr& e);
    Theorem rewriteNotAnd(const Expr& e);
    Theorem rewriteNotOr(const Expr& e);
    Theorem rewriteNotIff(const Expr& e);
    Theorem rewriteNotIte(const Expr& e);
    Theorem rewriteIteThen(const Expr& e, const Theorem& thenThm);
    Theorem rewriteIteElse(const Expr& e, const Theorem& elseThm);
    Theorem rewriteIteBool(const Expr& c,
			   const Expr& e1, const Expr& e2);
    Theorem orDistributivityRule(const Expr& e);
    Theorem andDistributivityRule(const Expr& e);
    Theorem rewriteImplies(const Expr& e);
    Theorem rewriteDistinct(const Expr& e);
    Theorem NotToIte(const Expr& not_e);
    Theorem OrToIte(const Expr& e);
    Theorem AndToIte(const Expr& e);
    Theorem IffToIte(const Expr& e);
    Theorem ImpToIte(const Expr& e);
    Theorem rewriteIteToNot(const Expr& e);
    Theorem rewriteIteToOr(const Expr& e);
    Theorem rewriteIteToAnd(const Expr& e);
    Theorem rewriteIteToIff(const Expr& e);
    Theorem rewriteIteToImp(const Expr& e);
    Theorem rewriteIteCond(const Expr& e);
    Theorem ifLiftUnaryRule(const Expr& e);
    Theorem iffOrDistrib(const Expr& iff);
    Theorem iffAndDistrib(const Expr& iff);
    Theorem rewriteAndSubterms(const Expr& e, int idx);
    Theorem rewriteOrSubterms(const Expr& e, int idx);
    Theorem dummyTheorem(const Expr& e);

  }; // end of class CoreTheoremProducer

} // end of namespace CVC3

#endif
