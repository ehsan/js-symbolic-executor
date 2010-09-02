/*****************************************************************************/
/*!
 * \file common_theorem_producer.h
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
// CLASS: CommonTheoremProducer
//
// AUTHOR: Sergey Berezin, 12/09/2002
//
// Description: Implementation of the proof rules for ground
// equational logic (reflexivity, symmetry, transitivity, and
// substitutivity).
//
///////////////////////////////////////////////////////////////////////////////

#ifndef _cvc3__common_theorem_producer_h_
#define _cvc3__common_theorem_producer_h_

#include "common_proof_rules.h"
#include "theorem_producer.h"
#include "theorem.h"
#include "cdmap.h"

namespace CVC3 {

  class CommonTheoremProducer: public CommonProofRules, public TheoremProducer {
  private:

    // TODO: do we need to record skolem axioms?  do we need context-dependence?

    // skolem axioms
    std::vector<Theorem> d_skolem_axioms;

    /* @brief Keep skolemization axioms so that they can be reused 
       without being recreated each time */
    CDMap<Expr, Theorem> d_skolemized_thms;

    //! Mapping of e to "|- e = v" for fresh Skolem vars v
    CDMap<Expr, Theorem> d_skolemVars;

    //! Helper function for liftOneITE
    void findITE(const Expr& e, Expr& condition, Expr& thenpart, Expr& elsepart);

  public:
    CommonTheoremProducer(TheoremManager* tm);
    virtual ~CommonTheoremProducer() { }

    Theorem3 queryTCC(const Theorem& phi, const Theorem& D_phi);
    Theorem3 implIntro3(const Theorem3& phi,
			const std::vector<Expr>& assump,
			const std::vector<Theorem>& tccs);
    Theorem assumpRule(const Expr& a, int scope = -1);
    Theorem reflexivityRule(const Expr& a);
    Theorem rewriteReflexivity(const Expr& t);
    Theorem symmetryRule(const Theorem& a1_eq_a2);
    Theorem rewriteUsingSymmetry(const Expr& a1_eq_a2);
    Theorem transitivityRule(const Theorem& a1_eq_a2,
                             const Theorem& a2_eq_a3);
    Theorem substitutivityRule(const Expr& e,
                               const Theorem& thm);
    Theorem substitutivityRule(const Expr& e,
                               const Theorem& thm1,
                               const Theorem& thm2);
    Theorem substitutivityRule(const Op& op,
                               const std::vector<Theorem>& thms);
    Theorem substitutivityRule(const Expr& e,
                               const std::vector<unsigned>& changed,
                               const std::vector<Theorem>& thms);
    Theorem substitutivityRule(const Expr& e,
                               const int changed,
                               const Theorem& thm);
    Theorem contradictionRule(const Theorem& e, const Theorem& not_e);
    Theorem excludedMiddle(const Expr& e);
    Theorem iffTrue(const Theorem& e);
    Theorem iffNotFalse(const Theorem& e);
    Theorem iffTrueElim(const Theorem& e);
    Theorem iffFalseElim(const Theorem& e);
    Theorem iffContrapositive(const Theorem& thm);
    Theorem notNotElim(const Theorem& e);
    Theorem iffMP(const Theorem& e1, const Theorem& e1_iff_e2);
    Theorem implMP(const Theorem& e1, const Theorem& e1_impl_e2);
    Theorem andElim(const Theorem& e, int i);
    Theorem andIntro(const Theorem& e1, const Theorem& e2);
    Theorem andIntro(const std::vector<Theorem>& es);
    Theorem implIntro(const Theorem& phi, const std::vector<Expr>& assump);
    Theorem implContrapositive(const Theorem& thm);
    Theorem rewriteIteTrue(const Expr& e);
    Theorem rewriteIteFalse(const Expr& e);
    Theorem rewriteIteSame(const Expr& e);
    Theorem notToIff(const Theorem& not_e);
    Theorem xorToIff(const Expr& e);
    Theorem rewriteIff(const Expr& e);
    Theorem rewriteAnd(const Expr& e);
    Theorem rewriteOr(const Expr& e);
    Theorem rewriteNotTrue(const Expr& e);
    Theorem rewriteNotFalse(const Expr& e);
    Theorem rewriteNotNot(const Expr& e);
    Theorem rewriteNotForall(const Expr& forallExpr);
    Theorem rewriteNotExists(const Expr& existsExpr);
    Expr skolemize(const Expr& e);
    Theorem skolemizeRewrite(const Expr& e);
    Theorem skolemizeRewriteVar(const Expr& e);
    Theorem varIntroRule(const Expr& e);
    Theorem skolemize(const Theorem& thm);
    Theorem varIntroSkolem(const Expr& e);
    Theorem trueTheorem();
    Theorem rewriteAnd(const Theorem& e);
    Theorem rewriteOr(const Theorem& e);
    Theorem ackermann(const Expr& e1, const Expr& e2);
    Theorem liftOneITE(const Expr& e);

    std::vector<Theorem>& getSkolemAxioms() { return d_skolem_axioms; }
    void clearSkolemAxioms() { d_skolem_axioms.clear(); }

  }; // end of class CommonTheoremProducer

} // end of namespace CVC3

#endif
