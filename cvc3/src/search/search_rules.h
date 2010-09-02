/*****************************************************************************/
/*!
 * \file search_rules.h
 * \brief Abstract proof rules interface to the simple search engine
 * 
 * Author: Sergey Berezin
 * 
 * Created: Mon Feb 24 14:19:48 2003
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

#ifndef _cvc3__search__search_rules_h_
#define _cvc3__search__search_rules_h_

namespace CVC3 {

  class Theorem;
  class Expr;

/*! \defgroup SE_Rules Proof Rules for the Search Engines
 * \ingroup SE
 */
  //! API to the proof rules for the Search Engines
  /*! \ingroup SE_Rules */
  class SearchEngineRules {
    /*! \addtogroup SE_Rules
     * @{ 
     */
  public:
    //! Destructor
    virtual ~SearchEngineRules() { }    

    /*! Eliminate skolem axioms: 
     * Gamma, Delta |- false => Gamma|- false 
     * where Delta is a set of skolem axioms {|-Exists(x) phi (x) => phi(c)}
     * and gamma does not contain any of the skolem constants c.
     */
    virtual Theorem eliminateSkolemAxioms(const Theorem& tFalse, 
				       const std::vector<Theorem>& delta) = 0;

    // !A |- FALSE ==> |- A
    /*! @brief Proof by contradiction: 
      \f[\frac{\Gamma, \neg A \vdash\mathrm{FALSE}}{\Gamma \vdash A}\f]
    */
    /*! \f$\neg A\f$ does not have to be present in the assumptions.
     * \param a is the assumption \e A
     *
     * \param pfFalse is the theorem \f$\Gamma, \neg A \vdash\mathrm{FALSE}\f$
     */
    virtual Theorem proofByContradiction(const Expr& a,
					 const Theorem& pfFalse) = 0;

    // A |- FALSE ==> !A
    /*! @brief Negation introduction:
      \f[\frac{\Gamma, A \vdash\mathrm{FALSE}}{\Gamma\vdash\neg A}\f]
     */
    /*!
     * \param not_a is the formula \f$\neg A\f$.  We pass the negation
     * \f$\neg A\f$, and not just \e A, for efficiency: building
     * \f$\neg A\f$ is more expensive (due to uniquifying pointers in
     * Expr package) than extracting \e A from \f$\neg A\f$.
     *
     * \param pfFalse is the theorem \f$\Gamma, A \vdash\mathrm{FALSE}\f$
     */
    virtual Theorem negIntro(const Expr& not_a, const Theorem& pfFalse) = 0;
    
    // u1:A |- C, u2:!A |- C  ==>  |- C
    /*! @brief Case split: 
      \f[\frac{\Gamma_1, A\vdash C \quad \Gamma_2, \neg A\vdash C}
              {\Gamma_1\cup\Gamma_2\vdash C}\f]
     */
    /*!
     * \param a is the assumption A to split on
     *
     * \param a_proves_c is the theorem \f$\Gamma_1, A\vdash C\f$
     *
     * \param not_a_proves_c is the theorem \f$\Gamma_2, \neg A\vdash C\f$
     */
    virtual Theorem caseSplit(const Expr& a,
			      const Theorem& a_proves_c,
			      const Theorem& not_a_proves_c) = 0;

    // Gamma, A_1,...,A_n |- FALSE ==> Gamma |- (OR !A_1 ... !A_n)
    /*! @brief Conflict clause rule: 
      \f[\frac{\Gamma,A_1,\ldots,A_n\vdash\mathrm{FALSE}}
              {\Gamma\vdash\neg A_1\vee\cdots\vee \neg A_n}\f]
     */
    /*!
     * \param thm is the theorem
     * \f$\Gamma,A_1,\ldots,A_n\vdash\mathrm{FALSE}\f$
     *
     * \param lits is the vector of literals <em>A<sub>i</sub></em>.
     * They must be present in the set of assumptions of \e thm.
     *
     * \param gamma FIXME: document this!!
     */
    virtual Theorem conflictClause(const Theorem& thm,
				   const std::vector<Theorem>& lits,
				   const std::vector<Theorem>& gamma) = 0;

    
    // "Cut" rule: { G_i |- A_i };  G', { A_i } |- B ==> union(G_i)+G' |- B.
    /*! @brief Cut rule:
      \f[\frac{\Gamma_1\vdash A_1\quad\cdots\quad\Gamma_n\vdash A_n
                \quad \Gamma', A_1,\ldots,A_n\vdash B}
              {\bigcup_{i=1}^n\Gamma_i\cup\Gamma'\vdash B}\f]
     */
    /*!
     * \param thmsA is a vector of theorems \f$\Gamma_i\vdash A_i\f$
     *
     * \param as_prove_b is the theorem 
     *    \f$\Gamma', A_1,\ldots,A_n\vdash B\f$
     * (the name means "A's prove B")
     */
    virtual Theorem cutRule(const std::vector<Theorem>& thmsA,
			    const Theorem& as_prove_b) = 0;

    // { G_j |- !A_j, j in [1..n]-{i} }
    // G |- (OR A_1 ... A_i ... A_n) ==> G, G_j |- A_i
    /*! @brief  Unit propagation rule:
      \f[\frac{\Gamma_j\vdash\neg A_j\mbox{ for }j\in[1\ldots n]-\{i\}
               \quad \Gamma\vdash A_1\vee\cdots\vee A_n}
              {\bigcup_{j\in[1\ldots n]-\{i\}}\Gamma_j\cup\Gamma\vdash A_i}\f]
     */
    /*!
     * \param clause is the proof of the clause \f$ \Gamma\vdash
     * A_1\vee\cdots\vee A_n\f$
     *
     * \param i is the index (0..n-1) of the literal to be unit-propagated
     *
     * \param thms is the vector of theorems \f$\Gamma_j\vdash\neg
     * A_j\f$ for all literals except <em>A<sub>i</sub></em>
     */
    virtual Theorem unitProp(const std::vector<Theorem>& thms,
			     const Theorem& clause, unsigned i) = 0;
    
    // { G_j |- !A_j, j in [1..n] } , G |- (OR A_1 ... A_n) ==> FALSE
    /*! @brief "Conflict" rule (all literals in a clause become FALSE)
      \f[\frac{\Gamma_j\vdash\neg A_j\mbox{ for }j\in[1\ldots n]
               \quad \Gamma\vdash A_1\vee\cdots\vee A_n}
              {\bigcup_{j\in[1\ldots n]}\Gamma_j\cup\Gamma
               \vdash\mathrm{FALSE}}\f]
     */
    /*!
     * \param clause is the proof of the clause \f$ \Gamma\vdash
     * A_1\vee\cdots\vee A_n\f$
     *
     * \param thms is the vector of theorems \f$\Gamma_j\vdash\neg
     * A_j\f$
     */
    virtual Theorem conflictRule(const std::vector<Theorem>& thms,
				 const Theorem& clause) = 0;


    // Unit propagation for AND
    virtual Theorem propAndrAF(const Theorem& andr_th,
			       bool left,
			       const Theorem& b_th) = 0;

    virtual Theorem propAndrAT(const Theorem& andr_th,
			       const Theorem& l_th,
			       const Theorem& r_th) = 0;
    

    virtual void propAndrLRT(const Theorem& andr_th,
			     const Theorem& a_th,
			     Theorem* l_th,
			     Theorem* r_th) = 0;

    virtual Theorem propAndrLF(const Theorem& andr_th,
			       const Theorem& a_th,
			       const Theorem& r_th) = 0;

    virtual Theorem propAndrRF(const Theorem& andr_th,
			       const Theorem& a_th,
			       const Theorem& l_th) = 0;

    // Conflicts for AND
    virtual Theorem confAndrAT(const Theorem& andr_th,
			       const Theorem& a_th,
			       bool left,
			       const Theorem& b_th) = 0;

    virtual Theorem confAndrAF(const Theorem& andr_th,
			       const Theorem& a_th,
			       const Theorem& l_th,
			       const Theorem& r_th) = 0;

    // Unit propagation for IFF
    virtual Theorem propIffr(const Theorem& iffr_th,
			     int p,
			     const Theorem& a_th,
			     const Theorem& b_th) = 0;

    // Conflicts for IFF
    virtual Theorem confIffr(const Theorem& iffr_th,
			     const Theorem& i_th,
			     const Theorem& l_th,
			     const Theorem& r_th) = 0;

    // Unit propagation for ITE
    virtual Theorem propIterIte(const Theorem& iter_th,
				bool left,
				const Theorem& if_th,
				const Theorem& then_th) = 0;

    virtual void propIterIfThen(const Theorem& iter_th,
				bool left,
				const Theorem& ite_th,
				const Theorem& then_th,
				Theorem* if_th,
				Theorem* else_th) = 0;

    virtual Theorem propIterThen(const Theorem& iter_th,
				 const Theorem& ite_th,
				 const Theorem& if_th) = 0;

    // Conflict for ITE
    virtual Theorem confIterThenElse(const Theorem& iter_th,
				     const Theorem& ite_th,
				     const Theorem& then_th,
				     const Theorem& else_th) = 0;

    virtual Theorem confIterIfThen(const Theorem& iter_th,
				   bool left,
				   const Theorem& ite_th,
				   const Theorem& if_th,
				   const Theorem& then_th) = 0;

    // CNF Rules

    //! AND(x1,...,xn) <=> v  |-  CNF[AND(x1,...,xn) <=> v]
    virtual Theorem andCNFRule(const Theorem& thm) = 0;
    //! OR(x1,...,xn) <=> v  |-  CNF[OR(x1,...,xn) <=> v]
    virtual Theorem orCNFRule(const Theorem& thm) = 0;
    //! (x1 => x2) <=> v  |-  CNF[(x1 => x2) <=> v]
    virtual Theorem impCNFRule(const Theorem& thm) = 0;
    //! (x1 <=> x2) <=> v  |-  CNF[(x1 <=> x2) <=> v]
    virtual Theorem iffCNFRule(const Theorem& thm) = 0;
    //! ITE(c, x1, x2) <=> v  |-  CNF[ITE(c, x1, x2) <=> v]
    virtual Theorem iteCNFRule(const Theorem& thm) = 0;
    //! ITE(c, f1, f2) |- (NOT c OR f1) AND (c OR f2)
    virtual Theorem iteToClauses(const Theorem& ite) = 0;
    //! e1 <=> e2 |- (NOT e1 OR e2) AND (e1 OR NOT e2)
    virtual Theorem iffToClauses(const Theorem& iff) = 0;

    virtual Theorem satProof(const Expr& queryExpr, const Proof& satProof) = 0;

    /*! @} */ // end of SE_Rules
  }; // end of class SearchEngineRules

} // end of namespace CVC3

#endif
