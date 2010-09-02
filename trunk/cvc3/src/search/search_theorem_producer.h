/*****************************************************************************/
/*!
 * \file search_theorem_producer.h
 * \brief Implementation API to proof rules for the simple search engine
 * 
 * Author: Sergey Berezin
 * 
 * Created: Mon Feb 24 14:48:03 2003
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

#ifndef _cvc3__search__search_theorem_producer_h_
#define _cvc3__search__search_theorem_producer_h_

#include "theorem_producer.h"
#include "search_rules.h"

namespace CVC3 {

class CommonProofRules;

  class SearchEngineTheoremProducer
    : public SearchEngineRules,
      public TheoremProducer {
  private:
    CommonProofRules* d_commonRules;

    void verifyConflict(const Theorem& thm, TheoremMap& m);
     
    void checkSoundNoSkolems(const Expr& e, ExprMap<bool>& visited, 
                             const ExprMap<bool>& skolems);
    void checkSoundNoSkolems(const Theorem& t, ExprMap<bool>& visited, 
                             const ExprMap<bool>& skolems);
  public:

    SearchEngineTheoremProducer(TheoremManager* tm);
    // Destructor
    virtual ~SearchEngineTheoremProducer() { }
    
    // Proof by contradiction: !A |- FALSE ==> |- A.  "!A" doesn't
    // have to be present in the assumptions.
    virtual Theorem proofByContradiction(const Expr& a,
					 const Theorem& pfFalse);
    
    // Similar rule, only negation introduction:
    // A |- FALSE ==> !A
    virtual Theorem negIntro(const Expr& not_a, const Theorem& pfFalse);
    
    // Case split: u1:A |- C, u2:!A |- C  ==>  |- C
    virtual Theorem caseSplit(const Expr& a,
			      const Theorem& a_proves_c,
			      const Theorem& not_a_proves_c);


   

    
    /*! Eliminate skolem axioms: 
     * Gamma, Delta |- false => Gamma|- false 
     * where Delta is a set of skolem axioms {|-Exists(x) phi (x) => phi(c)}
     * and gamma does not contain any of the skolem constants c.
     */
    virtual Theorem eliminateSkolemAxioms(const Theorem& tFalse, 
					  const std::vector<Theorem>& delta);
 

    // Conflict clause rule: 
    // Gamma, A_1,...,A_n |- B ==> Gamma |- (OR B !A_1 ... !A_n)
    // The assumptions A_i are given by the vector 'lits'.
    // If B==FALSE, it is omitted from the result.
    
    // NOTE: here "!A_i" means an inverse of A_i, not just a negation.
    // That is, if A_i is NOT C, then !A_i is C.

    // NOTE: Theorems with same expressions must 
    // be eliminated before passing as lits.
    virtual Theorem conflictClause(const Theorem& thm,
				   const std::vector<Theorem>& lits, 
				   const std::vector<Theorem>& gamma);

    // "Cut" rule: { G_i |- A_i };  G', { A_i } |- B ==> union(G_i)+G' |- B.
    virtual Theorem cutRule(const std::vector<Theorem>& thmsA,
			    const Theorem& as_prove_b);

    // "Unit propagation" rule:
    // G_j |- !l_j, j in [1..n]-{i}
    // G |- (OR l_1 ... l_i ... l_n) ==> G, G_j |- l_i
    virtual Theorem unitProp(const std::vector<Theorem>& thms,
			     const Theorem& clause, unsigned i);

    // "Conflict" rule (all literals in a clause become FALSE)
    // { G_j |- !l_j, j in [1..n] } , G |- (OR l_1 ... l_n) ==> FALSE
    virtual Theorem conflictRule(const std::vector<Theorem>& thms,
				 const Theorem& clause);
 
    // Unit propagation for AND
    virtual Theorem propAndrAF(const Theorem& andr_th,
			       bool left,
			       const Theorem& b_th);

    virtual Theorem propAndrAT(const Theorem& andr_th,
			       const Theorem& l_th,
			       const Theorem& r_th);
    

    virtual void propAndrLRT(const Theorem& andr_th,
			     const Theorem& a_th,
			     Theorem* l_th,
			     Theorem* r_th);

    virtual Theorem propAndrLF(const Theorem& andr_th,
			       const Theorem& a_th,
			       const Theorem& r_th);

    virtual Theorem propAndrRF(const Theorem& andr_th,
			       const Theorem& a_th,
			       const Theorem& l_th);

    // Conflicts for AND
    virtual Theorem confAndrAT(const Theorem& andr_th,
			       const Theorem& a_th,
			       bool left,
			       const Theorem& b_th);

    virtual Theorem confAndrAF(const Theorem& andr_th,
			       const Theorem& a_th,
			       const Theorem& l_th,
			       const Theorem& r_th);

    // Unit propagation for IFF
    virtual Theorem propIffr(const Theorem& iffr_th,
			     int p,
			     const Theorem& a_th,
			     const Theorem& b_th);

    // Conflicts for IFF
    virtual Theorem confIffr(const Theorem& iffr_th,
			     const Theorem& i_th,
			     const Theorem& l_th,
			     const Theorem& r_th);

    // Unit propagation for ITE
    virtual Theorem propIterIte(const Theorem& iter_th,
				bool left,
				const Theorem& if_th,
				const Theorem& then_th);

    virtual void propIterIfThen(const Theorem& iter_th,
				bool left,
				const Theorem& ite_th,
				const Theorem& then_th,
				Theorem* if_th,
				Theorem* else_th);

    virtual Theorem propIterThen(const Theorem& iter_th,
				 const Theorem& ite_th,
				 const Theorem& if_th);

    // Conflicts for ITE
    virtual Theorem confIterThenElse(const Theorem& iter_th,
				     const Theorem& ite_th,
				     const Theorem& then_th,
				     const Theorem& else_th);

    virtual Theorem confIterIfThen(const Theorem& iter_th,
				   bool left,
				   const Theorem& ite_th,
				   const Theorem& if_th,
				   const Theorem& then_th);

    // CNF Rules
    Theorem andCNFRule(const Theorem& thm);
    Theorem orCNFRule(const Theorem& thm);
    Theorem impCNFRule(const Theorem& thm);
    Theorem iffCNFRule(const Theorem& thm);
    Theorem iteCNFRule(const Theorem& thm);
    Theorem iteToClauses(const Theorem& ite);
    Theorem iffToClauses(const Theorem& iff);

    //theorrm for minisat proofs, by yeting
    Theorem satProof(const Expr& queryExpr, const Proof& satProof);

    /////////////////////////////////////////////////////////////////////////
    //// helper functions for CNF (Conjunctive Normal Form) conversion
    /////////////////////////////////////////////////////////////////////////
    private:
    Theorem opCNFRule(const Theorem& thm, int kind,
		      const std::string& ruleName);
    
    Expr convertToCNF(const Expr& v, const Expr & phi);      

    //! checks if phi has v in local cache of opCNFRule, if so reuse v.
    /*! similarly for ( ! ... ! (phi)) */
    Expr findInLocalCache(const Expr& i, 
			  ExprMap<Expr>& localCache,
			  std::vector<Expr>& boundVars);

  }; // end of class SearchEngineRules
} // end of namespace CVC3
#endif
