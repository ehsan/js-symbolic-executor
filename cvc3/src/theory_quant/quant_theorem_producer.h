/*****************************************************************************/
/*!
 * \file quant_theorem_producer.h
 * 
 * Author: Daniel Wichs
 * 
 * Created: Jul 07 22:22:38 GMT 2003
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
#ifndef _cvc3__quant_theorem_producer_h_
#define _cvc3__quant_theorem_producer_h_

#include "quant_proof_rules.h"
#include "theorem_producer.h"
#include "theory_quant.h"

namespace CVC3 {
  
  class QuantTheoremProducer: public QuantProofRules, public TheoremProducer {
    TheoryQuant* d_theoryQuant;
    std::map<Expr,int> d_typeFound;
  private:

    //! find all bound variables in e and maps them to true in boundVars
    void recFindBoundVars(const Expr& e, 
			  ExprMap<bool> & boundVars, ExprMap<bool> &visited);
  public:
    //! Constructor
    QuantTheoremProducer(TheoremManager* tm, TheoryQuant* theoryQuant):
      TheoremProducer(tm), d_theoryQuant(theoryQuant) { d_typeFound.clear(); }

    virtual Theorem addNewConst(const Expr& e) ;
    virtual Theorem newRWThm(const Expr& e, const Expr& newE) ;
    virtual Theorem normalizeQuant(const Expr& e) ;

    //! ==> NOT EXISTS (vars): e  IFF FORALL (vars) NOT e
    virtual Theorem rewriteNotExists(const Expr& e);
    //! ==> NOT FORALL (vars): e  IFF EXISTS (vars) NOT e 
    virtual Theorem rewriteNotForall(const Expr& e);
    //! Instantiate a  universally quantified formula
    /*! From T|-FORALL(var): e generate T|-e' where e' is obtained
     * from e by instantiating bound variables with terms in
     * vector<Expr>& terms.  The vector of terms should be the same
     * size as the vector of bound variables in e. Also elements in
     * each position i need to have matching types.
     * \param t1 is the quantifier (a Theorem)
     * \param terms are the terms to instantiate.
     * \param quantLevel the quantification level for the theorem.

     */

    virtual Theorem universalInst(const Theorem& t1, 
				  const std::vector<Expr>& terms, int quantLevel ,
				  Expr gterm);

    virtual Theorem universalInst(const Theorem& t1,
				  const std::vector<Expr>& terms, int quantLevel);

    virtual Theorem universalInst(const Theorem& t1,
				  const std::vector<Expr>& terms);


    virtual Theorem partialUniversalInst(const Theorem& t1,
					 const std::vector<Expr>& terms,
					 int quantLevel) ;

    
    /*! @brief From T|- QUANTIFIER (vars): e we get T|-QUANTIFIER(vars') e
     * where vars' is obtained from vars by removing all bound variables
     *  not used in e. If vars' is empty the produced theorem is just T|-e
     */
    virtual Theorem boundVarElim(const Theorem& t1);

    virtual Theorem adjustVarUniv(const Theorem& t1, 
				  const std::vector<Expr>& newBvs);

    virtual Theorem packVar(const Theorem& t1);

    virtual Theorem pullVarOut(const Theorem& t1);


  }; 

} 

#endif
