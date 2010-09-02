/*****************************************************************************/
/*!
 * \file quant_proof_rules.h
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
#ifndef _cvc3__quant_proof_rules_h_
#define _cvc3__quant_proof_rules_h_

#include <vector>

namespace CVC3 {

  class Expr;
  class Theorem;

  class QuantProofRules {
  public:
    //! Destructor
    virtual ~QuantProofRules() { }
    
    virtual Theorem addNewConst(const Expr& e) =0;

    virtual Theorem newRWThm(const Expr& e, const Expr& newE) = 0 ;

    virtual Theorem normalizeQuant(const Expr& e) =0;
    
    //! ==> NOT EXISTS (vars): e  IFF FORALL (vars) NOT e
    virtual Theorem rewriteNotExists(const Expr& e) = 0;
    
    //! ==> NOT FORALL (vars): e  IFF EXISTS (vars) NOT e 
    virtual Theorem rewriteNotForall(const Expr& e) = 0;

    //! Instantiate a  universally quantified formula
    /*! From T|-FORALL(var): e generate T|-e' where e' is obtained
     * from e by instantiating bound variables with terms in
     * vector<Expr>& terms.  The vector of terms should be the same
     * size as the vector of bound variables in e. Also elements in
     * each position i need to have matching types.
     * \param t1 is the quantifier (a Theorem)
     * \param terms are the terms to instantiate.
     * \param quantLevel is the quantification level for the theorem.
     */
    virtual Theorem universalInst(const Theorem& t1,  const std::vector<Expr>& terms, int quantLevel, Expr gterm ) = 0 ;

    virtual Theorem universalInst(const Theorem& t1,
				  const std::vector<Expr>& terms, int quantLevel) = 0;

    virtual Theorem universalInst(const Theorem& t1,
				  const std::vector<Expr>& terms) = 0;


    virtual Theorem partialUniversalInst(const Theorem& t1,
					 const std::vector<Expr>& terms,
					 int quantLevel) = 0;

    /*! @brief From T|- QUANTIFIER (vars): e we get T|-QUANTIFIER(vars') e
     * where vars' is obtained from vars by removing all bound variables
     *  not used in e. If vars' is empty the produced theorem is just T|-e
     */
    virtual Theorem boundVarElim(const Theorem& t1) = 0;

    virtual Theorem packVar(const Theorem& t1) = 0;

    virtual Theorem pullVarOut(const Theorem& t1) = 0;

    virtual Theorem adjustVarUniv(const Theorem& t1, 
				  const std::vector<Expr>& newBvs) = 0;

  }; 
}
#endif
