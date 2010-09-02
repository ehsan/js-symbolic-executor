/*****************************************************************************/
/*!
 * \file cnf_rules.h
 * \brief Abstract proof rules for CNF conversion
 * 
 * Author: Clark Barrett
 * 
 * Created: Thu Jan  5 05:24:45 2006
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

#ifndef _cvc3__sat__cnf_rules_h_
#define _cvc3__sat__cnf_rules_h_

namespace CVC3 {

  class Theorem;

/*! \defgroup CNF_Rules Proof Rules for the Search Engines
 * \ingroup CNF
 */
  //! API to the CNF proof rules
  /*! \ingroup CNF_Rules */
  class CNF_Rules {
    /*! \addtogroup CNF_Rules
     * @{ 
     */
  public:
    //! Destructor
    virtual ~CNF_Rules() { }    

    // A_1,...,A_n |- B ==> |- (OR !A_1 ... !A_n B)
    /*! @brief Learned clause rule: 
      \f[\frac{A_1,\ldots,A_n\vdash B}
              {\vdash\neg A_1\vee\cdots\vee \neg A_n\vee B}\f]
     *
     * \param thm is the theorem
     * \f$ A_1,\ldots,A_n\vdash B\f$
     * Each \f$A_i\f$ and \f$B\f$ should be literals
     * \f$B\f$ can also be \f$\mathrm{FALSE}\f$
     */
    virtual void learnedClauses(const Theorem& thm,
                                std::vector<Theorem>&,
                                bool newLemma) = 0;

    //! |- P(_, ITE(cond,a,b), _) <=> ITE(cond,Pred(_, a, _),Pred(_, b, _))
    virtual Theorem ifLiftRule(const Expr& e, int itePos) = 0;
    virtual Theorem CNFAddUnit(const Theorem& thm) = 0 ;
    virtual Theorem CNFConvert(const Expr& e, const Theorem& thm) = 0 ;
    virtual Theorem CNFtranslate(const Expr& before, 
				 const Expr& after, 
				 std::string reason, 
				 int pos,
				 const std::vector<Theorem>& thms) = 0;

    virtual Theorem CNFITEtranslate(const Expr& before, 
				    const std::vector<Expr>& after,
				    const std::vector<Theorem>& thms,
				    int pos) = 0;

    /*! @} */ // end of CNF_Rules
  }; // end of class CNF_Rules

} // end of namespace CVC3

#endif
