/*****************************************************************************/
/*!
 *\file cnf_theorem_producer.h
 *\brief Implementation of CNF_Rules API
 *
 * Author: Clark Barrett
 *
 * Created: Thu Jan  5 05:33:42 2006
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

#ifndef _cvc3__sat__cnf_theorem_producer_h_
#define _cvc3__sat__cnf_theorem_producer_h_

#include "theorem_producer.h"
#include "cnf_rules.h"
#include "command_line_flags.h"

namespace CVC3 {

  class CNF_TheoremProducer
    : public CNF_Rules,
      public TheoremProducer {
    const CLFlags& d_flags;
    const bool& d_smartClauses;

  public:
    CNF_TheoremProducer(TheoremManager* tm, const CLFlags& flags)
      : TheoremProducer(tm), d_flags(flags),
        d_smartClauses(flags["smart-clauses"].getBool()) { }
    ~CNF_TheoremProducer() { }

    void getSmartClauses(const Theorem& thm, std::vector<Theorem>& clauses);

    void learnedClauses(const Theorem& thm, std::vector<Theorem>& clauses,
                        bool newLemma);
    Theorem CNFAddUnit(const Theorem& thm);
    Theorem CNFConvert(const Expr & e, const Theorem& thm);
    Theorem ifLiftRule(const Expr& e, int itePos);
    Theorem CNFtranslate(const Expr& before, 
			 const Expr& after, 
			 std::string reason, 
			 int pos,
			 const std::vector<Theorem>& thms) ;
    Theorem CNFITEtranslate(const Expr& before, 
			    const std::vector<Expr>& after,
			    const std::vector<Theorem>& thms,
			    int pos) ;
    
    
  }; // end of class CNF_TheoremProducer
} // end of namespace CVC3
#endif
