/*****************************************************************************/
/*!
 *\file datatype_theorem_producer.h
 *\brief TRUSTED implementation of recursive datatype proof rules
 *
 * Author: Clark Barrett
 *
 * Created: Mon Jan 10 15:42:22 2005
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
 * CLASS: DatatypeTheoremProducer
 * 
 */
/*****************************************************************************/
#ifndef _cvc3__theory_datatype__datatype_theorem_producer_h_
#define _cvc3__theory_datatype__datatype_theorem_producer_h_

#include "datatype_proof_rules.h"
#include "theorem_producer.h"
#include "theory_datatype.h"
#include "theory_core.h"

namespace CVC3 {
  
class DatatypeTheoremProducer: public DatatypeProofRules, public TheoremProducer {
  TheoryDatatype* d_theoryDatatype;
private:
public:
  //! Constructor
  DatatypeTheoremProducer(TheoryDatatype* theoryDatatype) :
    TheoremProducer(theoryDatatype->theoryCore()->getTM()),
    d_theoryDatatype(theoryDatatype) { }

  Theorem dummyTheorem(const CDList<Theorem>& facts, const Expr& e);
  Theorem rewriteSelCons(const CDList<Theorem>& facts, const Expr& e);
  Theorem rewriteTestCons(const Expr& e);
  Theorem decompose(const Theorem& e);
  Theorem noCycle(const Expr& e);

  }; // end of class DatatypeTheoremProducer
} // end of namespace CVC3

#endif

