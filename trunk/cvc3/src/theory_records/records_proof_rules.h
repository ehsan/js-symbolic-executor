/*****************************************************************************/
/*!
 * \file records_proof_rules.h
 * 
 * Author: Daniel Wichs
 * 
 * Created: Jul 22 22:59:07 GMT 2003
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
#ifndef _cvc3__records_proof_rules_h_
#define _cvc3__records_proof_rules_h_

namespace CVC3 {

  class Expr;
  class Theorem;

  class RecordsProofRules {
  public:
    //!< Destructor
    virtual ~RecordsProofRules() { }
    
    //! ==> (REC_LITERAL (f1 v1) ... (fi vi) ...).fi = vi
    virtual Theorem rewriteLitSelect(const Expr &e)  = 0;
    
    //! ==> (REC_SELECT (REC_UPDATE e fi vi) fi) = vi
    virtual Theorem rewriteUpdateSelect(const Expr& e) = 0;
    
    
    //! ==> (REC_UPDATE (REC_LITERAL (f1 v1) ... (fi vi) ...) fi v') =(REC_LITERAL (f1 v1) ... (fi v') ...)
    virtual Theorem rewriteLitUpdate(const Expr& e) = 0;
    //! From T|- e = e' return T|- AND (e.i = e'.i) for all i
    virtual Theorem expandEq(const Theorem& eqThrm) = 0;
    //! From T|- NOT e=e' return T|- NOT AND (e.i = e'.i) for all i
    virtual Theorem expandNeq(const Theorem& neqThrm) = 0;
    //! Expand a record into a literal: |- e = (# f1:=e.f1, ..., fn:=e.fn #)
    virtual Theorem expandRecord(const Expr& e) = 0;
    //! Expand a tuple into a literal: |- e = (e.0, ..., e.n-1)
    virtual Theorem expandTuple(const Expr& e) = 0;
  };
}
#endif
