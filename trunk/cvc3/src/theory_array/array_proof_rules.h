/*****************************************************************************/
/*!
 * \file array_proof_rules.h
 * 
 * Author: Clark Barrett 5/29/2003
 * 
 * Created: May 29 19:16:33 GMT 2003
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
 * CLASS: ArrayProofRules
 * 
 * 
 * Description: Array proof rules.
 */
/*****************************************************************************/

#ifndef _cvc3__theory_array__array_proof_rules_h_
#define _cvc3__theory_array__array_proof_rules_h_

#include <vector>

namespace CVC3 {

  class Theorem;
  class Expr;
  
  class ArrayProofRules {
  public:
    // Destructor
    virtual ~ArrayProofRules() { }

    ////////////////////////////////////////////////////////////////////
    // Proof rules
    ////////////////////////////////////////////////////////////////////

    // ==>
    // write(store, index_0, v_0, index_1, v_1, ..., index_n, v_n) = store IFF
    //
    // read(store, index_n) = v_n &
    // index_{n-1} != index_n -> read(store, index_{n-1}) = v_{n-1} &
    // (index_{n-2} != index_{n-1} & index_{n-2} != index_n) -> read(store, index_{n-2}) = v_{n-2} &
    // ...
    // (index_1 != index_2 & ... & index_1 != index_n) -> read(store, index_1) = v_1
    // (index_0 != index_1 & index_0 != index_2 & ... & index_0 != index_n) -> read(store, index_0) = v_0
    virtual Theorem rewriteSameStore(const Expr& e, int n) = 0;

    // ==> write(store, index, value) = write(...) IFF
    //       store = write(write(...), index, read(store, index)) &
    //       value = read(write(...), index)
    virtual Theorem rewriteWriteWrite(const Expr& e) = 0;

    // ==> read(write(store, index1, value), index2) =
    //   ite(index1 = index2, value, read(store, index2))
    virtual Theorem rewriteReadWrite(const Expr& e) = 0;

    // e = read(write(store, index1, value), index2):
    // ==> ite(index1 = index2,
    //         read(write(store, index1, value), index2) = value,
    //         read(write(store, index1, value), index2) = read(store, index2))
    virtual Theorem rewriteReadWrite2(const Expr& e) = 0;

    // value = read(store, index) ==>
    //   write(store, index, value) = store
    virtual Theorem rewriteRedundantWrite1(const Theorem& v_eq_r,
					   const Expr& write) = 0;

    // ==>
    //   write(write(store, index, v1), index, v2) = write(store, index, v2)
    virtual Theorem rewriteRedundantWrite2(const Expr& e) = 0;

    // ==>
    //   write(write(store, index1, v1), index2, v2) =
    //   write(write(store, index2, v2), index1, ite(index1 = index2, v2, v1))
    virtual Theorem interchangeIndices(const Expr& e) = 0;
    //! Beta reduction of array literal: |- (array x. f(x))[arg] = f(arg)
    virtual Theorem readArrayLiteral(const Expr& e) = 0;

    //! Lift ite over read
    virtual Theorem liftReadIte(const Expr& e) = 0;

    //! a /= b |- exists i. a[i] /= b[i]
    virtual Theorem arrayNotEq(const Theorem& e) = 0;

    virtual Theorem splitOnConstants(const Expr& a, const std::vector<Expr>& consts) = 0;

    virtual Theorem propagateIndexDiseq(const Theorem& read1eqread2isFalse) = 0;

  }; // end of class ArrayProofRules

} // end of namespace CVC3

#endif
