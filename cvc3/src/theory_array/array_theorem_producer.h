/*****************************************************************************/
/*!
 * \file array_theorem_producer.h
 * 
 * Author: Clark Barrett, 5/29/2003
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
 * Description: TRUSTED implementation of array proof rules.  DO
 * NOT use this file in any DP code, use the exported API in
 * array_proof_rules.h instead.
 * 
 */
/*****************************************************************************/
#ifndef _cvc3__theory_array__array_theorem_producer_h_
#define _cvc3__theory_array__array_theorem_producer_h_

#include "array_proof_rules.h"
#include "theorem_producer.h"

namespace CVC3 {
  
  class TheoryArray;

  class ArrayTheoremProducer: public ArrayProofRules, public TheoremProducer {
  private:
    TheoryArray* d_theoryArray;

  public:
    // Constructor
    ArrayTheoremProducer(TheoryArray* theoryArray);

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
    Theorem rewriteSameStore(const Expr& e, int n);

    // ==> write(store, index, value) = write(...) IFF
    //       store = write(write(...), index, read(store, index)) &
    //       value = read(write(...), index)
    Theorem rewriteWriteWrite(const Expr& e);

    // ==> read(write(store, index1, value), index2) =
    //   ite(index1 = index2, value, read(store, index2))
    Theorem rewriteReadWrite(const Expr& e);

    // e = read(write(store, index1, value), index2):
    // ==> ite(index1 = index2,
    //         read(write(store, index1, value), index2) = value,
    //         read(write(store, index1, value), index2) = read(store, index2))
    Theorem rewriteReadWrite2(const Expr& e);

    // value = read(store, index) ==>
    //   write(store, index, value) = store
    Theorem rewriteRedundantWrite1(const Theorem& v_eq_r,
				   const Expr& write);

    // ==>
    //   write(write(store, index, v1), index, v2) = write(store, index, v2)
    Theorem rewriteRedundantWrite2(const Expr& e);

    // ==>
    //   write(write(store, index1, v1), index2, v2) =
    //   write(write(store, index2, v2), index1, ite(index1 = index2, v2, v1))
    Theorem interchangeIndices(const Expr& e);
    // Beta reduction of array literal: |- (array x. f(x))[arg] = f(arg)
    Theorem readArrayLiteral(const Expr& e);

    Theorem liftReadIte(const Expr& e);

    // a /= b |- exists i. a[i] /= b[i]
    Theorem arrayNotEq(const Theorem& e);

    Theorem splitOnConstants(const Expr& a, const std::vector<Expr>& consts);

    Theorem propagateIndexDiseq(const Theorem& read1eqread2isFalse);

  }; // end of class ArrayTheoremProducer

} // end of namespace CVC3

#endif
