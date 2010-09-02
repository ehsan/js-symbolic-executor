/*****************************************************************************/
/*!
 *\file core_proof_rules.h
 *\brief Proof rules used by theory_core
 *
 * Author: Clark Barrett
 *
 * Created: Wed Jan 11 15:48:35 2006
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

#ifndef _cvc3__core_proof_rules_h_
#define _cvc3__core_proof_rules_h_

#include <vector>

namespace CVC3 {

  class Theorem;
  class Theorem3;
  class Expr;
  class Op;

  class CoreProofRules {
  public:
    //! Destructor
    virtual ~CoreProofRules() { }

    //! e: T ==> |- typePred_T(e)  [deriving the type predicate of e]
    virtual Theorem typePred(const Expr& e) = 0;

    ////////////////////////////////////////////////////////////////////////
    // Core rewrite rules
    ////////////////////////////////////////////////////////////////////////

    //! Replace LETDECL with its definition
    /*! Used only in TheoryCore */ 
    virtual Theorem rewriteLetDecl(const Expr& e) = 0;
    //! ==> NOT (AND e1 ... en) IFF (OR !e1 ... !en), takes (AND ...)
    virtual Theorem rewriteNotAnd(const Expr& e) = 0;
    //! ==> NOT (OR e1 ... en) IFF (AND !e1 ... !en), takes (OR ...)
    virtual Theorem rewriteNotOr(const Expr& e) = 0;
    //! ==> NOT IFF(e1,e2) IFF IFF(e1,NOT e2)
    virtual Theorem rewriteNotIff(const Expr& e) = 0;
    //! ==> NOT ITE(a,b,c) IFF ITE(a,NOT b,NOT c)
    virtual Theorem rewriteNotIte(const Expr& e) = 0;
    //! a |- b == d ==> ITE(a, b, c) == ITE(a, d, c)
    virtual Theorem rewriteIteThen(const Expr& e, const Theorem& thenThm) = 0;
    //! !a |- c == d ==> ITE(a, b, c) == ITE(a, b, d)
    virtual Theorem rewriteIteElse(const Expr& e, const Theorem& elseThm) = 0;
    //! ==> ITE(c, e1, e2) <=> (c => e1) AND (!c => e2)
    virtual Theorem rewriteIteBool(const Expr& c,
				   const Expr& e1, const Expr& e2) = 0;

    //! |= (A & B1) | (A & B2) | ... | (A & bn) <=> A & (B1 | B2 | ...| Bn)
    virtual Theorem orDistributivityRule(const Expr& e) = 0;
    //! |= (A | B1) & (A | B2) & ... & (A | bn) <=> A | (B1 & B2 & ...& Bn)
    virtual Theorem andDistributivityRule(const Expr& e) = 0;


    //! ==> IMPLIES(e1,e2) IFF OR(!e1, e2)
    virtual Theorem rewriteImplies(const Expr& e) = 0;

    //! ==> DISTINCT(e1,...,en) IFF AND 1 <= i < j <= n (e[i] /= e[j])
    virtual Theorem rewriteDistinct(const Expr& e) = 0;

    //! ==> NOT(e) == ITE(e, FALSE, TRUE)
    virtual Theorem NotToIte(const Expr& not_e) = 0;
    //! ==> Or(e) == ITE(e[1], TRUE, e[0])
    virtual Theorem OrToIte(const Expr& e) = 0;
    //! ==> And(e) == ITE(e[1], e[0], FALSE)
    virtual Theorem AndToIte(const Expr& e) = 0;
    //! ==> IFF(a,b) == ITE(a, b, !b)
    virtual Theorem IffToIte(const Expr& e) = 0;
    //! ==> IMPLIES(a,b) == ITE(a, b, TRUE)
    virtual Theorem ImpToIte(const Expr& e) = 0;

    //! ==> ITE(e, FALSE, TRUE) IFF NOT(e)
    virtual Theorem rewriteIteToNot(const Expr& e) = 0;
    //! ==> ITE(a, TRUE, b) IFF OR(a, b)
    virtual Theorem rewriteIteToOr(const Expr& e) = 0;
    //! ==> ITE(a, b, FALSE) IFF AND(a, b)
    virtual Theorem rewriteIteToAnd(const Expr& e) = 0;
    //! ==> ITE(a, b, !b) IFF IFF(a, b)
    virtual Theorem rewriteIteToIff(const Expr& e) = 0;
    //! ==> ITE(a, b, TRUE) IFF IMPLIES(a, b)
    virtual Theorem rewriteIteToImp(const Expr& e) = 0;
    //! ==> ITE(a, b(a), c(a)) IFF ITE(a, b(TRUE), c(FALSE))
    virtual Theorem rewriteIteCond(const Expr& e) = 0;

    //! |- op(ITE(cond,a,b)) =/<=> ITE(cond,op(a),op(b))
    virtual Theorem ifLiftUnaryRule(const Expr& e) = 0;
    //! ((a|b)<=>(a|c))<=>(a|(b<=>c)); takes ((a|b)<=>(a|c)) as 'iff'
    virtual Theorem iffOrDistrib(const Expr& iff) = 0;
    //! ((a&b)<=>(a&c))<=>(!a|(b<=>c)); takes ((a&b)<=>(a&c)) as 'iff'
    virtual Theorem iffAndDistrib(const Expr& iff) = 0;

    // Advanced Boolean transformations

    //! (a & b) <=> a & b[a/true]; takes the index of a
    /*! and rewrites all the other conjuncts. */
    virtual Theorem rewriteAndSubterms(const Expr& e, int idx) = 0;
    //! (a | b) <=> a | b[a/false]; takes the index of a
    /*! and rewrites all the other disjuncts. */
    virtual Theorem rewriteOrSubterms(const Expr& e, int idx) = 0;

    //! Temporary cheat for building theorems
    virtual Theorem dummyTheorem(const Expr& e) = 0;

  }; // end of class CoreProofRules

} // end of namespace CVC3

#endif
