/*****************************************************************************/
/*!
 * \file arith_theorem_producer.cpp
 *
 * Author: Vijay Ganesh, Sergey Berezin
 *
 * Created: Dec 13 02:09:04 GMT 2002
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
// CLASS: ArithProofRules
//
// AUTHOR: Sergey Berezin, 12/11/2002
// AUTHOR: Vijay Ganesh,   05/30/2003
//
// Description: TRUSTED implementation of arithmetic proof rules.
//
///////////////////////////////////////////////////////////////////////////////

// This code is trusted
#define _CVC3_TRUSTED_

#include "arith_theorem_producer_old.h"
#include "theory_core.h"
#include "theory_arith_old.h"
#include <algorithm>

using namespace std;
using namespace CVC3;

////////////////////////////////////////////////////////////////////
// TheoryArith: trusted method for creating ArithTheoremProducerOld
////////////////////////////////////////////////////////////////////

ArithProofRules* TheoryArithOld::createProofRulesOld() {
  return new ArithTheoremProducerOld(theoryCore()->getTM(), this);
}

////////////////////////////////////////////////////////////////////
// Canonization rules
////////////////////////////////////////////////////////////////////


#define CLASS_NAME "ArithTheoremProducerOld"


// Rule for variables: e == 1 * e
Theorem ArithTheoremProducerOld::varToMult(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("var_to_mult", e);
  return newRWTheorem(e, (rat(1) * e), Assumptions::emptyAssump(), pf);
}


// Rule for unary minus: -e == (-1) * e
Theorem ArithTheoremProducerOld::uMinusToMult(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("uminus_to_mult", e);
  return newRWTheorem((-e), (rat(-1) * e), Assumptions::emptyAssump(), pf);
}


// ==> x - y = x + (-1) * y
Theorem ArithTheoremProducerOld::minusToPlus(const Expr& x, const Expr& y)
{
  Proof pf;
  if(withProof()) pf = newPf("minus_to_plus", x, y);
  return newRWTheorem((x-y), (x + (rat(-1) * y)), Assumptions::emptyAssump(), pf);
}


// Rule for unary minus: -e == e/(-1)
// This is to reduce the number of almost identical rules for uminus and div
Theorem ArithTheoremProducerOld::canonUMinusToDivide(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("canon_uminus", e);
  return newRWTheorem((-e), (e / rat(-1)), Assumptions::emptyAssump(), pf);
}

// Rules for division by constant

// (c)/(d) ==> (c/d).  When d==0, c/0 = 0 (our total extension).
Theorem ArithTheoremProducerOld::canonDivideConst(const Expr& c,
                                               const Expr& d) {
  // Make sure c and d are a const
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(c),
                CLASS_NAME "::canonDivideConst:\n c not a constant: "
                + c.toString());
    CHECK_SOUND(isRational(d),
                CLASS_NAME "::canonDivideConst:\n d not a constant: "
                + d.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("canon_divide_const", c, d, d_hole);
  const Rational& dr = d.getRational();
  return newRWTheorem((c/d), (rat(dr==0? 0 : (c.getRational()/dr))), Assumptions::emptyAssump(), pf);
}

// (c * x)/d ==> (c/d) * x, takes (c*x) and d
Theorem ArithTheoremProducerOld::canonDivideMult(const Expr& cx,
                                              const Expr& d) {
  // Check the format of c*x
  if(CHECK_PROOFS) {
    CHECK_SOUND(isMult(cx) && isRational(cx[0]),
                CLASS_NAME "::canonDivideMult:\n  "
                "Not a (c * x) expression: "
                + cx.toString());
    CHECK_SOUND(isRational(d),
                CLASS_NAME "::canonDivideMult:\n  "
                "d is not a constant: " + d.toString());
  }
  const Rational& dr = d.getRational();
  Rational cdr(dr==0? 0 : (cx[0].getRational()/dr));
  Expr cd(rat(cdr));
  Proof pf;
  if(withProof())
    pf = newPf("canon_divide_mult", cx[0], cx[1], d);
  // (c/d) may be == 1, so we also need to canonize 1*x to x
  if(cdr == 1)
    return newRWTheorem((cx/d), (cx[1]), Assumptions::emptyAssump(), pf);
  else if(cdr == 0) // c/0 == 0 case
    return newRWTheorem((cx/d), cd, Assumptions::emptyAssump(), pf);
  else
    return newRWTheorem((cx/d), (cd*cx[1]), Assumptions::emptyAssump(), pf);
}

// (+ t1 ... tn)/d ==> (+ (t1/d) ... (tn/d))
Theorem ArithTheoremProducerOld::canonDividePlus(const Expr& sum, const Expr& d) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(isPlus(sum) && sum.arity() >= 2 && isRational(sum[0]),
                CLASS_NAME "::canonUMinusPlus:\n  "
                "Expr is not a canonical sum: "
                + sum.toString());
    CHECK_SOUND(isRational(d),
                CLASS_NAME "::canonUMinusPlus:\n  "
                "d is not a const: " + d.toString());
  }
  // First, propagate '/d' down to the args
  Proof pf;
  if(withProof())
    pf = newPf("canon_divide_plus", rat(sum.arity()),
               sum.begin(), sum.end());
  vector<Expr> newKids;
  for(Expr::iterator i=sum.begin(), iend=sum.end(); i!=iend; ++i)
    newKids.push_back((*i)/d);
  // (+ t1 ... tn)/d == (+ (t1/d) ... (tn/d))
  return newRWTheorem((sum/d), (plusExpr(newKids)), Assumptions::emptyAssump(), pf);
}

// x/(d) ==> (1/d) * x, unless d == 1
Theorem ArithTheoremProducerOld::canonDivideVar(const Expr& e, const Expr& d) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(d),
                CLASS_NAME "::canonDivideVar:\n  "
                "d is not a const: " + d.toString());
  }
  Proof pf;

  if(withProof())
    pf = newPf("canon_divide_var", e);

  const Rational& dr = d.getRational();
  if(dr == 1)
    return newRWTheorem(e/d, e, Assumptions::emptyAssump(), pf);
  if(dr == 0) // e/0 == 0 (total extension of division)
    return newRWTheorem(e/d, d, Assumptions::emptyAssump(), pf);
  else
    return newRWTheorem(e/d, rat(1/dr) * e, Assumptions::emptyAssump(), pf);
}


// Multiplication
// (MULT expr1 expr2 expr3 ...)
// Each expr is in canonical form, i.e. it can be a
// 1) Rational constant
// 2) Arithmetic Leaf (var or term from another theory)
// 3) (POW rational leaf)
// where rational cannot be 0 or 1
// 4) (MULT rational mterm'_1 ...) where each mterm' is of type (2) or (3)
// If rational == 1 then there should be at least two mterms
// 5) (PLUS rational sterm_1 ...) where each sterm is of
//     type (2) or (3) or (4)
//    if rational == 0 then there should be at least two sterms


Expr ArithTheoremProducerOld::simplifiedMultExpr(std::vector<Expr> & mulKids)
{
  DebugAssert(mulKids.size() >= 1 && mulKids[0].isRational(), "");
  if (mulKids.size() == 1) {
    return mulKids[0];
  }
  if ((mulKids[0] == rat(1)) && mulKids.size() == 2) {
    return mulKids[1];
  }
  else
    return multExpr(mulKids);
}

Expr ArithTheoremProducerOld::canonMultConstMult(const Expr & c,
                                              const Expr & e)
{
  // c is a rational
  // e is (MULT rat mterm'_1 ....)
  // assume that e2 is already in canonic form
  DebugAssert(c.isRational() && e.getKind() == MULT, "");
  std::vector<Expr> mulKids;
  DebugAssert ((e.arity() > 1) && (e[0].isRational()),
               "ArithTheoremProducerOld::canonMultConstMult: "
               "a canonized MULT expression must have arity "
               "greater than 1: and first child must be "
               "rational " + e.toString());
  Expr::iterator i = e.begin();
  mulKids.push_back(rat(c.getRational() * (*i).getRational()));
  ++i;
  for(; i != e.end(); ++i) {
    mulKids.push_back(*i);
  }
  return simplifiedMultExpr(mulKids);
}

Expr ArithTheoremProducerOld::canonMultConstPlus(const Expr & e1,
                                              const Expr & e2)
{
  DebugAssert(e1.isRational() && e2.getKind() == PLUS &&
              e2.arity() > 0, "");
  // e1 is a rational
  // e2 is of the form (PLUS rational sterm1 sterm2 ...)
  // assume that e2 is already in canonic form
  std::vector<Theorem> thmPlusVector;
  Expr::iterator i = e2.begin();
  for(; i!= e2.end(); ++i) {
    thmPlusVector.push_back(canonMultMtermMterm(e1*(*i)));
  }

  Theorem thmPlus1 =
    d_theoryArith->substitutivityRule(e2.getOp(), thmPlusVector);
  return thmPlus1.getRHS();
}

Expr ArithTheoremProducerOld::canonMultPowPow(const Expr & e1,
                                           const Expr & e2)
{
  DebugAssert(e1.getKind() == POW && e2.getKind() == POW, "");
  // (POW r1 leaf1) * (POW r2 leaf2)
  Expr leaf1 = e1[1];
  Expr leaf2 = e2[1];
  Expr can_expr;
  if (leaf1 == leaf2) {
    Rational rsum = e1[0].getRational() + e2[0].getRational();
    if (rsum == 0) {
      return rat(1);
    }
    else if (rsum == 1) {
      return leaf1;
    }
    else
      {
        return powExpr(rat(rsum), leaf1);
      }
  }
  else
    {
      std::vector<Expr> mulKids;
      mulKids.push_back(rat(1));
      // the leafs should be put in decreasing order
      if (leaf1 < leaf2) {
        mulKids.push_back(e2);
        mulKids.push_back(e1);
      }
      else
        {
          mulKids.push_back(e1);
          mulKids.push_back(e2);
        }
      // FIXME: don't really need to simplify, just wrap up a MULT?
      return simplifiedMultExpr(mulKids);
    }
}

Expr ArithTheoremProducerOld::canonMultPowLeaf(const Expr & e1,
                                            const Expr & e2)
{
  DebugAssert(e1.getKind() == POW, "");
  // (POW r1 leaf1) * leaf2
  Expr leaf1 = e1[1];
  Expr leaf2 = e2;
  Expr can_expr;
  if (leaf1 == leaf2) {
    Rational rsum = e1[0].getRational() + 1;
    if (rsum == 0) {
      return rat(1);
    }
    else if (rsum == 1) {
      return leaf1;
    }
    else
      {
        return powExpr(rat(rsum), leaf1);
      }
  }
  else
    {
      std::vector<Expr> mulKids;
      mulKids.push_back(rat(1));
      // the leafs should be put in decreasing order
      if (leaf1 < leaf2) {
        mulKids.push_back(e2);
        mulKids.push_back(e1);
      }
      else
        {
          mulKids.push_back(e1);
          mulKids.push_back(e2);
        }
      return simplifiedMultExpr(mulKids);
    }
}

Expr ArithTheoremProducerOld::canonMultLeafLeaf(const Expr & e1,
                                             const Expr & e2)
{
  // leaf1 * leaf2
  Expr leaf1 = e1;
  Expr leaf2 = e2;
  Expr can_expr;
  if (leaf1 == leaf2) {
    return powExpr(rat(2), leaf1);
  }
  else
    {
      std::vector<Expr> mulKids;
      mulKids.push_back(rat(1));
      // the leafs should be put in decreasing order
      if (leaf1 < leaf2) {
        mulKids.push_back(e2);
        mulKids.push_back(e1);
      }
      else
        {
          mulKids.push_back(e1);
          mulKids.push_back(e2);
        }
      return simplifiedMultExpr(mulKids);
    }
}

Expr ArithTheoremProducerOld::canonMultLeafOrPowMult(const Expr & e1,
                                                  const Expr & e2)
{
  DebugAssert(e2.getKind() == MULT, "");
  // Leaf * (MULT rat1 mterm1 ...)
  // (POW r1 leaf1) * (MULT rat1 mterm1 ...) where
  // each mterm is a leaf or (POW r leaf).  Furthermore the leafs
  // in the mterms are in descending order
  Expr leaf1 = e1.getKind() == POW ? e1[1] : e1;
  std::vector<Expr> mulKids;
  DebugAssert(e2.arity() > 1, "MULT expr must have arity 2 or more");
  Expr::iterator i = e2.begin();
  // push the rational
  mulKids.push_back(*i);
  ++i;
  // Now i points to the first mterm
  for(; i != e2.end(); ++i) {
    Expr leaf2 = ((*i).getKind() == POW) ? (*i)[1] : (*i);
    if (leaf1 == leaf2) {
      Rational r1 = e1.getKind() == POW ? e1[0].getRational() : 1;
      Rational r2 =
        ((*i).getKind() == POW ? (*i)[0].getRational() : 1);
      // if r1 + r2 == 0 then it is the case of x^n * x^{-n}
      // So, nothing needs to be added
      if (r1 + r2 != 0) {
        if (r1 + r2 == 1) {
          mulKids.push_back(leaf1);
        }
        else
          {
            mulKids.push_back(powExpr(rat(r1 + r2), leaf1));
          }
      }
      break;
    }
    // This ensures that the leaves in the mterms are also arranged
    // in decreasing order
    // Note that this will need to be changed if we want the order to
    // be increasing order.
    else if (leaf2 < leaf1) {
      mulKids.push_back(e1);
      mulKids.push_back(*i);
      break;
    }
    else // leaf1 < leaf2
      mulKids.push_back(*i);
  }
  if (i == e2.end()) {
    mulKids.push_back(e1);
  }
  else
    {
      // e1 and *i have already been added
      for (++i; i != e2.end(); ++i) {
        mulKids.push_back(*i);
      }
    }
  return simplifiedMultExpr(mulKids);
}

// Local class for ordering monomials; note, that it flips the
// ordering given by greaterthan(), to sort in ascending order.
class MonomialLess {
public:
  bool operator()(const Expr& e1, const Expr& e2) const {
    return ArithTheoremProducerOld::greaterthan(e1,e2);
  }
};

typedef map<Expr,Rational,MonomialLess> MonomMap;

Expr
ArithTheoremProducerOld::canonCombineLikeTerms(const std::vector<Expr> & sumExprs)
{
  Rational constant = 0;
  MonomMap sumHashMap;
  vector<Expr> sumKids;

  // Add each distinct mterm (not including the rational) into
  // an appropriate hash map entry
  std::vector<Expr>::const_iterator i = sumExprs.begin();
  for (; i != sumExprs.end(); ++i) {
    Expr mul = *i;
    if (mul.isRational()) {
      constant = constant + mul.getRational();
    }
    else {
      switch (mul.getKind()) {
      case MULT: {
        std::vector<Expr> mulKids;
        DebugAssert(mul.arity() > 1 && mul[0].isRational(),"");
        mulKids.push_back(rat(1));
        Expr::iterator j = mul.begin();
        ++j;
        for (; j!= mul.end(); ++j) {
          mulKids.push_back(*j);
        }

        // make sure that tempExpr is also in canonic form
        Expr tempExpr = mulKids.size() > 2 ? multExpr(mulKids): mulKids[1];
	MonomMap::iterator i=sumHashMap.find(tempExpr);
        if (i == sumHashMap.end()) {
          sumHashMap[tempExpr] = mul[0].getRational();
        }
        else {
          (*i).second += mul[0].getRational();
        }
      }
        break;
      default: {
	MonomMap::iterator i=sumHashMap.find(mul);
        // covers the case of POW, leaf
        if (i == sumHashMap.end()) {
          sumHashMap[mul] = 1;
        }
        else {
          (*i).second += 1;
        }
        break;
      }
      }
    }
  }
  // Now transfer to sumKids
  sumKids.push_back(rat(constant));
  MonomMap::iterator j = sumHashMap.begin(), jend=sumHashMap.end();
  for(; j != jend; ++j) {
    if ((*j).second != 0)
      sumKids.push_back
	(canonMultMtermMterm(rat((*j).second) * (*j).first).getRHS());
  }

  /*
    for (unsigned k = 0; k < sumKids.size(); ++k)
    {
    cout << "sumKids[" << k << "] = " << sumKids[k].toString() << endl;
    }
  */

  // The ordering in map guarantees the correct order; no need to sort

  // std::sort(sumKids.begin(), sumKids.end(), greaterthan);

  if ((constant == 0) && (sumKids.size() == 2)) {
    return sumKids[1];
  }
  else if (sumKids.size() == 1) {
    return sumKids[0];
  }
  else
    return plusExpr(sumKids);
}

Expr ArithTheoremProducerOld::canonMultLeafOrPowOrMultPlus(const Expr & e1,
                                                        const Expr & e2)
{
  DebugAssert(e2.getKind() == PLUS, "");
  // Leaf *  (PLUS rational sterm1 ...)
  // or
  // (POW n1 x1) * (PLUS rational sterm1 ...)
  // or
  // (MULT r1 m1 m2 ...) * (PLUS rational sterm1 ...)
  // assume that e1 and e2 are themselves canonized
  std::vector<Expr> sumExprs;
  // Multiply each term in turn.
  Expr::iterator i = e2.begin();
  for (; i != e2.end(); ++i) {
    sumExprs.push_back(canonMultMtermMterm(e1 * (*i)).getRHS());
  }
  return canonCombineLikeTerms(sumExprs);
}

Expr ArithTheoremProducerOld::canonMultPlusPlus(const Expr & e1,
                                             const Expr & e2)
{
  DebugAssert(e1.getKind() == PLUS && e2.getKind() == PLUS, "");
  // (PLUS r1 .... ) * (PLUS r1' ...)
  // assume that e1 and e2 are themselves canonized

  std::vector<Expr> sumExprs;
  // Multiply each term in turn.
  Expr::iterator i = e1.begin();
  for (;  i != e1.end(); ++i) {
    Expr::iterator j = e2.begin();
    for (;  j != e2.end(); ++j) {
      sumExprs.push_back(canonMultMtermMterm((*i) * (*j)).getRHS());
    }
  }
  return canonCombineLikeTerms(sumExprs);
}



// The following produces a Theorem which is the result of multiplication
// of two canonized mterms.  e = e1*e2
Theorem
ArithTheoremProducerOld::canonMultMtermMterm(const Expr& e)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(isMult(e) && e.arity() == 2,
		"canonMultMtermMterm: e = "+e.toString());
  }
  Proof pf;
  Expr rhs;
  const Expr& e1 = e[0];
  const Expr& e2 = e[1];
  string cmmm = "canon_mult_mterm_mterm";

  if (e1.isRational()) {
    // e1 is a Rational
    const Rational& c = e1.getRational();
    if (c == 0)
      return canonMultZero(e2);
    else if (c == 1)
      return canonMultOne(e2);
    else {
      switch (e2.getKind()) {
      case RATIONAL_EXPR :
        // rat * rat
        return canonMultConstConst(e1,e2);
        break;
        // TODO case of leaf
      case POW:
        // rat * (POW rat leaf)
        // nothing to simplify
        return d_theoryArith->reflexivityRule (e);

        break;
      case MULT:
        rhs = canonMultConstMult(e1,e2);
        if(withProof()) pf = newPf(cmmm,e,rhs);
        return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
        break;
      case PLUS:
        rhs = canonMultConstPlus(e1,e2);
        if(withProof()) pf = newPf(cmmm,e,rhs);
        return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
        break;
      default:
        // TODO: I am going to assume that this is just a leaf
        // i.e., a variable or term from another theory
        return d_theoryArith->reflexivityRule(e);
        break;
      }
    }
  }
  else if (e1.getKind() == POW) {
    switch (e2.getKind()) {
    case RATIONAL_EXPR:
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    case POW:
      rhs = canonMultPowPow(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e,rhs, Assumptions::emptyAssump(), pf);
      break;
    case MULT:
      rhs = canonMultLeafOrPowMult(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    case PLUS:
      rhs = canonMultLeafOrPowOrMultPlus(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    default:
      rhs = canonMultPowLeaf(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e,rhs, Assumptions::emptyAssump(), pf);
      break;
    }
  }
  else if (e1.getKind() == MULT) {
    switch (e2.getKind()) {
    case RATIONAL_EXPR:
    case POW:
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    case MULT:
      {
        // (Mult r m1 m2 ...) (Mult r' m1' m2' ...)
        Expr result = e2;
        Expr::iterator i = e1.begin();
        for (; i != e1.end(); ++i) {
          result = canonMultMtermMterm((*i) * result).getRHS();
        }
        if(withProof()) pf = newPf(cmmm,e,result);
        return newRWTheorem(e, result, Assumptions::emptyAssump(), pf);
      }
      break;
    case PLUS:
      rhs = canonMultLeafOrPowOrMultPlus(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e,rhs, Assumptions::emptyAssump(), pf);
      break;
    default:
      // leaf
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    }
  }
  else if (e1.getKind() == PLUS) {
    switch (e2.getKind()) {
    case RATIONAL_EXPR:
    case POW:
    case MULT:
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    case PLUS:
      rhs = canonMultPlusPlus(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    default:
      // leaf
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    }
  }
  else {
    // leaf
    switch (e2.getKind()) {
    case RATIONAL_EXPR:
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    case POW:
      rhs = canonMultPowLeaf(e2,e1);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    case MULT:
      rhs = canonMultLeafOrPowMult(e1,e2);;
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    case PLUS:
      rhs = canonMultLeafOrPowOrMultPlus(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    default:
      // leaf * leaf
      rhs = canonMultLeafLeaf(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    }
  }
  FatalAssert(false, "Unreachable");
  return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
}

// (PLUS expr1 expr2 ...) where each expr is itself in canonic form
Theorem
ArithTheoremProducerOld::canonPlus(const Expr& e)
{
  Proof pf;

  if (withProof()) {
    pf = newPf("canon_plus", e);
  }
  DebugAssert(e.getKind() == PLUS, "");

  // First flatten the PLUS

  std::vector<Expr> sumKids;
  Expr::iterator i = e.begin();
  for(; i != e.end(); ++i) {
    if ((*i).getKind() != PLUS) {
      sumKids.push_back(*i);
    }
    else
      {
        Expr::iterator j = (*i).begin();
        for(; j != (*i).end(); ++j)
          sumKids.push_back(*j);
      }
  }
  Expr val = canonCombineLikeTerms(sumKids);
  if (withProof()) {
    pf = newPf("canon_plus", e, val);
  }
  return newRWTheorem(e, val, Assumptions::emptyAssump(), pf);
}

// (MULT expr1 expr2 ...) where each expr is itself in canonic form
Theorem
ArithTheoremProducerOld::canonMult(const Expr& e)
{
  Proof pf;
  TRACE("arith canon", "canonMult(", e.toString(), ")");
  DebugAssert(e.getKind() == MULT && e.arity() > 1, "");
  Expr::iterator i = e.begin();
  Expr result = *i;
  ++i;
  for (; i != e.end(); ++i) {
    result = canonMultMtermMterm(result * (*i)).getRHS();
  }
  if (withProof()) {
    pf = newPf("canon_mult", e,result);
  }

  // If multiplicative sign split is on do it
  if (d_theoryArith->nonlinearSignSplit()) {

	  // Add the sign splits
	  Expr positive = d_em->trueExpr();
	  Expr negative = d_em->falseExpr();
	  vector<Expr> zero;

	  // we do the case split if it's not trivial
	  int count_non_trivial = 0;
	  int count_constants = 0;

	  // a1*a2*...*an is positive if there is an even number of negative ones
	  // a1*a2*...*an is negative if there is an odd number of negative ones
	  for (i = e.begin(); i != e.end(); ++i) {
		  Expr current = (*i);

		  if (isPlus(current)) count_non_trivial ++;
		  if (current.isRational()) count_constants ++;
		  if (isPow(current) && current[0].getRational() < 0) {
			  // Bail on negative powers, it's normalization
			  count_non_trivial = 0;
			  break;
		  }

		  zero.push_back(current.eqExpr(rat(0)));
		  positive = Expr(XOR, positive, ltExpr(current, rat(0)));
		  negative = Expr(XOR, negative, ltExpr(current, rat(0)));
	  }

	  if (count_non_trivial > 0 && !count_constants == (e.arity() - 1)) {
		  // Any of the factors is zero
		  Expr zero_lemma = orExpr(zero).iffExpr(result.eqExpr(rat(0)));
		  Expr positive_lemma = positive.impExpr(geExpr(result, rat(0)));
		  Expr negative_lemma = negative.impExpr(leExpr(result, rat(0)));
		  Expr lemma = positive_lemma.andExpr(negative_lemma.andExpr(zero_lemma));

		  Proof split_pf;
		  if (withProof()) split_pf = newPf("multiplicative_sign_split", e, lemma);
		  Theorem case_split_thm = newTheorem(lemma, Assumptions::emptyAssump(), split_pf);

		  TRACE("arith nonlinear", "adding sign split: ", lemma, "");

		  d_theoryArith->addMultiplicativeSignSplit(case_split_thm);
	  }
  }

  return newRWTheorem(e, result, Assumptions::emptyAssump(), pf);
}


Theorem
ArithTheoremProducerOld::canonInvertConst(const Expr& e)
{
  if(CHECK_PROOFS)
    CHECK_SOUND(isRational(e), "expecting a rational: e = "+e.toString());

  Proof pf;

  if (withProof()) {
    pf = newPf("canon_invert_const", e);
  }
  const Rational& er = e.getRational();
  return newRWTheorem((rat(1)/e), rat(er==0? 0 : (1/er)), Assumptions::emptyAssump(), pf);
}


Theorem
ArithTheoremProducerOld::canonInvertLeaf(const Expr& e)
{
  Proof pf;

  if (withProof()) {
    pf = newPf("canon_invert_leaf", e);
  }
  return newRWTheorem((rat(1)/e), powExpr(rat(-1), e), Assumptions::emptyAssump(), pf);
}


Theorem
ArithTheoremProducerOld::canonInvertPow(const Expr& e)
{
  DebugAssert(e.getKind() == POW, "expecting a rational"+e[0].toString());

  Proof pf;

  if (withProof()) {
    pf = newPf("canon_invert_pow", e);
  }
  if (e[0].getRational() == -1)
    return newRWTheorem((rat(1)/e), e[1], Assumptions::emptyAssump(), pf);
  else
    return newRWTheorem((rat(1)/e),
                        powExpr(rat(-e[0].getRational()), e[1]),
                        Assumptions::emptyAssump(),
                        pf);
}

Theorem
ArithTheoremProducerOld::canonInvertMult(const Expr& e)
{
  DebugAssert(e.getKind() == MULT, "expecting a rational"+e[0].toString());

  Proof pf;

  if (withProof()) {
    pf = newPf("canon_invert_mult", e);
  }

  DebugAssert(e.arity() > 1, "MULT should have arity > 1"+e.toString());
  Expr result = canonInvert(e[0]).getRHS();
  for (int i = 1; i < e.arity(); ++i) {
    result =
      canonMultMtermMterm(result * canonInvert(e[i]).getRHS()).getRHS();
  }
  return newRWTheorem((rat(1)/e), result, Assumptions::emptyAssump(), pf);
}


// Given an expression e in Canonic form generate 1/e in canonic form
// This function assumes that e is not a PLUS expression
Theorem
ArithTheoremProducerOld::canonInvert(const Expr& e)
{
  DebugAssert(e.getKind() != PLUS,
              "Cannot do inverse on a PLUS"+e.toString());
  switch (e.getKind()) {
  case RATIONAL_EXPR:
    return canonInvertConst(e);
    break;
  case POW:
    return canonInvertPow(e);
    break;
  case MULT:
    return canonInvertMult(e);
    break;
  default:
    // leaf
    return canonInvertLeaf(e);
    break;
  }
}


Theorem ArithTheoremProducerOld::moveSumConstantRight(const Expr& e) {

 	// Check soundness of the rule if necessary
 	if (CHECK_PROOFS) {
 		CHECK_SOUND(isIneq(e) || e.isEq(), "moveSumConstantRight: input must be Eq or Ineq: " + e.toString());
 		CHECK_SOUND(isRational(e[0]) || isPlus(e[0]), "moveSumConstantRight: left side must be a canonised sum: " + e.toString());
 		CHECK_SOUND(isRational(e[1]) && e[1].getRational() == 0, "moveSumConstantRight: right side must be 0: " + e.toString());
 	}

	// The rational constant of the sum
	Rational r = 0;

	// The right hand side of the expression
	Expr right = e[0];

	// The vector of sum terms
	vector<Expr> sumTerms;

	// Get all the non rational children and
	if (!right.isRational())
		for(Expr::iterator it = right.begin(); it != right.end(); it ++) {
			// If the term is rational then add the rational number to r
			if ((*it).isRational()) r = r + (*it).getRational();
			// Otherwise just add the sumTerm to the sumTerms
			else sumTerms.push_back((*it));
		}

	// Setup the new expression
	Expr transformed;
	if (sumTerms.size() > 1)
		// If the number of summands is > 1 return the sum of them
		transformed = Expr(e.getKind(), plusExpr(sumTerms), rat(-r));
	else
		// Otherwise return the one summand as itself
		transformed = Expr(e.getKind(), sumTerms[0], rat(-r));


	// If proof is needed set it up
	Proof pf;
	if (withProof()) pf = newPf("arithm_sum_constant_right", e);

	// Retrun the theorem explaining the transformation
	return newRWTheorem(e, transformed, Assumptions::emptyAssump(), pf);
}

Theorem
ArithTheoremProducerOld::canonDivide(const Expr& e)
{
  DebugAssert(e.getKind() == DIVIDE, "Expecting Divide"+e.toString());
  Proof pf;

  if (withProof()) {
    pf = newPf("canon_invert_divide", e);
  }

  Theorem thm = newRWTheorem(e, e[0]*(canonInvert(e[1]).getRHS()), Assumptions::emptyAssump(), pf);

  return d_theoryArith->transitivityRule(thm, canonMult(thm.getRHS()));
}


// Rules for multiplication
// t*c ==> c*t, takes constant c and term t
Theorem
ArithTheoremProducerOld::canonMultTermConst(const Expr& c, const Expr& t) {
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(c),
                CLASS_NAME "::canonMultTermConst:\n  "
                "c is not a constant: " + c.toString());
  }
  if(withProof()) pf = newPf("canon_mult_term_const", c, t);
  return newRWTheorem((t*c), (c*t), Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// t1*t2 ==> Error, takes t1 and t2 where both are non-constants
Theorem
ArithTheoremProducerOld::canonMultTerm1Term2(const Expr& t1, const Expr& t2) {
  // Proof pf;
  // if(withProof()) pf = newPf("canon_mult_term1_term2", t1, t2);
  if(CHECK_PROOFS) {
    CHECK_SOUND(false, "Fatal Error: We don't support multiplication"
                "of two non constant terms at this time "
                + t1.toString() + " and " + t2.toString());
  }
  return Theorem();
}

// Rules for multiplication
// 0*x = 0, takes x
Theorem ArithTheoremProducerOld::canonMultZero(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("canon_mult_zero", e);
  return newRWTheorem((rat(0)*e), rat(0), Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// 1*x ==> x, takes x
Theorem ArithTheoremProducerOld::canonMultOne(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("canon_mult_one", e);
  return newRWTheorem((rat(1)*e), e, Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// c1*c2 ==> c', takes constant c1*c2
Theorem
ArithTheoremProducerOld::canonMultConstConst(const Expr& c1, const Expr& c2) {
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(c1),
                CLASS_NAME "::canonMultConstConst:\n  "
                "c1 is not a constant: " + c1.toString());
    CHECK_SOUND(isRational(c2),
                CLASS_NAME "::canonMultConstConst:\n  "
                "c2 is not a constant: " + c2.toString());
  }
  if(withProof()) pf = newPf("canon_mult_const_const", c1, c2);
  return
    newRWTheorem((c1*c2), rat(c1.getRational()*c2.getRational()), Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// c1*(c2*t) ==> c'*t, takes c1 and c2 and t
Theorem
ArithTheoremProducerOld::canonMultConstTerm(const Expr& c1,
                                         const Expr& c2,const Expr& t) {
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(c1),
                CLASS_NAME "::canonMultConstTerm:\n  "
                "c1 is not a constant: " + c1.toString());
    CHECK_SOUND(isRational(c2),
                CLASS_NAME "::canonMultConstTerm:\n  "
                "c2 is not a constant: " + c2.toString());
  }

  if(withProof()) pf = newPf("canon_mult_const_term", c1, c2, t);
  return
    newRWTheorem(c1*(c2*t), rat(c1.getRational()*c2.getRational())*t, Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// c1*(+ c2 v1 ...) ==> (+ c1c2 c1v1 ...), takes c1 and the sum
Theorem
ArithTheoremProducerOld::canonMultConstSum(const Expr& c1, const Expr& sum) {
  Proof pf;
  std::vector<Expr> sumKids;

  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(c1),
                CLASS_NAME "::canonMultConstTerm:\n  "
                "c1 is not a constant: " + c1.toString());
    CHECK_SOUND(PLUS == sum.getKind(),
                CLASS_NAME "::canonMultConstTerm:\n  "
                "the kind must be a PLUS: " + sum.toString());
  }
  Expr::iterator i = sum.begin();
  for(; i != sum.end(); ++i)
    sumKids.push_back(c1*(*i));
  Expr ret = plusExpr(sumKids);
  if(withProof()) pf = newPf("canon_mult_const_sum", c1, sum, ret);
  return newRWTheorem((c1*sum),ret , Assumptions::emptyAssump(), pf);
}


// c^n = c' (compute the constant power expression)
Theorem
ArithTheoremProducerOld::canonPowConst(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == POW && e.arity() == 2
		&& e[0].isRational() && e[1].isRational(),
		"ArithTheoremProducerOld::canonPowConst("+e.toString()+")");
  }
  const Rational& p = e[0].getRational();
  const Rational& base = e[1].getRational();
  if(CHECK_PROOFS) {
    CHECK_SOUND(p.isInteger(),
		"ArithTheoremProducerOld::canonPowConst("+e.toString()+")");
  }
  Expr res;
  if (base == 0 && p < 0) {
    res = rat(0);
  }
  else res = rat(pow(p, base));
  Proof pf;
  if(withProof())
    pf = newPf("canon_pow_const", e, res);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


// Rules for addition
// flattens the input. accepts a PLUS expr
Theorem
ArithTheoremProducerOld::canonFlattenSum(const Expr& e) {
  Proof pf;
  std::vector<Expr> sumKids;
  if(CHECK_PROOFS) {
    CHECK_SOUND(PLUS == e.getKind(),
                CLASS_NAME "::canonFlattenSum:\n"
                "input must be a PLUS:" + e.toString());
  }

  Expr::iterator i = e.begin();
  for(; i != e.end(); ++i){
    if (PLUS != (*i).getKind())
      sumKids.push_back(*i);
    else {
      Expr::iterator j = (*i).begin();
      for(; j != (*i).end(); ++j)
        sumKids.push_back(*j);
    }
  }
  Expr ret =  plusExpr(sumKids);
  if(withProof()) pf = newPf("canon_flatten_sum", e,ret);
  return newRWTheorem(e,ret, Assumptions::emptyAssump(), pf);
}

// Rules for addition
// combine like terms. accepts a flattened PLUS expr
Theorem
ArithTheoremProducerOld::canonComboLikeTerms(const Expr& e) {
  Proof pf;
  std::vector<Expr> sumKids;
  ExprMap<Rational> sumHashMap;
  Rational constant = 0;

  if(CHECK_PROOFS) {
    Expr::iterator k = e.begin();
    for(; k != e.end(); ++k)
      CHECK_SOUND(!isPlus(*k),
                  CLASS_NAME "::canonComboLikeTerms:\n"
                  "input must be a flattened PLUS:" + k->toString());
  }
  Expr::iterator i = e.begin();
  for(; i != e.end(); ++i){
    if(i->isRational())
      constant = constant + i->getRational();
    else {
      if (!isMult(*i)) {
        if(0 == sumHashMap.count((*i)))
          sumHashMap[*i] = 1;
        else
          sumHashMap[*i] += 1;
      }
      else {
        if(0 == sumHashMap.count((*i)[1]))
          sumHashMap[(*i)[1]] = (*i)[0].getRational();
        else
          sumHashMap[(*i)[1]] = sumHashMap[(*i)[1]] + (*i)[0].getRational();
      }
    }
  }

  sumKids.push_back(rat(constant));
  ExprMap<Rational>::iterator j = sumHashMap.begin();
  for(; j != sumHashMap.end(); ++j) {
    if(0 == (*j).second)
      ;//do nothing
    else if (1 == (*j).second)
      sumKids.push_back((*j).first);
    else
      sumKids.push_back(rat((*j).second) * (*j).first);
  }

  //constant is same as sumKids[0].
  //corner cases: "0 + monomial" and "constant"(no monomials)

  Expr ret;
  if(2 == sumKids.size() && 0 == constant) ret = sumKids[1];
  else if (1 == sumKids.size()) ret = sumKids[0];
  else ret = plusExpr(sumKids);

  if(withProof()) pf = newPf("canon_combo_like_terms",e,ret);
  return newRWTheorem(e, ret, Assumptions::emptyAssump(), pf);
}


// 0 = (* e1 e2 ...) <=> 0 = e1 OR 0 = e2 OR ...
Theorem ArithTheoremProducerOld::multEqZero(const Expr& expr)
{
  Proof pf;
  vector<Expr> kids;

  int side = expr[0].isRational() ? 1 : 0;

  vector<Expr> non_zero;

  Expr::iterator i = expr[side].begin(), iend = expr[side].end();
  for (; i != iend; ++i) {
	  Expr x = *i;
	  // If a rational it can't be 0, so it is false, i.e. just skip it
	  if (x.isRational()) {
		  CHECK_SOUND(x.getRational() != 0, "multEqZero: once of the constants is 0");
	  } else {
		  Expr leaf = x;
		  if (isPow(x)) {
                    // We assume that 1 / 0 = 0 for simplicity and totality.
                    // Divisions by zero that affect the result can be identified by enabling TCCs.
                    //			  if (x[0].getRational() < 0) {
                    //				  non_zero.push_back(x[1].eqExpr(rat(0)).notExpr());
                    //				  continue;
                    //			  }
                    //			  else
                    leaf = x[1];
		  }
		  if (leaf >= rat(0))
			  kids.push_back(leaf.eqExpr(rat(0)));
		  else
			  kids.push_back(rat(0).eqExpr(leaf));
	  }
  }
  Expr newExpr;
  if (kids.size() == 1) newExpr = kids[0];
  else newExpr = Expr(OR, kids);
  if (withProof()) {
    pf = newPf("multEqZero", expr);
  }
  //  if (non_zero.size() == 0)
  return newRWTheorem(expr, newExpr, Assumptions::emptyAssump(), pf);
  //  else return newRWTheorem(expr, Expr(OR, kids).andExpr(Expr(AND, non_zero)), Assumptions::emptyAssump(), pf);
}


// 0 = (^ c x) <=> false if c <=0
//             <=> 0 = x if c > 0
Theorem ArithTheoremProducerOld::powEqZero(const Expr& expr)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(expr.isEq() && expr[0].isRational() &&
                expr[0].getRational() == 0 &&
                isPow(expr[1]) && expr[1].arity() == 2 &&
                expr[1][0].isRational(),
                "powEqZero invariant violated"+expr.toString());
  }
  Proof pf;
  if (withProof()) {
    pf = newPf("powEqZero", expr);
  }
  Rational r = expr[1][0].getRational();
  Expr res;
  if (r <= 0) {
    res = d_em->falseExpr();
  }
  else {
    res = rat(0).eqExpr(expr[1][1]);
  }
  return newRWTheorem(expr, res, Assumptions::emptyAssump(), pf);
}


// x^n - y^n = 0 <=> x = y (if n is odd)
// x^n - y^n = 0 <=> x = y OR x = -y (if n is even)
Theorem ArithTheoremProducerOld::elimPower(const Expr& expr)
{
	Expr power1, power2;
	bool ok = d_theoryArith->isPowersEquality(expr, power1, power2);
	if (CHECK_PROOFS)
		CHECK_SOUND(ok, "elimPower invariant violated"+expr.toString());
	Proof pf;
	if (withProof())
		pf = newPf("elimPower", expr);
	Rational r = power1[0].getRational();
	Expr res = power1[1].eqExpr(power2[1]);
	if (r % 2 == 0)
		res = res.orExpr(power1[1].eqExpr(-power2[1]));
	return newRWTheorem(expr, res, Assumptions::emptyAssump(), pf);
}


// x^n = c <=> x = root (if n is odd and root^n = c)
// x^n = c <=> x = root OR x = -root (if n is even and root^n = c)
Theorem ArithTheoremProducerOld::elimPowerConst(const Expr& expr, const Rational& root)
{
	if (CHECK_PROOFS)
	    CHECK_SOUND(expr.isEq(), "elimPowerConst invariant violated" + expr.toString());
	Rational constant;
	Expr power;
	bool ok = d_theoryArith->isPowerEquality(expr, constant, power);
	if (CHECK_PROOFS) {
		CHECK_SOUND(ok, "elimPowerConst invariant violated" + expr.toString());
		CHECK_SOUND(pow(power[0].getRational(), root) == constant, "elimPowerConst invariant violated" + expr.toString());
	}

	Proof pf;
	if (withProof())
		pf = newPf("elimPowerConst", expr, rat(root));
	Rational r = power[0].getRational();
	Expr res = power[1].eqExpr(rat(root));
	if (r % 2 == 0)
		res = res.orExpr(power[1].eqExpr(rat(-root)));

	return newRWTheorem(expr, res, Assumptions::emptyAssump(), pf);
}


// x^n = c <=> false (if n is even and c is negative)
Theorem ArithTheoremProducerOld::evenPowerEqNegConst(const Expr& expr)
{
	if (CHECK_PROOFS)
		CHECK_SOUND(expr.isEq(), "evenPowerEqNegConst, expecting equality, got " + expr.toString());
	Rational constant;
	Expr power;
	bool ok = d_theoryArith->isPowerEquality(expr, constant, power);
	if (CHECK_PROOFS) {
		CHECK_SOUND(ok, "evenPowerEqNegConst invariant violated" + expr.toString());
		CHECK_SOUND(constant < 0, "evenPowerEqNegConst invariant violated" + expr.toString());
		CHECK_SOUND(power[0].getRational().isInteger() && power[0].getRational() % 2 == 0, "evenPowerEqNegConst invariant violated" + expr.toString());
	}
	Proof pf;
	if (withProof())
		pf = newPf("evenPowerEqNegConst", expr);
	return newRWTheorem(expr, d_em->falseExpr(), Assumptions::emptyAssump(), pf);
}


// x^n = c <=> ` (if x is an integer and c is not a perfect n power)
Theorem ArithTheoremProducerOld::intEqIrrational(const Expr& expr, const Theorem& isIntx)
{
	if (CHECK_PROOFS)
	    CHECK_SOUND(expr.isEq(), "intEqIrrational invariant violated" + expr.toString());
	Rational constant;
	Expr power;
	bool ok = d_theoryArith->isPowerEquality(expr, constant, power);
	if (CHECK_PROOFS) {
		CHECK_SOUND(ok, "intEqIrrational invariant violated" + expr.toString());
		CHECK_SOUND(constant != 0, "intEqIrrational invariant violated" + expr.toString());
		CHECK_SOUND(power[0].getRational() > 0, "intEqIrrational invariant violated" + expr.toString());
		CHECK_SOUND(ratRoot(constant, power[0].getRational().getUnsigned()) == 0, "intEqIrrational invariant violated" + expr.toString());
		CHECK_SOUND(isIntPred(isIntx.getExpr()) && isIntx.getExpr()[0] == expr[0], "intEqIrrational invariant violated" + isIntx.getExpr()[0].toString());
	}

	const Assumptions& assump(isIntx.getAssumptionsRef());
	Proof pf;
	if (withProof())
		pf = newPf("int_eq_irr", expr, isIntx.getProof());
	return newRWTheorem(expr, d_em->falseExpr(), assump, pf);
}


// e[0] kind e[1] <==> true when e[0] kind e[1],
// false when e[0] !kind e[1], for constants only
Theorem ArithTheoremProducerOld::constPredicate(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.arity() == 2 && isRational(e[0]) && isRational(e[1]),
                CLASS_NAME "::constPredicate:\n  "
                "non-const parameters: " + e.toString());
  }
  Proof pf;
  bool result(false);
  int kind = e.getKind();
  Rational r1 = e[0].getRational(), r2 = e[1].getRational();
  switch(kind) {
  case EQ:
    result = (r1 == r2)?true : false;
    break;
  case LT:
    result = (r1 < r2)?true : false;
    break;
  case LE:
    result = (r1 <= r2)?true : false;
    break;
  case GT:
    result = (r1 > r2)?true : false;
    break;
  case GE:
    result = (r1 >= r2)?true : false;
    break;
  default:
    if(CHECK_PROOFS) {
      CHECK_SOUND(false,
                  "ArithTheoremProducerOld::constPredicate: wrong kind");
    }
    break;
  }
  Expr ret = (result) ? d_em->trueExpr() : d_em->falseExpr();
  if(withProof()) pf = newPf("const_predicate", e,ret);
  return newRWTheorem(e, ret, Assumptions::emptyAssump(), pf);
}

// e[0] kind e[1] <==> 0 kind e[1] - e[0]
Theorem ArithTheoremProducerOld::rightMinusLeft(const Expr& e)
{
  Proof pf;
  int kind = e.getKind();
  if(CHECK_PROOFS) {
    CHECK_SOUND((EQ==kind) ||
                (LT==kind) ||
                (LE==kind) ||
                (GE==kind) ||
                (GT==kind),
                "ArithTheoremProducerOld::rightMinusLeft: wrong kind");
  }
  if(withProof()) pf = newPf("right_minus_left",e);
  return newRWTheorem(e, Expr(e.getOp(), rat(0), e[1] - e[0]), Assumptions::emptyAssump(), pf);
}


// e[0] kind e[1] <==> 0 kind e[1] - e[0]
Theorem ArithTheoremProducerOld::leftMinusRight(const Expr& e)
{
  Proof pf;
  int kind = e.getKind();
  if(CHECK_PROOFS) {
    CHECK_SOUND((EQ==kind) ||
                (LT==kind) ||
                (LE==kind) ||
                (GE==kind) ||
                (GT==kind),
                "ArithTheoremProducerOld::rightMinusLeft: wrong kind");
  }
  if(withProof()) pf = newPf("left_minus_right",e);
  return newRWTheorem(e, Expr(e.getOp(), e[0] - e[1], rat(0)), Assumptions::emptyAssump(), pf);
}


// x kind y <==> x + z kind y + z
Theorem ArithTheoremProducerOld::plusPredicate(const Expr& x,
                                      const Expr& y,
                                      const Expr& z, int kind) {
  if(CHECK_PROOFS) {
    CHECK_SOUND((EQ==kind) ||
                (LT==kind) ||
                (LE==kind) ||
                (GE==kind) ||
                (GT==kind),
                "ArithTheoremProducerOld::plusPredicate: wrong kind");
  }
  Proof pf;
  Expr left = Expr(kind, x, y);
  Expr right = Expr(kind, x + z, y + z);
  if(withProof()) pf = newPf("plus_predicate",left,right);
  return newRWTheorem(left, right, Assumptions::emptyAssump(), pf);
}

// x = y <==> x * z = y * z
Theorem ArithTheoremProducerOld::multEqn(const Expr& x,
                                      const Expr& y,
                                      const Expr& z) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(z.isRational() && z.getRational() != 0,
		"ArithTheoremProducerOld::multEqn(): multiplying equation by 0");
  if(withProof()) pf = newPf("mult_eqn", x, y, z);
  return newRWTheorem(x.eqExpr(y), (x * z).eqExpr(y * z), Assumptions::emptyAssump(), pf);
}


// x = y <==> z=0 OR x * 1/z = y * 1/z
Theorem ArithTheoremProducerOld::divideEqnNonConst(const Expr& x,
                                                   const Expr& y,
                                                   const Expr& z) {
  Proof pf;
  if(withProof()) pf = newPf("mult_eqn_nonconst", x, y, z);
  return newRWTheorem(x.eqExpr(y), (z.eqExpr(rat(0))).orExpr((x / z).eqExpr(y / z)),
                      Assumptions::emptyAssump(), pf);
}


// if z is +ve, return e[0] LT|LE|GT|GE e[1] <==> e[0]*z LT|LE|GT|GE e[1]*z
// if z is -ve, return e[0] LT|LE|GT|GE e[1] <==> e[1]*z LT|LE|GT|GE e[0]*z
Theorem ArithTheoremProducerOld::multIneqn(const Expr& e, const Expr& z)
{
  int kind = e.getKind();

  if(CHECK_PROOFS) {
    CHECK_SOUND((LT==kind) ||
                (LE==kind) ||
                (GE==kind) ||
                (GT==kind),
                "ArithTheoremProducerOld::multIneqn: wrong kind");
    CHECK_SOUND(z.isRational() && z.getRational() != 0,
                "ArithTheoremProducerOld::multIneqn: "
		"z must be non-zero rational: " + z.toString());
  }
  Op op(e.getOp());
  Proof pf;

  Expr ret;
  if(0 < z.getRational())
    ret = Expr(op, e[0]*z, e[1]*z);
  else
    ret = Expr(op, e[1]*z, e[0]*z);
  if(withProof()) pf = newPf("mult_ineqn", e, ret);
  return newRWTheorem(e, ret, Assumptions::emptyAssump(), pf);
}


//
// If expr:
// If b > 0 then (0 <= a + bx) <==> (0 <= floor(a/b) + x)
//    b < 0 then (0 <= a + bx) <==> (0 >= ceil(a/b) + x)
//    b > 0 then (0 >= a + bx) <==> (0 >= ceil(a/b) + x)
//    b < 0 then (0 >= a + bx) <==> (0 <= floor(a/b) + x)
//
Theorem ArithTheoremProducerOld::simpleIneqInt(const Expr& ineq, const Theorem& isIntRHS)
{
	// Get the inequality parts
	Expr lhs = ineq[0];
	Expr rhs = ineq[1];

	// Get the kind of the inequality
	int kind = ineq.getKind();


	if(CHECK_PROOFS) {
		// isIntRHS should be an int proof of rhs
		const Expr& isIntRHSExpr = isIntRHS.getExpr();
		CHECK_SOUND(isIntPred(isIntRHSExpr) && isIntRHSExpr[0] == rhs, "ArithTheoremProducerOld::multSimpleIneqnInt: not an integer proof of rhs");

		// It's an inequality
		CHECK_SOUND((LT == kind) || (LE==kind) || (GE==kind) || (GT==kind), "ArithTheoremProducerOld::multSimpleIneqnInt: wrong kind");

		// Left-hand side is 0
		CHECK_SOUND(lhs.isRational() && lhs.getRational() == 0, "ArithTheoremProducerOld::multSimpleIneqnInt: left-hand side must be 0");

		// Tight hand side is a sum (a + b*x) where a and b are integers, x is a var
		CHECK_SOUND(isPlus(rhs), "ArithTheoremProducerOld::multSimpleIneqnInt: right-hand side must be a plus");
		CHECK_SOUND(rhs.arity() == 2, "ArithTheoremProducerOld::multSimpleIneqnInt: right-hand side a simple plus");

		Expr a  = rhs[0]; // Should be an integer
		Expr bx = rhs[1]; // Should be an integer multiplied by a variable

		// a is an integer
		CHECK_SOUND(a.isRational() && a.getRational().isInteger(), "ArithTheoremProducerOld::multSimpleIneqnInt: right-hand side a simple plus of a constant");

		// bx should be a multiplication of an intgere and a variable
		CHECK_SOUND(isMult(bx) && bx.arity() == 2, "ArithTheoremProducerOld::multSimpleIneqnInt: right-hand side a simple plus of and a multiplication");
		Expr b = bx[0];
		Expr x = bx[1];

		// b should be an integer
		CHECK_SOUND(b.isRational() && b.getRational().isInteger(), "ArithTheoremProducerOld::multSimpleIneqnInt: right-hand side a simple plus of and a multiplication of a constant");
		// x should be a variable
		CHECK_SOUND(x.isVar(), "ArithTheoremProducerOld::multSimpleIneqnInt: right-hand side a simple plus of and a multiplication of a constant and a leaf");

		// GCD(a, b) should be 1
		//CHECK_SOUND(gcd(a.getRational(), b.getRational()) == 1, "ArithTheoremProducerOld::multSimpleIneqnInt: inequation not normalized!!!");
	}

	Proof pf;
	if(withProof()) {
		vector<Proof> pfs;
		pfs.push_back(isIntRHS.getProof());
		pf = newPf("simpleineqint", ineq, pf);
	}

	Rational a = rhs[0].getRational();
	Rational b = rhs[1][0].getRational();
	Expr x = rhs[1][1];

	Rational new_const;
	Expr ret;
	switch (kind) {
		case LT:
			if (b > 0) {
				new_const = floor(a/b);
				if (new_const != 0)
					ret = Expr(kind, rat(0), rat(new_const) + x);
				else
					ret = Expr(kind, rat(0), x);
			}
			else {
				new_const = ceil(a/b);
				//ret = geExpr(rat(0), rat(new_const) + x);
				if (new_const != 0)
					ret = Expr(kind, rat(0), rat(-new_const) + rat(-1)*x);
				else
					ret = Expr(kind, rat(0), rat(-1)*x);
			}
			break;
			break;
		case LE:
			if (b > 0) {
				new_const = floor(a/b);
				if (new_const != 0)
					ret = Expr(kind, rat(0), rat(new_const) + x);
				else
					ret = Expr(kind, rat(0), x);
			}
			else {
				new_const = ceil(a/b);
				//ret = geExpr(rat(0), rat(new_const) + x);
				if (new_const != 0)
					ret = Expr(kind, rat(0), rat(-new_const) + rat(-1)*x);
				else
					ret = Expr(kind, rat(0), rat(-1)*x);
			}
			break;
		case GE:
		case GT:
			// Setup the result kind
			if (kind == GT) kind = LT;
			else kind = LE;

			if (b > 0) {
				new_const = ceil(a/b);
				//ret = geExpr(rat(0), rat(new_const) + x);
				if (new_const != 0)
					ret = Expr(kind, rat(0), rat(-new_const) + rat(-1)*x);
				else
					ret = Expr(kind, rat(0), rat(-1)*x);
			}
			else {
				new_const = floor(a/b);
				if (new_const != 0)
					ret = Expr(kind, rat(0), rat(new_const) + x);
				else
					ret = Expr(kind, rat(0), x);
			}
			break;
	}

	// Return the new theorem
	return newRWTheorem(ineq, ret, Assumptions::emptyAssump(), pf);
}


Theorem ArithTheoremProducerOld::eqToIneq(const Expr& e) {

  	// Check soundness of the rule if necessary
 	if (CHECK_PROOFS)
 		CHECK_SOUND(e.isEq(), "eqToIneq: input must be an equality: " + e.toString());

  	// The proof object we will use
  	Proof pf;

	// The parts of the equality x = y
  	const Expr& x = e[0];
  	const Expr& y = e[1];

	// Setup the proof if needed
  	if (withProof())
    	pf = newPf("eqToIneq", e);

  	// Retrun the theorem explaining the transformation
	return newRWTheorem(e, leExpr(x,y).andExpr(geExpr(x,y)), Assumptions::emptyAssump(), pf);
}

// "op1 GE|GT op2" <==> op2 LE|LT op1
Theorem ArithTheoremProducerOld::flipInequality(const Expr& e)
{
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGT(e) || isGE(e),
                "ArithTheoremProducerOld::flipInequality: wrong kind: " +
                e.toString());
  }

  int kind = isGE(e) ? LE : LT;
  Expr ret =  Expr(kind, e[1], e[0]);
  if(withProof()) pf = newPf("flip_inequality", e,ret);
  return newRWTheorem(e,ret, Assumptions::emptyAssump(), pf);
}


// NOT (op1 LT op2)  <==> (op1 GE op2)
// NOT (op1 LE op2)  <==> (op1 GT op2)
// NOT (op1 GT op2)  <==> (op1 LE op2)
// NOT (op1 GE op2)  <==> (op1 LT op2)
Theorem ArithTheoremProducerOld::negatedInequality(const Expr& e)
{
  const Expr& ineq = e[0];
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot(),
                "ArithTheoremProducerOld::negatedInequality: wrong kind: " +
                e.toString());
    CHECK_SOUND(isIneq(ineq),
                "ArithTheoremProducerOld::negatedInequality: wrong kind: " +
                (ineq).toString());
  }
  Proof pf;
  if(withProof()) pf = newPf("negated_inequality", e);

  int kind;
  // NOT (op1 LT op2)  <==> (op1 GE op2)
  // NOT (op1 LE op2)  <==> (op1 GT op2)
  // NOT (op1 GT op2)  <==> (op1 LE op2)
  // NOT (op1 GE op2)  <==> (op1 LT op2)
  kind =
    isLT(ineq) ? GE :
    isLE(ineq) ? GT :
    isGT(ineq) ? LE :
    LT;
  return newRWTheorem(e, Expr(kind, ineq[0], ineq[1]), Assumptions::emptyAssump(), pf);
}

//takes two ineqs "|- alpha LT|LE t" and "|- t LT|LE beta"
//and returns "|- alpha LT|LE beta"
Theorem ArithTheoremProducerOld::realShadow(const Theorem& alphaLTt,
                                         const Theorem& tLTbeta)
{
  const Expr& expr1 = alphaLTt.getExpr();
  const Expr& expr2 = tLTbeta.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND((isLE(expr1) || isLT(expr1)) &&
                (isLE(expr2) || isLT(expr2)),
                "ArithTheoremProducerOld::realShadow: Wrong Kind: " +
                alphaLTt.toString() +  tLTbeta.toString());

    CHECK_SOUND(expr1[1] == expr2[0],
                "ArithTheoremProducerOld::realShadow:"
                " t must be same for both inputs: " +
                expr1[1].toString() + " , " + expr2[0].toString());
  }
  Assumptions a(alphaLTt, tLTbeta);
  int firstKind = expr1.getKind();
  int secondKind = expr2.getKind();
  int kind = (firstKind == secondKind) ? firstKind : LT;
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(alphaLTt.getProof());
    pfs.push_back(tLTbeta.getProof());
    pf = newPf("real_shadow",expr1, expr2, pfs);
  }
  return newTheorem(Expr(kind, expr1[0], expr2[1]), a, pf);
}

//! alpha <= t <= alpha ==> t = alpha

/*! takes two ineqs "|- alpha LE t" and "|- t LE alpha"
  and returns "|- t = alpha"
*/
Theorem ArithTheoremProducerOld::realShadowEq(const Theorem& alphaLEt,
                                           const Theorem& tLEalpha)
{
  const Expr& expr1 = alphaLEt.getExpr();
  const Expr& expr2 = tLEalpha.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isLE(expr1) && isLE(expr2),
                "ArithTheoremProducerOld::realShadowLTLE: Wrong Kind: " +
                alphaLEt.toString() +  tLEalpha.toString());

    CHECK_SOUND(expr1[1] == expr2[0],
                "ArithTheoremProducerOld::realShadowLTLE:"
                " t must be same for both inputs: " +
                alphaLEt.toString() + " , " + tLEalpha.toString());

    CHECK_SOUND(expr1[0] == expr2[1],
                "ArithTheoremProducerOld::realShadowLTLE:"
                " alpha must be same for both inputs: " +
                alphaLEt.toString() + " , " + tLEalpha.toString());
  }
  Assumptions a(alphaLEt, tLEalpha);
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(alphaLEt.getProof());
    pfs.push_back(tLEalpha.getProof());
    pf = newPf("real_shadow_eq", alphaLEt.getExpr(), tLEalpha.getExpr(), pfs);
  }
  return newRWTheorem(expr1[0], expr1[1], a, pf);
}

Theorem
ArithTheoremProducerOld::finiteInterval(const Theorem& aLEt,
				     const Theorem& tLEac,
				     const Theorem& isInta,
				     const Theorem& isIntt) {
  const Expr& e1 = aLEt.getExpr();
  const Expr& e2 = tLEac.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isLE(e1) && isLE(e2),
		"ArithTheoremProducerOld::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // term 't' is the same in both inequalities
    CHECK_SOUND(e1[1] == e2[0],
		"ArithTheoremProducerOld::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // RHS in e2 is (a+c)
    CHECK_SOUND(isPlus(e2[1]) && e2[1].arity() == 2,
		"ArithTheoremProducerOld::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // term 'a' in LHS of e1 and RHS of e2 is the same
    CHECK_SOUND(e1[0] == e2[1][0],
		"ArithTheoremProducerOld::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // 'c' in the RHS of e2 is a positive integer constant
    CHECK_SOUND(e2[1][1].isRational() && e2[1][1].getRational().isInteger()
		&& e2[1][1].getRational() >= 1,
		"ArithTheoremProducerOld::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // Integrality constraints
    const Expr& isIntaExpr = isInta.getExpr();
    const Expr& isInttExpr = isIntt.getExpr();
    CHECK_SOUND(isIntPred(isIntaExpr) && isIntaExpr[0] == e1[0],
		"Wrong integrality constraint:\n e1 = "
		+e1.toString()+"\n isInta = "+isIntaExpr.toString());
    CHECK_SOUND(isIntPred(isInttExpr) && isInttExpr[0] == e1[1],
		"Wrong integrality constraint:\n e1 = "
		+e1.toString()+"\n isIntt = "+isInttExpr.toString());
  }
  vector<Theorem> thms;
  thms.push_back(aLEt);
  thms.push_back(tLEac);
  thms.push_back(isInta);
  thms.push_back(isIntt);
  Assumptions a(thms);
  Proof pf;
  if(withProof()) {
    vector<Expr> es;
    vector<Proof> pfs;
    es.push_back(e1);
    es.push_back(e2);
    es.push_back(isInta.getExpr());
    es.push_back(isIntt.getExpr());
    pfs.push_back(aLEt.getProof());
    pfs.push_back(tLEac.getProof());
    pfs.push_back(isInta.getProof());
    pfs.push_back(isIntt.getProof());
    pf = newPf("finite_interval", es, pfs);
  }
  // Construct GRAY_SHADOW(t, a, 0, c)
  Expr g(grayShadow(e1[1], e1[0], 0, e2[1][1].getRational()));
  return newTheorem(g, a, pf);
}


// Dark & Gray shadows when a <= b
Theorem ArithTheoremProducerOld::darkGrayShadow2ab(const Theorem& betaLEbx,
						const Theorem& axLEalpha,
						const Theorem& isIntAlpha,
						const Theorem& isIntBeta,
						const Theorem& isIntx) {
  const Expr& expr1 = betaLEbx.getExpr();
  const Expr& expr2 = axLEalpha.getExpr();
  const Expr& isIntAlphaExpr = isIntAlpha.getExpr();
  const Expr& isIntBetaExpr = isIntBeta.getExpr();
  const Expr& isIntxExpr = isIntx.getExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(isLE(expr1) && isLE(expr2),
                "ArithTheoremProducerOld::darkGrayShadow2ab: Wrong Kind: " +
                betaLEbx.toString() +  axLEalpha.toString());
  }

  const Expr& beta = expr1[0];
  const Expr& bx = expr1[1];
  const Expr& ax = expr2[0];
  const Expr& alpha = expr2[1];
  Expr a_expr, b_expr, x;
  d_theoryArith->separateMonomial(ax, a_expr, x);
  d_theoryArith->separateMonomial(bx, b_expr, x);
  Rational a = a_expr.getRational();
  Rational b = b_expr.getRational();

  if(CHECK_PROOFS) {
    // Integrality constraints
    CHECK_SOUND(isIntPred(isIntAlphaExpr) && isIntAlphaExpr[0] == alpha,
		"ArithTheoremProducerOld::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n alpha = "
		+alpha.toString()+"\n isIntAlpha = "
		+isIntAlphaExpr.toString());
    CHECK_SOUND(isIntPred(isIntBetaExpr) && isIntBetaExpr[0] == beta,
		"ArithTheoremProducerOld::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n beta = "
		+beta.toString()+"\n isIntBeta = "
		+isIntBetaExpr.toString());
    CHECK_SOUND(isIntPred(isIntxExpr) && isIntxExpr[0] == x,
		"ArithTheoremProducerOld::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n x = "
		+x.toString()+"\n isIntx = "
		+isIntxExpr.toString());
    // NOT FOR NONLINEAR: Expressions ax and bx should match on x
//    CHECK_SOUND(!isMult(ax) || ax.arity() == 2,
//		"ArithTheoremProducerOld::darkGrayShadow2ab:\n ax<=alpha: " +
//                axLEalpha.toString());
//    CHECK_SOUND(!isMult(bx) || (bx.arity() == 2 && bx[1] == x),
//		"ArithTheoremProducerOld::darkGrayShadow2ab:\n beta<=bx: "
//		+betaLEbx.toString()
//		+"\n ax<=alpha: "+ axLEalpha.toString());
    CHECK_SOUND(1 <= a && a <= b && 2 <= b,
		"ArithTheoremProducerOld::darkGrayShadow2ab:\n beta<=bx: "
		+betaLEbx.toString()
		+"\n ax<=alpha: "+ axLEalpha.toString());
  }
  vector<Theorem> thms;
  thms.push_back(betaLEbx);
  thms.push_back(axLEalpha);
  thms.push_back(isIntAlpha);
  thms.push_back(isIntBeta);
  thms.push_back(isIntx);
  Assumptions A(thms);

  Expr bAlpha = multExpr(rat(b), alpha);
  Expr aBeta = multExpr(rat(a), beta);
  Expr t = minusExpr(bAlpha, aBeta);
  Expr d = geExpr(t, rat(a*b-1));
  Expr g = grayShadow(ax, alpha, -a+1, 0);

  Proof pf;
  if(withProof()) {
    vector<Expr> exprs;
    exprs.push_back(expr1);
    exprs.push_back(expr2);
    exprs.push_back(d);
    exprs.push_back(g);

    vector<Proof> pfs;
    pfs.push_back(betaLEbx.getProof());
    pfs.push_back(axLEalpha.getProof());
    pfs.push_back(isIntAlpha.getProof());
    pfs.push_back(isIntBeta.getProof());
    pfs.push_back(isIntx.getProof());

    pf = newPf("dark_grayshadow_2ab", exprs, pfs);
  }

  return newTheorem((d || g), A, pf);
}

// Dark & Gray shadows when b <= a
Theorem ArithTheoremProducerOld::darkGrayShadow2ba(const Theorem& betaLEbx,
						const Theorem& axLEalpha,
						const Theorem& isIntAlpha,
						const Theorem& isIntBeta,
						const Theorem& isIntx) {
  const Expr& expr1 = betaLEbx.getExpr();
  const Expr& expr2 = axLEalpha.getExpr();
  const Expr& isIntAlphaExpr = isIntAlpha.getExpr();
  const Expr& isIntBetaExpr = isIntBeta.getExpr();
  const Expr& isIntxExpr = isIntx.getExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(isLE(expr1) && isLE(expr2),
                "ArithTheoremProducerOld::darkGrayShadow2ba: Wrong Kind: " +
                betaLEbx.toString() +  axLEalpha.toString());
  }

  const Expr& beta = expr1[0];
  const Expr& bx = expr1[1];
  const Expr& ax = expr2[0];
  const Expr& alpha = expr2[1];

  Expr a_expr, b_expr, x;
  d_theoryArith->separateMonomial(ax, a_expr, x);
  d_theoryArith->separateMonomial(bx, b_expr, x);
  Rational a = a_expr.getRational();
  Rational b = b_expr.getRational();

  if(CHECK_PROOFS) {
	// Integrality constraints
    CHECK_SOUND(isIntPred(isIntAlphaExpr) && isIntAlphaExpr[0] == alpha,
		"ArithTheoremProducerOld::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n alpha = "
		+alpha.toString()+"\n isIntAlpha = "
		+isIntAlphaExpr.toString());
    CHECK_SOUND(isIntPred(isIntBetaExpr) && isIntBetaExpr[0] == beta,
		"ArithTheoremProducerOld::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n beta = "
		+beta.toString()+"\n isIntBeta = "
		+isIntBetaExpr.toString());
    CHECK_SOUND(isIntPred(isIntxExpr) && isIntxExpr[0] == x,
		"ArithTheoremProducerOld::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n x = "
		+x.toString()+"\n isIntx = "
		+isIntxExpr.toString());
    // NOT FOR NONLINEAR: Expressions ax and bx should match on x
//    CHECK_SOUND(!isMult(ax) || ax.arity() == 2,
//		"ArithTheoremProducerOld::darkGrayShadow2ba:\n ax<=alpha: " +
//                axLEalpha.toString());
//    CHECK_SOUND(!isMult(bx) || (bx.arity() == 2 && bx[1] == x),
//		"ArithTheoremProducerOld::darkGrayShadow2ba:\n beta<=bx: "
//		+betaLEbx.toString()
//		+"\n ax<=alpha: "+ axLEalpha.toString());
    CHECK_SOUND(1 <= b && b <= a && 2 <= a,
		"ArithTheoremProducerOld::darkGrayShadow2ba:\n beta<=bx: "
		+betaLEbx.toString()
		+"\n ax<=alpha: "+ axLEalpha.toString());
  }
  vector<Theorem> thms;
  thms.push_back(betaLEbx);
  thms.push_back(axLEalpha);
  thms.push_back(isIntAlpha);
  thms.push_back(isIntBeta);
  thms.push_back(isIntx);
  Assumptions A(thms);
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(betaLEbx.getProof());
    pfs.push_back(axLEalpha.getProof());
    pfs.push_back(isIntAlpha.getProof());
    pfs.push_back(isIntBeta.getProof());
    pfs.push_back(isIntx.getProof());

    pf = newPf("dark_grayshadow_2ba", betaLEbx.getExpr(),
	       axLEalpha.getExpr(), pfs);
  }

  Expr bAlpha = multExpr(rat(b), alpha);
  Expr aBeta = multExpr(rat(a), beta);
  Expr t = minusExpr(bAlpha, aBeta);
  Expr d = geExpr(t, rat(a*b-1));
  Expr g = grayShadow(bx, beta, 0, b-1);
  return newTheorem((d || g), A, pf);
}

/*! takes a dark shadow and expands it into an inequality.
*/
Theorem ArithTheoremProducerOld::expandDarkShadow(const Theorem& darkShadow) {
  const Expr& theShadow = darkShadow.getExpr();
  if(CHECK_PROOFS){
    CHECK_SOUND(isDarkShadow(theShadow),
		"ArithTheoremProducerOld::expandDarkShadow: not DARK_SHADOW: " +
		theShadow.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("expand_dark_shadow", theShadow, darkShadow.getProof());
  return newTheorem(leExpr(theShadow[0], theShadow[1]), darkShadow.getAssumptionsRef(), pf);
}


// takes a grayShadow (c1==c2) and expands it into an equality
Theorem ArithTheoremProducerOld::expandGrayShadow0(const Theorem& grayShadow) {
  const Expr& theShadow = grayShadow.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducerOld::expandGrayShadowConst0:"
		" not GRAY_SHADOW: " +
		theShadow.toString());
    CHECK_SOUND(theShadow[2] == theShadow[3],
		"ArithTheoremProducerOld::expandGrayShadow0: c1!=c2: " +
		theShadow.toString());
  }
  Proof pf;
  if(withProof()) pf = newPf("expand_gray_shadowconst0", theShadow,
			     grayShadow.getProof());
  const Expr& v = theShadow[0];
  const Expr& e = theShadow[1];
  return newRWTheorem(v, e + theShadow[2], grayShadow.getAssumptionsRef(), pf);
}


// G ==> (G1 or G2) and (!G1 or !G2),
// where G  = G(x, e, c1, c2),
//       G1 = G(x,e,c1,c)
//       G2 = G(x,e,c+1,c2),
// and    c = floor((c1+c2)/2)
Theorem ArithTheoremProducerOld::splitGrayShadow(const Theorem& gThm) {
  const Expr& theShadow = gThm.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducerOld::expandGrayShadowConst: not a shadow" +
		theShadow.toString());
  }

  const Rational& c1 = theShadow[2].getRational();
  const Rational& c2 = theShadow[3].getRational();

  if(CHECK_PROOFS) {
    CHECK_SOUND(c1.isInteger() && c2.isInteger() && c1 < c2,
		"ArithTheoremProducerOld::expandGrayShadow: " +
		theShadow.toString());
  }

  const Expr& v = theShadow[0];
  const Expr& e = theShadow[1];

  Proof pf;
  Rational c(floor((c1+c2) / 2));
  Expr g1(grayShadow(v, e, c1, c));
  Expr g2(grayShadow(v, e, c+1, c2));

  if(withProof()){
    vector<Expr> exprs;
    exprs.push_back(theShadow);
    exprs.push_back(g1);
    exprs.push_back(g2);
    pf = newPf("split_gray_shadow", exprs, gThm.getProof());
  }

  return newTheorem((g1 || g2) && (!g1 || !g2), gThm.getAssumptionsRef(), pf);
}


Theorem ArithTheoremProducerOld::expandGrayShadow(const Theorem& gThm) {
  const Expr& theShadow = gThm.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducerOld::expandGrayShadowConst: not a shadow" +
		theShadow.toString());
  }

  const Rational& c1 = theShadow[2].getRational();
  const Rational& c2 = theShadow[3].getRational();

  if(CHECK_PROOFS) {
    CHECK_SOUND(c1.isInteger() && c2.isInteger() && c1 < c2,
		"ArithTheoremProducerOld::expandGrayShadow: " +
		theShadow.toString());
  }

  const Expr& v = theShadow[0];
  const Expr& e = theShadow[1];

  Proof pf;
  if(withProof())
    pf = newPf("expand_gray_shadow", theShadow, gThm.getProof());
  Expr ineq1(leExpr(e+rat(c1), v));
  Expr ineq2(leExpr(v, e+rat(c2)));
  return newTheorem(ineq1 && ineq2, gThm.getAssumptionsRef(), pf);
}


// Expanding GRAY_SHADOW(a*x, c, b), where c is a constant
Theorem
ArithTheoremProducerOld::expandGrayShadowConst(const Theorem& gThm) {
  const Expr& theShadow = gThm.getExpr();
  const Expr& ax = theShadow[0];
  const Expr& cExpr = theShadow[1];
  const Expr& bExpr = theShadow[2];

  if(CHECK_PROOFS) {
    CHECK_SOUND(!isMult(ax) || ax[0].isRational(),
		"ArithTheoremProducerOld::expandGrayShadowConst: "
		"'a' in a*x is not a const: " +theShadow.toString());
  }

  Rational a = isMult(ax)? ax[0].getRational() : 1;

  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducerOld::expandGrayShadowConst: "
		"not a GRAY_SHADOW: " +theShadow.toString());
    CHECK_SOUND(a.isInteger() && a >= 1,
		"ArithTheoremProducerOld::expandGrayShadowConst: "
		"'a' is not integer: " +theShadow.toString());
    CHECK_SOUND(cExpr.isRational(),
		"ArithTheoremProducerOld::expandGrayShadowConst: "
		"'c' is not rational" +theShadow.toString());
    CHECK_SOUND(bExpr.isRational() && bExpr.getRational().isInteger(),
		"ArithTheoremProducerOld::expandGrayShadowConst: b not integer: "
		+theShadow.toString());
  }

  const Rational& b = bExpr.getRational();
  const Rational& c = cExpr.getRational();
  Rational j = constRHSGrayShadow(c,b,a);
  // Compute sign(b)*j(c,b,a)
  Rational signB = (b>0)? 1 : -1;
  // |b| (absolute value of b)
  Rational bAbs = abs(b);

  const Assumptions& assump(gThm.getAssumptionsRef());
  Proof pf;
  Theorem conc;  // Conclusion of the rule

  if(bAbs < j) {
    if(withProof())
      pf = newPf("expand_gray_shadow_const_0", theShadow,
		 gThm.getProof());
    conc = newTheorem(d_em->falseExpr(), assump, pf);
  } else if(bAbs < a+j) {
    if(withProof())
      pf = newPf("expand_gray_shadow_const_1", theShadow,
		 gThm.getProof());
    conc = newRWTheorem(ax, rat(c+b-signB*j), assump, pf);
  } else {
    if(withProof())
      pf = newPf("expand_gray_shadow_const", theShadow,
		 gThm.getProof());
    Expr newGrayShadow(Expr(GRAY_SHADOW, ax, cExpr, rat(b-signB*(a+j))));
    conc = newTheorem(ax.eqExpr(rat(c+b-signB*j)).orExpr(newGrayShadow),
		      assump, pf);
  }

  return conc;
}


Theorem
ArithTheoremProducerOld::grayShadowConst(const Theorem& gThm) {
  const Expr& g = gThm.getExpr();
  bool checkProofs(CHECK_PROOFS);
  if(checkProofs) {
    CHECK_SOUND(isGrayShadow(g), "ArithTheoremProducerOld::grayShadowConst("
		+g.toString()+")");
  }

  const Expr& ax = g[0];
  const Expr& e = g[1];
  const Rational& c1 = g[2].getRational();
  const Rational& c2 = g[3].getRational();
  Expr aExpr, x;
  d_theoryArith->separateMonomial(ax, aExpr, x);

  if(checkProofs) {
    CHECK_SOUND(e.isRational() && e.getRational().isInteger(),
		"ArithTheoremProducerOld::grayShadowConst("+g.toString()+")");
    CHECK_SOUND(aExpr.isRational(),
		"ArithTheoremProducerOld::grayShadowConst("+g.toString()+")");
  }

  const Rational& a = aExpr.getRational();
  const Rational& c = e.getRational();

  if(checkProofs) {
    CHECK_SOUND(a.isInteger() && a >= 2,
		"ArithTheoremProducerOld::grayShadowConst("+g.toString()+")");
  }

  Rational newC1 = ceil((c1+c)/a), newC2 = floor((c2+c)/a);
  Expr newG((newC1 > newC2)? d_em->falseExpr()
	    : grayShadow(x, rat(0), newC1, newC2));
  Proof pf;
  if(withProof())
    pf = newPf("gray_shadow_const", g, newG, gThm.getProof());
  return newTheorem(newG, gThm.getAssumptionsRef(), pf);
}


Rational ArithTheoremProducerOld::constRHSGrayShadow(const Rational& c,
						  const Rational& b,
						  const Rational& a) {
  DebugAssert(c.isInteger() &&
	      b.isInteger() &&
	      a.isInteger() &&
	      b != 0,
	      "ArithTheoremProducerOld::constRHSGrayShadow: a, b, c must be ints");
  if (b > 0)
    return mod(c+b, a);
  else
    return mod(a-(c+b), a);
}

/*! Takes a Theorem(\\alpha < \\beta) and returns
 *  Theorem(\\alpha < \\beta <==> \\alpha <= \\beta -1)
 * where \\alpha and \\beta are integer expressions
 */
Theorem ArithTheoremProducerOld::lessThanToLE(const Theorem& less,
					   const Theorem& isIntLHS,
					   const Theorem& isIntRHS,
					   bool changeRight) {
  const Expr& ineq = less.getExpr();
  const Expr& isIntLHSexpr = isIntLHS.getExpr();
  const Expr& isIntRHSexpr = isIntRHS.getExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(isLT(ineq),
		"ArithTheoremProducerOld::LTtoLE: ineq must be <");
    // Integrality check
    CHECK_SOUND(isIntPred(isIntLHSexpr)	&& isIntLHSexpr[0] == ineq[0],
		"ArithTheoremProducerOld::lessThanToLE: bad integrality check:\n"
		" ineq = "+ineq.toString()+"\n isIntLHS = "
		+isIntLHSexpr.toString());
    CHECK_SOUND(isIntPred(isIntRHSexpr) && isIntRHSexpr[0] == ineq[1],
		"ArithTheoremProducerOld::lessThanToLE: bad integrality check:\n"
		" ineq = "+ineq.toString()+"\n isIntRHS = "
		+isIntRHSexpr.toString());
  }
  vector<Theorem> thms;
  thms.push_back(less);
  thms.push_back(isIntLHS);
  thms.push_back(isIntRHS);
  Assumptions a(thms);
  Proof pf;
  Expr le = changeRight?
    leExpr(ineq[0], ineq[1] + rat(-1))
    : leExpr(ineq[0] + rat(1), ineq[1]);
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(less.getProof());
    pfs.push_back(isIntLHS.getProof());
    pfs.push_back(isIntRHS.getProof());
    pf = newPf(changeRight? "lessThan_To_LE_rhs" : "lessThan_To_LE_lhs",
	       ineq,le, pfs);
  }

  return newRWTheorem(ineq, le, a, pf);
}


/*! \param eqn is an equation 0 = a.x or 0 = c + a.x
 *  \param isIntx is a proof of IS_INTEGER(x)
 *
 * \return the theorem 0 = c + a.x <==> x=-c/a if -c/a is int else
 *  return the theorem 0 = c + a.x <==> false.
 *
 * It also handles the special case of 0 = a.x <==> x = 0
 */
Theorem
ArithTheoremProducerOld::intVarEqnConst(const Expr& eqn,
				     const Theorem& isIntx) {
  const Expr& left(eqn[0]);
  const Expr& right(eqn[1]);
  const Expr& isIntxexpr(isIntx.getExpr());

  if(CHECK_PROOFS) {
    CHECK_SOUND((isMult(right) && right[0].isRational())
                || (right.arity() == 2 && isPlus(right)
                    && right[0].isRational()
                    && ((!isMult(right[1]) || right[1][0].isRational()))),
                "ArithTheoremProducerOld::intVarEqnConst: "
		"rhs has a wrong format: " + right.toString());
    CHECK_SOUND(left.isRational() && 0 == left.getRational(),
                "ArithTheoremProducerOld:intVarEqnConst:left is not a zero: " +
                left.toString());
  }
  // Integrality constraint
  Expr x(right);
  Rational a(1), c(0);
  if(isMult(right)) {
    Expr aExpr;
    d_theoryArith->separateMonomial(right, aExpr, x);
    a = aExpr.getRational();
  } else { // right is a PLUS
    c = right[0].getRational();
    Expr aExpr;
    d_theoryArith->separateMonomial(right[1], aExpr, x);
    a = aExpr.getRational();
  }
  if(CHECK_PROOFS) {
    CHECK_SOUND(isIntPred(isIntxexpr) && isIntxexpr[0] == x,
                "ArithTheoremProducerOld:intVarEqnConst: "
		"bad integrality constraint:\n right = " +
                right.toString()+"\n isIntx = "+isIntxexpr.toString());
    CHECK_SOUND(a!=0, "ArithTheoremProducerOld:intVarEqnConst: eqn = "
		+eqn.toString());
  }
  const Assumptions& assump(isIntx.getAssumptionsRef());

  /*
      Proof pf;
  if(withProof())
    pf = newPf("int_const_eq", eqn, isIntx.getProof());

  // Solve for x:   x = r = -c/a
  Rational r(-c/a);

  if(r.isInteger()){
    return newRWTheorem(eqn, x.eqExpr(rat(r)), assump, pf);
  else
    return newRWTheorem(eqn, d_em->falseExpr(), assump, pf);
  */

  Proof pf;
  // Solve for x:   x = r = -c/a
  Rational r(-c/a);

  if(r.isInteger()){
    if(withProof())
      pf = newPf("int_const_eq", eqn, x.eqExpr(rat(r)),isIntx.getProof());
    return newRWTheorem(eqn, x.eqExpr(rat(r)), assump, pf);
  }
  else{
    if(withProof())
      pf = newPf("int_const_eq", eqn, d_em->falseExpr(),isIntx.getProof());
    return newRWTheorem(eqn, d_em->falseExpr(), assump, pf);
  }
}


Expr
ArithTheoremProducerOld::create_t(const Expr& eqn) {
  const Expr& lhs = eqn[0];
  DebugAssert(isMult(lhs),
              CLASS_NAME "create_t : lhs must be a MULT"
              + lhs.toString());
  const Expr& x = lhs[1];
  Rational m = lhs[0].getRational()+1;
  DebugAssert(m > 0, "ArithTheoremProducerOld::create_t: m = "+m.toString());
  vector<Expr> kids;
  if(isPlus(eqn[1]))
    sumModM(kids, eqn[1], m, m);
  else
    kids.push_back(monomialModM(eqn[1], m, m));

  kids.push_back(multExpr(rat(1/m), x));
  return plusExpr(kids);
}

Expr
ArithTheoremProducerOld::create_t2(const Expr& lhs, const Expr& rhs,
				const Expr& sigma) {
  Rational m = lhs[0].getRational()+1;
  DebugAssert(m > 0, "ArithTheoremProducerOld::create_t2: m = "+m.toString());
  vector<Expr> kids;
  if(isPlus(rhs))
    sumModM(kids, rhs, m, -1);
  else {
    kids.push_back(rat(0)); // For canonical form
    Expr monom = monomialModM(rhs, m, -1);
    if(!monom.isRational())
      kids.push_back(monom);
    else
      DebugAssert(monom.getRational() == 0, "");
  }
  kids.push_back(rat(m)*sigma);
  return plusExpr(kids);
}

Expr
ArithTheoremProducerOld::create_t3(const Expr& lhs, const Expr& rhs,
				const Expr& sigma) {
  const Rational& a = lhs[0].getRational();
  Rational m = a+1;
  DebugAssert(m > 0, "ArithTheoremProducerOld::create_t3: m = "+m.toString());
  vector<Expr> kids;
  if(isPlus(rhs))
    sumMulF(kids, rhs, m, 1);
  else {
    kids.push_back(rat(0)); // For canonical form
    Expr monom = monomialMulF(rhs, m, 1);
    if(!monom.isRational())
      kids.push_back(monom);
    else
      DebugAssert(monom.getRational() == 0, "");
  }
  kids.push_back(rat(-a)*sigma);
  return plusExpr(kids);
}

Rational
ArithTheoremProducerOld::modEq(const Rational& i, const Rational& m) {
  DebugAssert(m > 0, "ArithTheoremProducerOld::modEq: m = "+m.toString());
  Rational half(1,2);
  Rational res((i - m*(floor((i/m) + half))));
  TRACE("arith eq", "modEq("+i.toString()+", "+m.toString()+") = ", res, "");
  return res;
}

Rational
ArithTheoremProducerOld::f(const Rational& i, const Rational& m) {
  DebugAssert(m > 0, "ArithTheoremProducerOld::f: m = "+m.toString());
  Rational half(1,2);
  return (floor(i/m + half)+modEq(i,m));
}

void
ArithTheoremProducerOld::sumModM(vector<Expr>& summands, const Expr& sum,
                              const Rational& m, const Rational& divisor) {
  DebugAssert(divisor != 0, "ArithTheoremProducerOld::sumModM: divisor = "
	      +divisor.toString());
  Expr::iterator i = sum.begin();
  DebugAssert(i != sum.end(), CLASS_NAME "::sumModM");
  Rational C = i->getRational();
  C = modEq(C,m)/divisor;
  summands.push_back(rat(C));
  i++;
  for(Expr::iterator iend=sum.end(); i!=iend; ++i) {
    Expr monom = monomialModM(*i, m, divisor);
    if(!monom.isRational())
      summands.push_back(monom);
    else
      DebugAssert(monom.getRational() == 0, "");
  }
}

Expr
ArithTheoremProducerOld::monomialModM(const Expr& i,
                                   const Rational& m, const Rational& divisor)
{
  DebugAssert(divisor != 0, "ArithTheoremProducerOld::monomialModM: divisor = "
	      +divisor.toString());
  Expr res;
  if(isMult(i)) {
    Rational ai = i[0].getRational();
    ai = modEq(ai,m)/divisor;
    if(0 == ai) res = rat(0);
    else if(1 == ai && i.arity() == 2) res = i[1];
    else {
      vector<Expr> kids = i.getKids();
      kids[0] = rat(ai);
      res = multExpr(kids);
    }
  } else { // It's a single variable
    Rational ai = modEq(1,m)/divisor;
    if(1 == ai) res = i;
    else res = rat(ai)*i;
  }
  DebugAssert(!res.isNull(), "ArithTheoremProducerOld::monomialModM()");
  TRACE("arith eq", "monomialModM(i="+i.toString()+", m="+m.toString()
	+", div="+divisor.toString()+") = ", res, "");
  return res;
}

void
ArithTheoremProducerOld::sumMulF(vector<Expr>& summands, const Expr& sum,
                              const Rational& m, const Rational& divisor) {
  DebugAssert(divisor != 0, "ArithTheoremProducerOld::sumMulF: divisor = "
	      +divisor.toString());
  Expr::iterator i = sum.begin();
  DebugAssert(i != sum.end(), CLASS_NAME "::sumModM");
  Rational C = i->getRational();
  C = f(C,m)/divisor;
  summands.push_back(rat(C));
  i++;
  for(Expr::iterator iend=sum.end(); i!=iend; ++i) {
    Expr monom = monomialMulF(*i, m, divisor);
    if(!monom.isRational())
      summands.push_back(monom);
    else
      DebugAssert(monom.getRational() == 0, "");
  }
}

Expr
ArithTheoremProducerOld::monomialMulF(const Expr& i,
                                   const Rational& m, const Rational& divisor)
{
  DebugAssert(divisor != 0, "ArithTheoremProducerOld::monomialMulF: divisor = "
	      +divisor.toString());
  Rational ai = isMult(i) ? (i)[0].getRational() : 1;
  Expr xi = isMult(i) ? (i)[1] : (i);
  ai = f(ai,m)/divisor;
  if(0 == ai) return rat(0);
  if(1 == ai) return xi;
  return multExpr(rat(ai), xi);
}

// This recursive function accepts a term, t, and a 'map' of
// substitutions [x1/t1, x2/t2,...,xn/tn].  it returns a t' which is
// basically t[x1/t1,x2/t2...xn/tn]
Expr
ArithTheoremProducerOld::substitute(const Expr& term, ExprMap<Expr>& eMap)
{
  ExprMap<Expr>::iterator i, iend = eMap.end();

  i = eMap.find(term);
  if(iend != i)
    return (*i).second;

  if (isMult(term)) {
    //in this case term is of the form c.x
    i = eMap.find(term[1]);
    if(iend != i)
      return term[0]*(*i).second;
    else
      return term;
  }

  if(isPlus(term)) {
    vector<Expr> output;
    for(Expr::iterator j = term.begin(), jend = term.end(); j != jend; ++j)
      output.push_back(substitute(*j, eMap));
    return plusExpr(output);
  }
  return term;
}

bool ArithTheoremProducerOld::greaterthan(const Expr & l, const Expr & r)
{
  //    DebugAssert(l != r, "");
  if (l==r) return false;

  switch(l.getKind()) {
  case RATIONAL_EXPR:
    DebugAssert(!r.isRational(), "");
    return true;
    break;
  case POW:
    switch (r.getKind()) {
    case RATIONAL_EXPR:
      // TODO:
      // alternately I could return (not greaterthan(r,l))
      return false;
      break;
    case POW:
      // x^n > y^n if x > y
      // x^n1 > x^n2 if n1 > n2
      return
        ((r[1] < l[1]) ||
         ((r[1]==l[1]) && (r[0].getRational() < l[0].getRational())));
      break;

    case MULT:
      DebugAssert(r.arity() > 1, "");
      DebugAssert((r.arity() > 2) || (r[1] != l), "");
      if (r[1] == l) return false;
      return greaterthan(l, r[1]);
      break;
    case PLUS:
      DebugAssert(false, "");
      return true;
      break;
    default:
      // leaf
      return ((r < l[1]) || ((r == l[1]) && l[0].getRational() > 1));
      break;
    }
    break;
  case MULT:
    DebugAssert(l.arity() > 1, "");
    switch (r.getKind()) {
    case RATIONAL_EXPR:
      return false;
      break;
    case POW:
      DebugAssert(l.arity() > 1, "");
      DebugAssert((l.arity() > 2) || (l[1] != r), "");
      // TODO:
      // alternately return (not greaterthan(r,l)
      return ((l[1] == r) || greaterthan(l[1], r));
      break;
    case MULT:
      {

        DebugAssert(r.arity() > 1, "");
        Expr::iterator i = l.begin();
        Expr::iterator j = r.begin();
        ++i;
        ++j;
        for (; i != l.end() && j != r.end(); ++i, ++j) {
          if (*i == *j)
            continue;
          return greaterthan(*i,*j);
        }
        DebugAssert(i != l.end() || j != r.end(), "");
        if (i == l.end()) {
          // r is bigger
          return false;
        }
        else
          {
            // l is bigger
            return true;
          }
      }
      break;
    case PLUS:
      DebugAssert(false, "");
      return true;
      break;
    default:
      // leaf
      DebugAssert((l.arity() > 2) || (l[1] != r), "");
      return ((l[1] == r) || greaterthan(l[1], r));
      break;
    }
    break;
  case PLUS:
    DebugAssert(false, "");
    return true;
    break;
  default:
    // leaf
    switch (r.getKind()) {
    case RATIONAL_EXPR:
      return false;
      break;
    case POW:
      return ((r[1] < l) || ((r[1] == l) && (r[0].getRational() < 1)));
      break;
    case MULT:
      DebugAssert(r.arity() > 1, "");
      DebugAssert((r.arity() > 2) || (r[1] != l), "");
      if (l == r[1]) return false;
      return greaterthan(l,r[1]);
      break;
    case PLUS:
      DebugAssert(false, "");
      return true;
      break;
    default:
      // leaf
      return (r < l);
      break;
    }
    break;
  }
}


/*! IS_INTEGER(x) |= EXISTS (y : INT) y = x
 * where x is not already known to be an integer.
 */
Theorem ArithTheoremProducerOld::IsIntegerElim(const Theorem& isIntx)
{
  Expr expr = isIntx.getExpr();
  if (CHECK_PROOFS) {
    CHECK_SOUND(expr.getKind() == IS_INTEGER,
                "Expected IS_INTEGER predicate");
  }
  expr = expr[0];
  DebugAssert(!d_theoryArith->isInteger(expr), "Expected non-integer");

  Assumptions a(isIntx);
  Proof pf;

  if (withProof())
  {
    pf = newPf("isIntElim", isIntx.getProof());
  }

  Expr newVar = d_em->newBoundVarExpr(d_theoryArith->intType());
  Expr res = d_em->newClosureExpr(EXISTS, newVar, newVar.eqExpr(expr));

  return newTheorem(res, a, pf);
}


Theorem
ArithTheoremProducerOld::eqElimIntRule(const Theorem& eqn, const Theorem& isIntx,
				    const vector<Theorem>& isIntVars) {
  TRACE("arith eq", "eqElimIntRule(", eqn.getExpr(), ") {");
  Proof pf;

  if(CHECK_PROOFS)
    CHECK_SOUND(eqn.isRewrite(),
                "ArithTheoremProducerOld::eqElimInt: input must be an equation" +
                eqn.toString());

  const Expr& lhs = eqn.getLHS();
  const Expr& rhs = eqn.getRHS();
  Expr a, x;
  d_theoryArith->separateMonomial(lhs, a, x);

  if(CHECK_PROOFS) {
    // Checking LHS
    const Expr& isIntxe = isIntx.getExpr();
    CHECK_SOUND(isIntPred(isIntxe) && isIntxe[0] == x,
		"ArithTheoremProducerOld::eqElimInt\n eqn = "
		+eqn.getExpr().toString()
		+"\n isIntx = "+isIntxe.toString());
    CHECK_SOUND(isRational(a) && a.getRational().isInteger()
		&& a.getRational() >= 2,
		"ArithTheoremProducerOld::eqElimInt:\n lhs = "+lhs.toString());
    // Checking RHS
    // It cannot be a division (we don't handle it)
    CHECK_SOUND(!isDivide(rhs),
		"ArithTheoremProducerOld::eqElimInt:\n rhs = "+rhs.toString());
    // If it's a single monomial, then it's the only "variable"
    if(!isPlus(rhs)) {
      Expr c, v;
      d_theoryArith->separateMonomial(rhs, c, v);
      CHECK_SOUND(isIntVars.size() == 1
		  && isIntPred(isIntVars[0].getExpr())
		  && isIntVars[0].getExpr()[0] == v
		  && isRational(c) && c.getRational().isInteger(),
		  "ArithTheoremProducerOld::eqElimInt:\n rhs = "+rhs.toString()
		  +"isIntVars.size = "+int2string(isIntVars.size()));
    } else { // RHS is a plus
      CHECK_SOUND(isIntVars.size() + 1 == (size_t)rhs.arity(),
		  "ArithTheoremProducerOld::eqElimInt: rhs = "+rhs.toString());
      // Check the free constant
      CHECK_SOUND(isRational(rhs[0]) && rhs[0].getRational().isInteger(),
		  "ArithTheoremProducerOld::eqElimInt: rhs = "+rhs.toString());
      // Check the vars
      for(size_t i=0, iend=isIntVars.size(); i<iend; ++i) {
	Expr c, v;
	d_theoryArith->separateMonomial(rhs[i+1], c, v);
	const Expr& isInt(isIntVars[i].getExpr());
	CHECK_SOUND(isIntPred(isInt) && isInt[0] == v
		    && isRational(c) && c.getRational().isInteger(),
		    "ArithTheoremProducerOld::eqElimInt:\n rhs["+int2string(i+1)
		    +"] = "+rhs[i+1].toString()
		    +"\n isInt = "+isInt.toString());
      }
    }
  }

  // Creating a fresh bound variable
  static int varCount(0);
  Expr newVar = d_em->newBoundVarExpr("_int_var", int2string(varCount++));
  newVar.setType(intType());
  Expr t2 = create_t2(lhs, rhs, newVar);
  Expr t3 = create_t3(lhs, rhs, newVar);
  vector<Expr> vars;
  vars.push_back(newVar);
  Expr res = d_em->newClosureExpr(EXISTS, vars,
                                  x.eqExpr(t2) && rat(0).eqExpr(t3));

  vector<Theorem> thms(isIntVars);
  thms.push_back(isIntx);
  thms.push_back(eqn);
  Assumptions assump(thms);

  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(eqn.getProof());
    pfs.push_back(isIntx.getProof());
    vector<Theorem>::const_iterator i=isIntVars.begin(), iend=isIntVars.end();
    for(; i!=iend; ++i)
      pfs.push_back(i->getProof());
    pf = newPf("eq_elim_int", eqn.getExpr(), res, pfs);
  }

  Theorem thm(newTheorem(res, assump, pf));
  TRACE("arith eq", "eqElimIntRule => ", thm.getExpr(), " }");
  return thm;
}


Theorem
ArithTheoremProducerOld::isIntConst(const Expr& e) {
  Proof pf;

  if(CHECK_PROOFS) {
    CHECK_SOUND(isIntPred(e) && e[0].isRational(),
		"ArithTheoremProducerOld::isIntConst(e = "
		+e.toString()+")");
  }
  if(withProof())
    pf = newPf("is_int_const", e);
  bool isInt = e[0].getRational().isInteger();
  return newRWTheorem(e, isInt? d_em->trueExpr() : d_em->falseExpr(), Assumptions::emptyAssump(), pf);
}


Theorem
ArithTheoremProducerOld::equalLeaves1(const Theorem& thm)
{
  Proof pf;
  const Expr& e = thm.getRHS();

  if (CHECK_PROOFS) {
    CHECK_SOUND(e[1].getKind() == RATIONAL_EXPR &&
		e[1].getRational() == Rational(0) &&
		e[0].getKind() == PLUS &&
		e[0].arity() == 3 &&
		e[0][0].getKind() == RATIONAL_EXPR &&
		e[0][0].getRational() == Rational(0) &&
		e[0][1].getKind() == MULT &&
		e[0][1].arity() == 2 &&
		e[0][1][0].getKind() == RATIONAL_EXPR &&
		e[0][1][0].getRational() == Rational(-1),
		"equalLeaves1");
  }
  if (withProof())
  {
    vector<Proof> pfs;
    pfs.push_back(thm.getProof());
    pf = newPf("equalLeaves1", e, pfs);
  }
  return newRWTheorem(e, e[0][1][1].eqExpr(e[0][2]), thm.getAssumptionsRef(), pf);
}


Theorem
ArithTheoremProducerOld::equalLeaves2(const Theorem& thm)
{
  Proof pf;
  const Expr& e = thm.getRHS();

  if (CHECK_PROOFS) {
    CHECK_SOUND(e[0].getKind() == RATIONAL_EXPR &&
		e[0].getRational() == Rational(0) &&
		e[1].getKind() == PLUS &&
		e[1].arity() == 3 &&
		e[1][0].getKind() == RATIONAL_EXPR &&
		e[1][0].getRational() == Rational(0) &&
		e[1][1].getKind() == MULT &&
		e[1][1].arity() == 2 &&
		e[1][1][0].getKind() == RATIONAL_EXPR &&
		e[1][1][0].getRational() == Rational(-1),
		"equalLeaves2");
  }
  if (withProof())
  {
    vector<Proof> pfs;
    pfs.push_back(thm.getProof());
    pf = newPf("equalLeaves2", e, pfs);
  }
  return newRWTheorem(e, e[1][1][1].eqExpr(e[1][2]), thm.getAssumptionsRef(), pf);
}


Theorem
ArithTheoremProducerOld::equalLeaves3(const Theorem& thm)
{
  Proof pf;
  const Expr& e = thm.getRHS();

  if (CHECK_PROOFS) {
    CHECK_SOUND(e[1].getKind() == RATIONAL_EXPR &&
		e[1].getRational() == Rational(0) &&
		e[0].getKind() == PLUS &&
		e[0].arity() == 3 &&
		e[0][0].getKind() == RATIONAL_EXPR &&
		e[0][0].getRational() == Rational(0) &&
		e[0][2].getKind() == MULT &&
		e[0][2].arity() == 2 &&
		e[0][2][0].getKind() == RATIONAL_EXPR &&
		e[0][2][0].getRational() == Rational(-1),
		"equalLeaves3");
  }
  if (withProof())
  {
    vector<Proof> pfs;
    pfs.push_back(thm.getProof());
    pf = newPf("equalLeaves3", e, pfs);
  }
  return newRWTheorem(e, e[0][2][1].eqExpr(e[0][1]), thm.getAssumptionsRef(), pf);
}


Theorem
ArithTheoremProducerOld::equalLeaves4(const Theorem& thm)
{
  Proof pf;
  const Expr& e = thm.getRHS();

  if (CHECK_PROOFS) {
    CHECK_SOUND(e[0].getKind() == RATIONAL_EXPR &&
		e[0].getRational() == Rational(0) &&
		e[1].getKind() == PLUS &&
		e[1].arity() == 3 &&
		e[1][0].getKind() == RATIONAL_EXPR &&
		e[1][0].getRational() == Rational(0) &&
		e[1][2].getKind() == MULT &&
		e[1][2].arity() == 2 &&
		e[1][2][0].getKind() == RATIONAL_EXPR &&
		e[1][2][0].getRational() == Rational(-1),
		"equalLeaves4");
  }
  if (withProof())
  {
    vector<Proof> pfs;
    pfs.push_back(thm.getProof());
    pf = newPf("equalLeaves4", e, pfs);
  }
  return newRWTheorem(e, e[1][2][1].eqExpr(e[1][1]), thm.getAssumptionsRef(), pf);
}

Theorem
ArithTheoremProducerOld::diseqToIneq(const Theorem& diseq) {
  Proof pf;

  const Expr& e = diseq.getExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot() && e[0].isEq(),
		"ArithTheoremProducerOld::diseqToIneq: expected disequality:\n"
		" e = "+e.toString());
  }

  const Expr& x = e[0][0];
  const Expr& y = e[0][1];

  if(withProof())
    pf = newPf(e, diseq.getProof());
  return newTheorem(ltExpr(x,y).orExpr(gtExpr(x,y)), diseq.getAssumptionsRef(), pf);
}

Theorem ArithTheoremProducerOld::dummyTheorem(const Expr& e) {
	Proof pf;
	return newRWTheorem(e, d_em->trueExpr(), Assumptions::emptyAssump(), pf);
}

Theorem ArithTheoremProducerOld::oneElimination(const Expr& e) {

	// Check soundness
	if (CHECK_PROOFS)
		CHECK_SOUND(isMult(e) &&
					e.arity() == 2 &&
		            e[0].isRational() &&
		            e[0].getRational() == 1,
		            "oneElimination: input must be a multiplication by one" + e.toString());

	// The proof object that we will us
	Proof pf;

	// Setup the proof if needed
	if (withProof())
		pf = newPf("oneElimination", e);

	// Return the rewrite theorem that explains the phenomenon
	return newRWTheorem(e, e[1], Assumptions::emptyAssump(), pf);
}

Theorem ArithTheoremProducerOld::clashingBounds(const Theorem& lowerBound, const Theorem& upperBound) {

	// Get the expressions
	const Expr& lowerBoundExpr = lowerBound.getExpr();
	const Expr& upperBoundExpr = upperBound.getExpr();

	// Check soundness
	if (CHECK_PROOFS) {
		CHECK_SOUND(isLE(lowerBoundExpr) || isLT(lowerBoundExpr), "clashingBounds: lowerBound should be >= or > " + lowerBoundExpr.toString());
		CHECK_SOUND(isGE(upperBoundExpr) || isGT(upperBoundExpr), "clashingBounds: upperBound should be <= or < " + upperBoundExpr.toString());
		CHECK_SOUND(lowerBoundExpr[0].isRational(), "clashingBounds: lowerBound left side should be a rational " + lowerBoundExpr.toString());
		CHECK_SOUND(upperBoundExpr[0].isRational(), "clashingBounds: upperBound left side should be a rational " + upperBoundExpr.toString());
		CHECK_SOUND(lowerBoundExpr[1] == upperBoundExpr[1], "clashingBounds: bounds not on the same term " + lowerBoundExpr.toString() + ", " + upperBoundExpr.toString());

		// Get the bounds
		Rational lowerBoundR = lowerBoundExpr[0].getRational();
		Rational upperBoundR = upperBoundExpr[0].getRational();

		if (isLE(lowerBoundExpr) && isGE(upperBoundExpr)) {
			CHECK_SOUND(upperBoundR < lowerBoundR, "clashingBounds: bounds are satisfiable");
		} else {
			CHECK_SOUND(upperBoundR <= lowerBoundR, "clashingBounds: bounds are satisfiable");
		}
	}

	// The proof object that we will use
	Proof pf;
	// Setup the proof if needed
	if (withProof())
		pf = newPf("clashingBounds", lowerBoundExpr, upperBoundExpr);

	// Put the bounds expressions in the assumptions
	Assumptions assumptions;
	assumptions.add(lowerBound);
	assumptions.add(upperBound);

	// Return the theorem
	return newTheorem(d_em->falseExpr(), assumptions, pf);
}

Theorem ArithTheoremProducerOld::addInequalities(const Theorem& thm1, const Theorem& thm2) {

	// Get the expressions of the theorem
	const Expr& expr1 = thm1.getExpr();
	const Expr& expr2 = thm2.getExpr();

	// Check soundness
	if (CHECK_PROOFS) {

		CHECK_SOUND(isIneq(expr1), "addInequalities: expecting an inequality for thm1, got " + expr1.toString());
		CHECK_SOUND(isIneq(expr2), "addInequalities: expecting an inequality for thm2, got " + expr2.toString());

		if (isLE(expr1) || isLT(expr1))
			CHECK_SOUND(isLE(expr2) || isLT(expr2), "addInequalities: expr2 should be <(=) also " + expr2.toString());
		if (isGE(expr1) || isGT(expr1))
			CHECK_SOUND(isGE(expr2) || isGT(expr2), "addInequalities: expr2 should be >(=) also" + expr2.toString());
	}

	// Create the assumptions
	Assumptions a(thm1, thm2);

  	// Get the kinds of the inequalitites
  	int kind1  = expr1.getKind();
  	int kind2  = expr2.getKind();

  	// Set-up the resulting inequality
  	int kind = (kind1 == kind2) ? kind1 : ((kind1 == LT) || (kind2 == LT))? LT : GT;

  	// Create the proof object
  	Proof pf;
  	if(withProof()) {
    	vector<Proof> pfs;
    	pfs.push_back(thm1.getProof());
    	pfs.push_back(thm2.getProof());
    	pf = newPf("addInequalities", expr1, expr2, pfs);
  	}

  	// Create the new expressions
  	Expr leftSide  = plusExpr(expr1[0], expr2[0]);
  	Expr rightSide = plusExpr(expr1[1], expr2[1]);

  	// Return the theorem
  	return newTheorem(Expr(kind, leftSide, rightSide), a, pf);
}

//
// 0 <= c1 + t
// ==> 0 <= c2 + t
// if c2 > c1
Theorem ArithTheoremProducerOld::implyWeakerInequality(const Expr& expr1, const Expr& expr2) {

	// Check soundness
	if (CHECK_PROOFS) {

		// Both must be inequalitites
		CHECK_SOUND(isIneq(expr1), "implyWeakerInequality: expr1 should be an inequality" + expr1.toString());
		CHECK_SOUND(isIneq(expr2), "implyWeakerInequality: expr1 should be an inequality" + expr2.toString());

		// Left sides must be zero
		CHECK_SOUND(expr1[0].isRational() && expr1[0].getRational() == 0, "implyWeakerInequality: expr1 should have a rational on the left side" + expr1.toString());
		CHECK_SOUND(expr2[0].isRational() && expr2[0].getRational() == 0, "implyWeakerInequality: expr2 should have a rational on the left side" + expr2.toString());

		// Get the expr1 monomials and constant 0 <= c1 + t1
		Rational c1 = 0;
		vector<Expr> t1_children;
		if (isPlus(expr1[1])) {
			int start_i = 0;
			if (expr1[1][0].isRational()) {
				start_i = 1;
				c1 = expr1[1][0].getRational();
			}
			int end_i = expr1[1].arity();
		    for(int i = start_i; i < end_i; i ++) {
		    	const Expr& term = expr1[1][i];
				t1_children.push_back(term);
			}
		} else
			t1_children.push_back(expr1[1]);
		Expr t1 = (t1_children.size() > 1 ? plusExpr(t1_children) : t1_children[0]);

		// Get the expr1 monomials and constant 0 <= c1 + t1
		Rational c2 = 0;
		vector<Expr> t2_children;
		if (isPlus(expr2[1])) {
			int start_i = 0;
			if (expr2[1][0].isRational()) {
				start_i = 1;
				c2 = expr2[1][0].getRational();
			}
			int end_i = expr2[1].arity();
		    for(int i = start_i; i < end_i; i ++) {
		    	const Expr& term = expr2[1][i];
				t2_children.push_back(term);
			}
		} else
			t2_children.push_back(expr2[1]);
		Expr t2 = (t2_children.size() > 1 ? plusExpr(t2_children) : t2_children[0]);

		CHECK_SOUND(t2 == t1, "implyWeakerInequality: terms different " + t1.toString() + " vs " + t2.toString());
		CHECK_SOUND(c2 > c1 || (c2 == c1 && !(expr1.getKind() == LE && expr2.getKind() == LT)), "implyWeakerInequality: c2 is not bigger than c1" + expr1.toString() + " --> " + expr2.toString());
	}
  	// Create the proof object
  	Proof pf;
  	if(withProof())	pf = newPf("implyWeakerInequality", expr1, expr2);

	// Return the theorem
	return newTheorem(expr1.impExpr(expr2), Assumptions::emptyAssump(), pf);
}

// Takes
// Expr1: 0 <= c1 + t1
// Expr2: 0 <= c2 + t2    (t2 is -t1)
// if c1 + c2 < 0 then Expr1 => !Expr2
//

Theorem ArithTheoremProducerOld::implyNegatedInequality(const Expr& expr1, const Expr& expr2) {

	// Check soundness
	// Check soundness
	if (CHECK_PROOFS) {

		// Both must be inequalitites
		CHECK_SOUND(isIneq(expr1), "implyNegatedInequality: expr1 should be an inequality" + expr1.toString());
		CHECK_SOUND(isIneq(expr2), "implyNegatedInequality: expr1 should be an inequality" + expr2.toString());

		// Left sides must be zero
		CHECK_SOUND(expr1[0].isRational() && expr1[0].getRational() == 0, "implyNegatedInequality: expr1 should have a rational on the left side" + expr1.toString());
		CHECK_SOUND(expr2[0].isRational() && expr2[0].getRational() == 0, "implyNegatedInequality: expr2 should have a rational on the left side" + expr2.toString());

		// Get the expr1 monomials and constant 0 <= c1 + t1
		Rational c1 = 0;
		vector<Expr> t1_children;
		if (isPlus(expr1[1])) {
			int start_i = 0;
			if (expr1[1][0].isRational()) {
				start_i = 1;
				c1 = expr1[1][0].getRational();
			}
			int end_i = expr1[1].arity();
		    for(int i = start_i; i < end_i; i ++) {
		    	const Expr& term = expr1[1][i];
				t1_children.push_back(term);
			}
		} else
			t1_children.push_back(expr1[1]);
		Expr t1 = (t1_children.size() > 1 ? plusExpr(t1_children) : t1_children[0]);

		// Get the expr1 monomials and constant 0 <= c1 + t1
		Rational c2 = 0;
		vector<Expr> t2_children;
		if (isPlus(expr2[1])) {
			int start_i = 0;
			if (expr2[1][0].isRational()) {
				start_i = 1;
				c2 = expr2[1][0].getRational();
			}
			int end_i = expr2[1].arity();
		    for(int i = start_i; i < end_i; i ++) {
		    	const Expr& term = expr2[1][i];
				t2_children.push_back(term);
			}
		} else
			t2_children.push_back(expr2[1]);
		Expr t2 = (t2_children.size() > 1 ? plusExpr(t2_children) : t2_children[0]);

		// t1 shoud be -t2
		if (isPlus(t1) && isPlus(t2)) {
			CHECK_SOUND(t1.arity() == t2.arity(), "implyNegatedInequality: t1 should be -t2 : " + t1.toString() + " vs " + t2.toString());
			for (int i = 0; i < t1.arity(); i++) {
				Expr term_t1 = t1[i];
				Expr term_t2 = t2[i];
				Rational t1_c = (isMult(term_t1) ? term_t1[0].getRational() : 1);
				term_t1 = (isMult(term_t1) ? term_t1[1] : term_t1);
				Rational t2_c = (isMult(term_t2) ? term_t2[0].getRational() : 1);
				term_t2 = (isMult(term_t2) ? term_t2[1] : term_t2);
				CHECK_SOUND(t1_c == - t2_c, "implyNegatedInequality: t1 should be -t2 : " + t1.toString() + " vs " + t2.toString());
				CHECK_SOUND(term_t1 == term_t2, "implyNegatedInequality: t1 should be -t2 : " + t1.toString() + " vs " + t2.toString());
			}
		} else {
			Rational t1_c = (isMult(t1) ? t1[0].getRational() : 1);
			Expr term_t1  = (isMult(t1) ? t1[1] : t1);
			Rational t2_c = (isMult(t2) ? t2[0].getRational() : 1);
			Expr term_t2  = (isMult(t2) ? t2[1] : t2);
			CHECK_SOUND(t1_c == - t2_c, "implyNegatedInequality: t1 should be -t2 : " + t1.toString() + " vs " + t2.toString());
			CHECK_SOUND(term_t1 == term_t2, "implyNegatedInequality: t1 should be -t2 : " + t1.toString() + " vs " + t2.toString());
		}

		int kind1 = expr1.getKind();
		int kind2 = expr2.getKind();
		bool bothStrict = kind1 == LT && kind2 == LT;
		CHECK_SOUND(c1 + c2 < 0 || (c1 + c2 == 0 && bothStrict), "implyNegatedInequality: sum of constants not negative!");
	}

	// The proof object that we will use
	Proof pf;
	if (withProof()) pf = newPf("implyNegatedInequality", expr1, expr2, expr2.negate());

	// Return the theorem
	return newTheorem(expr1.impExpr(expr2.negate()), Assumptions::emptyAssump(), pf);
}

Theorem ArithTheoremProducerOld::trustedRewrite(const Expr& expr1, const Expr& expr2) {

	// The proof object that we will us
	Proof pf;

	// Setup the proof if needed
	if (withProof()) pf = newPf("trustedRewrite", expr1, expr2);

	// Return the rewrite theorem that explains the phenomenon
	return newRWTheorem(expr1, expr2, Assumptions::emptyAssump(), pf);

}

Theorem ArithTheoremProducerOld::integerSplit(const Expr& intVar, const Rational& intPoint) {

	// Check soundness
	if (CHECK_PROOFS) {
		CHECK_SOUND(intPoint.isInteger(), "integerSplit: we can only split on integer points, given" + intPoint.toString());
	}

	// Create the expression
	const Expr& split = Expr(IS_INTEGER, intVar).impExpr(leExpr(intVar, rat(intPoint)).orExpr(geExpr(intVar, rat(intPoint + 1))));

	// The proof object that we will use
	Proof pf;
	if (withProof()) pf = newPf("integerSplit", intVar, rat(intPoint));

	// Return the theorem
	return newTheorem(split, Assumptions::emptyAssump(), pf);
}

//
// Changed from the new arithmetic, takes
// 0 op c + t, where t is an integer expression but c is a rational
// or 0 op x, where x is a leaf
//
Theorem ArithTheoremProducerOld::rafineStrictInteger(const Theorem& isIntConstrThm, const Expr& constr) {

	// Check soundness
	if (CHECK_PROOFS) {
		// Right side of the constraint should correspond to the proved integer expression
		CHECK_SOUND(isIneq(constr), "rafineStrictInteger: expected a constraint got : " + constr.toString());
		CHECK_SOUND(constr[0].isRational() && constr[0].getRational() == 0, "rafineStrictInteger: left hand side must be 0");
		CHECK_SOUND(d_theoryArith->isLeaf(constr[1]) || constr[1][0].isRational(), "rafineStrictInteger: right side of the constraint must be a leaf or a sum, with the first one a rational");

		// We have to check that the non-constant children of inequality correspond to the integrality theorem's children
		Expr intSum = isIntConstrThm.getExpr()[0];
		Expr ineqSum = constr[1];
		if (isPlus(intSum)) {
			int i, j;
			for (i = 0, j = 1; i < intSum.arity() && j < ineqSum.arity(); i ++, j ++)
				if (!(intSum[i] == ineqSum[j])) break;
			CHECK_SOUND(i == intSum.arity() && j == ineqSum.arity(), "rafineStrictInteger: proof of intger doesn't correspond to the constarint right side");
		} else
			CHECK_SOUND(intSum == ineqSum || intSum == ineqSum[1], "rafineStrictInteger: proof of intger doesn't correspond to the constarint right side:" + intSum.getString() + " vs " + ineqSum[1].getString());
	}

	// Get the contraint bound
	Rational c = (isPlus(constr[1]) ? constr[1][0].getRational() : 0);

	// Get the kind of the constraint
	int kind = constr.getKind();

	// If the bound is strict, make it non-strict
	switch (kind) {
		case LT:
			kind = LE;
			if (c.isInteger()) c --;            // 0 < 3 + x   --> 0 <= 2 + x
			else c = floor(c);                  // 0 < 3.4 + x --> 0 <= 3 + x
			break;
		case LE:
			kind = LE;
			if (!c.isInteger()) c = floor(c);   // 0 <= 3.5 + x --> 0 <= 3 + x
			break;
		case GT:
			kind = GE;
			if (c.isInteger()) c ++;            // 0 > 3 + x   -->  0 >= 4 + x
			else c = ceil(c);                   // 0 > 3.4 + x -->  0 >= 4 + x
			break;
		case GE:
			kind = GE;
			if (!c.isInteger()) c = ceil(c);   // 0 >= 3.4 + x --> 4 >= x
			break;
	}

	// The new constraint
	vector<Expr> newChildren;
	if (isPlus(constr[1])) {
		for (int i = 0; i < constr[1].arity(); i ++)
			if (constr[1][i].isRational()) newChildren.push_back(rat(c));
			else newChildren.push_back(constr[1][i]);
	} else {
		if (c != 0) newChildren.push_back(rat(c));
		newChildren.push_back(constr[1]);
	}
	Expr newSum = newChildren.size() > 1 ? plusExpr(newChildren) : newChildren[0];
	Expr newConstr(kind, rat(0), newSum);

	// Pick up the assumptions from the integer proof
	const Assumptions& assump(isIntConstrThm.getAssumptionsRef());

  	// Construct the proof object if necessary
  	Proof pf;
	if (withProof())
	  pf = newPf("rafineStrictInteger", constr,newConstr, isIntConstrThm.getProof());

	// Return the rewrite theorem that explains the phenomenon
	return newRWTheorem(constr, newConstr, assump, pf);
}


// Given:
// 0 = c + t
// where t is integer and c is not
// deduce bot
Theorem ArithTheoremProducerOld::intEqualityRationalConstant(const Theorem& isIntConstrThm, const Expr& constr) {

	// Check soundness
	if (CHECK_PROOFS) {
		// Right side of the constraint should correspond to the proved integer expression
		CHECK_SOUND(constr.getKind() == EQ, "intEqualityRationalConstant: expected a constraint got : " + constr.toString());
		bool sum_on_rhs = (constr[0].isRational() && constr[0].getRational() == 0);
		bool sum_on_lhs = (constr[1].isRational() && constr[1].getRational() == 0);
		CHECK_SOUND((sum_on_rhs && !sum_on_lhs) ||(!sum_on_rhs && sum_on_lhs),
				    "intEqualityRationalConstant: left or right hand side must be 0");
		CHECK_SOUND((sum_on_rhs && constr[1][0].isRational() && !constr[1][0].getRational().isInteger()) ||
				    (sum_on_lhs && constr[0][0].isRational() && !constr[0][0].getRational().isInteger()),
		            "intEqualityRationalConstant: left or right side of the constraint must be a sum, with the first one a rational (non integer)");

		// We have to check that the non-constant children of inequality correspond to the integrality theorem's children
		Expr intSum = isIntConstrThm.getExpr()[0];
		Expr eqSum = (sum_on_lhs ? constr[0] : constr[1]);
		if (isPlus(intSum)) {
			int i, j;
			for (i = 0, j = 1; i < intSum.arity() && j < eqSum.arity(); i ++, j ++)
				if (!(intSum[i] == eqSum[j])) break;
			CHECK_SOUND(i == intSum.arity() && j == eqSum.arity(), "intEqualityRationalConstant: proof of intger doesn't correspond to the constarint right side");
		} else
			CHECK_SOUND(intSum == eqSum[1], "intEqualityRationalConstant: proof of intger doesn't correspond to the constarint right side:" + intSum.getString() + " vs " + eqSum[1].getString());
	}

	const Assumptions& assump(isIntConstrThm.getAssumptionsRef());

  	// Construct the proof object if necessary
  	Proof pf;
	if (withProof())
		pf = newPf("intEqualityRationalConstant", constr, isIntConstrThm.getProof());

	// Return the rewrite theorem that explains the phenomenon
	return newRWTheorem(constr, d_em->falseExpr(), assump, pf);
}

Theorem ArithTheoremProducerOld::cycleConflict(const vector<Theorem>& inequalitites) {
	Proof pf;
	if(withProof()) {
    	vector<Expr> es;
    	vector<Proof> pfs;
	    for(unsigned i = 0; i < inequalitites.size(); i++) {
	    	es.push_back(inequalitites[i].getExpr());
	    	pfs.push_back(inequalitites[i].getProof());
	    }
	    pf = newPf("cycleConflict", es, pfs);
	  }

	Assumptions a;
	for(unsigned i = 0; i < inequalitites.size(); i ++)
		a.add(inequalitites[i]);

	return newTheorem(d_em->falseExpr(), a, pf);
}

Theorem ArithTheoremProducerOld::implyEqualities(const std::vector<Theorem>& inequalities) {
	Assumptions a;
	vector<Expr> conjuncts;
	for(unsigned i = 0; i < inequalities.size(); i ++) {
		a.add(inequalities[i]);
		Expr inequality = inequalities[i].getExpr();
		Expr equality = inequality[0].eqExpr(inequality[1]);
		conjuncts.push_back(equality);
	}

	Proof pf;
	if(withProof()) {
	   	vector<Expr> es;
	   	vector<Proof> pfs;
	    for(unsigned i = 0; i < inequalities.size(); i++) {
	    	es.push_back(inequalities[i].getExpr());
	    	pfs.push_back(inequalities[i].getProof());
	    }
	    pf = newPf("implyEqualities", Expr(RAW_LIST,conjuncts),Expr(RAW_LIST,es), pfs);
	}

	return newTheorem(andExpr(conjuncts), a, pf);
}

/*! Takes a Theorem(\\alpha < \\beta) and returns
 *  Theorem(\\alpha < \\beta <==> \\alpha <= \\beta -1)
 * where \\alpha and \\beta are integer expressions
 */
Theorem ArithTheoremProducerOld::lessThanToLERewrite(const Expr& ineq,
					   const Theorem& isIntLHS,
					   const Theorem& isIntRHS,
					   bool changeRight) {

	const Expr& isIntLHSexpr = isIntLHS.getExpr();
	const Expr& isIntRHSexpr = isIntRHS.getExpr();

	if(CHECK_PROOFS) {
		CHECK_SOUND(isLT(ineq), "ArithTheoremProducerOld::LTtoLE: ineq must be <");
		// Integrality check
		CHECK_SOUND(isIntPred(isIntLHSexpr)	&& isIntLHSexpr[0] == ineq[0],
		"ArithTheoremProducerOld::lessThanToLE: bad integrality check:\n"
		" ineq = "+ineq.toString()+"\n isIntLHS = "
		+isIntLHSexpr.toString());
		CHECK_SOUND(isIntPred(isIntRHSexpr) && isIntRHSexpr[0] == ineq[1],
		"ArithTheoremProducerOld::lessThanToLE: bad integrality check:\n"
		" ineq = "+ineq.toString()+"\n isIntRHS = "
		+isIntRHSexpr.toString());
	}

	vector<Theorem> thms;
	thms.push_back(isIntLHS);
	thms.push_back(isIntRHS);
	Assumptions a(thms);
	Proof pf;
	Expr le = changeRight? leExpr(ineq[0], ineq[1] + rat(-1)) : leExpr(ineq[0] + rat(1), ineq[1]);
	if(withProof()) {
		vector<Proof> pfs;
		pfs.push_back(isIntLHS.getProof());
		pfs.push_back(isIntRHS.getProof());
		pf = newPf(changeRight? "lessThan_To_LE_rhs_rwr" : "lessThan_To_LE_lhs_rwr", ineq, le, pfs);
	}

	return newRWTheorem(ineq, le, a, pf);
}

// G ==> (G1 or G2) and (!G1 or !G2),
// where G  = G(x, e, c1, c2),
//       V x = e + i, for i in c1 .. c2
Theorem ArithTheoremProducerOld::splitGrayShadowSmall(const Theorem& gThm) {
  const Expr& theShadow = gThm.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducerOld::expandGrayShadowConst: not a shadow" +
		theShadow.toString());
  }

  const Rational& c1 = theShadow[2].getRational();
  const Rational& c2 = theShadow[3].getRational();

  if(CHECK_PROOFS) {
    CHECK_SOUND(c1.isInteger() && c2.isInteger() && c1 < c2,
		"ArithTheoremProducerOld::expandGrayShadow: " +
		theShadow.toString());
  }

  const Expr& v = theShadow[0];
  const Expr& e = theShadow[1];

  vector<Expr> disjuncts;
  for (int i = c1.getInt(); i <= c2.getInt(); i ++) {
	  Expr disjunct = v.eqExpr(e + rat(i));
	  disjuncts.push_back(disjunct);
  }
  Expr bigOr = orExpr(disjuncts);

  Proof pf;
    if(withProof()){
    vector<Expr> exprs;
    exprs.push_back(theShadow);
    exprs.push_back(bigOr);
    pf = newPf("split_gray_shadow", exprs, gThm.getProof());
  }

  return newTheorem(bigOr, gThm.getAssumptionsRef(), pf);
}

Theorem ArithTheoremProducerOld::implyWeakerInequalityDiffLogic(const std::vector<Theorem>& antecedentThms, const Expr& implied) {
	Proof pf;

	if(withProof()) {
	   	vector<Expr> es;
	   	vector<Proof> pfs;
	    for(unsigned i = 0; i < antecedentThms.size(); i++) {
	    	es.push_back(antecedentThms[i].getExpr());
	    	pfs.push_back(antecedentThms[i].getProof());
	    }
	    pf = newPf("implyWeakerInequalityDiffLogic", implied, Expr(RAW_LIST,es), pfs);
	}

	Assumptions a;
	for(unsigned i = 0; i < antecedentThms.size(); i ++) {
		a.add(antecedentThms[i]);
	}

	return newTheorem(implied, a, pf);

}

Theorem ArithTheoremProducerOld::implyNegatedInequalityDiffLogic(const std::vector<Theorem>& antecedentThms, const Expr& implied) {
	Proof pf;

	if(withProof()) {
	   	vector<Expr> es;
	   	vector<Proof> pfs;
	    for(unsigned i = 0; i < antecedentThms.size(); i++) {
	    	es.push_back(antecedentThms[i].getExpr());
	    	pfs.push_back(antecedentThms[i].getProof());
	    }
	    pf = newPf("implyNegatedInequalityDiffLogic",implied.notExpr(), Expr(RAW_LIST, es), pfs);
	}

	Assumptions a;
	for(unsigned i = 0; i < antecedentThms.size(); i ++) {
		a.add(antecedentThms[i]);
	}

	return newTheorem(implied.notExpr(), a, pf);

}


Theorem ArithTheoremProducerOld::expandGrayShadowRewrite(const Expr& theShadow) {

  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducerOld::expandGrayShadowConst: not a shadow" +
		theShadow.toString());
  }

  const Rational& c1 = theShadow[2].getRational();
  const Rational& c2 = theShadow[3].getRational();

  if(CHECK_PROOFS) {
    CHECK_SOUND(c1.isInteger() && c2.isInteger() && c1 < c2,
		"ArithTheoremProducerOld::expandGrayShadow: " +
		theShadow.toString());
  }

  const Expr& v = theShadow[0];
  const Expr& e = theShadow[1];

  Proof pf;
  if(withProof())
    pf = newPf("expand_gray_shadow", theShadow);
  Expr ineq1(leExpr(e+rat(c1), v));
  Expr ineq2(leExpr(v, e+rat(c2)));
  return newRWTheorem(theShadow, ineq1 && ineq2, Assumptions::emptyAssump(), pf);
}

Theorem ArithTheoremProducerOld::compactNonLinearTerm(const Expr& nonLinear) {

	// The set of common leaves
	multiset<Expr> commonLeaves;
	bool first = true;

	// Go through the terms and intersect the leaf sets
	for (int i = 0; i < nonLinear.arity(); i ++) {
		if (!nonLinear[i].isRational()) {
			// Get the current monomial
			Expr monomial = nonLinear[i];

			// A set to keep the variables
			multiset<Expr> currentLeaves;

			// Get the set of leaves in this term
			if (isMult(monomial)) {
				for (int j = 0; j < monomial.arity(); j ++)
					if (!monomial[j].isRational()) {
						if (isPow(monomial[j])) {
							for (int p = 0; p < monomial[j][0].getRational().getInt(); p ++)
								currentLeaves.insert(monomial[j][1]);
						} else
							currentLeaves.insert(monomial[j]);
					}
			} else if (isPow(monomial)) {
				for (int p = 0; p < monomial[0].getRational().getInt(); p ++)
					currentLeaves.insert(monomial[1]);
			} else
				currentLeaves.insert(monomial);

			// And intersect them
			if (first) {
				commonLeaves.swap(currentLeaves);
				first = false;
			} else {
				multiset<Expr> intersectLeaves;
				set_intersection(currentLeaves.begin(), currentLeaves.end(),
						      commonLeaves.begin(), commonLeaves.end(),
						      insert_iterator< multiset<Expr> >
				                  (intersectLeaves, intersectLeaves.begin()));
				intersectLeaves.swap(commonLeaves);
			}
		}
	}

	Expr result;
	if (commonLeaves.size() > 0) {

		// The constant to add in the beginnings
		Expr constant = rat(0);

		// The sum of of the rest when we pullout the common factors
		vector<Expr> sumChildren;

		// Go through them again and construct the sum of the rest
		for (int i = 0; i < nonLinear.arity(); i ++) {
			if (!nonLinear[i].isRational()) {
				// Get the current monomial
				Expr monomial = nonLinear[i];

				// A set to keep the variables
				multiset<Expr> currentChildren;

				// Get the set of childrent of this multiplication
				if (isMult(monomial)) {
					for (int j = 0; j < monomial.arity(); j ++)
						if (isPow(monomial[j])) {
							for (int p = 0; p < monomial[j][0].getRational().getInt(); p ++)
								currentChildren.insert(monomial[j][1]);
						} else
							currentChildren.insert(monomial[j]);
				} else if (isPow(monomial)) {
					for (int p = 0; p < monomial[0].getRational().getInt(); p ++)
						currentChildren.insert(monomial[1]);
				} else
					currentChildren.insert(monomial);

				// Take the difference and construct a multiplication
				multiset<Expr> diffChildren;
				set_difference(currentChildren.begin(), currentChildren.end(),
							   commonLeaves.begin(), commonLeaves.end(),
							   insert_iterator< multiset<Expr> >
					                  (diffChildren, diffChildren.begin()));

				// Go create another sumChildren element
				if (diffChildren.size() == 1) {
					sumChildren.push_back(*diffChildren.begin());
				} else if (diffChildren.size() == 0) {
					sumChildren.push_back(rat(1));
				} else {
					multiset<Expr>::iterator it     = diffChildren.begin();
					multiset<Expr>::iterator it_end = diffChildren.end();
					vector<Expr> multChildren;
					while (it != it_end) {
						multChildren.push_back(*it);
						it ++;
					}
					sumChildren.push_back(multExpr(multChildren));
				}
			} else
				constant = nonLinear[i];
		}

		// The children of the final multiplication
		vector<Expr> multChildren;
		multChildren.push_back(plusExpr(sumChildren));
		multiset<Expr>::iterator it = commonLeaves.begin();
		multiset<Expr>::iterator it_end = commonLeaves.end();
		for (; it != it_end; it ++)
			multChildren.push_back(*it);
		result = plusExpr(constant, multExpr(multChildren));
	} else {
		// We have no common leaves to take out
		result = nonLinear;
	}

    Proof pf;
	if(withProof())
	  pf = newPf("compactNonlinear", nonLinear, result);

	return newRWTheorem(nonLinear, result, Assumptions::emptyAssump(), pf);
}

//
// -c <= x1*x2*...*xn
// if c = 0 then "only even number of x_i's can be negative" or one of them is zero
//               x1 = 0 or x2 = 0 or ... or xn = 0
//               or (x1
// else "only only even number of x_i's can be negative" and none of them is zero"
Theorem ArithTheoremProducerOld::nonLinearIneqSignSplit(const Theorem& ineqThm) {

	// Get the inequality
	Expr ineq = ineqThm.getExpr();
	Expr rhs = ineq[1];

	// Get the constant
	Rational c = (isMult(rhs) ? 0 : rhs[0].getRational());
	if(CHECK_PROOFS) {
	    CHECK_SOUND(c <= 0, "ArithTheoremProducerOld::nonLinearIneqSignSplit: " + ineq.toString());
	    CHECK_SOUND(isMult(rhs) || (isPlus(rhs) && rhs.arity() == 2), "ArithTheoremProducerOld::nonLinearIneqSignSplit: " + ineq.toString());
	}

	Expr signXor = d_em->trueExpr();
	Expr mult = (isMult(rhs) ? rhs : rhs[1]);
	for (int i = 0; i < mult.arity(); i ++) {
		Expr term = mult[i];
		if (isPow(term) && term[0].getRational() < 0)
			term = Expr(POW, -term[0], term[1]);
		signXor = Expr(XOR, signXor, ltExpr(term, rat(0)));
	}

	if (c == 0 && ineq.getKind() == LE) {
		Expr zeroOr = d_em->falseExpr();
		for (int i = 0; i < mult.arity(); i ++) {
			Expr term = mult[i];
			zeroOr = zeroOr.orExpr(term.eqExpr(rat(0)));
		}
		signXor = zeroOr.orExpr(signXor);
	}

	Proof pf;
	if(withProof()) {
		vector<Expr> exprs;
	    exprs.push_back(ineq);
	    exprs.push_back(signXor);
	    pf = newPf("nonLinearIneqSignSplit", exprs, ineqThm.getProof());
	}

	Assumptions assumptions;
	assumptions.add(ineqThm);

	return newTheorem(signXor, assumptions, pf);
}

Theorem ArithTheoremProducerOld::implyDiffLogicBothBounds(const Expr& x,
		std::vector<Theorem>& c1_le_x, Rational c1,
    	std::vector<Theorem>& x_le_c2, Rational c2)
{
	Proof pf;

	if(withProof()) {
	   	vector<Expr> es;
	   	vector<Proof> pfs;
	    for(unsigned i = 0; i < c1_le_x.size(); i++) {
	    	es.push_back(c1_le_x[i].getExpr());
	    	pfs.push_back(c1_le_x[i].getProof());
	    }
	    for(unsigned i = 0; i < x_le_c2.size(); i++) {
	    	es.push_back(x_le_c2[i].getExpr());
	    	pfs.push_back(x_le_c2[i].getProof());
	    }
	    pf = newPf("implyDiffLogicBothBounds", es, pfs);
	}

	Assumptions a;
	for(unsigned i = 0; i < x_le_c2.size(); i ++) {
		a.add(c1_le_x[i]);
	}
	for(unsigned i = 0; i < x_le_c2.size(); i ++) {
		a.add(c1_le_x[i]);
	}

	Expr implied = grayShadow(x, rat(0), c1, c2);

	return newTheorem(implied, a, pf);
}

Theorem ArithTheoremProducerOld::addInequalities(const vector<Theorem>& thms) {

	// Check soundness
	if (CHECK_PROOFS) {
		for (unsigned i = 0; i < thms.size(); i ++) {
			Expr expr = thms[i].getExpr();
			CHECK_SOUND(isIneq(expr), "addInequalities: expecting an inequality for, got " + expr.toString());
			CHECK_SOUND(isLE(expr) || isLT(expr), "addInequalities: expr should be <(=) " + expr.toString());
		}
	}

	// Create the assumptions
	Assumptions a;
	for (unsigned i = 0; i < thms.size(); i ++)
		a.add(thms[i]);

  	// Get the kinds of the inequalitites
	int kind = LE;
	for (unsigned i = 0; i < thms.size(); i ++)
		if (thms[i].getExpr().getKind() == LT) kind = LT;

  	// Create the proof object
  	Proof pf;
  	if(withProof()) {
    	vector<Proof> pfs;
    	vector<Expr> exps;
    	for (unsigned i = 0; i < thms.size(); i ++) {
    	    pfs.push_back(thms[i].getProof());
    	    exps.push_back(thms[i].getExpr());
    	}
    	pf = newPf("addInequalities", exps, pfs);
  	}

  	// Create the new expressions
  	vector<Expr> summandsLeft;
  	vector<Expr> summandsRight;
  	for (unsigned i = 0; i < thms.size(); i ++)  {
  		summandsLeft.push_back(thms[i].getExpr()[0]);
  		summandsRight.push_back(thms[i].getExpr()[1]);
  	}
  	Expr leftSide  = plusExpr(summandsLeft);
  	Expr rightSide = plusExpr(summandsRight);

  	// Return the theorem
  	return newTheorem(Expr(kind, leftSide, rightSide), a, pf);
}

// x^1 <-> x
Theorem ArithTheoremProducerOld::powerOfOne(const Expr& e) {

	if(CHECK_PROOFS) {
		CHECK_SOUND(isPow(e), "ArithTheoremProducerOld::powerOfOne: not a power expression" + e.toString());
		CHECK_SOUND(e[0].isRational() && e[0].getRational() == 1, "ArithTheoremProducerOld::powerOfOne: not a power of 1" + e.toString());
	}

	Proof pf;
	if(withProof())
		pf = newPf("power_of_one", e);

	return newRWTheorem(e, e[1], Assumptions::emptyAssump(), pf);
}


void ArithTheoremProducerOld::getLeaves(const Expr& e, set<Rational>& s, ExprHashMap<bool>& cache)
{
  if (e.isRational()) {
    s.insert(e.getRational());
    return;
  }

  if (e.isAtomic() && d_theoryArith->isLeaf(e)) {
    return;
  }

  ExprHashMap<bool>::iterator it = cache.find(e);
  if (it != cache.end()) return;

  cache[e] = true;

  DebugAssert(e.arity() > 0, "Expected non-zero arity");
  int k = 0;

  if (e.isITE()) {
    k = 1;
  }

  for (; k < e.arity(); ++k) {
    getLeaves(e[k], s, cache);
  }
}


Theorem ArithTheoremProducerOld::rewriteLeavesConst(const Expr& e)
{
  DebugAssert(e.isPropAtom() && d_theoryArith->leavesAreNumConst(e),
              "invariant violated");
  DebugAssert(e.getKind() == EQ || e.getKind() == LT || e.getKind() == LE || e.getKind() == GT || e.getKind() == GE,
              "Unexpected kind");
  set<Rational> lhs, rhs;
  ExprHashMap<bool> cache;
  getLeaves(e[0], lhs, cache);

  cache.clear();
  getLeaves(e[1], rhs, cache);

  Expr res;
  switch (e.getKind()) {
    case EQ: {
      set<Rational> common;
      set_intersection(lhs.begin(), lhs.end(), rhs.begin(), rhs.end(),
                       inserter(common, common.begin()));
      if (common.empty()) {
        res = d_em->falseExpr();
      }
      break;
    }
    case LT: {
      set<Rational>::iterator it;
      it = lhs.end();
      --it;
      if ((*it) < (*(rhs.begin()))) {
        res = d_em->trueExpr();
      } else {
        it = rhs.end();
        --it;
        if ((*it) <= (*(lhs.begin()))) {
          res = d_em->falseExpr();
        }
      }
      break;
    }
    case LE: {
      set<Rational>::iterator it;
      it = lhs.end();
      --it;
      if ((*it) <= (*(rhs.begin()))) {
        res = d_em->trueExpr();
      }
      else {
        it = rhs.end();
        --it;
        if ((*it) < (*(lhs.begin()))) {
          res = d_em->falseExpr();
          break;
        }
      }
      break;
    }
    case GT: {
      set<Rational>::iterator it;
      it = lhs.end();
      --it;
      if ((*it) > (*(rhs.begin()))) {
        res = d_em->trueExpr();
      } else {
        it = rhs.end();
        --it;
        if ((*it) >= (*(lhs.begin()))) {
          res = d_em->falseExpr();
        }
      }
      break;
    }
    case GE: {
      set<Rational>::iterator it;
      it = lhs.end();
      --it;
      if ((*it) >= (*(rhs.begin()))) {
        res = d_em->trueExpr();
      }
      else {
        it = rhs.end();
        --it;
        if ((*it) > (*(lhs.begin()))) {
          res = d_em->falseExpr();
          break;
        }
      }
      break;
    }
    default:
      break;
    }
  if (res.isNull()) return d_theoryArith->reflexivityRule(e);
  else {
    Proof pf;
    if(withProof())
      pf = newPf("rewrite_leaves_const", e);
    return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
  }
}
