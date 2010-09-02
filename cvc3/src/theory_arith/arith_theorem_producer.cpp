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

#include "arith_theorem_producer.h"
#include "theory_core.h"
#include "theory_arith_new.h"

using namespace std;
using namespace CVC3;

////////////////////////////////////////////////////////////////////
// TheoryArith: trusted method for creating ArithTheoremProducer
////////////////////////////////////////////////////////////////////

ArithProofRules* TheoryArithNew::createProofRules() {
  return new ArithTheoremProducer(theoryCore()->getTM(), this);
}

////////////////////////////////////////////////////////////////////
// Canonization rules
////////////////////////////////////////////////////////////////////


#define CLASS_NAME "ArithTheoremProducer"

// Rule for variables: e == 1 * e
Theorem ArithTheoremProducer::varToMult(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("var_to_mult", e);
  return newRWTheorem(e, (rat(1) * e), Assumptions::emptyAssump(), pf);
}

// Rule for unary minus: -e == (-1) * e
Theorem ArithTheoremProducer::uMinusToMult(const Expr& e) {
  // The proof object to use
  Proof pf;

  // If the proof is needed set it up
  if(withProof()) pf = newPf("uminus_to_mult", e);

  // Return the rewrite theorem explaining the rewrite
  return newRWTheorem((-e), (rat(-1) * e), Assumptions::emptyAssump(), pf);
}


// ==> x - y = x + (-1) * y
Theorem ArithTheoremProducer::minusToPlus(const Expr& x, const Expr& y) {
	// The proof object to use
  	Proof pf;

  	// If proof is needed, set it up
  	if (withProof()) pf = newPf("minus_to_plus", x, y);

  	// Return a new rewrite theorem describing the change
  	return newRWTheorem((x-y), (x + (rat(-1) * y)), Assumptions::emptyAssump(), pf);
}


// Rule for unary minus: -e == e/(-1)
// This is to reduce the number of almost identical rules for uminus and div
Theorem ArithTheoremProducer::canonUMinusToDivide(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("canon_uminus", e);
  return newRWTheorem((-e), (e / rat(-1)), Assumptions::emptyAssump(), pf);
}

// Rules for division by constant

// (c)/(d) ==> (c/d).  When d==0, c/0 = 0 (our total extension).
Theorem ArithTheoremProducer::canonDivideConst(const Expr& c,
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
Theorem ArithTheoremProducer::canonDivideMult(const Expr& cx,
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
Theorem ArithTheoremProducer::canonDividePlus(const Expr& sum, const Expr& d) {
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
Theorem ArithTheoremProducer::canonDivideVar(const Expr& e, const Expr& d) {
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


Expr ArithTheoremProducer::simplifiedMultExpr(std::vector<Expr> & mulKids) {

	// Check that the number of kids is at least 1 and that the first one is rational
 	DebugAssert(mulKids.size() >= 1 && mulKids[0].isRational(), "");

 	// If the number of kids is only one, return the kid, no multiplication is necessary
 	if (mulKids.size() == 1) return mulKids[0];
 	// Otherwise return the multiplication of given expression
 	else return multExpr(mulKids);
}

Expr ArithTheoremProducer::canonMultConstMult(const Expr & c, const Expr & e) {

  	// The constant must be a rational and e must be a multiplication
  	DebugAssert(c.isRational() && e.getKind() == MULT, "ArithTheoremProducer::canonMultConstMult: c must be a rational a e must be a MULT");

  	// Multiplication must include a rational multiplier
  	DebugAssert ((e.arity() > 1) && (e[0].isRational()), "arith_theorem_producer::canonMultConstMult: a canonized MULT expression must have \
                                                        arity greater than 1: and first child must be rational " + e.toString());

	// The kids of the new multiplication
  	std::vector<Expr> mulKids;

  	// Create new multiplication expression, multiplying the constant with the given constant
  	Expr::iterator i = e.begin();
  	mulKids.push_back(rat(c.getRational() * (*i).getRational()));
  	// All the rest, just push them to the kids vector
  	for(i ++; i != e.end(); i ++)
    	mulKids.push_back(*i);

	// Return the simplified multiplication expression
  	return simplifiedMultExpr(mulKids);
}

Expr ArithTheoremProducer::canonMultConstPlus(const Expr & e1, const Expr & e2) {

  // e1 must be a rational and e2 must be a sum in canonic form
  DebugAssert(e1.isRational() && e2.getKind() == PLUS && e2.arity() > 0, "");

  // Vector to hold all the sum terms
  std::vector<Theorem> thmPlusVector;

  // Go through all the sum terms and multiply them with the constant
  for(Expr::iterator i = e2.begin(); i != e2.end(); i++)
    thmPlusVector.push_back(canonMultMtermMterm(e1*(*i)));

  // Substitute the canonized terms into the sum
  Theorem thmPlus1 = d_theoryArith->substitutivityRule(e2.getOp(), thmPlusVector);

  // Return the resulting expression
  return thmPlus1.getRHS();
}

Expr ArithTheoremProducer::canonMultPowPow(const Expr & e1,
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

Expr ArithTheoremProducer::canonMultPowLeaf(const Expr & e1,
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

Expr ArithTheoremProducer::canonMultLeafLeaf(const Expr & e1,
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

Expr ArithTheoremProducer::canonMultLeafOrPowMult(const Expr & e1,
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
    return ArithTheoremProducer::greaterthan(e1,e2);
  }
};

typedef map<Expr,Rational,MonomialLess> MonomMap;

Expr ArithTheoremProducer::canonCombineLikeTerms(const std::vector<Expr> & sumExprs) {

  	Rational constant = 0;     // The constant at the begining of the sum
  	MonomMap sumHashMap;       // The hash map of the summands, so that we can gather them and sum in the right order
  	vector<Expr> sumKids;      // The kids of the sum

  	// Add each distinct mterm (not including the rational) into an appropriate hash map entry
  	std::vector<Expr>::const_iterator i     = sumExprs.begin();
  	std::vector<Expr>::const_iterator i_end = sumExprs.end();
  	for (; i != i_end; i++) {
    	// Take the current expression (it must be a multiplication, a leaf or a rational number)
    	Expr mul = *i;

    	// If it's a rational, just add it to the constant factor c
   		if (mul.isRational())
   			constant = constant + mul.getRational();
    	else {
    		// Depending on the type of the expression decide what to do with this sum term
      		switch (mul.getKind()) {

      			// Multiplication is
      			case MULT: {

        			// The multiplication must be of arity > 1 and the first one must be rational
        			DebugAssert(mul.arity() > 1 && mul[0].isRational(),"If sum term is multiplication it must have the first term a rational, and at least another one");

        			// Get the rational constant of multiplication
        			Rational r = mul[0].getRational();

        			// Make a new multiplication term with a 1 instead of the rational r
        			vector<Expr> newKids;
        			// Copy the children to the newKids vector (including the rational)
        			for(Expr::iterator m = mul.begin(); m != mul.end(); m ++) newKids.push_back(*m);
        			// Change the rational to 1
     				newKids[0] = rat(1);
     				// Make the newMul expression
        			Expr newMul = multExpr(newKids);

                	// Find the term in the hashmap, so that we can add the coefficient (a*t + b*t = (a+b)*t)
        			MonomMap::iterator i = sumHashMap.find(newMul);

        			// If not found, just add the rational to the hash map
        			if (i == sumHashMap.end()) sumHashMap[newMul] = r;
        			// Otherwise, add it to the existing coefficient
        			else (*i).second += r;

      				// MULT case break
      				break;
      			}

      			default: {

      				// Find the term in the hashmap (add the 1*mul for being canonical)
      				MonomMap::iterator i = sumHashMap.find(multExpr(rat(1), mul));

        			// covers the case of POW, leaf
        			if (i == sumHashMap.end()) sumHashMap[multExpr(rat(1), mul)] = 1;
        			else (*i).second += 1;

        			// Default break
        			break;
        		}
      		}
    	}
  	}

  // Now transfer to sumKids, first adding the rational constant if different from 0 (b + a_1*x_1 + a_2*x_2 + ... + a_n*x_n)
  if (constant != 0) sumKids.push_back(rat(constant));

  // After the constant, add all the other summands, in the right order (the hashmap order)
  MonomMap::iterator j = sumHashMap.begin(), jend=sumHashMap.end();
  for(; j != jend; j++) {
    // If the corresponding coefficient is non-zero, add the term to the sum
    if ((*j).second != 0) {
    	// Again, make a new multiplication term with a the coefficient instead of the rational one (1)
		vector<Expr> newKids;
        // Copy the children to the newKids vector (including the rational)
        for(Expr::iterator m = (*j).first.begin(); m != (*j).first.end(); m ++) newKids.push_back(*m);
        // Change the rational to the summed rationals for this term
     	newKids[0] = rat((*j).second);
     	// Make the newMul expression and add it to the sum
        sumKids.push_back(multExpr(newKids));
    }
  }

  // If the whole sum is only the constant, the whole sum is only the constant (TODO: CLEAN THIS UP, ITS HORRIBLE)
  if (constant != 0 && sumKids.size() == 1) return sumKids[0];

  // If the constant is 0 and there is only one more summand, return only the summand
  if (constant == 0 && sumKids.size() == 1) return sumKids[0];

  // If the constant is 0 and there are no summands, return 0
  if (constant == 0 && sumKids.size() == 0) return rat(0);

  // Otherwise return the sum of the sumkids
  return plusExpr(sumKids);
}

Expr ArithTheoremProducer::canonMultLeafOrPowOrMultPlus(const Expr & e1,
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

Expr ArithTheoremProducer::canonMultPlusPlus(const Expr & e1,
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
Theorem ArithTheoremProducer::canonMultMtermMterm(const Expr& e) {

  // Check if the rule is sound
  if(CHECK_PROOFS) {
    CHECK_SOUND(isMult(e) && e.arity() == 2, "canonMultMtermMterm: e = " + e.toString());
  }

  // The proof we are using
  Proof pf;

  // The resulting expression
  Expr rhs;

  // Get the parts of the multiplication
  const Expr& e1 = e[0];
  const Expr& e2 = e[1];

  // The name of the proof
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
Theorem ArithTheoremProducer::canonPlus(const Expr& e)
{
	// Create the proof object in case we need it
	Proof pf;

  	// The operation must be PLUS
  	DebugAssert(e.getKind() == PLUS, "");

  	// Add all the summands to the sumKids vector
	std::vector<Expr> sumKids;
  	Expr::iterator i = e.begin();
  	for(; i != e.end(); ++i) {
    	if ((*i).getKind() != PLUS)
      		sumKids.push_back(*i);
    	else {
    		// If the kid is also a sum, add it to the sumKids vector (no need for recursion, kids are already canonized)
        	Expr::iterator j = (*i).begin();
        	for(; j != (*i).end(); ++j)
          		sumKids.push_back(*j);
      	}
  	}

  	// Combine all the kids to sum (gather the same variables and stuff)
  	Expr val = canonCombineLikeTerms(sumKids);

	// If proofs needed set it up with starting expression and the value
  	if (withProof()) {
    	pf = newPf("canon_plus", e, val);
  	}

  	// Return the explaining rewrite theorem
  	return newRWTheorem(e, val, Assumptions::emptyAssump(), pf);
}

// (MULT expr1 expr2 ...) where each expr is itself in canonic form
Theorem ArithTheoremProducer::canonMult(const Expr& e)
{
  // The proof we might need
  Proof pf;

  // Expression must be of kind MULT
  DebugAssert(e.getKind() == MULT && e.arity() > 1, "");

  // Get the first operand of the multiplication
  Expr::iterator i = e.begin();

  // Set the result to the first element
  Expr result = *i;

  // Skip to the next one
  ++i;

  // For all the other elements
  for (; i != e.end(); ++i) {
  	// Multiply each element into the result
    result = canonMultMtermMterm(result * (*i)).getRHS();
  }

  // If the proof is needed, create one
  if (withProof()) {
    pf = newPf("canon_mult", e,result);
  }

  // Return a new rewrite theorem with the result
  return newRWTheorem(e, result, Assumptions::emptyAssump(), pf);
}


Theorem
ArithTheoremProducer::canonInvertConst(const Expr& e)
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
ArithTheoremProducer::canonInvertLeaf(const Expr& e)
{
  Proof pf;

  if (withProof()) {
    pf = newPf("canon_invert_leaf", e);
  }
  return newRWTheorem((rat(1)/e), powExpr(rat(-1), e), Assumptions::emptyAssump(), pf);
}


Theorem
ArithTheoremProducer::canonInvertPow(const Expr& e)
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
                        powExpr(rat(-e[0].getRational()), e),
                        Assumptions::emptyAssump(),
                        pf);
}

Theorem
ArithTheoremProducer::canonInvertMult(const Expr& e)
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
ArithTheoremProducer::canonInvert(const Expr& e)
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


Theorem ArithTheoremProducer::canonDivide(const Expr& e)
{
  // The expression should be of type DIVIDE
  DebugAssert(e.getKind() == DIVIDE, "Expecting Divide"+e.toString());

  // The proof if we need one
  Proof pf;

  // If the proof is needed make it
  if (withProof()) {
    pf = newPf("canon_invert_divide", e);
  }

  // Rewrite e[0] / e[1] as e[0]*(e[1])^-1
  Theorem thm = newRWTheorem(e, e[0]*(canonInvert(e[1]).getRHS()), Assumptions::emptyAssump(), pf);

  // Return the proof with canonizing the above multiplication
  return d_theoryArith->transitivityRule(thm, canonMult(thm.getRHS()));
}


// Rules for multiplication
// t*c ==> c*t, takes constant c and term t
Theorem
ArithTheoremProducer::canonMultTermConst(const Expr& c, const Expr& t) {
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
ArithTheoremProducer::canonMultTerm1Term2(const Expr& t1, const Expr& t2) {
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
Theorem ArithTheoremProducer::canonMultZero(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("canon_mult_zero", e);
  return newRWTheorem((rat(0)*e), rat(0), Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// 1*x ==> x, takes x (if x is other than a leaf)
// otherwise 1*x ==> 1*x
Theorem ArithTheoremProducer::canonMultOne(const Expr& e) {

  	// Setup the proof object
  	Proof pf;
  	if(withProof()) pf = newPf("canon_mult_one", e);

	// If it is a leaf multiply it by one
	if (d_theoryArith->isLeaf(e)) return d_theoryArith->reflexivityRule (rat(1)*e);

 	// Otherwise, just return the expression itself
 	return newRWTheorem((rat(1)*e), e, Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// c1*c2 ==> c', takes constant c1*c2
Theorem
ArithTheoremProducer::canonMultConstConst(const Expr& c1, const Expr& c2) {
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
ArithTheoremProducer::canonMultConstTerm(const Expr& c1,
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
ArithTheoremProducer::canonMultConstSum(const Expr& c1, const Expr& sum) {
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
Theorem ArithTheoremProducer::canonPowConst(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == POW && e.arity() == 2
		&& e[0].isRational() && e[1].isRational(),
		"ArithTheoremProducer::canonPowConst("+e.toString()+")");
  }
  const Rational& p = e[0].getRational();
  const Rational& base = e[1].getRational();
  if(CHECK_PROOFS) {
    CHECK_SOUND(p.isInteger(),
		"ArithTheoremProducer::canonPowConst("+e.toString()+")");
  }
  Expr res;
  if (base == 0 && p < 0) {
    res = rat(0);
  }
  else res = rat(pow(p, base));
  Proof pf;
  if(withProof())
    pf = newPf("canon_pow_const", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


// Rules for addition
// flattens the input. accepts a PLUS expr
Theorem
ArithTheoremProducer::canonFlattenSum(const Expr& e) {
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
ArithTheoremProducer::canonComboLikeTerms(const Expr& e) {
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
Theorem ArithTheoremProducer::multEqZero(const Expr& expr)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(expr.isEq() && expr[0].isRational() &&
                expr[0].getRational() == 0 &&
                isMult(expr[1]) && expr[1].arity() > 1,
                "multEqZero invariant violated"+expr.toString());
  }
  Proof pf;
  vector<Expr> kids;
  Expr::iterator i = expr[1].begin(), iend = expr[1].end();
  for (; i != iend; ++i) {
    kids.push_back(rat(0).eqExpr(*i));
  }
  if (withProof()) {
    pf = newPf("multEqZero", expr);
  }
  return newRWTheorem(expr, Expr(OR, kids), Assumptions::emptyAssump(), pf);
}


// 0 = (^ c x) <=> false if c <=0
//             <=> 0 = x if c > 0
Theorem ArithTheoremProducer::powEqZero(const Expr& expr)
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


// x^n = y^n <=> x = y (if n is odd)
// x^n = y^n <=> x = y OR x = -y (if n is even)
Theorem ArithTheoremProducer::elimPower(const Expr& expr)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(expr.isEq() && isPow(expr[0]) &&
                isPow(expr[1]) &&
                isIntegerConst(expr[0][0]) &&
                expr[0][0].getRational() > 0 &&
                expr[0][0] == expr[1][0],
                "elimPower invariant violated"+expr.toString());
  }
  Proof pf;
  if (withProof()) {
    pf = newPf("elimPower", expr);
  }
  Rational r = expr[0][0].getRational();
  Expr res = expr[0][1].eqExpr(expr[1][1]);
  if (r % 2 == 0) {
    res = res.orExpr(expr[0][1].eqExpr(-expr[1][1]));
  }
  return newRWTheorem(expr, res, Assumptions::emptyAssump(), pf);
}


// x^n = c <=> x = root (if n is odd and root^n = c)
// x^n = c <=> x = root OR x = -root (if n is even and root^n = c)
Theorem ArithTheoremProducer::elimPowerConst(const Expr& expr, const Rational& root)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(expr.isEq() && isPow(expr[0]) &&
                isIntegerConst(expr[0][0]) &&
                expr[0][0].getRational() > 0 &&
                expr[1].isRational() &&
                pow(expr[0][0].getRational(), root) == expr[1].getRational(),
                "elimPowerConst invariant violated"+expr.toString());
  }
  Proof pf;
  if (withProof()) {
    pf = newPf("elimPowerConst", expr, rat(root));
  }
  Rational r = expr[0][0].getRational();
  Expr res = expr[0][1].eqExpr(rat(root));
  if (r % 2 == 0) {
    res = res.orExpr(expr[0][1].eqExpr(rat(-root)));
  }
  return newRWTheorem(expr, res, Assumptions::emptyAssump(), pf);
}


// x^n = c <=> false (if n is even and c is negative)
Theorem ArithTheoremProducer::evenPowerEqNegConst(const Expr& expr)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(expr.isEq() && isPow(expr[0]) &&
                expr[1].isRational() &&
                isIntegerConst(expr[0][0]) &&
                expr[0][0].getRational() % 2 == 0 &&
                expr[1].getRational() < 0,
                "evenPowerEqNegConst invariant violated"+expr.toString());
  }
  Proof pf;
  if (withProof()) {
    pf = newPf("evenPowerEqNegConst", expr);
  }
  return newRWTheorem(expr, d_em->falseExpr(), Assumptions::emptyAssump(), pf);
}


// x^n = c <=> false (if x is an integer and c is not a perfect n power)
Theorem ArithTheoremProducer::intEqIrrational(const Expr& expr, const Theorem& isIntx)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(expr.isEq() && isPow(expr[0]) &&
                expr[1].isRational() &&
                expr[1].getRational() != 0 &&
                isIntegerConst(expr[0][0]) &&
                expr[0][0].getRational() > 0 &&
                ratRoot(expr[1].getRational(), expr[0][0].getRational().getUnsigned()) == 0,
                "intEqIrrational invariant violated"+expr.toString());
    CHECK_SOUND(isIntPred(isIntx.getExpr()) && isIntx.getExpr()[0] == expr[0][1],
		"ArithTheoremProducerOld::intEqIrrational:\n "
		"wrong integrality constraint:\n expr = "
		+expr.toString()+"\n isIntx = "
		+isIntx.getExpr().toString());
  }
  const Assumptions& assump(isIntx.getAssumptionsRef());
  Proof pf;
  if (withProof()) {
    pf = newPf("int_eq_irr", expr, isIntx.getProof());
  }
  return newRWTheorem(expr, d_em->falseExpr(), assump, pf);
}


// e[0] kind e[1] <==> true when e[0] kind e[1],
// false when e[0] !kind e[1], for constants only
Theorem ArithTheoremProducer::constPredicate(const Expr& e) {
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
                  "ArithTheoremProducer::constPredicate: wrong kind");
    }
    break;
  }
  Expr ret = (result) ? d_em->trueExpr() : d_em->falseExpr();
  if(withProof()) pf = newPf("const_predicate", e,ret);
  return newRWTheorem(e, ret, Assumptions::emptyAssump(), pf);
}


// e[0] kind e[1] <==> 0 kind e[1] - e[0]
Theorem ArithTheoremProducer::rightMinusLeft(const Expr& e)
{
  Proof pf;
  int kind = e.getKind();
  if(CHECK_PROOFS) {
    CHECK_SOUND((EQ==kind) ||
                (LT==kind) ||
                (LE==kind) ||
                (GE==kind) ||
                (GT==kind),
                "ArithTheoremProduder::rightMinusLeft: wrong kind");
  }
  if(withProof()) pf = newPf("right_minus_left",e);
  return newRWTheorem(e, Expr(e.getOp(), rat(0), e[1] - e[0]), Assumptions::emptyAssump(), pf);
}

// e[0] kind e[1] <==> 0 kind e[1] - e[0]
Theorem ArithTheoremProducer::leftMinusRight(const Expr& e)
{
  Proof pf;
  int kind = e.getKind();
  if(CHECK_PROOFS) {
    CHECK_SOUND((EQ==kind) ||
                (LT==kind) ||
                (LE==kind) ||
                (GE==kind) ||
                (GT==kind),
                "ArithTheoremProduder::rightMinusLeft: wrong kind");
  }
  if(withProof()) pf = newPf("left_minus_right",e);
  return newRWTheorem(e, Expr(e.getOp(), e[0] - e[1], rat(0)), Assumptions::emptyAssump(), pf);
}



// x kind y <==> x + z kind y + z
Theorem ArithTheoremProducer::plusPredicate(const Expr& x,
                                      const Expr& y,
                                      const Expr& z, int kind) {
  if(CHECK_PROOFS) {
    CHECK_SOUND((EQ==kind) ||
                (LT==kind) ||
                (LE==kind) ||
                (GE==kind) ||
                (GT==kind),
                "ArithTheoremProduder::plusPredicate: wrong kind");
  }
  Proof pf;
  Expr left = Expr(kind, x, y);
  Expr right = Expr(kind, x + z, y + z);
  if(withProof()) pf = newPf("plus_predicate",left,right);
  return newRWTheorem(left, right, Assumptions::emptyAssump(), pf);
}

// x = y <==> x * z = y * z
Theorem ArithTheoremProducer::multEqn(const Expr& x,
                                      const Expr& y,
                                      const Expr& z) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(z.isRational() && z.getRational() != 0,
		"ArithTheoremProducer::multEqn(): multiplying equation by 0");
  if(withProof()) pf = newPf("mult_eqn", x, y, z);
  return newRWTheorem(x.eqExpr(y), (x * z).eqExpr(y * z), Assumptions::emptyAssump(), pf);
}


// x = y <==> z=0 OR x * 1/z = y * 1/z
Theorem ArithTheoremProducer::divideEqnNonConst(const Expr& x,
                                                const Expr& y,
                                                const Expr& z) {
  Proof pf;
  if(withProof()) pf = newPf("mult_eqn_nonconst", x, y, z);
  return newRWTheorem(x.eqExpr(y), (z.eqExpr(rat(0))).orExpr((x / z).eqExpr(y / z)),
                      Assumptions::emptyAssump(), pf);
}


// if z is +ve, return e[0] LT|LE|GT|GE e[1] <==> e[0]*z LT|LE|GT|GE e[1]*z
// if z is -ve, return e[0] LT|LE|GT|GE e[1] <==> e[1]*z LT|LE|GT|GE e[0]*z
Theorem ArithTheoremProducer::multIneqn(const Expr& e, const Expr& z) {

	// Check the proofs in necessary
  	if(CHECK_PROOFS) {
    	CHECK_SOUND(isIneq(e), "ArithTheoremProduder::multIneqn: wrong kind");
    	CHECK_SOUND(z.isRational() && z.getRational() != 0, "ArithTheoremProduder::multIneqn: z must be non-zero rational: " + z.toString());
  	}

  	// Operation of the expression
  	Op op(e.getOp());

    // Calculate the returning expression
  	Expr ret;
  	// If constant is positive, just multiply both sides
  	if(0 < z.getRational())
    	ret = Expr(op, e[0]*z, e[1]*z);
  	else
  		// The constant is negative, reverse the relation
  		switch (e.getKind()) {
  			case LE: ret = geExpr(e[0]*z, e[1]*z); break;
  			case LT: ret = gtExpr(e[0]*z, e[1]*z); break;
  			case GE: ret = leExpr(e[0]*z, e[1]*z); break;
  			case GT: ret = ltExpr(e[0]*z, e[1]*z); break;
  			default:
  				//TODO: exception, we shouldn't be here
  				break;
  		}

  	// If we need the proof, set it up
  	Proof pf;
  	if(withProof()) pf = newPf("mult_ineqn", e, ret);

  	// Return the explaining rewrite theorem
  	return newRWTheorem(e, ret, Assumptions::emptyAssump(), pf);
}

//// multiply a canonised expression e = e[0] @ 0 with a constant c
//Theorem ArithTheoremProducer::multConst(const Expr& e, const Rational c)
//{
//	// The proof object
//	Proof pf;
//
//	// The resulting expression
//	Expr ret;
//
//	// If expression is just a rational multiply it and thats it
//	if (e[0].isRational())
//		ret = rat(e[0].getRational() * c);
//	// The expression is a canonised sum, multiply each one
//	else {
//		// Vector to hold all the sum children
//		vector<Expr> sumKids;
//
//		// Put all the sum children to the sumKids vector
//		for(Expression::iterator m = e[0].begin(); m != e[0].end(); m ++) {
//			// The current term in the sum
//			const Expr& sumTerm = (*m);
//
//			// If the child is rational, just multiply it
//			if (sumTerm.isRational()) sumKids.push_back(rat(sumTerm.getRational() * c));
//			// Otherwise multiply the coefficient with c and add it to the sumKids (TODO: Is the multiplication binary???)
//			else sumKids.pushBack(multExpr(rat(c * sumTerm[0].getRational()), sumTerm[1]));
//		}
//
//		// The resulting expression is the sum of the sumKids
//		ret = plusExpr(sumKids);
//	}
//
//	// If proof is needed set it up
//	if(withProof()) pf = newPf("arith_mult_const", e, ret);
//
//  	// Return the theorem explaining the multiplication
//  	return newRWTheorem(e, ret, Assumptions::emptyAssump(), pf);
//}



// "op1 GE|GT op2" <==> op2 LE|LT op1
Theorem ArithTheoremProducer::flipInequality(const Expr& e)
{
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGT(e) || isGE(e),
                "ArithTheoremProducer::flipInequality: wrong kind: " +
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
Theorem ArithTheoremProducer::negatedInequality(const Expr& e)
{
  const Expr& ineq = e[0];
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot(),
                "ArithTheoremProducer::negatedInequality: wrong kind: " +
                e.toString());
    CHECK_SOUND(isIneq(ineq),
                "ArithTheoremProducer::negatedInequality: wrong kind: " +
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
Theorem ArithTheoremProducer::realShadow(const Theorem& alphaLTt,
                                         const Theorem& tLTbeta)
{
  const Expr& expr1 = alphaLTt.getExpr();
  const Expr& expr2 = tLTbeta.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND((isLE(expr1) || isLT(expr1)) &&
                (isLE(expr2) || isLT(expr2)),
                "ArithTheoremProducer::realShadow: Wrong Kind: " +
                alphaLTt.toString() +  tLTbeta.toString());

    CHECK_SOUND(expr1[1] == expr2[0],
                "ArithTheoremProducer::realShadow:"
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
Theorem ArithTheoremProducer::realShadowEq(const Theorem& alphaLEt,
                                           const Theorem& tLEalpha)
{
  const Expr& expr1 = alphaLEt.getExpr();
  const Expr& expr2 = tLEalpha.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isLE(expr1) && isLE(expr2),
                "ArithTheoremProducer::realShadowLTLE: Wrong Kind: " +
                alphaLEt.toString() +  tLEalpha.toString());

    CHECK_SOUND(expr1[1] == expr2[0],
                "ArithTheoremProducer::realShadowLTLE:"
                " t must be same for both inputs: " +
                alphaLEt.toString() + " , " + tLEalpha.toString());

    CHECK_SOUND(expr1[0] == expr2[1],
                "ArithTheoremProducer::realShadowLTLE:"
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
ArithTheoremProducer::finiteInterval(const Theorem& aLEt,
				     const Theorem& tLEac,
				     const Theorem& isInta,
				     const Theorem& isIntt) {
  const Expr& e1 = aLEt.getExpr();
  const Expr& e2 = tLEac.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isLE(e1) && isLE(e2),
		"ArithTheoremProducer::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // term 't' is the same in both inequalities
    CHECK_SOUND(e1[1] == e2[0],
		"ArithTheoremProducer::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // RHS in e2 is (a+c)
    CHECK_SOUND(isPlus(e2[1]) && e2[1].arity() == 2,
		"ArithTheoremProducer::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // term 'a' in LHS of e1 and RHS of e2 is the same
    CHECK_SOUND(e1[0] == e2[1][0],
		"ArithTheoremProducer::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // 'c' in the RHS of e2 is a positive integer constant
    CHECK_SOUND(e2[1][1].isRational() && e2[1][1].getRational().isInteger()
		&& e2[1][1].getRational() >= 1,
		"ArithTheoremProducer::finiteInterval:\n e1 = "
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
Theorem ArithTheoremProducer::darkGrayShadow2ab(const Theorem& betaLEbx,
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
                "ArithTheoremProducer::darkGrayShadow2ab: Wrong Kind: " +
                betaLEbx.toString() +  axLEalpha.toString());
  }

  const Expr& beta = expr1[0];
  const Expr& bx = expr1[1];
  const Expr& ax = expr2[0];
  const Expr& alpha = expr2[1];
  Rational a = isMult(ax)? ax[0].getRational() : 1;
  Rational b = isMult(bx)? bx[0].getRational() : 1;
  const Expr& x = isMult(ax)? ax[1] : ax;

  if(CHECK_PROOFS) {
    // Integrality constraints
    CHECK_SOUND(isIntPred(isIntAlphaExpr) && isIntAlphaExpr[0] == alpha,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n alpha = "
		+alpha.toString()+"\n isIntAlpha = "
		+isIntAlphaExpr.toString());
    CHECK_SOUND(isIntPred(isIntBetaExpr) && isIntBetaExpr[0] == beta,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n beta = "
		+beta.toString()+"\n isIntBeta = "
		+isIntBetaExpr.toString());
    CHECK_SOUND(isIntPred(isIntxExpr) && isIntxExpr[0] == x,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n x = "
		+x.toString()+"\n isIntx = "
		+isIntxExpr.toString());
    // Expressions ax and bx should match on x
    CHECK_SOUND(!isMult(ax) || ax.arity() == 2,
		"ArithTheoremProducer::darkGrayShadow2ab:\n ax<=alpha: " +
                axLEalpha.toString());
    CHECK_SOUND(!isMult(bx) || (bx.arity() == 2 && bx[1] == x),
		"ArithTheoremProducer::darkGrayShadow2ab:\n beta<=bx: "
		+betaLEbx.toString()
		+"\n ax<=alpha: "+ axLEalpha.toString());
    CHECK_SOUND(1 <= a && a <= b && 2 <= b,
		"ArithTheoremProducer::darkGrayShadow2ab:\n beta<=bx: "
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
  Expr d = darkShadow(rat(a*b-1), t);
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

  return newTheorem((d || g) && (!d || !g), A, pf);
}

// Dark & Gray shadows when b <= a
Theorem ArithTheoremProducer::darkGrayShadow2ba(const Theorem& betaLEbx,
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
                "ArithTheoremProducer::darkGrayShadow2ba: Wrong Kind: " +
                betaLEbx.toString() +  axLEalpha.toString());
  }

  const Expr& beta = expr1[0];
  const Expr& bx = expr1[1];
  const Expr& ax = expr2[0];
  const Expr& alpha = expr2[1];
  Rational a = isMult(ax)? ax[0].getRational() : 1;
  Rational b = isMult(bx)? bx[0].getRational() : 1;
  const Expr& x = isMult(ax)? ax[1] : ax;

  if(CHECK_PROOFS) {
    // Integrality constraints
    CHECK_SOUND(isIntPred(isIntAlphaExpr) && isIntAlphaExpr[0] == alpha,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n alpha = "
		+alpha.toString()+"\n isIntAlpha = "
		+isIntAlphaExpr.toString());
    CHECK_SOUND(isIntPred(isIntBetaExpr) && isIntBetaExpr[0] == beta,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n beta = "
		+beta.toString()+"\n isIntBeta = "
		+isIntBetaExpr.toString());
    CHECK_SOUND(isIntPred(isIntxExpr) && isIntxExpr[0] == x,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n x = "
		+x.toString()+"\n isIntx = "
		+isIntxExpr.toString());
    // Expressions ax and bx should match on x
    CHECK_SOUND(!isMult(ax) || ax.arity() == 2,
		"ArithTheoremProducer::darkGrayShadow2ba:\n ax<=alpha: " +
                axLEalpha.toString());
    CHECK_SOUND(!isMult(bx) || (bx.arity() == 2 && bx[1] == x),
		"ArithTheoremProducer::darkGrayShadow2ba:\n beta<=bx: "
		+betaLEbx.toString()
		+"\n ax<=alpha: "+ axLEalpha.toString());
    CHECK_SOUND(1 <= b && b <= a && 2 <= a,
		"ArithTheoremProducer::darkGrayShadow2ba:\n beta<=bx: "
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
  Expr d = darkShadow(rat(a*b-1), t);
  Expr g = grayShadow(bx, beta, 0, b-1);
  return newTheorem((d || g) && (!d || !g), A, pf);
}

/*! takes a dark shadow and expands it into an inequality.
*/
Theorem ArithTheoremProducer::expandDarkShadow(const Theorem& darkShadow) {
  const Expr& theShadow = darkShadow.getExpr();
  if(CHECK_PROOFS){
    CHECK_SOUND(isDarkShadow(theShadow),
		"ArithTheoremProducer::expandDarkShadow: not DARK_SHADOW: " +
		theShadow.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("expand_dark_shadow", theShadow, darkShadow.getProof());
  return newTheorem(leExpr(theShadow[0], theShadow[1]), darkShadow.getAssumptionsRef(), pf);
}


// takes a grayShadow (c1==c2) and expands it into an equality
Theorem ArithTheoremProducer::expandGrayShadow0(const Theorem& grayShadow) {
  const Expr& theShadow = grayShadow.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducer::expandGrayShadowConst0:"
		" not GRAY_SHADOW: " +
		theShadow.toString());
    CHECK_SOUND(theShadow[2] == theShadow[3],
		"ArithTheoremProducer::expandGrayShadow0: c1!=c2: " +
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
Theorem ArithTheoremProducer::splitGrayShadow(const Theorem& gThm) {
  const Expr& theShadow = gThm.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducer::expandGrayShadowConst: not a shadow" +
		theShadow.toString());
  }

  const Rational& c1 = theShadow[2].getRational();
  const Rational& c2 = theShadow[3].getRational();

  if(CHECK_PROOFS) {
    CHECK_SOUND(c1.isInteger() && c2.isInteger() && c1 < c2,
		"ArithTheoremProducer::expandGrayShadow: " +
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


Theorem ArithTheoremProducer::expandGrayShadow(const Theorem& gThm) {
  const Expr& theShadow = gThm.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducer::expandGrayShadowConst: not a shadow" +
		theShadow.toString());
  }

  const Rational& c1 = theShadow[2].getRational();
  const Rational& c2 = theShadow[3].getRational();

  if(CHECK_PROOFS) {
    CHECK_SOUND(c1.isInteger() && c2.isInteger() && c1 < c2,
		"ArithTheoremProducer::expandGrayShadow: " +
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
ArithTheoremProducer::expandGrayShadowConst(const Theorem& gThm) {
  const Expr& theShadow = gThm.getExpr();
  const Expr& ax = theShadow[0];
  const Expr& cExpr = theShadow[1];
  const Expr& bExpr = theShadow[2];

  if(CHECK_PROOFS) {
    CHECK_SOUND(!isMult(ax) || ax[0].isRational(),
		"ArithTheoremProducer::expandGrayShadowConst: "
		"'a' in a*x is not a const: " +theShadow.toString());
  }

  Rational a = isMult(ax)? ax[0].getRational() : 1;

  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducer::expandGrayShadowConst: "
		"not a GRAY_SHADOW: " +theShadow.toString());
    CHECK_SOUND(a.isInteger() && a >= 1,
		"ArithTheoremProducer::expandGrayShadowConst: "
		"'a' is not integer: " +theShadow.toString());
    CHECK_SOUND(cExpr.isRational(),
		"ArithTheoremProducer::expandGrayShadowConst: "
		"'c' is not rational" +theShadow.toString());
    CHECK_SOUND(bExpr.isRational() && bExpr.getRational().isInteger(),
		"ArithTheoremProducer::expandGrayShadowConst: b not integer: "
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
ArithTheoremProducer::grayShadowConst(const Theorem& gThm) {
  const Expr& g = gThm.getExpr();
  bool checkProofs(CHECK_PROOFS);
  if(checkProofs) {
    CHECK_SOUND(isGrayShadow(g), "ArithTheoremProducer::grayShadowConst("
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
		"ArithTheoremProducer::grayShadowConst("+g.toString()+")");
    CHECK_SOUND(aExpr.isRational(),
		"ArithTheoremProducer::grayShadowConst("+g.toString()+")");
  }

  const Rational& a = aExpr.getRational();
  const Rational& c = e.getRational();

  if(checkProofs) {
    CHECK_SOUND(a.isInteger() && a >= 2,
		"ArithTheoremProducer::grayShadowConst("+g.toString()+")");
  }

  Rational newC1 = ceil((c1+c)/a), newC2 = floor((c2+c)/a);
  Expr newG((newC1 > newC2)? d_em->falseExpr()
	    : grayShadow(x, rat(0), newC1, newC2));
  Proof pf;
  if(withProof())
    pf = newPf("gray_shadow_const", g, newG, gThm.getProof());
  return newTheorem(newG, gThm.getAssumptionsRef(), pf);
}


Rational ArithTheoremProducer::constRHSGrayShadow(const Rational& c,
						  const Rational& b,
						  const Rational& a) {
  DebugAssert(c.isInteger() &&
	      b.isInteger() &&
	      a.isInteger() &&
	      b != 0,
	      "ArithTheoremProducer::constRHSGrayShadow: a, b, c must be ints");
  if (b > 0)
    return mod(c+b, a);
  else
    return mod(a-(c+b), a);
}

/*! Takes a Theorem(\\alpha < \\beta) and returns
 *  Theorem(\\alpha < \\beta <==> \\alpha <= \\beta -1)
 * where \\alpha and \\beta are integer expressions
 */
Theorem ArithTheoremProducer::lessThanToLE(const Theorem& less,
					   const Theorem& isIntLHS,
					   const Theorem& isIntRHS,
					   bool changeRight) {
  const Expr& ineq = less.getExpr();
  const Expr& isIntLHSexpr = isIntLHS.getExpr();
  const Expr& isIntRHSexpr = isIntRHS.getExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(isLT(ineq),
		"ArithTheoremProducer::LTtoLE: ineq must be <");
    // Integrality check
    CHECK_SOUND(isIntPred(isIntLHSexpr)	&& isIntLHSexpr[0] == ineq[0],
		"ArithTheoremProducer::lessThanToLE: bad integrality check:\n"
		" ineq = "+ineq.toString()+"\n isIntLHS = "
		+isIntLHSexpr.toString());
    CHECK_SOUND(isIntPred(isIntRHSexpr) && isIntRHSexpr[0] == ineq[1],
		"ArithTheoremProducer::lessThanToLE: bad integrality check:\n"
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
	       ineq, le, pfs);
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
ArithTheoremProducer::intVarEqnConst(const Expr& eqn,
				     const Theorem& isIntx) {
  const Expr& left(eqn[0]);
  const Expr& right(eqn[1]);
  const Expr& isIntxexpr(isIntx.getExpr());

  if(CHECK_PROOFS) {
    CHECK_SOUND((isMult(right) && right[0].isRational())
                || (right.arity() == 2 && isPlus(right)
                    && right[0].isRational()
                    && ((!isMult(right[1]) || right[1][0].isRational()))),
                "ArithTheoremProducer::intVarEqnConst: "
		"rhs has a wrong format: " + right.toString());
    CHECK_SOUND(left.isRational() && 0 == left.getRational(),
                "ArithTheoremProducer:intVarEqnConst:left is not a zero: " +
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
                "ArithTheoremProducer:intVarEqnConst: "
		"bad integrality constraint:\n right = " +
                right.toString()+"\n isIntx = "+isIntxexpr.toString());
    CHECK_SOUND(a!=0, "ArithTheoremProducer:intVarEqnConst: eqn = "
		+eqn.toString());
  }
  const Assumptions& assump(isIntx.getAssumptionsRef());
  Proof pf;
  if(withProof())
    pf = newPf("int_const_eq", eqn, isIntx.getProof());

  // Solve for x:   x = r = -c/a
  Rational r(-c/a);

  if(r.isInteger())
    return newRWTheorem(eqn, x.eqExpr(rat(r)), assump, pf);
  else
    return newRWTheorem(eqn, d_em->falseExpr(), assump, pf);
}


Expr
ArithTheoremProducer::create_t(const Expr& eqn) {
  const Expr& lhs = eqn[0];
  DebugAssert(isMult(lhs),
              CLASS_NAME "create_t : lhs must be a MULT"
              + lhs.toString());
  const Expr& x = lhs[1];
  Rational m = lhs[0].getRational()+1;
  DebugAssert(m > 0, "ArithTheoremProducer::create_t: m = "+m.toString());
  vector<Expr> kids;
  if(isPlus(eqn[1]))
    sumModM(kids, eqn[1], m, m);
  else
    kids.push_back(monomialModM(eqn[1], m, m));

  kids.push_back(multExpr(rat(1/m), x));
  return plusExpr(kids);
}

Expr
ArithTheoremProducer::create_t2(const Expr& lhs, const Expr& rhs,
				const Expr& sigma) {
  Rational m = lhs[0].getRational()+1;
  DebugAssert(m > 0, "ArithTheoremProducer::create_t2: m = "+m.toString());
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
ArithTheoremProducer::create_t3(const Expr& lhs, const Expr& rhs,
				const Expr& sigma) {
  const Rational& a = lhs[0].getRational();
  Rational m = a+1;
  DebugAssert(m > 0, "ArithTheoremProducer::create_t3: m = "+m.toString());
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
ArithTheoremProducer::modEq(const Rational& i, const Rational& m) {
  DebugAssert(m > 0, "ArithTheoremProducer::modEq: m = "+m.toString());
  Rational half(1,2);
  Rational res((i - m*(floor((i/m) + half))));
  TRACE("arith eq", "modEq("+i.toString()+", "+m.toString()+") = ", res, "");
  return res;
}

Rational
ArithTheoremProducer::f(const Rational& i, const Rational& m) {
  DebugAssert(m > 0, "ArithTheoremProducer::f: m = "+m.toString());
  Rational half(1,2);
  return (floor(i/m + half)+modEq(i,m));
}

void
ArithTheoremProducer::sumModM(vector<Expr>& summands, const Expr& sum,
                              const Rational& m, const Rational& divisor) {
  DebugAssert(divisor != 0, "ArithTheoremProducer::sumModM: divisor = "
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
ArithTheoremProducer::monomialModM(const Expr& i,
                                   const Rational& m, const Rational& divisor)
{
  DebugAssert(divisor != 0, "ArithTheoremProducer::monomialModM: divisor = "
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
  DebugAssert(!res.isNull(), "ArithTheoremProducer::monomialModM()");
  TRACE("arith eq", "monomialModM(i="+i.toString()+", m="+m.toString()
	+", div="+divisor.toString()+") = ", res, "");
  return res;
}

void
ArithTheoremProducer::sumMulF(vector<Expr>& summands, const Expr& sum,
                              const Rational& m, const Rational& divisor) {
  DebugAssert(divisor != 0, "ArithTheoremProducer::sumMulF: divisor = "
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
ArithTheoremProducer::monomialMulF(const Expr& i,
                                   const Rational& m, const Rational& divisor)
{
  DebugAssert(divisor != 0, "ArithTheoremProducer::monomialMulF: divisor = "
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
ArithTheoremProducer::substitute(const Expr& term, ExprMap<Expr>& eMap)
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

bool ArithTheoremProducer::greaterthan(const Expr & l, const Expr & r)
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
Theorem ArithTheoremProducer::IsIntegerElim(const Theorem& isIntx)
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
ArithTheoremProducer::eqElimIntRule(const Theorem& eqn, const Theorem& isIntx,
				    const vector<Theorem>& isIntVars) {
  TRACE("arith eq", "eqElimIntRule(", eqn.getExpr(), ") {");
  Proof pf;

  if(CHECK_PROOFS)
    CHECK_SOUND(eqn.isRewrite(),
                "ArithTheoremProducer::eqElimInt: input must be an equation" +
                eqn.toString());

  const Expr& lhs = eqn.getLHS();
  const Expr& rhs = eqn.getRHS();
  Expr a, x;
  d_theoryArith->separateMonomial(lhs, a, x);

  if(CHECK_PROOFS) {
    // Checking LHS
    const Expr& isIntxe = isIntx.getExpr();
    CHECK_SOUND(isIntPred(isIntxe) && isIntxe[0] == x,
		"ArithTheoremProducer::eqElimInt\n eqn = "
		+eqn.getExpr().toString()
		+"\n isIntx = "+isIntxe.toString());
    CHECK_SOUND(isRational(a) && a.getRational().isInteger()
		&& a.getRational() >= 2,
		"ArithTheoremProducer::eqElimInt:\n lhs = "+lhs.toString());
    // Checking RHS
    // It cannot be a division (we don't handle it)
    CHECK_SOUND(!isDivide(rhs),
		"ArithTheoremProducer::eqElimInt:\n rhs = "+rhs.toString());
    // If it's a single monomial, then it's the only "variable"
    if(!isPlus(rhs)) {
      Expr c, v;
      d_theoryArith->separateMonomial(rhs, c, v);
      CHECK_SOUND(isIntVars.size() == 1
		  && isIntPred(isIntVars[0].getExpr())
		  && isIntVars[0].getExpr()[0] == v
		  && isRational(c) && c.getRational().isInteger(),
		  "ArithTheoremProducer::eqElimInt:\n rhs = "+rhs.toString()
		  +"isIntVars.size = "+int2string(isIntVars.size()));
    } else { // RHS is a plus
      CHECK_SOUND(isIntVars.size() + 1 == (size_t)rhs.arity(),
		  "ArithTheoremProducer::eqElimInt: rhs = "+rhs.toString());
      // Check the free constant
      CHECK_SOUND(isRational(rhs[0]) && rhs[0].getRational().isInteger(),
		  "ArithTheoremProducer::eqElimInt: rhs = "+rhs.toString());
      // Check the vars
      for(size_t i=0, iend=isIntVars.size(); i<iend; ++i) {
	Expr c, v;
	d_theoryArith->separateMonomial(rhs[i+1], c, v);
	const Expr& isInt(isIntVars[i].getExpr());
	CHECK_SOUND(isIntPred(isInt) && isInt[0] == v
		    && isRational(c) && c.getRational().isInteger(),
		    "ArithTheoremProducer::eqElimInt:\n rhs["+int2string(i+1)
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
    pf = newPf("eq_elim_int", eqn.getExpr(), res , pfs);
  }

  Theorem thm(newTheorem(res, assump, pf));
  TRACE("arith eq", "eqElimIntRule => ", thm.getExpr(), " }");
  return thm;
}


Theorem
ArithTheoremProducer::isIntConst(const Expr& e) {
  Proof pf;

  if(CHECK_PROOFS) {
    CHECK_SOUND(isIntPred(e) && e[0].isRational(),
		"ArithTheoremProducer::isIntConst(e = "
		+e.toString()+")");
  }
  if(withProof())
    pf = newPf("is_int_const", e);
  bool isInt = e[0].getRational().isInteger();
  return newRWTheorem(e, isInt? d_em->trueExpr() : d_em->falseExpr(), Assumptions::emptyAssump(), pf);
}


Theorem
ArithTheoremProducer::equalLeaves1(const Theorem& thm)
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
ArithTheoremProducer::equalLeaves2(const Theorem& thm)
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
ArithTheoremProducer::equalLeaves3(const Theorem& thm)
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
ArithTheoremProducer::equalLeaves4(const Theorem& thm)
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
ArithTheoremProducer::diseqToIneq(const Theorem& diseq) {
  Proof pf;

  const Expr& e = diseq.getExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot() && e[0].isEq(),
		"ArithTheoremProducer::diseqToIneq: expected disequality:\n"
		" e = "+e.toString());
  }

  const Expr& x = e[0][0];
  const Expr& y = e[0][1];

  if(withProof())
    pf = newPf(e, diseq.getProof());
  return newTheorem(ltExpr(x,y).orExpr(gtExpr(x,y)), diseq.getAssumptionsRef(), pf);
}

Theorem ArithTheoremProducer::moveSumConstantRight(const Expr& e) {

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

Theorem ArithTheoremProducer::eqToIneq(const Expr& e) {

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

Theorem ArithTheoremProducer::dummyTheorem(const Expr& e) {
	Proof pf;
	return newRWTheorem(e, d_em->trueExpr(), Assumptions::emptyAssump(), pf);
}

Theorem ArithTheoremProducer::oneElimination(const Expr& e) {

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

Theorem ArithTheoremProducer::clashingBounds(const Theorem& lowerBound, const Theorem& upperBound) {

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

Theorem ArithTheoremProducer::addInequalities(const Theorem& thm1, const Theorem& thm2) {

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

Theorem ArithTheoremProducer::implyWeakerInequality(const Expr& expr1, const Expr& expr2) {

	// Check soundness
	if (CHECK_PROOFS) {

		// Both must be inequalitites
		CHECK_SOUND(isIneq(expr1), "implyWeakerInequality: expr1 should be an inequality" + expr1.toString());
		CHECK_SOUND(isIneq(expr2), "implyWeakerInequality: expr1 should be an inequality" + expr2.toString());

		bool type_less_than = true;

		// Should be of the same type
		if (isLE(expr1) || isLT(expr1))
			CHECK_SOUND(isLE(expr2) || isLT(expr2), "implyWeakerInequality: expr2 should be <(=) also " + expr2.toString());
		if (isGE(expr1) || isGT(expr1)) {
			CHECK_SOUND(isGE(expr2) || isGT(expr2), "implyWeakerInequality: expr2 should be >(=) also" + expr2.toString());
			type_less_than = false;
		}

		// Left sides must be rational numbers
		CHECK_SOUND(expr1[0].isRational(), "implyWeakerInequality: expr1 should have a rational on the left side" + expr1.toString());
		CHECK_SOUND(expr2[0].isRational(), "implyWeakerInequality: expr2 should have a rational on the left side" + expr2.toString());

		// Right sides must be identical
		CHECK_SOUND(expr1[1] == expr2[1], "implyWeakerInequality: the expression must be the same" + expr1.toString() + " and " + expr2.toString());

		Rational expr1rat = expr1[0].getRational();
		Rational expr2rat = expr2[0].getRational();


		// Check the bounds
		if (type_less_than) {
			if (isLE(expr1) || isLT(expr2)) {
				CHECK_SOUND(expr2rat < expr1rat,  "implyWeakerInequality: the implication doesn't apply" + expr1.toString() + " and " + expr2.toString());
			} else {
				CHECK_SOUND(expr2rat <= expr1rat, "implyWeakerInequality: the implication doesn't apply" + expr1.toString() + " and " + expr2.toString());
			}
		} else {
			if (isGE(expr1) || isGT(expr2)) {
				CHECK_SOUND(expr2rat > expr1rat,  "implyWeakerInequality: the implication doesn't apply" + expr1.toString() + " and " + expr2.toString());
			} else {
				CHECK_SOUND(expr2rat >= expr1rat, "implyWeakerInequality: the implication doesn't apply" + expr1.toString() + " and " + expr2.toString());
			}
		}
	}

  	// Create the proof object
  	Proof pf;
  	if(withProof())	pf = newPf("implyWeakerInequality", expr1, expr2);

	// Return the theorem
	return newTheorem(expr1.impExpr(expr2), Assumptions::emptyAssump(), pf);
}

Theorem ArithTheoremProducer::implyNegatedInequality(const Expr& expr1, const Expr& expr2) {

	// Check soundness
	if (CHECK_PROOFS) {
		CHECK_SOUND(isIneq(expr1), "implyNegatedInequality: lowerBound should be an inequality " + expr1.toString());
		CHECK_SOUND(isIneq(expr2), "implyNegatedInequality: upperBound should be be an inequality " + expr2.toString());
		CHECK_SOUND(expr1[0].isRational(), "implyNegatedInequality: lowerBound left side should be a rational " + expr1.toString());
		CHECK_SOUND(expr2[0].isRational(), "implyNegatedInequality: upperBound left side should be a rational " + expr2.toString());
		CHECK_SOUND(expr1[1] == expr2[1], "implyNegatedInequality: bounds not on the same term " + expr1.toString() + ", " + expr2.toString());

		// Get the bounds
		Rational lowerBoundR = expr1[0].getRational();
		Rational upperBoundR = expr2[0].getRational();

		if (isLE(expr1) && isGE(expr2))
			CHECK_SOUND(upperBoundR < lowerBoundR, "implyNegatedInequality: cant imply negation" + expr1.toString() + ", " + expr2.toString());
		if (isLT(expr1) || isGT(expr2))
			CHECK_SOUND(upperBoundR <= lowerBoundR, "implyNegatedInequality: cant imply negation" + expr1.toString() + ", " + expr2.toString());
		if (isGE(expr1) && isLE(expr2))
			CHECK_SOUND(upperBoundR > lowerBoundR, "implyNegatedInequality: cant imply negation" + expr1.toString() + ", " + expr2.toString());
		if (isGT(expr1) || isLT(expr2))
			CHECK_SOUND(upperBoundR >= lowerBoundR, "implyNegatedInequality: cant imply negation" + expr1.toString() + ", " + expr2.toString());
	}

	// The proof object that we will use
	Proof pf;
	if (withProof()) pf = newPf("implyNegatedInequality", expr1, expr2);

	// Return the theorem
	return newTheorem(expr1.impExpr(expr2.negate()), Assumptions::emptyAssump(), pf);
}

Theorem ArithTheoremProducer::trustedRewrite(const Expr& expr1, const Expr& expr2) {

	// The proof object that we will us
	Proof pf;

	// Setup the proof if needed
	if (withProof()) pf = newPf("trustedRewrite", expr1, expr2);

	// Return the rewrite theorem that explains the phenomenon
	return newRWTheorem(expr1, expr2, Assumptions::emptyAssump(), pf);

}

Theorem ArithTheoremProducer::integerSplit(const Expr& intVar, const Rational& intPoint) {

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


Theorem ArithTheoremProducer::rafineStrictInteger(const Theorem& isIntConstrThm, const Expr& constr) {


	// Check soundness
	if (CHECK_PROOFS) {
		// Right side of the constraint should correspond to the proved integer expression
		CHECK_SOUND(isIneq(constr), "rafineStrictInteger: expected a constraint got : " + constr.toString());
		CHECK_SOUND(isIntConstrThm.getExpr()[0] == constr[1], "rafineStrictInteger: proof of intger doesn't correspond to the constarint right side");
		CHECK_SOUND(constr[0].isRational(), "rafineStrictInteger: right side of the constraint muts be a rational");
	}

	// Get the contraint bound
	Rational bound = constr[0].getRational();

	// Get the kind of the constraint
	int kind = constr.getKind();

	// If the bound is strict, make it non-strict
	switch (kind) {
		case LT:
			kind = LE;
			if (bound.isInteger()) bound ++;             // 3 < x   --> 4 <= x
			else bound = ceil(bound);                    // 3.4 < x --> 4 <= x
			break;
		case LE:
			kind = LE;
			if (!bound.isInteger()) bound = ceil(bound); // 3.5 <= x --> 4 <= x
			break;
		case GT:
			kind = GE;
			if (bound.isInteger()) bound --;             // 3 > x   --> 2 >= x
			else bound = floor(bound);                   // 3.4 > x --> 3 >= x
			break;
		case GE:
			kind = GE;
			if (!bound.isInteger()) bound = floor(bound); // 3.4 >= x --> 3 >= x
			break;
	}

	// The new constraint
	Expr newConstr(kind, rat(bound), constr[1]);

	// Pick up the assumptions from the integer proof
	const Assumptions& assump(isIntConstrThm.getAssumptionsRef());

  	// Construct the proof object if necessary
  	Proof pf;
	if (withProof()) pf = newPf("rafineStrictInteger", constr, newConstr,isIntConstrThm.getProof());

	// Return the rewrite theorem that explains the phenomenon
	return newRWTheorem(constr, newConstr, assump, pf);
}

//
// This one is here just to compile... the code is in old arithmetic
Theorem ArithTheoremProducer::simpleIneqInt(const Expr& ineq, const Theorem& isIntRHS)
{
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

// Given:
// 0 = c + t
// where t is integer and c is not
// deduce bot
Theorem ArithTheoremProducer::intEqualityRationalConstant(const Theorem& isIntConstrThm, const Expr& constr) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

Theorem ArithTheoremProducer::cycleConflict(const vector<Theorem>& inequalitites) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

Theorem ArithTheoremProducer::implyEqualities(const vector<Theorem>& inequalitites) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

/*! Takes a Theorem(\\alpha < \\beta) and returns
 *  Theorem(\\alpha < \\beta <==> \\alpha <= \\beta -1)
 * where \\alpha and \\beta are integer expressions
 */
Theorem ArithTheoremProducer::lessThanToLERewrite(const Expr& ineq,
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


Theorem ArithTheoremProducer::splitGrayShadowSmall(const Theorem& gThm) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

Theorem ArithTheoremProducer::implyWeakerInequalityDiffLogic(const std::vector<Theorem>& antecedentThms, const Expr& implied) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

Theorem ArithTheoremProducer::implyNegatedInequalityDiffLogic(const std::vector<Theorem>& antecedentThms, const Expr& implied) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

Theorem ArithTheoremProducer::expandGrayShadowRewrite(const Expr& theShadow) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

Theorem ArithTheoremProducer::compactNonLinearTerm(const Expr& nonLinear) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

Theorem ArithTheoremProducer::nonLinearIneqSignSplit(const Theorem& ineqThm) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

Theorem ArithTheoremProducer::implyDiffLogicBothBounds(const Expr& x,
							std::vector<Theorem>& c1_le_x, Rational c1,
    						std::vector<Theorem>& x_le_c2, Rational c2) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

Theorem ArithTheoremProducer::addInequalities(const vector<Theorem>& thms) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}

Theorem ArithTheoremProducer::powerOfOne(const Expr& e) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}


////////////////////////////////////////////////////////////////////
// Stubs for ArithProofRules
////////////////////////////////////////////////////////////////////


Theorem ArithProofRules::rewriteLeavesConst(const Expr& e) {
	DebugAssert(false, "Not implemented!!!");
	return Theorem();
}
