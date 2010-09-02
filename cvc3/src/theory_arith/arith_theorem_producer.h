/*****************************************************************************/
/*!
 * \file arith_theorem_producer.h
 * \brief TRUSTED implementation of arithmetic proof rules
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

#ifndef _cvc3__arith_theorem_producer_h_
#define _cvc3__arith_theorem_producer_h_

#include "arith_proof_rules.h"
#include "theorem_producer.h"
#include "theory_arith_new.h"

namespace CVC3 {
  class TheoryArithNew;
  
  class ArithTheoremProducer: public ArithProofRules, public TheoremProducer {
    TheoryArithNew* d_theoryArith;
  private:
    /*! \name Auxiliary functions for eqElimIntRule()
     * Methods that compute the subterms used in eqElimIntRule()
     *@{
     */
    //! Compute the special modulus: i - m*floor(i/m+1/2)
    Rational modEq(const Rational& i, const Rational& m);
    //! Create the term 't'.  See eqElimIntRule().
    Expr create_t(const Expr& eqn);
    //! Create the term 't2'.  See eqElimIntRule().
    Expr create_t2(const Expr& lhs, const Expr& rhs, const Expr& t);
    //! Create the term 't3'.  See eqElimIntRule().
    Expr create_t3(const Expr& lhs, const Expr& rhs, const Expr& t);
    /*! @brief Takes sum = a_0 + a_1*x_1+...+a_n*x_n and returns the
     * vector of similar monomials (in 'summands') with coefficients
     * mod(a_i, m).  If divide flag is true, the coefficients will be
     * mod(a_i,m)/m.
     */
    void sumModM(std::vector<Expr>& summands, const Expr& sum,
		 const Rational& m, const Rational& divisor);
    Expr monomialModM(const Expr& e,
		      const Rational& m, const Rational& divisor);
    void sumMulF(std::vector<Expr>& summands, const Expr& sum,
		 const Rational& m, const Rational& divisor);
    Expr monomialMulF(const Expr& e,
		      const Rational& m, const Rational& divisor);
    //! Compute floor(i/m+1/2) + mod(i,m)
    Rational f(const Rational& i, const Rational& m);
    Expr substitute(const Expr& term, ExprMap<Expr>& eMap);

    /*@}*/
  public:
    //! Constructor
    ArithTheoremProducer(TheoremManager* tm, TheoryArithNew* theoryArith):
      TheoremProducer(tm), d_theoryArith(theoryArith) { }

    //! Create Expr from Rational (for convenience)
    Expr rat(Rational r) { return d_em->newRatExpr(r); }
    Type realType() { return d_theoryArith->realType(); }
    Type intType() { return d_theoryArith->intType(); }
    //! Construct the dark shadow expression representing lhs <= rhs
    Expr darkShadow(const Expr& lhs, const Expr& rhs) {
      return d_theoryArith->darkShadow(lhs, rhs);
    }
    //! Construct the gray shadow expression representing c1 <= v - e <= c2
    /*! Alternatively, v = e + i for some i s.t. c1 <= i <= c2
     */
    Expr grayShadow(const Expr& v, const Expr& e,
		    const Rational& c1, const Rational& c2) {
      return d_theoryArith->grayShadow(v, e, c1, c2);
    }

    ////////////////////////////////////////////////////////////////////
    // Canonization rules
    ////////////////////////////////////////////////////////////////////

    // ==> x = 1 * x
    virtual Theorem varToMult(const Expr& e);

    // ==> -(e) = (-1) * e
    virtual Theorem uMinusToMult(const Expr& e);

    // ==> x - y = x + (-1) * y
    virtual Theorem minusToPlus(const Expr& x, const Expr& y);

    // Rule for unary minus: it just converts it to division by -1,
    virtual Theorem canonUMinusToDivide(const Expr& e);

    // Rules for division by constant 'd'
    // (c) / d ==> (c/d), takes c and d
    virtual Theorem canonDivideConst(const Expr& c, const Expr& d);
    // (c * x) / d ==> (c/d) * x, takes (c*x) and d
    virtual Theorem canonDivideMult(const Expr& cx, const Expr& d);
    // (+ c ...)/d ==> push division to all the coefficients.
    // The result is not canonical, but canonizing the summands will
    // make it canonical.
    // Takes (+ c ...) and d
    virtual Theorem canonDividePlus(const Expr& e, const Expr& d);
    // x / d ==> (1/d) * x, takes x and d
    virtual Theorem canonDivideVar(const Expr& e1, const Expr& e2);

    // Canon Rules for multiplication

    // TODO Deepak:
    // t1 * t2 where t1 and t2 are canonized expressions, i.e. it can be a
    // 1) Rational constant
    // 2) Arithmetic Leaf (var or term from another theory)
    // 3) (POW rational leaf)
    // 4) (MULT rational mterm'_1 ...) where each mterm' is of type (2) or (3)
    // 5) (PLUS rational sterm_1 sterm_2 ...) where each sterm is of 
    //     type (2) or (3) or (4) 

    static bool greaterthan(const Expr &, const Expr &);
    virtual Expr simplifiedMultExpr(std::vector<Expr> & mulKids);
    virtual Expr canonMultConstMult(const Expr & c, const Expr & e);
    virtual Expr canonMultConstPlus(const Expr & e1, const Expr & e2);
    virtual Expr canonMultPowPow(const Expr & e1, const Expr & e2);
    virtual Expr canonMultPowLeaf(const Expr & e1, const Expr & e2);
    virtual Expr canonMultLeafLeaf(const Expr & e1, const Expr & e2);
    virtual Expr canonMultLeafOrPowMult(const Expr & e1, const Expr & e2);
    virtual Expr canonCombineLikeTerms(const std::vector<Expr> & sumExprs);
    virtual Expr 
	canonMultLeafOrPowOrMultPlus(const Expr & e1, const Expr & e2);
    virtual Expr canonMultPlusPlus(const Expr & e1, const Expr & e2);
    virtual Theorem canonMultMtermMterm(const Expr& e);
    virtual Theorem canonPlus(const Expr & e);
    virtual Theorem canonInvertConst(const Expr & e);
    virtual Theorem canonInvertLeaf(const Expr & e);
    virtual Theorem canonInvertPow(const Expr & e);
    virtual Theorem canonInvertMult(const Expr & e);
    virtual Theorem canonInvert(const Expr & e);

    /**
     * Transform e = (SUM r t1 ... tn) @ 0 into (SUM t1 ... tn) @ -r. The first 
     * sum term (r) must be a rational and t1 ... tn terms must be canonised.
     * 
     * @param e the expression to transform 
     * @return rewrite theorem representing the transformation  
     */
    virtual Theorem moveSumConstantRight(const Expr& e);

    /** e[0]/e[1] ==> e[0]*(e[1])^-1 */
    virtual Theorem canonDivide(const Expr & e);
    
    /** Multiply out the operands of the multiplication (each of them is expected to be canonised */
    virtual Theorem canonMult(const Expr & e);

    // t*c ==> c*t, takes constant c and term t
    virtual Theorem canonMultTermConst(const Expr& c, const Expr& t);
    // t1*t2 ==> Error, takes t1 and t2 where both are non-constants
    virtual Theorem canonMultTerm1Term2(const Expr& t1, const Expr& t2);
    // 0*t ==> 0, takes 0*t
    virtual Theorem canonMultZero(const Expr& e);
    // 1*t ==> t, takes 1*t
    virtual Theorem canonMultOne(const Expr& e);
    // c1*c2 ==> c', takes constant c1*c2 
    virtual Theorem canonMultConstConst(const Expr& c1, const Expr& c2);
    // c1*(c2*t) ==> c'*t, takes c1 and c2 and t
    virtual Theorem 
      canonMultConstTerm(const Expr& c1, const Expr& c2, const Expr&t);
    // c1*(+ c2 v1 ...) ==> (+ c' c1v1 ...), takes c1 and the sum
    virtual Theorem canonMultConstSum(const Expr& c1, const Expr& sum);
    // c^n = c' (compute the constant power expression)
    virtual Theorem canonPowConst(const Expr& pow);

    // Rules for addition
    // flattens the input. accepts a PLUS expr
    virtual Theorem canonFlattenSum(const Expr& e);
    
    // Rules for addition
    // combine like terms. accepts a flattened PLUS expr
    virtual Theorem canonComboLikeTerms(const Expr& e);
    
    // 0 = (* e1 e2 ...) <=> 0 = e1 OR 0 = e2 OR ...
    virtual Theorem multEqZero(const Expr& expr);

    // 0 = (^ c x) <=> false if c <=0
    //             <=> 0 = x if c > 0
    virtual Theorem powEqZero(const Expr& expr);

    // x^n = y^n <=> x = y (if n is odd)
    // x^n = y^n <=> x = y OR x = -y (if n is even)
    virtual Theorem elimPower(const Expr& expr);

    // x^n = c <=> x = root (if n is odd and root^n = c)
    // x^n = c <=> x = root OR x = -root (if n is even and root^n = c)
    virtual Theorem elimPowerConst(const Expr& expr, const Rational& root);

    // x^n = c <=> false (if n is even and c is negative)
    virtual Theorem evenPowerEqNegConst(const Expr& expr);

    // x^n = c <=> false (if x is an integer and c is not a perfect n power)
    virtual Theorem intEqIrrational(const Expr& expr, const Theorem& isInt);

    // e[0] kind e[1] <==> true when e[0] kind e[1],
    // false when e[0] !kind e[1], for constants only
    virtual Theorem constPredicate(const Expr& e);

    // e[0] kind e[1] <==> 0 kind e[1] - e[0]
    virtual Theorem rightMinusLeft(const Expr& e);

    // e[0] kind e[1] <==> e[0] - e[1] kind 0
    virtual Theorem leftMinusRight(const Expr& e);

    // x kind y <==> x + z kind y + z
    virtual Theorem plusPredicate(const Expr& x, 
				  const Expr& y, 
				  const Expr& z, int kind);

    // x = y <==> x * z = y * z
    virtual Theorem multEqn(const Expr& x, const Expr& y, const Expr& z);

    // x = y <==> z=0 OR x * 1/z = y * 1/z
    virtual Theorem divideEqnNonConst(const Expr& x, const Expr& y, const Expr& z);

    // if z is +ve, return e[0] LT|LE|GT|GE e[1] <==> e[0]*z LT|LE|GT|GE e[1]*z
    // if z is -ve, return e[0] LT|LE|GT|GE e[1] <==> e[1]*z LT|LE|GT|GE e[0]*z
    virtual Theorem multIneqn(const Expr& e, const Expr& z);

    // x = y ==> x <= y and x >= y
    virtual Theorem eqToIneq(const Expr& e);

    // "op1 GE|GT op2" <==> op2 LE|LT op1
    virtual Theorem flipInequality(const Expr& e);
    
    // NOT (op1 LT op2)  <==> (op1 GE op2)
    // NOT (op1 LE op2)  <==> (op1 GT op2)
    // NOT (op1 GT op2)  <==> (op1 LE op2)
    // NOT (op1 GE op2)  <==> (op1 LT op2)
    Theorem negatedInequality(const Expr& e);

    Theorem realShadow(const Theorem& alphaLTt, const Theorem& tLTbeta);
    Theorem realShadowEq(const Theorem& alphaLEt, const Theorem& tLEalpha);
    Theorem finiteInterval(const Theorem& aLEt, const Theorem& tLEac,
			   const Theorem& isInta, const Theorem& isIntt);
    
    Theorem darkGrayShadow2ab(const Theorem& betaLEbx, 
			      const Theorem& axLEalpha,
			      const Theorem& isIntAlpha,
			      const Theorem& isIntBeta,
			      const Theorem& isIntx);
      
    Theorem darkGrayShadow2ba(const Theorem& betaLEbx, 
			      const Theorem& axLEalpha,
			      const Theorem& isIntAlpha,
			      const Theorem& isIntBeta,
			      const Theorem& isIntx);
        
    Theorem expandDarkShadow(const Theorem& darkShadow);
    Theorem expandGrayShadow0(const Theorem& grayShadow);
    Theorem splitGrayShadow(const Theorem& grayShadow);
    Theorem splitGrayShadowSmall(const Theorem& grayShadow);
    Theorem expandGrayShadow(const Theorem& grayShadow);
    Theorem expandGrayShadowConst(const Theorem& grayShadow);
    Theorem grayShadowConst(const Theorem& g);

    //! Implements j(c,b,a)
    /*! accepts 3 integers a,b,c and returns
     *  (b > 0)? (c+b) mod a :  (a - (c+b)) mod a
     */
    Rational constRHSGrayShadow(const Rational& c,
				const Rational& b,
				const Rational& a);

    Theorem lessThanToLE(const Theorem& less, const Theorem& isIntLHS,
			 const Theorem& isIntRHS, bool changeRight);
    
    Theorem lessThanToLERewrite(const Expr& ineq, const Theorem& isIntLHS,
    			 const Theorem& isIntRHS, bool changeRight);
    
    Theorem intVarEqnConst(const Expr& eqn, const Theorem& isIntx);

    Theorem IsIntegerElim(const Theorem& isIntx);
    Theorem eqElimIntRule(const Theorem& eqn, const Theorem& isIntx,
			  const std::vector<Theorem>& isIntVars);

    Theorem isIntConst(const Expr& e);

    Theorem equalLeaves1(const Theorem& e);
    Theorem equalLeaves2(const Theorem& e);
    Theorem equalLeaves3(const Theorem& e);
    Theorem equalLeaves4(const Theorem& e);

    Theorem diseqToIneq(const Theorem& diseq);
    
    Theorem dummyTheorem(const Expr& e);
    
    Theorem oneElimination(const Expr& x);
    
    Theorem clashingBounds(const Theorem& lowerBound, const Theorem& upperBound);
    
    Theorem addInequalities(const Theorem& thm1, const Theorem& thm2);
    Theorem addInequalities(const std::vector<Theorem>& thms);
    
    Theorem implyWeakerInequality(const Expr& expr1, const Expr& expr2);
    
    Theorem implyNegatedInequality(const Expr& expr1, const Expr& expr2);

    Theorem integerSplit(const Expr& intVar, const Rational& intPoint);
    
    Theorem trustedRewrite(const Expr& expr1, const Expr& expr2);
	
    Theorem rafineStrictInteger(const Theorem& isIntConstrThm, const Expr& constr);
    
    Theorem simpleIneqInt(const Expr& ineq, const Theorem& isIntRHS);
    
    Theorem intEqualityRationalConstant(const Theorem& isIntConstrThm, const Expr& constr);
    
    Theorem cycleConflict(const std::vector<Theorem>& inequalitites);
    
    Theorem implyEqualities(const std::vector<Theorem>& inequalities);
    
    Theorem implyWeakerInequalityDiffLogic(const std::vector<Theorem>& antecedentThms, const Expr& implied);
    
    Theorem implyNegatedInequalityDiffLogic(const std::vector<Theorem>& antecedentThms, const Expr& implied);
    
    Theorem expandGrayShadowRewrite(const Expr& theShadow);
    
    Theorem compactNonLinearTerm(const Expr& nonLinear);
    
    Theorem nonLinearIneqSignSplit(const Theorem& ineqThm);
    
    Theorem implyDiffLogicBothBounds(const Expr& x, std::vector<Theorem>& c1_le_x, Rational c1, 
        						     std::vector<Theorem>& x_le_c2, Rational c2);
    
    Theorem powerOfOne(const Expr& e);

  }; // end of class ArithTheoremProducer

} // end of namespace CVC3

#endif
