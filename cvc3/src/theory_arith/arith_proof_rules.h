/*****************************************************************************/
/*!
 * \file arith_proof_rules.h
 * \brief Arithmetic proof rules
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

#ifndef _cvc3__arith_proof_rules_h_
#define _cvc3__arith_proof_rules_h_

#include <vector>

namespace CVC3 {

  class Theorem;
  class Expr;
  class Rational;

  class ArithProofRules {
  public:
    // Destructor
    virtual ~ArithProofRules() { }

    ////////////////////////////////////////////////////////////////////
    // Canonization rules
    ////////////////////////////////////////////////////////////////////

    //! ==> e = 1 * e
    virtual Theorem varToMult(const Expr& e) = 0;

    //! ==> -(e) = (-1) * e
    virtual Theorem uMinusToMult(const Expr& e) = 0;

    //! ==> x - y = x + (-1) * y
    virtual Theorem minusToPlus(const Expr& x, const Expr& y) = 0;

    //! -(e) ==> e / (-1); takes 'e'
    /*! Canon Rule for unary minus: it just converts it to division by
     * -1, the result is not yet canonical:
     */
    virtual Theorem canonUMinusToDivide(const Expr& e) = 0;

    /**
     * Transform e = (SUM r t1 ... tn) @ 0 into (SUM t1 ... tn) @ -r. The first 
     * sum term (r) must be a rational and t1 ... tn terms must be canonised.
     * 
     * @param e the expression to transform
     * @return rewrite theorem representing the transformation  
     */
    virtual Theorem moveSumConstantRight(const Expr& e) = 0;

    //! (c) / d ==> (c/d), takes c and d
    /*! Canon Rules for division by constant 'd' */
    virtual Theorem canonDivideConst(const Expr& c, const Expr& d) = 0;
    //! (c * x) / d ==> (c/d) * x, takes (c*x) and d
    virtual Theorem canonDivideMult(const Expr& cx, const Expr& d) = 0;
    //! (+ c ...)/d ==> push division to all the coefficients.
    /*! The result is not canonical, but canonizing the summands will
     * make it canonical.
     * Takes (+ c ...) and d
     */
    virtual Theorem canonDividePlus(const Expr& e, const Expr& d) = 0;
    //! x / d ==> (1/d) * x, takes x and d
    virtual Theorem canonDivideVar(const Expr& e, const Expr& d) = 0;

    // Canon Rules for multiplication

    // TODO Deepak:
    // e == t1 * t2 where t1 and t2 are canonized expressions, i.e. it can be a
    // 1) Rational constant
    // 2) Arithmetic Leaf (var or term from another theory)
    // 3) (POW rational leaf)
    // 4) (MULT rational mterm'_1 ...) where each mterm' is of type (2) or (3)
    // 5) (PLUS rational sterm_1 sterm_2 ...) where each sterm is of 
    //     type (2) or (3) or (4) 
    virtual Theorem canonMultMtermMterm(const Expr& e) = 0;
    //! Canonize (PLUS t1 ... tn)
    virtual Theorem canonPlus(const Expr & e) = 0;
    //! Canonize (MULT t1 ... tn)
    virtual Theorem canonMult(const Expr & e) = 0;
    //! ==> 1/e = e'  where e' is canonical; takes e.
    virtual Theorem canonInvert(const Expr & e) = 0;
    //! Canonize t1/t2
    virtual Theorem canonDivide(const Expr & e) = 0;

    //! t*c ==> c*t, takes constant c and term t
    virtual Theorem canonMultTermConst(const Expr& c, const Expr& t) = 0;
    //! t1*t2 ==> Error, takes t1 and t2 where both are non-constants
    virtual Theorem canonMultTerm1Term2(const Expr& t1, const Expr& t2) = 0;
    //! 0*t ==> 0, takes 0*t
    virtual Theorem canonMultZero(const Expr& e) = 0;
    //! 1*t ==> t, takes 1*t
    virtual Theorem canonMultOne(const Expr& e) = 0;
    //! c1*c2 ==> c', takes constant c1*c2 
    virtual Theorem canonMultConstConst(const Expr& c1, const Expr& c2) = 0;
    //! c1*(c2*t) ==> c'*t, takes c1 and c2 and t
    virtual Theorem 
      canonMultConstTerm(const Expr& c1, const Expr& c2, const Expr&t) = 0;
    //! c1*(+ c2 v1 ...) ==> (+ c' c1v1 ...), takes c1 and the sum
    virtual Theorem canonMultConstSum(const Expr& c1, const Expr& sum) = 0;
    //! c^n = c' (compute the constant power expression)
    virtual Theorem canonPowConst(const Expr& pow) = 0;

    // Rules for addition
    //! flattens the input. accepts a PLUS expr
    virtual Theorem canonFlattenSum(const Expr& e) = 0;
    
    //! combine like terms. accepts a flattened PLUS expr
    virtual Theorem canonComboLikeTerms(const Expr& e) = 0;
    
    // 0 = (* e1 e2 ...) <=> 0 = e1 OR 0 = e2 OR ...
    virtual Theorem multEqZero(const Expr& expr) = 0;

    // 0 = (^ c x) <=> false if c <=0
    //             <=> 0 = x if c > 0
    virtual Theorem powEqZero(const Expr& expr) = 0;

    // x^n = y^n <=> x = y (if n is odd)
    // x^n = y^n <=> x = y OR x = -y (if n is even)
    virtual Theorem elimPower(const Expr& expr) = 0;

    // x^n = c <=> x = root (if n is odd and root^n = c)
    // x^n = c <=> x = root OR x = -root (if n is even and root^n = c)
    virtual Theorem elimPowerConst(const Expr& expr, const Rational& root) = 0;

    // x^n = c <=> false (if n is even and c is negative)
    virtual Theorem evenPowerEqNegConst(const Expr& expr) = 0;

    // x^n = c <=> false (if x is an integer and c is not a perfect n power)
    virtual Theorem intEqIrrational(const Expr& expr, const Theorem& isInt) = 0;

    //! e0 \@ e1 <==> true | false, where \@ is {=,<,<=,>,>=}
    /*! \param e takes e is (e0\@e1) where e0 and e1 are constants
     */
    virtual Theorem constPredicate(const Expr& e) = 0;

    //! e[0] @ e[1] <==> 0 @ e[1] - e[0], where @ is {=,<,<=,>,>=}
    virtual Theorem rightMinusLeft(const Expr& e) = 0;

    //! e[0] @ e[1] <==> e[0] - e[1] @ 0, where @ is {=,<,<=,>,>=}
    virtual Theorem leftMinusRight(const Expr& e) = 0;

    //! x @ y <==> x + z @ y + z, where @ is {=,<,<=,>,>=} (given as 'kind')
    virtual Theorem plusPredicate(const Expr& x, 
				  const Expr& y, const Expr& z, int kind) = 0;

    //! x = y <==> x * z = y * z, where z is a non-zero constant
    virtual Theorem multEqn(const Expr& x, const Expr& y, const Expr& z) = 0;

    // x = y <==> z=0 OR x * 1/z = y * 1/z
    virtual Theorem divideEqnNonConst(const Expr& x, const Expr& y, const Expr& z) = 0;

    //! Multiplying inequation by a non-zero constant
    /*!
     * z>0 ==> e[0] @ e[1] <==> e[0]*z @ e[1]*z
     *
     * z<0 ==> e[0] @ e[1] <==> e[1]*z @ e[0]*z
     *
     * for @ in {<,<=,>,>=}:
     */
    virtual Theorem multIneqn(const Expr& e, const Expr& z) = 0;

    //! x = y ==> x <= y and x >= y
    virtual Theorem eqToIneq(const Expr& e) = 0;

    //! "op1 GE|GT op2" <==> op2 LE|LT op1
    virtual Theorem flipInequality(const Expr& e) = 0;

    //! Propagating negation over <,<=,>,>=
    /*! NOT (op1 < op2)  <==> (op1 >= op2)
     *
     * NOT (op1 <= op2)  <==> (op1 > op2)
     *
     * NOT (op1 > op2)  <==> (op1 <= op2)
     *
     * NOT (op1 >= op2)  <==> (op1 < op2)
     */
    virtual Theorem negatedInequality(const Expr& e) = 0;
    
    //! Real shadow: a <(=) t, t <(=) b ==> a <(=) b
    virtual Theorem realShadow(const Theorem& alphaLTt, 
			       const Theorem& tLTbeta) = 0;

    //! Projecting a tight inequality: alpha <= t <= alpha ==> t = alpha
    virtual Theorem realShadowEq(const Theorem& alphaLEt, 
				 const Theorem& tLEalpha) = 0;

    //! Finite interval for integers: a <= t <= a + c ==> G(t, a, 0, c)
    virtual Theorem finiteInterval(const Theorem& aLEt,
				   const Theorem& tLEac,
				   const Theorem& isInta,
				   const Theorem& isIntt) = 0;
    
    //! Dark & Gray shadows when a <= b
    /*! takes two integer ineqs (i.e. all vars are ints) 
     * "|- beta <= b.x" and "|- a.x <= alpha" and checks if "1 <= a <= b"
     * and returns (D or G) and (!D or !G), where
     * D = Dark_Shadow(ab-1, b.alpha - a.beta),
     * G = Gray_Shadow(a.x, alpha, -(a-1), 0).
     */
    virtual Theorem darkGrayShadow2ab(const Theorem& betaLEbx, 
				      const Theorem& axLEalpha,
				      const Theorem& isIntAlpha,
				      const Theorem& isIntBeta,
				      const Theorem& isIntx)=0;
      
    //! Dark & Gray shadows when b <= a
    /*! takes two integer ineqs (i.e. all vars are ints) 
     * "|- beta <= b.x" and "|- a.x <= alpha" and checks if "1 <= b < a"
     * and returns (D or G) and (!D or !G), where
     * D = Dark_Shadow(ab-1, b.alpha - a.beta),
     * G = Gray_Shadow(b.x, beta, 0, b-1).
     */
    virtual Theorem darkGrayShadow2ba(const Theorem& betaLEbx, 
				      const Theorem& axLEalpha,
				      const Theorem& isIntAlpha,
				      const Theorem& isIntBeta,
				      const Theorem& isIntx)=0;
        
    //! DARK_SHADOW(t1, t2) ==> t1 <= t2
    virtual Theorem expandDarkShadow(const Theorem& darkShadow)=0;
    
    //! GRAY_SHADOW(v, e, c, c) ==> v=e+c.
    virtual Theorem expandGrayShadow0(const Theorem& g)=0;

    // [used to be] GRAY_SHADOW(t1, t2, i) ==> t1 = t2+i OR
    // GRAY_SHADOW(t1, t2, i+/-1)

    //! G(x, e, c1, c2) ==> (G1 or G2) and (!G1 or !G2)
    /*! Here G1 = G(x,e,c1,c),
     *       G2 = G(x,e,c+1,c2),
     *   and  c = floor((c1+c2)/2).
     */
    virtual Theorem splitGrayShadow(const Theorem& g)=0;
    
    
    virtual Theorem splitGrayShadowSmall(const Theorem& g)=0;
        
    //! G(x, e, c1, c2) ==> e+c1 <= x AND x <= e+c2
    virtual Theorem expandGrayShadow(const Theorem& g)=0;

    //! Optimized rules: GRAY_SHADOW(a*x, c, c1, c2) ==> [expansion]
    /*! Implements three versions of the rule:
     *
     * \f[\frac{\mathrm{GRAY\_SHADOW}(ax,c,c1,c2)}
     *         {ax = c + i - \mathrm{sign}(i)\cdot j(c,i,a)
     *          \lor GRAY\_SHADOW(ax, c, i-\mathrm{sign}(i)\cdot (a+j(c,i,a)))}\f]
     *
     * where the conclusion may become FALSE or without the
     * GRAY_SHADOW part, depending on the values of a, c and i.
     */
    virtual Theorem expandGrayShadowConst(const Theorem& g)=0;
    //! |- G(ax, c, c1, c2) ==> |- G(x, 0, ceil((c1+c)/a), floor((c2+c)/a))
    /*! In the case the new c1 > c2, return |- FALSE */
    virtual Theorem grayShadowConst(const Theorem& g)=0;

    //! a,b: INT; a < b ==> a <= b-1 [or a+1 <= b]
    /*! Takes a Theorem(\\alpha < \\beta) and returns 
     *  Theorem(\\alpha < \\beta <==> \\alpha <= \\beta -1)
     * or Theorem(\\alpha < \\beta <==> \\alpha + 1 <= \\beta),
     * depending on which side must be changed (changeRight flag)
     */
    virtual Theorem lessThanToLE(const Theorem& less, 
				 const Theorem& isIntLHS,
				 const Theorem& isIntRHS,
				 bool changeRight)=0;

    virtual Theorem lessThanToLERewrite(const Expr& ineq, const Theorem& isIntLHS,
    			 const Theorem& isIntRHS, bool changeRight) = 0;

    
    /*! \param eqn is an equation 0 = a.x or 0 = c + a.x, where x is integer
     * \param isIntx is a proof of IS_INTEGER(x)
     *
     * \return the theorem 0 = c + a.x <==> x=-c/a if -c/a is int else
     *  return the theorem 0 = c + a.x <==> false.
     *
     * It also handles the special case of 0 = a.x <==> x = 0
     */
    virtual Theorem intVarEqnConst(const Expr& eqn,
				   const Theorem& isIntx) = 0;
    /*! IS_INTEGER(x) <=> EXISTS (y : INT) y = x
     * where x is not already known to be an integer.
     */
    virtual Theorem IsIntegerElim(const Theorem& isIntx) = 0;

    /*! @brief Equality elimination rule for integers:
     * \f[\frac{\mathsf{int}(a\cdot x)\quad
     *          \mathsf{int}(C+\sum_{i=1}^{n}a_{i}\cdot x_{i})}
     *     {a\cdot x=C+\sum_{i=1}^{n}a_{i}\cdot x_{i}
     *       \quad\equiv\quad x=t_{2}\wedge 0=t_{3}}
     * \f]
     * See the detailed description for explanations.
     * 
     * This rule implements a step in the iterative algorithm for
     * eliminating integer equality.  The terms in the rule are
     * defined as follows:
     *
     * \f[\begin{array}{rcl}
     *       t_{2} & = & 
     *          -(C\ \mathbf{mod}\  m+\sum_{i=1}^{n}(a_{i}\ \mathbf{mod}\  m)
     *             \cdot x_{i}-m\cdot\sigma(t))\\ & & \\
     *       t_{3} & = & 
     *         \mathbf{f}(C,m)+\sum_{i=1}^{n}\mathbf{f}(a_{i},m)\cdot x_{i}
     *           -a\cdot\sigma(t)\\ & & \\
     *       t & = &
     *          (C\ \mathbf{mod}\  m+\sum_{i=1}^{n}(a_{i}\ \mathbf{mod}\  m)
     *             \cdot x_{i}+x)/m\\ & & \\
     *       m & = & a+1\\ & & \\
     *       \mathbf{f}(i,m) & = & \left\lfloor \frac{i}{m}
     *       +\frac{1}{2}\right\rfloor +i\ \mathbf{mod}\  m\\ & & \\
     *       i\ \mathbf{mod}\  m & = & i-m\left\lfloor\frac{i}{m}
     *          +\frac{1}{2}\right\rfloor
     *    \end{array}
     * \f]
     *
     * All the variables and coefficients are integer, and a >= 2.
     *
     * \param eqn is the equation
     *   \f[a\cdot x = C + \sum_{i=1}^n a_i\cdot x_i.\f]
     * 
     */

    /*
    virtual Theorem eqElimIntRule(const Expr& eqn,
				  const Theorem& isIntLHS,
				  const Theorem& isIntRHS) = 0;
    //! a <=> b  ==>  c AND a <=> c AND b.  Takes "a <=> b" and "c".
    virtual Theorem cANDaIffcANDb(const Theorem& thm, 
				  const Expr& solvedEq) = 0;
    virtual Theorem substSolvedFormRule(const Expr& e1,
					ExprMap<Expr>& eMap) = 0;					
    virtual Theorem aANDcIffbANDc(const Theorem& thm, const Expr& newEq) = 0;
    */

    ///////////////////////////////////////////////////////////////////////
    // Alternative implementation of integer equality elimination
    ///////////////////////////////////////////////////////////////////////

    /*! @brief
     * \f[\frac{\Gamma\models ax=t\quad
     *          \Gamma'\models\mathsf{int}(x)\quad
     *          \{\Gamma_i\models\mathsf{int}(x_i) | x_i\mbox{ is var in }t\}}
     *      {\Gamma,\Gamma',\bigcup_i\Gamma_i\models
     *         \exists (y:\mathrm{int}).\ x=t_2(y)\wedge 0=t_3(y)}
     * \f]
     * See detailed docs for more information.
     *
     * This rule implements a step in the iterative algorithm for
     * eliminating integer equality.  The terms in the rule are
     * defined as follows:
     *
     * \f[\begin{array}{rcl}
     *       t & = & C+\sum_{i=1}^na_{i}\cdot x_{i}\\
     *       t_{2}(y) & = & 
     *          -(C\ \mathbf{mod}\  m+\sum_{i=1}^{n}(a_{i}\ \mathbf{mod}\  m)
     *             \cdot x_{i}-m\cdot y)\\ & & \\
     *       t_{3}(y) & = & 
     *         \mathbf{f}(C,m)+\sum_{i=1}^{n}\mathbf{f}(a_{i},m)\cdot x_{i}
     *           -a\cdot y\\ & & \\
     *       m & = & a+1\\ & & \\
     *       \mathbf{f}(i,m) & = & \left\lfloor \frac{i}{m}
     *       +\frac{1}{2}\right\rfloor +i\ \mathbf{mod}\  m\\ & & \\
     *       i\ \mathbf{mod}\  m & = & i-m\left\lfloor\frac{i}{m}
     *          +\frac{1}{2}\right\rfloor
     *    \end{array}
     * \f]
     *
     * All the variables and coefficients are integer, and a >= 2.
     *
     * \param eqn is the equation ax=t:
     *   \f[a\cdot x = C + \sum_{i=1}^n a_i\cdot x_i.\f]
     *
     * \param isIntx is a Theorem deriving the integrality of the
     * LHS variable: IS_INTEGER(x)
     *
     * \param isIntVars is a vector of Theorems deriving the
     * integrality of all variables on the RHS
     */
    virtual Theorem eqElimIntRule(const Theorem& eqn,
				  const Theorem& isIntx,
				  const std::vector<Theorem>& isIntVars) = 0;

    /*!
     * @brief return e <=> TRUE/FALSE for e == IS_INTEGER(c), where c
     * is a constant
     *
     * \param e is a predicate IS_INTEGER(c) where c is a rational constant
     */
    virtual Theorem isIntConst(const Expr& e) = 0;

    virtual Theorem equalLeaves1(const Theorem& thm) = 0;
    virtual Theorem equalLeaves2(const Theorem& thm) = 0;
    virtual Theorem equalLeaves3(const Theorem& thm) = 0;
    virtual Theorem equalLeaves4(const Theorem& thm) = 0;

    //! x /= y  ==>  (x < y) OR (x > y)
    /*! Used in concrete model generation */
    virtual Theorem diseqToIneq(const Theorem& diseq) = 0;

    virtual Theorem dummyTheorem(const Expr& e) = 0;
      
    virtual Theorem oneElimination(const Expr& x) = 0;
    
    virtual Theorem clashingBounds(const Theorem& lowerBound, const Theorem& upperBound) = 0;
    
    virtual Theorem addInequalities(const Theorem& thm1, const Theorem& thm2) = 0;
    virtual Theorem addInequalities(const std::vector<Theorem>& thms) = 0;
    
    virtual Theorem implyWeakerInequality(const Expr& expr1, const Expr& expr2) = 0;
    
    virtual Theorem implyNegatedInequality(const Expr& expr1, const Expr& expr2) = 0;

    virtual Theorem integerSplit(const Expr& intVar, const Rational& intPoint) = 0;
    
    virtual Theorem trustedRewrite(const Expr& expr1, const Expr& expr2) = 0;
    
    virtual Theorem rafineStrictInteger(const Theorem& isIntConstrThm, const Expr& constr) = 0;

    virtual Theorem simpleIneqInt(const Expr& ineq, const Theorem& isIntRHS) = 0;
    
    virtual Theorem intEqualityRationalConstant(const Theorem& isIntConstrThm, const Expr& constr) = 0;
    
    virtual Theorem cycleConflict(const std::vector<Theorem>& inequalitites) = 0;

    virtual Theorem implyEqualities(const std::vector<Theorem>& inequalities) = 0;
    
    virtual Theorem implyWeakerInequalityDiffLogic(const std::vector<Theorem>& antecedentThms, const Expr& implied) = 0;
    
    virtual Theorem implyNegatedInequalityDiffLogic(const std::vector<Theorem>& antecedentThms, const Expr& implied) = 0;
            
    virtual Theorem expandGrayShadowRewrite(const Expr& theShadow) = 0;
    
    virtual Theorem compactNonLinearTerm(const Expr& nonLinear) = 0;
    
    virtual Theorem nonLinearIneqSignSplit(const Theorem& ineqThm) = 0;
    
    virtual Theorem implyDiffLogicBothBounds(const Expr& x, std::vector<Theorem>& c1_le_x, Rational c1, 
    										 std::vector<Theorem>& x_le_c2, Rational c2) = 0;
    
    virtual Theorem powerOfOne(const Expr& e) = 0;
    
    virtual Theorem rewriteLeavesConst(const Expr& e);

  }; // end of class ArithProofRules
} // end of namespace CVC3

#endif
