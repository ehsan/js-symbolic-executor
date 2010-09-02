/*****************************************************************************/
/*!
 * \file theory_arith_new.cpp
 * 
 * Author: Dejan Jovanovic
 * 
 * Created: Thu Jun 14 13:42:00 2007
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


#include "theory_arith_new.h" 
#include "arith_proof_rules.h"
//#include "arith_expr.h"
#include "arith_exception.h"
#include "typecheck_exception.h"
#include "eval_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
#include "theory_core.h"
#include "command_line_flags.h"


using namespace std;
using namespace CVC3;


///////////////////////////////////////////////////////////////////////////////
// TheoryArithNew::FreeConst Methods                                            //
///////////////////////////////////////////////////////////////////////////////

namespace CVC3 {

ostream& operator<<(ostream& os, const TheoryArithNew::FreeConst& fc) {
  os << "FreeConst(r=" << fc.getConst() << ", " 
     << (fc.strict()? "strict" : "non-strict") << ")";
  return os;
}

///////////////////////////////////////////////////////////////////////////////
// TheoryArithNew::Ineq Methods                                                 //
///////////////////////////////////////////////////////////////////////////////

ostream& operator<<(ostream& os, const TheoryArithNew::Ineq& ineq) {
  os << "Ineq(" << ineq.ineq().getExpr() << ", isolated on "
     << (ineq.varOnRHS()? "RHS" : "LHS") << ", const = "
     << ineq.getConst() << ")";
  return os;
}
} // End of namespace CVC3


///////////////////////////////////////////////////////////////////////////////
// TheoryArithNew Private Methods                                               //
///////////////////////////////////////////////////////////////////////////////


Theorem TheoryArithNew::isIntegerThm(const Expr& e) {
  // Quick check
  if(isReal(e.getType())) return Theorem();
  // Try harder
  return isIntegerDerive(Expr(IS_INTEGER, e), typePred(e));
}


Theorem TheoryArithNew::isIntegerDerive(const Expr& isIntE, const Theorem& thm) {
  const Expr& e = thm.getExpr();
  // We found it!
  if(e == isIntE) return thm;

  Theorem res;
  // If the theorem is an AND, look inside each child
  if(e.isAnd()) {
    int i, iend=e.arity();
    for(i=0; i<iend; ++i) {
      res = isIntegerDerive(isIntE, getCommonRules()->andElim(thm, i));
      if(!res.isNull()) return res;
    }
  }
  return res;
}


bool TheoryArithNew::kidsCanonical(const Expr& e) {
  if(isLeaf(e)) return true;
  bool res(true);
  for(int i=0; res && i<e.arity(); ++i) {
    Expr simp(canon(e[i]).getRHS());
    res = (e[i] == simp);
    IF_DEBUG(if(!res) debugger.getOS() << "\ne[" << i << "] = " << e[i]
	     << "\nsimplified = " << simp << endl;)
  }
  return res;
}




/**
 * Compute a canonical form for expression e and return a theorem that e is equal to its canonical form.
 * Note that canonical form for arith expressions is of the following form:
 * 
 * b + a_1 x_1 + a_2 x_2 + ... + a_n x_n (ONE SUM EXPRESION)
 * 
 * or just a rational b (RATIONAL EXPRESSION)
 * 
 * where a_i and b are rationals and x_i are arithmetical leaves (i.e. variables or non arithmetic terms)
 * 
 * @author Clark Barrett
 * @author Vijay Ganesh
 * @since Sat Feb  8 14:46:32 2003
 */  
Theorem TheoryArithNew::canon(const Expr& e)
{
 	// Trace the arith canon of the expression in the debug version
 	TRACE("arith", "canon(", e , ") {");
 	
 	// The invariant is that the kids of the expression should already be canonised	
 	//DebugAssert(kidsCanonical(e), "TheoryArithNew::canon("+e.toString()+")");
 	
 	// The resulting theorem object 
  	Theorem result;
  	
  	switch (e.getKind()) {
  		
  		// -E
  		case UMINUS: {
  			
  			// Convert the unary minus to multiplication with -1
  			result = d_rules->uMinusToMult(e[0]);
  			
  			// Get the resulting epression
      		Expr e2 = result.getRHS();
      		
      		// Canonise the resulting expression and combine the theorems
      		result = transitivityRule(result, canon(e2));
    	
    		// UMINUS case break
    		break;
  		}
      
      	// e[0] + e[1]
    	case PLUS: 
    		
    		// Call the canonPlus procedure to canonise +
    		result = d_rules->canonPlus(e);
      		
      		// PLUS case break
      		break;
    	
    	// e[0] - e[1]
    	case MINUS: {
      		
      		// Arity of the minus should be exactly 2 (TODO: looks useless, maybe remove)
      		DebugAssert(e.arity() == 2," ");
      
      		// This produces e[0] + (-1)*e[1], we have to canonize it in 2 steps 
      		Theorem minus_eq_sum = d_rules->minusToPlus(e[0], e[1]);
      
      		// The resulting sum expression
      		Expr sum(minus_eq_sum.getRHS());
      		
      		// Canonise the sum[1]
      		Theorem thm(canon(sum[1]));
      		
      		// If the sum[1] sayed the same, canonise the sum expression
      		if(thm.getLHS() == thm.getRHS()) 
        		result = canonThm(minus_eq_sum);
      		// The sum changed; do the work
      		else {
      			
        		// Substitute and try to canonise again
        		Theorem sum_eq_canon = canonThm(substitutivityRule(sum, 1, thm));
        		
        		// Combine the results, and thats it
        		result = transitivityRule(minus_eq_sum, sum_eq_canon);
      		}
      		
      		// MINUS case break 
      		break;
    	
    	}
  
  		// e[0] * e[1]
    	case MULT:
    
    		// Canonise using the canonMult() proof rule
      		result = d_rules->canonMult(e);
    
      		// MULT case break
      		break;
  
  		// e[0] DIV e[1]
    	case DIVIDE: {
  
      		// Division by 0 is OK (total extension, protected by TCCs)
	  		// if (e[1].isRational() && e[1].getRational() == 0)
			// throw ArithException("Divide by 0 error in "+e.toString());
      		if (e[1].getKind() == PLUS)
        		throw ArithException("Divide by a PLUS expression not handled in" + e.toString());
      		
      		// Canonise the divite using canonDivide() method 
      		result = d_rules->canonDivide(e);
      		
      		// DIVIDE case break
      		break;	
    	}
  	
  		// e[0]^e[1]
  	 	case POW :
  	
  			// If we are raising to a constant rational call canonPowConst() proof rule
    		if(e[1].isRational()) result = d_rules->canonPowConst(e);
    		// Othervise just return the same expression
    		else result = reflexivityRule(e);
    
   	 		// POW case break
   	 		break;
  	
  		default:
      	
      		// How did we get here (TODO: check if need to throw and exception), anyhow, just return the reflexivity rule
      		result = reflexivityRule(e);
     
	     	// Default break 
    	  	break;
    }
  
  // Finished with the canonisation, trace the result in the debug version
  TRACE("arith","canon => ",result," }");
  
  // Return the resulting theorem 
  return result;
}

Theorem TheoryArithNew::canonSimplify(const Expr& e) {
    // Trace the function on the arith trace flag
  	TRACE("arith", "canonSimplify(", e, ") {");
  
  	// Assert that all the kids must be already canonical
  	//DebugAssert(kidsCanonical(e), "TheoryArithNew::canonSimplify("+e.toString()+")");
  	// Assert that all the leaves must be simplified
  	//DebugAssert(leavesAreSimp(e), "Expected leaves to be simplified");
  
  	// Make a copy of the expression
  	Expr tmp(e);
  
  	// Canonise the expresion
  	Theorem thm = canon(e);
  	
  	// If the new simplified expression has a find, use it (TODO: Check whats going on here)
  	if(thm.getRHS().hasFind())
    	thm = transitivityRule(thm, find(thm.getRHS()));
  
  	// We shouldn't rely on simplification in this function anymore
  	DebugAssert(thm.getRHS() == simplifyExpr(thm.getRHS()), "canonSimplify("+e.toString()+")\n"+"canon(e) = "+thm.getRHS().toString()+"\nsimplify(canon(e)) = "+simplifyExpr(thm.getRHS()).toString());

	// Trace the resulting theorem
	TRACE("arith", "canonSimplify =>", thm, " }");
	
	// Return the theorem
	return thm;
}

/*! accepts a theorem, canonizes it, applies iffMP and substituvity to
 *  derive the canonized thm
 */
Theorem 
TheoryArithNew::canonPred(const Theorem& thm) {
  vector<Theorem> thms;
  DebugAssert(thm.getExpr().arity() == 2,
              "TheoryArithNew::canonPred: bad theorem: "+thm.toString());
  Expr e(thm.getExpr());
  thms.push_back(canonSimplify(e[0]));
  thms.push_back(canonSimplify(e[1]));
  return iffMP(thm, substitutivityRule(e.getOp(), thms));
}

/** 
 * Accepts an equivalence theorem, canonizes the subexpressions, applies transitivity and substituvity to derive the canonized theorem.
 * 
 * @param thm equivalence theorem
 * @return the canonised expression theorem
 */
Theorem TheoryArithNew::canonPredEquiv(const Theorem& thm) {
  
  vector<Theorem> thms; // Vector to hold the simplified versions of e[0] and e[1]
  
  // Arity of the expression should be 2
  DebugAssert(thm.getRHS().arity() == 2, "TheoryArithNew::canonPredEquiv: bad theorem: " + thm.toString());
  
  // Get the expression of the theorem
  Expr e(thm.getRHS());
  
  // Simplify both sides of the equivalence
  thms.push_back(canonSimplify(e[0]));
  thms.push_back(canonSimplify(e[1]));
  
  // Return the theorem substituting e[0] and e[1] with their simplified versions
  return transitivityRule(thm, substitutivityRule(e.getOp(), thms));
}

/*! accepts an equivalence theorem whose RHS is a conjunction,
 *  canonizes it, applies iffMP and substituvity to derive the
 *  canonized thm
 */
Theorem
TheoryArithNew::canonConjunctionEquiv(const Theorem& thm) {
  vector<Theorem> thms;
  return thm;
}

/*! Pseudo-code for doSolve. (Input is an equation) (output is a Theorem)
 *  -# translate e to the form e' = 0
 *  -# if (e'.isRational()) then {if e' != 0 return false else true}
 *  -# a for loop checks if all the variables are integers. 
 *      - if not isolate a suitable real variable and call processRealEq().
 *      - if all variables are integers then isolate suitable variable 
 *         and call processIntEq(). 
 */
Theorem TheoryArithNew::doSolve(const Theorem& thm)
{ 
  const Expr& e = thm.getExpr();
  TRACE("arith eq","doSolve(",e,") {");
  DebugAssert(thm.isRewrite(), "thm = "+thm.toString());
  Theorem eqnThm;
  vector<Theorem> thms;  
  // Move LHS to the RHS, if necessary
  if(e[0].isRational() && e[0].getRational() == 0)
    eqnThm = thm;
  else {
    eqnThm = iffMP(thm, d_rules->rightMinusLeft(e));
    eqnThm = canonPred(eqnThm);
  }
  // eqnThm is of the form 0 = e'
  // 'right' is of the form e'
  Expr right = eqnThm.getRHS();
  // Check for trivial equation
  if (right.isRational()) {
    Theorem result = iffMP(eqnThm, d_rules->constPredicate(eqnThm.getExpr()));
    TRACE("arith eq","doSolve => ",result," }");
    return result;
  }

  //normalize
  eqnThm = iffMP(eqnThm, normalize(eqnThm.getExpr()));
  right = eqnThm.getRHS();
  
  //eqn is of the form 0 = e' and is normalized where 'right' denotes e'
  //FIXME: change processRealEq to accept equations as well instead of theorems
  if(!isInteger(right)) {
    Theorem res;
    try {
      res = processRealEq(eqnThm);
    } catch(ArithException& e) {
      res = symmetryRule(eqnThm); // Flip to e' = 0
      TRACE("arith eq", "doSolve: failed to solve an equation: ", e, "");
      IF_DEBUG(debugger.counter("FAILED to solve real equalities")++;)
      setIncomplete("Non-linear arithmetic inequalities");
    }
    IF_DEBUG(debugger.counter("solved real equalities")++;)
    TRACE("arith eq", "doSolve [real] => ", res, " }");
    return res;
  }
  else {
    Theorem res = processIntEq(eqnThm);
    IF_DEBUG(debugger.counter("solved int equalities")++;)
    TRACE("arith eq", "doSolve [int] => ", res, " }");
    return res;
  }
}

/*! pick a monomial for the input equation. This function is used only
 *  if the equation is an integer equation. Choose the monomial with
 *  the smallest absolute value of coefficient.
 */
Expr
TheoryArithNew::pickIntEqMonomial(const Expr& right)
{
  DebugAssert(isPlus(right) && right.arity() > 2,
              "TheoryArithNew::pickIntEqMonomial right is wrong :-): " +
              right.toString());
  DebugAssert(right[0].isRational(),
              "TheoryArithNew::pickIntEqMonomial. right[0] must be const" +
              right.toString());
  DebugAssert(isInteger(right),
              "TheoryArithNew::pickIntEqMonomial: right is of type int: " +
              right.toString());
  //right is of the form "C + a1x1 + ... + anxn". min is initialized
  //to a1
  Expr::iterator i = right.begin();
  i++; //skip 'C'
  Rational min = isMult(*i) ? abs((*i)[0].getRational()) : 1;
  Expr pickedMon = *i;
  for(Expr::iterator iend = right.end(); i != iend; ++i) {
    Rational coeff = isMult(*i) ? abs((*i)[0].getRational()) : 1;
    if(min > coeff) {
      min = coeff;
      pickedMon = *i;
    }
  }
  return pickedMon;
}

/*! input is e1=e2<==>0=e' Theorem and some of the vars in e' are of
 * type REAL. isolate one of them and send back to framework. output
 * is "e1=e2 <==> var = e''" Theorem.
 */
Theorem 
TheoryArithNew::processRealEq(const Theorem& eqn)
{
  Expr right = eqn.getRHS();
  // Find variable to isolate and store it in left.  Pick the largest
  // (according to the total ordering) variable.  FIXME: change from
  // total ordering to the ordering we devised for inequalities.

  // TODO: I have to pick a variable that appears as a variable in the
  // term but does not appear as a variable anywhere else.  The variable
  // must appear as a single leaf and not in a MULT expression with some
  // other variables and nor in a POW expression.

  bool found = false;
  
  Expr left;
  
  if (isPlus(right))  {
    for(int i = right.arity()-1; i>=0; --i) {
      Expr c = right[i];
      if(isRational(c))
        continue;
      if(!isInteger(c))  {
        if (isLeaf(c) || 
            ((isMult(c) && c.arity() == 2 && isLeaf(c[1])))) {
          int numoccurs = 0;
          Expr leaf = isLeaf(c) ? c : c[1];
          for (int j = 0; j < right.arity(); ++j) {
            if (j!= i
		&& isLeafIn(leaf, right[j])
		// && leaf.subExprOf(right[j])
		) {
              numoccurs++;
              break;
            }
          }
          if (!numoccurs) {
            left = c;
            found = true;
            break;
          }
        }
      }
    }
  }
  else if ((isMult(right) && right.arity() == 2 && isLeaf(right[1])) ||
           isLeaf(right)) {
    left = right;
    found = true;
  }
  
  if (!found) {
    // TODO:
    // throw an arithmetic exception that this cannot be done.
    throw 
      ArithException("Can't find a leaf for solve in "+eqn.toString());
  }

  Rational r = -1;
  if (isMult(left))  {
    DebugAssert(left.arity() == 2, "only leaf should be chosen as lhs");
    DebugAssert(left[0].getRational() != 0, "left = "+left.toString());
    r = -1/left[0].getRational();
    left = left[1];
  }

  DebugAssert(isReal(getBaseType(left)) && !isInteger(left),
              "TheoryArithNew::ProcessRealEq: left is integer:\n left = "
	      +left.toString());
  // Normalize equation so that coefficient of the monomial
  // corresponding to "left" in eqn[1] is -1
  Theorem result(iffMP(eqn,
		       d_rules->multEqn(eqn.getLHS(), eqn.getRHS(), rat(r))));
  result = canonPred(result);

  // Isolate left
  result = iffMP(result, d_rules->plusPredicate(result.getLHS(),
						result.getRHS(), left, EQ));
  result = canonPred(result);
  TRACE("arith","processRealEq => ",result," }");
  return result;
}

/*!
 * \param eqn is a single equation 0 = e
 * \return an equivalent Theorem (x = t AND 0 = e'), or just x = t
 */
Theorem
TheoryArithNew::processSimpleIntEq(const Theorem& eqn)
{
  TRACE("arith eq", "processSimpleIntEq(", eqn.getExpr(), ") {");
  DebugAssert(eqn.isRewrite(),
              "TheoryArithNew::processSimpleIntEq: eqn must be equality" +
              eqn.getExpr().toString());

  Expr right = eqn.getRHS();

  DebugAssert(eqn.getLHS().isRational() && 0 == eqn.getLHS().getRational(),
              "TheoryArithNew::processSimpleIntEq: LHS must be 0:\n" +
              eqn.getExpr().toString());

  //recall that 0 = c case is already handled in doSolve() function.
  if(isMult(right)) {
    //here we take care of special case 0=c.x
    Expr c,x;
    separateMonomial(right, c, x);
    Theorem isIntx(isIntegerThm(x));
    DebugAssert(!isIntx.isNull(), "right = "+right.toString());
    Theorem res(iffMP(eqn, d_rules->intVarEqnConst(eqn.getExpr(), isIntx)));
    TRACE("arith eq", "processSimpleIntEq[0 = a*x] => ", res, " }");
    return res;
  } else if(isPlus(right)) {
    if(2 == right.arity()) {
      //we take care of special cases like 0 = c + a.x, 0 = c + x,
      Expr c,x;
      separateMonomial(right[1], c, x);
      Theorem isIntx(isIntegerThm(x));
      DebugAssert(!isIntx.isNull(), "right = "+right.toString()
		  +"\n x = "+x.toString());
      Theorem res(iffMP(eqn, d_rules->intVarEqnConst(eqn.getExpr(), isIntx)));
      TRACE("arith eq", "processSimpleIntEq[0 = c + a*x] => ", res, " }");
      return res;
    }
    DebugAssert(right.arity() > 2,
                "TheoryArithNew::processSimpleIntEq: RHS is not in correct form:"
                +eqn.getExpr().toString());
    // Pick a suitable monomial. isolated can be of the form x, a.x, -a.x
    Expr isolated = pickIntEqMonomial(right);
    TRACE("arith eq", "processSimpleIntEq: isolated = ", isolated, "");

    // First, we compute the 'sign factor' with which to multiply the
    // eqn.  if the coeff of isolated is positive (i.e. 'isolated' is
    // of the form x or a.x where a>0 ) then r must be -1 and if coeff
    // of 'isolated' is negative, r=1.
    Rational r = isMult(isolated) ?
      ((isolated[0].getRational() > 0) ? -1 : 1) : -1;
    Theorem result;
    if (-1 == r) {
      // r=-1 and hence 'isolated' is 'x' or 'a.x' where a is
      // positive.  modify eqn (0=e') to the equation (0=canon(-1*e'))
      result = iffMP(eqn, d_rules->multEqn(eqn.getLHS(), right, rat(r)));
      result = canonPred(result);
      Expr e = result.getRHS();

      // Isolate the 'isolated'
      result = iffMP(result,
		     d_rules->plusPredicate(result.getLHS(),result.getRHS(),
					    isolated, EQ));
    } else {
      //r is 1 and hence isolated is -a.x. Make 'isolated' positive.
      const Rational& minusa = isolated[0].getRational();
      Rational a = -1*minusa;
      isolated = (a == 1)? isolated[1] : rat(a) * isolated[1];
      
      // Isolate the 'isolated'
      result = iffMP(eqn, d_rules->plusPredicate(eqn.getLHS(), 
						 right,isolated,EQ));
    }
    // Canonize the result
    result = canonPred(result);
        
    //if isolated is 'x' or 1*x, then return result else continue processing.
    if(!isMult(isolated) || isolated[0].getRational() == 1) {   
      TRACE("arith eq", "processSimpleIntEq[x = rhs] => ", result, " }");
      return result;
    } else {
      DebugAssert(isMult(isolated) && isolated[0].getRational() >= 2,
                  "TheoryArithNew::processSimpleIntEq: isolated must be mult "
		  "with coeff >= 2.\n isolated = " + isolated.toString());

      // Compute IS_INTEGER() for lhs and rhs
      Expr lhs = result.getLHS();
      Expr rhs = result.getRHS();
      Expr a, x;
      separateMonomial(lhs, a, x);
      Theorem isIntLHS = isIntegerThm(x);
      vector<Theorem> isIntRHS;
      if(!isPlus(rhs)) { // rhs is a MULT
	Expr c, v;
	separateMonomial(rhs, c, v);
	isIntRHS.push_back(isIntegerThm(v));
	DebugAssert(!isIntRHS.back().isNull(), "");
      } else { // rhs is a PLUS
	DebugAssert(isPlus(rhs), "rhs = "+rhs.toString());
	DebugAssert(rhs.arity() >= 2, "rhs = "+rhs.toString());
	Expr::iterator i=rhs.begin(), iend=rhs.end();
	++i; // Skip the free constant
	for(; i!=iend; ++i) {
	  Expr c, v;
	  separateMonomial(*i, c, v);
	  isIntRHS.push_back(isIntegerThm(v));
	  DebugAssert(!isIntRHS.back().isNull(), "");
	}
      }
      // Derive (EXISTS (x:INT): x = t2 AND 0 = t3)
      result = d_rules->eqElimIntRule(result, isIntLHS, isIntRHS);
      // Skolemize the quantifier
      result = getCommonRules()->skolemize(result);
      // Canonize t2 and t3 generated by this rule
      DebugAssert(result.getExpr().isAnd() && result.getExpr().arity() == 2,
		  "processSimpleIntEq: result = "+result.getExpr().toString());
      Theorem thm1 = canonPred(getCommonRules()->andElim(result, 0));
      Theorem thm2 = canonPred(getCommonRules()->andElim(result, 1));
      Theorem newRes = getCommonRules()->andIntro(thm1, thm2);
      if(newRes.getExpr() != result.getExpr()) result = newRes;
      
      TRACE("arith eq", "processSimpleIntEq => ", result, " }");
      return result;
    }
  } else {
    // eqn is 0 = x.  Flip it and return
    Theorem result = symmetryRule(eqn);
    TRACE("arith eq", "processSimpleIntEq[x = 0] => ", result, " }");
    return result;
  }
}

/*! input is e1=e2<==>0=e' Theorem and all of the vars in e' are of
 * type INT. isolate one of them and send back to framework. output
 * is "e1=e2 <==> var = e''" Theorem and some associated equations in
 * solved form.
 */
Theorem 
TheoryArithNew::processIntEq(const Theorem& eqn)
{
  TRACE("arith eq", "processIntEq(", eqn.getExpr(), ") {");
  // Equations in the solved form.  
  std::vector<Theorem> solvedAndNewEqs;
  Theorem newEq(eqn), result;
  bool done(false);
  do {
    result = processSimpleIntEq(newEq);
    // 'result' is of the from (x1=t1)  AND 0=t'
    if(result.isRewrite()) {
      solvedAndNewEqs.push_back(result);
      done = true;
    }
    else if(!result.getExpr().isFalse()) {
      DebugAssert(result.getExpr().isAnd() && result.getExpr().arity() == 2,
		  "TheoryArithNew::processIntEq("+eqn.getExpr().toString()
		  +")\n result = "+result.getExpr().toString());
      solvedAndNewEqs.push_back(getCommonRules()->andElim(result, 0));
      newEq = getCommonRules()->andElim(result, 1);
    } else
      done = true;
  } while(!done);
  Theorem res;
  if(result.getExpr().isFalse()) res = result;
  else res = solvedForm(solvedAndNewEqs);
  TRACE("arith eq", "processIntEq => ", res.getExpr(), " }");
  return res;
}

/*!
 * Takes a vector of equations and for every equation x_i=t_i
 * substitutes t_j for x_j in t_i for all j>i.  This turns the system
 * of equations into a solved form.
 *
 * Assumption: variables x_j may appear in the RHS terms t_i ONLY for
 * i<j, but not for i>=j.
 */
Theorem
TheoryArithNew::solvedForm(const vector<Theorem>& solvedEqs) 
{
  DebugAssert(solvedEqs.size() > 0, "TheoryArithNew::solvedForm()");

  // Trace code
  TRACE_MSG("arith eq", "TheoryArithNew::solvedForm:solvedEqs(\n  [");
  IF_DEBUG(if(debugger.trace("arith eq")) {
    for(vector<Theorem>::const_iterator j = solvedEqs.begin(),
	  jend=solvedEqs.end(); j!=jend;++j)
      TRACE("arith eq", "", j->getExpr(), ",\n   ");
  })
  TRACE_MSG("arith eq", "  ]) {");
  // End of Trace code
  
  vector<Theorem>::const_reverse_iterator
    i = solvedEqs.rbegin(),
    iend = solvedEqs.rend();
  // Substitution map: a variable 'x' is mapped to a Theorem x=t.
  // This map accumulates the resulting solved form.
  ExprMap<Theorem> subst;
  for(; i!=iend; ++i) {
    if(i->isRewrite()) {
      Theorem thm = substAndCanonize(*i, subst);
      TRACE("arith eq", "solvedForm: subst["+i->getLHS().toString()+"] = ",
	    thm.getExpr(), "");
      subst[i->getLHS()] = thm;
    }
    else {
      // This is the FALSE case: just return the contradiction
      DebugAssert(i->getExpr().isFalse(),
		  "TheoryArithNew::solvedForm: an element of solvedEqs must "
		  "be either EQ or FALSE: "+i->toString());
      return *i;
    }
  }
  // Now we've collected the solved form in 'subst'.  Wrap it up into
  // a conjunction and return.
  vector<Theorem> thms;
  for(ExprMap<Theorem>::iterator i=subst.begin(), iend=subst.end();
      i!=iend; ++i)
    thms.push_back(i->second);
  if (thms.size() > 1)
    return getCommonRules()->andIntro(thms);
  else
    return thms.back();
}


/*!
 * ASSUMPTION: 't' is a fully canonized arithmetic term, and every
 * element of subst is a fully canonized equation of the form x=e,
 * indexed by the LHS variable.
 */

Theorem
TheoryArithNew::substAndCanonize(const Expr& t, ExprMap<Theorem>& subst)
{
  TRACE("arith eq", "substAndCanonize(", t, ") {");
  // Quick and dirty check: return immediately if subst is empty
  if(subst.empty()) {
    Theorem res(reflexivityRule(t));
    TRACE("arith eq", "substAndCanonize[subst empty] => ", res, " }");
    return res;
  }
  // Check if we can substitute 't' directly
  ExprMap<Theorem>::iterator i = subst.find(t), iend=subst.end();
  if(i!=iend) {
    TRACE("arith eq", "substAndCanonize[subst] => ", i->second, " }");
    return i->second;
  }
  // The base case: t is an i-leaf
  if(isLeaf(t)) {
    Theorem res(reflexivityRule(t));
    TRACE("arith eq", "substAndCanonize[i-leaf] => ", res, " }");
    return res;
  }
  // 't' is an arithmetic term; recurse into the children
  vector<Theorem> thms;
  vector<unsigned> changed;
  for(unsigned j=0, jend=t.arity(); j!=jend; ++j) {
    Theorem thm = substAndCanonize(t[j], subst);
    if(thm.getRHS() != t[j]) {
      thm = canonThm(thm);
      thms.push_back(thm);
      changed.push_back(j);
    }
  }
  // Do the actual substitution and canonize the result
  Theorem res;
  if(thms.size() > 0) {
    res = substitutivityRule(t, changed, thms);
    res = canonThm(res);
  }
  else
    res = reflexivityRule(t);
  TRACE("arith eq", "substAndCanonize => ", res, " }");
  return res;
}


/*!
 *  ASSUMPTION: 't' is a fully canonized equation of the form x = t,
 *  and so is every element of subst, indexed by the LHS variable.
 */

Theorem
TheoryArithNew::substAndCanonize(const Theorem& eq, ExprMap<Theorem>& subst)
{
  // Quick and dirty check: return immediately if subst is empty
  if(subst.empty()) return eq;

  DebugAssert(eq.isRewrite(), "TheoryArithNew::substAndCanonize: t = "
	      +eq.getExpr().toString());
  const Expr& t = eq.getRHS();
  // Do the actual substitution in the term t
  Theorem thm = substAndCanonize(t, subst);
  // Substitution had no result: return the original equation
  if(thm.getRHS() == t) return eq;
  // Otherwise substitute the result into the equation
  vector<Theorem> thms;
  vector<unsigned> changed;
  thms.push_back(thm);
  changed.push_back(1);
  return iffMP(eq, substitutivityRule(eq.getExpr(), changed, thms));
}


void TheoryArithNew::updateStats(const Rational& c, const Expr& v)
{
  TRACE("arith ineq", "updateStats("+c.toString()+", ", v, ")");
  if(c > 0) {
    if(d_countRight.count(v) > 0) d_countRight[v] = d_countRight[v] + 1;
    else d_countRight[v] = 1;
  }
  else
    if(d_countLeft.count(v) > 0) d_countLeft[v] = d_countLeft[v] + 1;
    else d_countLeft[v] = 1;
}


void TheoryArithNew::updateStats(const Expr& monomial)
{
  Expr c, m;
  separateMonomial(monomial, c, m);
  updateStats(c.getRational(), m);
}


void TheoryArithNew::addToBuffer(const Theorem& thm) {
  // First, turn the inequality into 0 < rhs
  // FIXME: check if this can be optimized away
  Theorem result(thm);
  const Expr& e = thm.getExpr();
  // int kind = e.getKind();
  if(!(e[0].isRational() && e[0].getRational() == 0)) {
    result = iffMP(result, d_rules->rightMinusLeft(e));
    result = canonPred(result);
  }
  TRACE("arith ineq", "addToBuffer(", result.getExpr(), ")");
  // Push it into the buffer
  d_buffer.push_back(thm);

  // Collect the statistics about variables
  const Expr& rhs = thm.getExpr()[1];
  if(isPlus(rhs))
    for(Expr::iterator i=rhs.begin(), iend=rhs.end(); i!=iend; ++i)
      updateStats(*i);
  else // It's a monomial
    updateStats(rhs);
}


Expr TheoryArithNew::computeNormalFactor(const Expr& right, NormalizationType type) {
  	// Strategy: compute f = lcm(d1...dn)/gcd(c1...cn), where the RHS is of the form c1/d1*x1 + ... + cn/dn*xn or a rational
  
  	// The expression must be canonised, i.e. it is a sum or a rational
  	DebugAssert(isRational(right) || isPlus(right),"TheoryArithNew::computeNormalFactor: " + right.toString() + "wrong kind");
  
	// The factor we will compute
  	Rational factor;
  	
  	// Sign of the factor 
  	int sign = 0;
    
    // In case the expression is a PLUS expression find the gcd
  	if(isPlus(right)) {
  		
  		// Vector of numerators and denominators
   		vector<Rational> nums, denoms;
   		
   		// Pass throught the sum and pick up the integers
    	for(int i = 0, iend = right.arity(); i < iend; i ++) {
      
      		Rational c(1); // The rational constant of the current summand
      		      
      		// If rational or multiplicatino set c to be the apropriate rational
      		switch(right[i].getKind()) {
      			
      			case RATIONAL_EXPR: 
      			
      				// Sum term is just a rational, so just add it 
      				c = abs(right[i].getRational()); 
      				break;
        	    
        	    case MULT:          
        	    	
        	    	// Sum term is involves multiplication
        	    	c = right[i][0].getRational();
        	    	
        	    	// If this is the first one (sign is still not set) set the sign depending on the sign of the term
        	    	if (!sign) {
        	    		
        	    		// If the normalization type is NORMALIZE_UNIT just return the invese of the first
        	    		if (type == NORMALIZE_UNIT) return rat(1/c);
        	    		
        	    		// Set the sign otherwise
        	    		sign = (c > 0 ? 1 : -1);        	    		
        	    	}
        	    	
        	    	// Constant should be positive for lcd and gcd computation
        	    	c = abs(c);
        	    	
        	    	break;
        	    	
        		default: // Stays 1 or everything else
        			
        			break;
      		}
      		
      		// Add the demoninator and the numerator to the apropriate vectors
      		nums.push_back(c.getNumerator());
        	denoms.push_back(c.getDenominator());		
    	}
    
		// Compute the gcd of all the numerators
    	Rational gcd_nums = gcd(nums);
    
    	// x/0 == 0 in our model, as a total extension of arithmetic.  The
    	// particular value of x/0 is irrelevant, since the DP is guarded
    	// by the top-level TCCs, and it is safe to return any value in
    	// cases when terms are undefined.
    	factor = (gcd_nums == 0)? 0 : (sign * lcm(denoms) / gcd_nums);
  	} else 
  		// The expression is a rational, just return 1
    	factor = 1;
  
  // Return the reational expression representing the factor
  return rat(factor);
}


bool TheoryArithNew::lessThanVar(const Expr& isolatedMonomial, const Expr& var2) 
{
  DebugAssert(!isRational(var2) && !isRational(isolatedMonomial),
              "TheoryArithNew::findMaxVar: isolatedMonomial cannot be rational" + 
              isolatedMonomial.toString());
  Expr c, var0, var1;
  separateMonomial(isolatedMonomial, c, var0);
  separateMonomial(var2, c, var1);
  return var0 < var1;
}


void TheoryArithNew::separateMonomial(const Expr& e, Expr& c, Expr& var) {
  TRACE("separateMonomial", "separateMonomial(", e, ")");
  DebugAssert(!isPlus(e), 
	      "TheoryArithNew::separateMonomial(e = "+e.toString()+")");
  if(isMult(e)) {
    DebugAssert(e.arity() >= 2,
		"TheoryArithNew::separateMonomial(e = "+e.toString()+")");
    c = e[0];
    if(e.arity() == 2) var = e[1];
    else {
      vector<Expr> kids = e.getKids();
      kids[0] = rat(1);
      var = multExpr(kids);
    }
  } else {
    c = rat(1);
    var = e;
  }
  DebugAssert(c.isRational(), "TheoryArithNew::separateMonomial(e = "
	      +e.toString()+", c = "+c.toString()+")");
  DebugAssert(!isMult(var) || (var[0].isRational() && var[0].getRational()==1),
	      "TheoryArithNew::separateMonomial(e = "
	      +e.toString()+", var = "+var.toString()+")");
}


//returns true if e1 < e2, else false(i.e e2 < e1 or e1,e2 are not
//comparable)
bool TheoryArithNew::VarOrderGraph::lessThan(const Expr& e1, const Expr& e2) 
{
  d_cache.clear();
  //returns true if e1 is in the subtree rooted at e2 implying e1 < e2
  return dfs(e1,e2);
}

//returns true if e1 is in the subtree rooted at e2 implying e1 < e2
bool TheoryArithNew::VarOrderGraph::dfs(const Expr& e1, const Expr& e2)
{
  if(e1 == e2)
    return true;
  if(d_cache.count(e2) > 0)
    return false;
  if(d_edges.count(e2) == 0)
    return false;
  d_cache[e2] = true;
  vector<Expr>& e2Edges = d_edges[e2];
  vector<Expr>::iterator i = e2Edges.begin();
  vector<Expr>::iterator iend = e2Edges.end();
  //if dfs finds e1 then i != iend else i is equal to iend
  for(; i != iend && !dfs(e1,*i); ++i);
  return (i != iend);
}


void TheoryArithNew::VarOrderGraph::selectSmallest(vector<Expr>& v1,
                                               vector<Expr>& v2) 
{
  int v1Size = v1.size();
  vector<bool> v3(v1Size);
  for(int j=0; j < v1Size; ++j)
    v3[j] = false;

  for(int j=0; j < v1Size; ++j) {
    if(v3[j]) continue;
    for(int i =0; i < v1Size; ++i) {
      if((i == j) || v3[i]) 
        continue;
      if(lessThan(v1[i],v1[j])) {
        v3[j] = true;
        break;
      }
    }
  }
  vector<Expr> new_v1;

  for(int j = 0; j < v1Size; ++j) 
    if(!v3[j]) v2.push_back(v1[j]);
    else new_v1.push_back(v1[j]);
  v1 = new_v1;
}


void TheoryArithNew::VarOrderGraph::selectLargest(const vector<Expr>& v1,
                                               vector<Expr>& v2) 
{
  int v1Size = v1.size();
  vector<bool> v3(v1Size);
  for(int j=0; j < v1Size; ++j)
    v3[j] = false;

  for(int j=0; j < v1Size; ++j) {
    if(v3[j]) continue;
    for(int i =0; i < v1Size; ++i) {
      if((i == j) || v3[i]) 
        continue;
      if(lessThan(v1[j],v1[i])) {
        v3[j] = true;
        break;
      }
    }
  }
  
  for(int j = 0; j < v1Size; ++j) 
    if(!v3[j]) v2.push_back(v1[j]);
}

///////////////////////////////////////////////////////////////////////////////
// TheoryArithNew Public Methods                                                //
///////////////////////////////////////////////////////////////////////////////


TheoryArithNew::TheoryArithNew(TheoryCore* core)
  : TheoryArith(core, "ArithmeticNew"),
    d_diseq(core->getCM()->getCurrentContext()),
    d_diseqIdx(core->getCM()->getCurrentContext(), 0, 0),
    d_inModelCreation(core->getCM()->getCurrentContext(), false, 0),
    d_freeConstDB(core->getCM()->getCurrentContext()),
    d_buffer(core->getCM()->getCurrentContext()),
    // Initialize index to 0 at scope 0
    d_bufferIdx(core->getCM()->getCurrentContext(), 0, 0),
    d_bufferThres(&(core->getFlags()["ineq-delay"].getInt())),
    d_countRight(core->getCM()->getCurrentContext()),
    d_countLeft(core->getCM()->getCurrentContext()),
    d_sharedTerms(core->getCM()->getCurrentContext()),
    d_sharedVars(core->getCM()->getCurrentContext()),
    consistent(core->getCM()->getCurrentContext()),
    lowerBound(core->getCM()->getCurrentContext()),
    upperBound(core->getCM()->getCurrentContext()),
    beta(core->getCM()->getCurrentContext()),
    assertedExprCount(core->getCM()->getCurrentContext()),
    integer_lemma(core->getCM()->getCurrentContext())
{
  IF_DEBUG(d_diseq.setName("CDList[TheoryArithNew::d_diseq]");)
  IF_DEBUG(d_buffer.setName("CDList[TheoryArithNew::d_buffer]");)
  IF_DEBUG(d_bufferIdx.setName("CDList[TheoryArithNew::d_bufferIdx]");)

  getEM()->newKind(REAL, "_REAL", true);
  getEM()->newKind(INT, "_INT", true);
  getEM()->newKind(SUBRANGE, "_SUBRANGE", true);

  getEM()->newKind(UMINUS, "_UMINUS");
  getEM()->newKind(PLUS, "_PLUS");
  getEM()->newKind(MINUS, "_MINUS");
  getEM()->newKind(MULT, "_MULT");
  getEM()->newKind(DIVIDE, "_DIVIDE");
  getEM()->newKind(POW, "_POW");
  getEM()->newKind(INTDIV, "_INTDIV");
  getEM()->newKind(MOD, "_MOD");
  getEM()->newKind(LT, "_LT");
  getEM()->newKind(LE, "_LE");
  getEM()->newKind(GT, "_GT");
  getEM()->newKind(GE, "_GE");
  getEM()->newKind(IS_INTEGER, "_IS_INTEGER");
  getEM()->newKind(NEGINF, "_NEGINF");
  getEM()->newKind(POSINF, "_POSINF");
  getEM()->newKind(DARK_SHADOW, "_DARK_SHADOW");
  getEM()->newKind(GRAY_SHADOW, "_GRAY_SHADOW");

  getEM()->newKind(REAL_CONST, "_REAL_CONST");

  vector<int> kinds;
  kinds.push_back(REAL);
  kinds.push_back(INT);
  kinds.push_back(SUBRANGE);
  kinds.push_back(IS_INTEGER);
  kinds.push_back(UMINUS);
  kinds.push_back(PLUS);
  kinds.push_back(MINUS);
  kinds.push_back(MULT);
  kinds.push_back(DIVIDE);
  kinds.push_back(POW);
  kinds.push_back(INTDIV);
  kinds.push_back(MOD);
  kinds.push_back(LT);
  kinds.push_back(LE);
  kinds.push_back(GT);
  kinds.push_back(GE);
  kinds.push_back(RATIONAL_EXPR);
  kinds.push_back(NEGINF);
  kinds.push_back(POSINF);
  kinds.push_back(DARK_SHADOW);
  kinds.push_back(GRAY_SHADOW);
  kinds.push_back(REAL_CONST);

  registerTheory(this, kinds, true);

  d_rules = createProofRules();

  d_realType = Type(getEM()->newLeafExpr(REAL));
  d_intType  = Type(getEM()->newLeafExpr(INT));
  consistent = SATISFIABLE;
  assertedExprCount = 0;
}


// Destructor: delete the proof rules class if it's present
TheoryArithNew::~TheoryArithNew() {
  if(d_rules != NULL) delete d_rules;
  // Clear the inequality databases
  for(ExprMap<CDList<Ineq> *>::iterator i=d_inequalitiesRightDB.begin(),
	iend=d_inequalitiesRightDB.end(); i!=iend; ++i) {
    delete (i->second);
    free(i->second);
  }
  for(ExprMap<CDList<Ineq> *>::iterator i=d_inequalitiesLeftDB.begin(),
	iend=d_inequalitiesLeftDB.end(); i!=iend; ++i) {
    delete (i->second);
    free (i->second);
  }
}

void TheoryArithNew::collectVars(const Expr& e, vector<Expr>& vars,
			      set<Expr>& cache) {
  // Check the cache first
  if(cache.count(e) > 0) return;
  // Not processed yet.  Cache the expression and proceed
  cache.insert(e);
  if(isLeaf(e)) vars.push_back(e);
  else
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
      collectVars(*i, vars, cache);
}

void
TheoryArithNew::processFiniteInterval(const Theorem& alphaLEax,
				   const Theorem& bxLEbeta) {
  const Expr& ineq1(alphaLEax.getExpr());
  const Expr& ineq2(bxLEbeta.getExpr());
  DebugAssert(isLE(ineq1), "TheoryArithNew::processFiniteInterval: ineq1 = "
	      +ineq1.toString());
  DebugAssert(isLE(ineq2), "TheoryArithNew::processFiniteInterval: ineq2 = "
	      +ineq2.toString());
  // If the inequalities are not integer, just return (nothing to do)
  if(!isInteger(ineq1[0])
     || !isInteger(ineq1[1])
     || !isInteger(ineq2[0])
     || !isInteger(ineq2[1]))
    return;

  const Expr& ax = ineq1[1];
  const Expr& bx = ineq2[0];
  DebugAssert(!isPlus(ax) && !isRational(ax),
	      "TheoryArithNew::processFiniteInterval:\n ax = "+ax.toString());
  DebugAssert(!isPlus(bx) && !isRational(bx),
	      "TheoryArithNew::processFiniteInterval:\n bx = "+bx.toString());
  Expr a = isMult(ax)? ax[0] : rat(1);
  Expr b = isMult(bx)? bx[0] : rat(1);

  Theorem thm1(alphaLEax), thm2(bxLEbeta);
  // Multiply the inequalities by 'b' and 'a', and canonize them, if necessary
  if(a != b) {
    thm1 = canonPred(iffMP(alphaLEax, d_rules->multIneqn(ineq1, b)));
    thm2 = canonPred(iffMP(bxLEbeta, d_rules->multIneqn(ineq2, a)));
  }
  // Check that a*beta - b*alpha == c > 0
  const Expr& alphaLEt = thm1.getExpr();
  const Expr& alpha = alphaLEt[0];
  const Expr& t = alphaLEt[1];
  const Expr& beta = thm2.getExpr()[1];
  Expr c = canon(beta - alpha).getRHS();

  if(c.isRational() && c.getRational() >= 1) {
    // This is a finite interval.  First, derive t <= alpha + c:
    // canon(alpha+c) => (alpha+c == beta) ==> [symmetry] beta == alpha+c
    // Then substitute that in thm2
    Theorem bEQac = symmetryRule(canon(alpha + c));
    // Substitute beta == alpha+c for the second child of thm2
    vector<unsigned> changed;
    vector<Theorem> thms;
    changed.push_back(1);
    thms.push_back(bEQac);
    Theorem tLEac = substitutivityRule(thm2.getExpr(), changed, thms);
    tLEac = iffMP(thm2, tLEac);
    // Derive and enqueue the finite interval constraint
    Theorem isInta(isIntegerThm(alpha));
    Theorem isIntt(isIntegerThm(t));
    enqueueFact(d_rules->finiteInterval(thm1, tLEac, isInta, isIntt));
  }
}


void
TheoryArithNew::processFiniteIntervals(const Expr& x) {
  // If x is not integer, do not bother
  if(!isInteger(x)) return;
  // Process every pair of the opposing inequalities for 'x'
  ExprMap<CDList<Ineq> *>::iterator iLeft, iRight;
  iLeft = d_inequalitiesLeftDB.find(x);
  if(iLeft == d_inequalitiesLeftDB.end()) return;
  iRight = d_inequalitiesRightDB.find(x);
  if(iRight == d_inequalitiesRightDB.end()) return;
  // There are some opposing inequalities; get the lists
  CDList<Ineq>& ineqsLeft = *(iLeft->second);
  CDList<Ineq>& ineqsRight = *(iRight->second);
  // Get the sizes of the lists
  size_t sizeLeft = ineqsLeft.size();
  size_t sizeRight = ineqsRight.size();
  // Process all the pairs of the opposing inequalities
  for(size_t l=0; l<sizeLeft; ++l)
    for(size_t r=0; r<sizeRight; ++r)
      processFiniteInterval(ineqsRight[r], ineqsLeft[l]);
}

/*! This function recursively decends expression tree <strong>without
 *  caching</strong> until it hits a node that is already setup.  Be
 *  careful on what expressions you are calling it.
 */
void
TheoryArithNew::setupRec(const Expr& e) {
  if(e.hasFind()) return;
  // First, set up the kids recursively
  for (int k = 0; k < e.arity(); ++k) {
    setupRec(e[k]);
  }
  // Create a find pointer for e
  e.setFind(reflexivityRule(e));
  e.setEqNext(reflexivityRule(e));
  // And call our own setup()   
  setup(e);
}


/*!
 * Keep track of all finitely bounded integer variables in shared
 * terms.
 *
 * When a new shared term t is reported, all of its variables x1...xn
 * are added to the set d_sharedVars.  
 *
 * For each newly added variable x, check all of its opposing
 * inequalities, find out all the finite bounds and assert the
 * corresponding GRAY_SHADOW constraints.
 *
 * When projecting integer inequalities, the database d_sharedVars is
 * consulted, and if the variable is in it, check the shadows for
 * being a finite interval, and produce the additional GRAY_SHADOW
 * constraints.
 */
void TheoryArithNew::addSharedTerm(const Expr& e) {
  d_sharedTerms[e] = true;
  /*
  set<Expr> cache; // Aux. cache for collecting i-leaves
  vector<Expr> vars; // Vector of vars in e
  collectVars(e, vars, cache);
  for(vector<Expr>::iterator i=vars.begin(), iend=vars.end(); i!=iend; ++i) {
    if(d_sharedVars.count(*i) == 0) {
      TRACE("arith shared", "TheoryArithNew::addSharedTerm: new var = ", *i, "");
      processFiniteIntervals(*i);
      d_sharedVars[*i]=true;
    }
  }
  */
}

void TheoryArithNew::refineCounterExample()
{
  d_inModelCreation = true;
  TRACE("model", "refineCounterExample[TheoryArithNew] ", "", "{");
  CDMap<Expr, bool>::iterator it = d_sharedTerms.begin(), it2,
    iend = d_sharedTerms.end();
  // Add equalities over all pairs of shared terms as suggested
  // splitters.  Notice, that we want to split on equality
  // (positively) first, to reduce the size of the model.
  for(; it!=iend; ++it) {
    // Copy by value: the elements in the pair from *it are NOT refs in CDMap
    Expr e1 = (*it).first;
    for(it2 = it, ++it2; it2!=iend; ++it2) {
      Expr e2 = (*it2).first;
      DebugAssert(isReal(getBaseType(e1)),
		  "TheoryArithNew::refineCounterExample: e1 = "+e1.toString()
		  +"\n type(e1) = "+e1.getType().toString());
      if(findExpr(e1) != findExpr(e2)) {
	DebugAssert(isReal(getBaseType(e2)),
		    "TheoryArithNew::refineCounterExample: e2 = "+e2.toString()
		    +"\n type(e2) = "+e2.getType().toString());
	Expr eq = simplifyExpr(e1.eqExpr(e2));
        if (!eq.isBoolConst())
          addSplitter(eq);
      }
    }
  }
  TRACE("model", "refineCounterExample[Theory::Arith] ", "", "}");
}


void
TheoryArithNew::findRationalBound(const Expr& varSide, const Expr& ratSide, 
			       const Expr& var,
			       Rational &r)
{
  Expr c, x;
  separateMonomial(varSide, c, x);
  
  DebugAssert(findExpr(c).isRational(), 
	      "seperateMonomial failed"); 
  DebugAssert(findExpr(ratSide).isRational(), 
	      "smallest variable in graph, should not have variables"
	      " in inequalities: ");
  DebugAssert(x == var, "separateMonomial found different variable: " 
	      + var.toString());
  r = findExpr(ratSide).getRational() / findExpr(c).getRational();
} 

bool
TheoryArithNew::findBounds(const Expr& e, Rational& lub, Rational&  glb)
{
  bool strictLB=false, strictUB=false;
  bool right = (d_inequalitiesRightDB.count(e) > 0
		       && d_inequalitiesRightDB[e]->size() > 0);
  bool left = (d_inequalitiesLeftDB.count(e) > 0
	       && d_inequalitiesLeftDB[e]->size() > 0);
  int numRight = 0, numLeft = 0;
  if(right) { //rationals less than e
    CDList<Ineq> * ratsLTe = d_inequalitiesRightDB[e];
    for(unsigned int i=0; i<ratsLTe->size(); i++) {
      DebugAssert((*ratsLTe)[i].varOnRHS(), "variable on wrong side!");
      Expr ineq = (*ratsLTe)[i].ineq().getExpr();
      Expr leftSide = ineq[0], rightSide = ineq[1];
      Rational r;
      findRationalBound(rightSide, leftSide, e , r);
      if(numRight==0 || r>glb){
	glb = r;
	strictLB = isLT(ineq);
      }
      numRight++;
    }
    TRACE("model", "   =>Lower bound ", glb.toString(), "");
  }
  if(left) {   //rationals greater than e
    CDList<Ineq> * ratsGTe = d_inequalitiesLeftDB[e];
    for(unsigned int i=0; i<ratsGTe->size(); i++) { 
      DebugAssert((*ratsGTe)[i].varOnLHS(), "variable on wrong side!");
      Expr ineq = (*ratsGTe)[i].ineq().getExpr();
      Expr leftSide = ineq[0], rightSide = ineq[1];
      Rational r;
      findRationalBound(leftSide, rightSide, e, r); 
      if(numLeft==0 || r<lub) {
	lub = r;
	strictUB = isLT(ineq);
      }
      numLeft++;
    }
    TRACE("model", "   =>Upper bound ", lub.toString(), "");
  }
  if(!left && !right) {
      lub = 0; 
      glb = 0;
  }
  if(!left && right) {lub = glb +2;}
  if(!right && left)  {glb =  lub-2;}
  DebugAssert(glb <= lub, "Greatest lower bound needs to be smaller "
	      "than least upper bound"); 
  return strictLB;
}

void TheoryArithNew::assignVariables(std::vector<Expr>&v)
{
  int count = 0;
  while (v.size() > 0) {
    std::vector<Expr> bottom;
    d_graph.selectSmallest(v, bottom);
    TRACE("model", "Finding variables to assign. Iteration # ", count, "");
    for(unsigned int i = 0; i<bottom.size(); i++) {
      Expr e = bottom[i];
      TRACE("model", "Found: ", e, "");
      // Check if it is already a concrete constant
      if(e.isRational()) continue;
      
      Rational lub, glb;
      bool strictLB;
      strictLB = findBounds(e, lub, glb);
      Rational mid;
      if(isInteger(e)) {
	if(strictLB && glb.isInteger())
	  mid = glb + 1;
	else
	  mid = ceil(glb);
      }
      else
	mid = (lub + glb)/2;
      TRACE("model", "Assigning mid = ", mid, " {");
      assignValue(e, rat(mid));
      TRACE("model", "Assigned find(e) = ", findExpr(e), " }");
      if(inconsistent()) return; // Punt immediately if failed
    }
    count++;
  }
}

void TheoryArithNew::computeModelBasic(const std::vector<Expr>& v)
{
  d_inModelCreation = true;
  vector<Expr> reps;
  TRACE("model", "Arith=>computeModel ", "", "{");
  for(unsigned int i=0; i <v.size(); ++i) {
    const Expr& e = v[i];
    if(findExpr(e) == e) {
      TRACE("model", "arith variable:", e , "");
      reps.push_back(e);
    }
    else {
      TRACE("model", "arith variable:", e , "");
      TRACE("model", " ==> is defined by: ", findExpr(e) , "");
    }
  }
  assignVariables(reps);
  TRACE("model", "Arith=>computeModel", "", "}");
  d_inModelCreation = false;
}

// For any arith expression 'e', if the subexpressions are assigned
// concrete values, then find(e) must already be a concrete value.
void TheoryArithNew::computeModel(const Expr& e, vector<Expr>& vars) {
  DebugAssert(findExpr(e).isRational(), "TheoryArithNew::computeModel("
	      +e.toString()+")\n e is not assigned concrete value.\n"
	      +" find(e) = "+findExpr(e).toString());
  assignValue(simplify(e));
  vars.push_back(e);
}

/*! accepts a rewrite theorem over eqn|ineqn and normalizes it
 *  and returns a theorem to that effect. assumes e is non-trivial
 *  i.e. e is not '0=const' or 'const=0' or '0 <= const' etc.
 */
Theorem TheoryArithNew::normalize(const Expr& e, NormalizationType type) {
  
 	//e is an eqn or ineqn. e is not a trivial eqn or ineqn
  	//trivial means 0 = const or 0 <= const.
  
  	// Trace the normalization on the arithm trace flag
  	TRACE("arith", "normalize(", e, ") {"); 
  
  	// The constraint must be an equality or inequality
  	DebugAssert(isIneq(e), "normalize: input must be an inequality: " + e.toString());
  
  	// The right side must be a sum or a multiplication 
  	DebugAssert(isPlus(e[1]) || (isMult(e[1]) && e[1][0].isRational()), "normalize: right side must be a sum or a mult: " + e.toString());
  
  	// The left side must be 0
  	DebugAssert(e[0].isRational() && 0 == e[0].getRational(), "normalize: e[0] must be 0" + e.toString());
  
  	// Compute the factor to use for normalizing the inequality  
  	Expr factor;
  	// If a mult, just take the coefficient
  	if (isMult(e[1])) factor = rat(1/e[1][0].getRational());
  	// Otherwise compute it
  	else factor = computeNormalFactor(e[1], type);
  
  	// Trace the rezult on the arith flag
  	TRACE("arith", "normalize: factor = ", factor, "");
    
  	// The theorem we will be creating (reflexivity, just in case)
  	Theorem thm;
  
  	// Now multiply the equality by the factor, unless it is 1
  	if(factor.getRational() != 1)
    	switch(e.getKind()) {
    		
    		case LE:
    		case LT:
    		case GE:
    		case GT:
      			      				
      			// Multiply inequality by the factor	
      			thm = d_rules->multIneqn(e, factor);
      			
      			// And canonize the result
      			thm = canonPredEquiv(thm);
      
      			// Inequalities case break
      			break;
    		
    		default:
      			
      			// How did we get here
      			FatalAssert(false, "normalize: control should not reach here" + e.toString());
      			
      			// Default case break
      			break;
    	}
    else 
    	// If rational is 1 then nothing to be done
    	thm = reflexivityRule(e);

  
  // Trace the resulting theorem on the arith trace flag
  TRACE("arith", "normalize => ", thm, " }");
  
  // Return the explaining theorem
  return(thm);
}


Theorem TheoryArithNew::normalize(const Theorem& eIffEqn, NormalizationType type) {
  return transitivityRule(eIffEqn, normalize(eIffEqn.getRHS(), type));
}

Theorem TheoryArithNew::rafineIntegerConstraints(const Theorem& thm) {
	
	// The resulting theorem
	Theorem result = thm;
	
	// Get the constraint
	const Expr& constr = result.getRHS();
	
	// Get the proof that this constraint is an integer constraint 
	Theorem isIntConstraintThm = isIntegerThm(constr[1]);
	
	// If not an integer, just return the same theorem
	if (isIntConstraintThm.isNull()) return result;
	
	// Trace the integer
	TRACE("integer", "TheoryArithNew::rafineIntegerConstraints(", constr, ")");
	TRACE("integer", "TheoryArithNew::rafineIntegerConstraints: int proof:", isIntConstraintThm, "");
	
	// Get the left-hand of the constraint (the rational)
	Rational r = constr[0].getRational();
	
	// If it is a strict inequality, make it non-strict
	if (constr.getKind() == LT || constr.getKind() == GT || !r.isInteger())
		result = transitivityRule(result, d_rules->rafineStrictInteger(isIntConstraintThm, constr));

	// Return the result		
	return result;
}

Theorem TheoryArithNew::rewrite(const Expr& e) {
	
    // Leaves are assumeed to be already simplified
    //DebugAssert(leavesAreSimp(e), "Expected leaves to be simplified");
  
    // Trace the rewrites on the arith flag
    TRACE("arith", "TheoryArithNew::rewrite(", e, ") {");
  
    // The resulting theorem object
    Theorem thm;
    
    // Are we in the NOT expression
    bool isNot = false;
  
    // If the expression is not a term, i.e a literal  
    if (!e.isTerm()) {
    	 
    	// If the expression is not a literal just return the reflexivity theorem
    	if (!e.isAbsLiteral()) { 
    		
    		// Set the expression REWRITE NORMAL FLAG
    		e.setRewriteNormal();
    		
    		// Create the reflaxivity rule
      		thm = reflexivityRule(e);
      	
      		// Trace the non-literal rewrite 
      		TRACE("arith", "TheoryArithNew::rewrite[non-literal] => ", thm, " }");
      	
      		// Return the theorem
      		return thm;
    	}
    
    	// Its a literal, switch the arithmetic relations for rewrite
    	switch(e.getKind()) {
    
    		// Equality
    		case EQ: {
    		
    			// Rewrite equality as two inequalities
    			thm = d_rules->eqToIneq(e);
    			Expr andExpr = thm.getRHS();
    
    			// Rewrite the left inequality
    			Expr leExpr = andExpr[0];
    			const Theorem& thmLeft = simplify(leExpr);
    			
    			// Rewrite the right inequality	
    			Expr geExpr = andExpr[1]; 
   				const Theorem& thmRight = simplify(geExpr);    			
  			
  				// Do the substitution
  				thm = transitivityRule(thm, substitutivityRule(andExpr, thmLeft, thmRight));
  						
    			// EQ case break
    			break;
    		}
    
    		// Negation of an atomic formula
    		case NOT:    

				// If here, the equality should have already been rewritten as two disequalitites
				DebugAssert(e[0].getKind() != EQ, "TheoryArithNew::rewrite, not expecting equality under negation");
    			
				// Negate the inequality and continue with the normal case
				thm = d_rules->negatedInequality(e);
			
				// IMPORTANT, LE, LT, GE, GT MUST BE UNDER THIS
				isNot = true;
			
    		case LT:
    		case GT:
    		case LE:
    		case GE:
    		
				// Move everything to the right side
				if (isNot)
					thm = transitivityRule(thm, d_rules->rightMinusLeft(thm.getRHS())); 
				else
					thm = d_rules->rightMinusLeft(e);

      			// Canonise children again
      			thm = canonPredEquiv(thm);
   
      			// If a trivial inequation just return true or false
      			if ((thm.getRHS())[1].isRational()) 
					thm = transitivityRule(thm, d_rules->constPredicate(thm.getRHS()));
      			else { // It's a non-trivial inequation
      				
      				// Normalize the inequality 
					thm = normalize(thm, NORMALIZE_UNIT);
				
					// Get the left and right side
					const Expr& normalised = thm.getRHS();
					const Expr& rightSide = normalised[1]; 
					const Expr& leftSide  = normalised[0];
				
					// If the right side is a sum, move the rational to the right side
					if (isPlus(rightSide)) {
						// Check if the fist of the sum is a rational
						if (rightSide[0].isRational()) {
							// Add the negative constant to both sides
							thm = transitivityRule(thm, d_rules->plusPredicate(leftSide, rightSide, rat(-rightSide[0].getRational()), thm.getRHS().getKind())); 	 
							// Canonize the left side
							const Theorem& thmLeft  = d_rules->canonPlus(thm.getRHS()[0]);
							// Canonize the right side
							const Theorem& thmRight = d_rules->canonPlus(thm.getRHS()[1]); 
							// Sunstitute the canonised into the expression
							thm = transitivityRule(thm, substitutivityRule(thm.getRHS(), thmLeft, thmRight));
						}
					}
      			}
      		
      			// If a strict inequality on integers, or bounded by a non-integer, rafine it to a non-strict one
//       			thm = rafineIntegerConstraints(thm);
      			
      			// EQ, LE, LT, GE, GT case break  			
      			break;
    
    		case IS_INTEGER:
    		
    			// TRACE
    			TRACE("integer", "Got ", e.toString(), "");
    			TRACE("integer", "Type ", e[0].getType().toString(), ""); 
    		
    			// TODO: What with the integers
				thm = d_rules->dummyTheorem(e);
    			
    			// IS_INTEGER case break
    			break;
    
    		default:
      			
      			// How did we get here
      			FatalAssert(false, "Theory_Arith::rewrite: control should not reach here");
      
      			// default break
      			break;
      			
    	} // End relation case
    	
  	} else { // Expression is a term 
  		
  		// Terms that don't contain formulas are canonised via the canon() function 
  		if (e.isAtomic()) thm = canon(e);
  		// Otherwise just return the same expression
    	else thm = reflexivityRule(e);
  	}
  
  	// Compact the theorem into one rule
  	//thm = d_rules->trustedRewrite(e, thm.getRHS());
  
  	// Arith canonization is idempotent, the theory should stay the same
  	if (theoryOf(thm.getRHS()) == this)
    	thm.getRHS().setRewriteNormal();
    
    // Finished, trace the end of rewrite on the arith flag	
  	TRACE("arith", "TheoryArithNew::rewrite => ", thm, " }");
  
  	// Return the final theorem
  	return thm;
}


void TheoryArithNew::setup(const Expr& e)
{
	//If the expression is not a term but rather a predicate
  	if (!e.isTerm()) {
  		
  		// If not or equality, just return
    	if (e.isNot() || e.isEq()) return;
    
    	// TODO: Integer::eqToIneq
    	if (isIntPred(e)) return;
    
	    // Check if the expression is canonised as (SUM t1 ... tn) @ b
    	DebugAssert(isIneq(e) && e[0].isRational(), "TheoryArithNew::setup: b @ (sum t1 ... tn) :" + e.toString());
    
    	// Add the sum to the notify list of e
    	e[1].addToNotify(this, e);
    	
  	} else {
  		
  		// The arity of the expression 
  		int arity(e.arity());
  		
  		// Go through all the children and add this expression to their notify lists 
  		for (int k = 0 ; k < arity; k ++) {
  			
    		// Add the to the notify list of the children 
    		e[k].addToNotify(this, e);
    		
    		// Trace this notification add
    		TRACE("arith setup", "e["+int2string(k)+"]: ", *(e[k].getNotify()), "");
  		}
  	}
}


void TheoryArithNew::update(const Theorem& e, const Expr& d)
{
  if (inconsistent()) return;
  IF_DEBUG(debugger.counter("arith update total")++;)
  if (!d.hasFind()) return;
  if (isIneq(d)) {
    // Substitute e[1] for e[0] in d and enqueue new inequality
    DebugAssert(e.getLHS() == d[1], "Mismatch");
    Theorem thm = find(d);
    //    DebugAssert(thm.getRHS() == trueExpr(), "Expected find = true");
    vector<unsigned> changed;
    vector<Theorem> children;
    changed.push_back(1);
    children.push_back(e);
    Theorem thm2 = substitutivityRule(d, changed, children);
    if (thm.getRHS() == trueExpr()) {
      enqueueFact(iffMP(getCommonRules()->iffTrueElim(thm), thm2));
    }
    else {
      enqueueFact(getCommonRules()->iffFalseElim(
        transitivityRule(symmetryRule(thm2), thm)));
    }
    IF_DEBUG(debugger.counter("arith update ineq")++;)
  }
  else if (find(d).getRHS() == d) {
    // Substitute e[1] for e[0] in d and assert the result equal to d
    Theorem thm = canonSimp(d);
    TRACE("arith", "TheoryArithNew::update(): thm = ", thm, "");
    DebugAssert(leavesAreSimp(thm.getRHS()), "updateHelper error: "
 		+thm.getExpr().toString());
    assertEqualities(transitivityRule(thm, rewrite(thm.getRHS())));
    IF_DEBUG(debugger.counter("arith update find(d)=d")++;)
  }
}


Theorem TheoryArithNew::solve(const Theorem& thm)
{
  DebugAssert(thm.isRewrite() && thm.getLHS().isTerm(), "");
  const Expr& lhs = thm.getLHS();
  const Expr& rhs = thm.getRHS();

  // Check for already solved equalities.

  // Have to be careful about the types: integer variable cannot be
  // assigned a real term.  Also, watch for e[0] being a subexpression
  // of e[1]: this would create an unsimplifiable expression.
  if (isLeaf(lhs) && !isLeafIn(lhs, rhs) 
      && (lhs.getType() != intType() || isInteger(rhs))
      // && !e[0].subExprOf(e[1])
      )
    return thm;

  // Symmetric version is already solved
  if (isLeaf(rhs) && !isLeafIn(rhs, lhs)
      && (rhs.getType() != intType() || isInteger(lhs))
      // && !e[1].subExprOf(e[0])
      )
    return symmetryRule(thm);

  return doSolve(thm);
}

 
void TheoryArithNew::computeModelTerm(const Expr& e, std::vector<Expr>& v) {
  switch(e.getKind()) {
  case RATIONAL_EXPR: // Skip the constants
    break;
  case PLUS:
  case MULT:
  case DIVIDE:
  case POW: // This is not a variable; extract the variables from children
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
      // getModelTerm(*i, v);
      v.push_back(*i);
    break;
  default: { // Otherwise it's a variable.  Check if it has a find pointer
    Expr e2(findExpr(e));
    if(e==e2) {
      TRACE("model", "TheoryArithNew::computeModelTerm(", e, "): a variable");
      // Leave it alone (it has no descendants)
      // v.push_back(e);
    } else {
      TRACE("model", "TheoryArithNew::computeModelTerm("+e.toString()
	    +"): has find pointer to ", e2, "");
      v.push_back(e2);
    }
  }
  }
}

Expr TheoryArithNew::computeTypePred(const Type& t, const Expr& e) {
  Expr tExpr = t.getExpr();
  switch(tExpr.getKind()) {
  case INT:  
    return Expr(IS_INTEGER, e);
  case SUBRANGE: {
    std::vector<Expr> kids;
    kids.push_back(Expr(IS_INTEGER, e));
    kids.push_back(leExpr(tExpr[0], e));
    kids.push_back(leExpr(e, tExpr[1]));
    return andExpr(kids);
  }
  default:
    return e.getEM()->trueExpr();
  }
}


void TheoryArithNew::checkAssertEqInvariant(const Theorem& e)
{
  return;
}


void TheoryArithNew::checkType(const Expr& e)
{
  switch (e.getKind()) {
    case INT:
    case REAL:
      if (e.arity() > 0) {
        throw Exception("Ill-formed arithmetic type: "+e.toString());
      }
      break;
    case SUBRANGE:
      if (e.arity() != 2 ||
          !isIntegerConst(e[0]) ||
          !isIntegerConst(e[1]) ||
          e[0].getRational() > e[1].getRational()) {
        throw Exception("bad SUBRANGE type expression"+e.toString());
      }
      break;
    default:
      DebugAssert(false, "Unexpected kind in TheoryArithNew::checkType"
                  +getEM()->getKindName(e.getKind()));
  }
}


Cardinality TheoryArithNew::finiteTypeInfo(Expr& e, Unsigned& n,
                                           bool enumerate, bool computeSize)
{
  Cardinality card = CARD_INFINITE;
  switch (e.getKind()) {
    case SUBRANGE: {
      card = CARD_FINITE;
      Expr typeExpr = e;
      if (enumerate) {
        Rational r = typeExpr[0].getRational() + n;
        if (r <= typeExpr[1].getRational()) {
          e = rat(r);
        }
        else e = Expr();
      }
      if (computeSize) {
        Rational r = typeExpr[1].getRational() - typeExpr[0].getRational() + 1;
        n = r.getUnsigned();
      }
      break;
    }
    default:
      break;
  }
  return card;
}


void TheoryArithNew::computeType(const Expr& e)
{
  switch (e.getKind()) {
    case REAL_CONST:
      e.setType(d_realType);
      break;
    case RATIONAL_EXPR:
      if(e.getRational().isInteger())
        e.setType(d_intType);
      else
        e.setType(d_realType);
      break;
    case UMINUS:
    case PLUS:
    case MINUS:
    case MULT:
    case POW: {
      bool isInt = true;
      for(int k = 0; k < e.arity(); ++k) {
        if(d_realType != getBaseType(e[k]))
          throw TypecheckException("Expecting type REAL with `" +
                                   getEM()->getKindName(e.getKind()) + "',\n"+
                                   "but got a " + getBaseType(e[k]).toString()+ 
                                   " for:\n" + e.toString());
        if(isInt && !isInteger(e[k]))
          isInt = false;
      }
      if(isInt)
        e.setType(d_intType);
      else
        e.setType(d_realType);
      break;
    }
    case DIVIDE: {
      Expr numerator = e[0];
      Expr denominator = e[1];
      if (getBaseType(numerator) != d_realType ||
          getBaseType(denominator) != d_realType) {
        throw TypecheckException("Expecting only REAL types with `DIVIDE',\n"
                                 "but got " + getBaseType(numerator).toString()+ 
                                 " and " + getBaseType(denominator).toString() +
                                 " for:\n" + e.toString());
      }
      if(denominator.isRational() && 1 == denominator.getRational())
        e.setType(numerator.getType());
      else
        e.setType(d_realType);
      break;
    }
    case LT:
    case LE:
    case GT:
    case GE:
    case GRAY_SHADOW:
      // Need to know types for all exprs -Clark
      //    e.setType(boolType());
      //    break;
    case DARK_SHADOW:
      for (int k = 0; k < e.arity(); ++k) {
        if (d_realType != getBaseType(e[k]))
          throw TypecheckException("Expecting type REAL with `" +
                                   getEM()->getKindName(e.getKind()) + "',\n"+
                                   "but got a " + getBaseType(e[k]).toString()+ 
                                   " for:\n" + e.toString());
      }
      
      e.setType(boolType());
      break;
    case IS_INTEGER:
      if(d_realType != getBaseType(e[0]))
        throw TypecheckException("Expected type REAL, but got "
                                 +getBaseType(e[0]).toString()
                                 +"\n\nExpr = "+e.toString());
      e.setType(boolType());
      break;
    default:
      DebugAssert(false,"TheoryArithNew::computeType: unexpected expression:\n "
                  +e.toString());
      break;
  }
}

Type TheoryArithNew::computeBaseType(const Type& t) {
  IF_DEBUG(int kind = t.getExpr().getKind();)
  DebugAssert(kind==INT || kind==REAL || kind==SUBRANGE,
	      "TheoryArithNew::computeBaseType("+t.toString()+")");
  return realType();
}

Expr TheoryArithNew::computeTCC(const Expr& e) {
  Expr tcc(Theory::computeTCC(e));
  switch(e.getKind()) {
  case DIVIDE:
    DebugAssert(e.arity() == 2, "");
    return tcc.andExpr(!(e[1].eqExpr(rat(0))));
  default:
    return tcc;
  }
}

///////////////////////////////////////////////////////////////////////////////
//parseExprOp:
//translating special Exprs to regular EXPR??
///////////////////////////////////////////////////////////////////////////////
Expr TheoryArithNew::parseExprOp(const Expr& e) {
  TRACE("parser", "TheoryArithNew::parseExprOp(", e, ")");
  //std::cout << "Were here";
  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  switch(e.getKind()) {
  case ID: {
    int kind = getEM()->getKind(e[0].getString());
    switch(kind) {
    case NULL_KIND: return e; // nothing to do
    case REAL:
    case INT:
    case NEGINF: 
    case POSINF: return getEM()->newLeafExpr(kind);
    default:
      DebugAssert(false, "Bad use of bare keyword: "+e.toString());
      return e;
    }
  }
  case RAW_LIST: break; // break out of switch, do the hard work
  default:
    return e;
  }

  DebugAssert(e.getKind() == RAW_LIST && e.arity() > 0,
	      "TheoryArithNew::parseExprOp:\n e = "+e.toString());
  
  const Expr& c1 = e[0][0];
  int kind = getEM()->getKind(c1.getString());
  switch(kind) {
    case UMINUS: {
      if(e.arity() != 2)
	throw ParserException("UMINUS requires exactly one argument: "
			+e.toString());
      return uminusExpr(parseExpr(e[1])); 
    }
    case PLUS: {
      vector<Expr> k;
      Expr::iterator i = e.begin(), iend=e.end();
      // Skip first element of the vector of kids in 'e'.
      // The first element is the operator.
      ++i; 
      // Parse the kids of e and push them into the vector 'k'
      for(; i!=iend; ++i) k.push_back(parseExpr(*i));
      return plusExpr(k); 
    }
    case MINUS: {
      if(e.arity() == 2)
	return uminusExpr(parseExpr(e[1]));
      else if(e.arity() == 3)
	return minusExpr(parseExpr(e[1]), parseExpr(e[2]));
      else
	throw ParserException("MINUS requires one or two arguments:"
			+e.toString());
    }
    case MULT: {
      vector<Expr> k;
      Expr::iterator i = e.begin(), iend=e.end();
      // Skip first element of the vector of kids in 'e'.
      // The first element is the operator.
      ++i; 
      // Parse the kids of e and push them into the vector 'k'
      for(; i!=iend; ++i) k.push_back(parseExpr(*i));
      return multExpr(k);
    }
    case POW: {	
      return powExpr(parseExpr(e[1]), parseExpr(e[2]));	
    }
    case DIVIDE:
      { return divideExpr(parseExpr(e[1]), parseExpr(e[2]));	}
    case LT:	
      { return ltExpr(parseExpr(e[1]), parseExpr(e[2]));	}
    case LE:	
      { return leExpr(parseExpr(e[1]), parseExpr(e[2]));	}
    case GT:	
      { return gtExpr(parseExpr(e[1]), parseExpr(e[2]));	}
    case GE:	
      { return geExpr(parseExpr(e[1]), parseExpr(e[2]));	}
    case INTDIV:
    case MOD:
    case SUBRANGE: {
      vector<Expr> k;
      Expr::iterator i = e.begin(), iend=e.end();
      // Skip first element of the vector of kids in 'e'.
      // The first element is the operator.
      ++i; 
      // Parse the kids of e and push them into the vector 'k'
      for(; i!=iend; ++i) 
        k.push_back(parseExpr(*i));
      return Expr(kind, k, e.getEM());
    }
    case IS_INTEGER: {
      if(e.arity() != 2)
	throw ParserException("IS_INTEGER requires exactly one argument: "
			+e.toString());
      return Expr(IS_INTEGER, parseExpr(e[1]));
    }
    default:
      DebugAssert(false,
	  	  "TheoryArithNew::parseExprOp: invalid input " + e.toString());
      break;
  }
  return e;
}

///////////////////////////////////////////////////////////////////////////////
// Pretty-printing                                                           //
///////////////////////////////////////////////////////////////////////////////


ExprStream& TheoryArithNew::print(ExprStream& os, const Expr& e) {
  switch(os.lang()) {
    case SIMPLIFY_LANG:
      switch(e.getKind()) {
      case RATIONAL_EXPR:
	e.print(os);
	break;
      case SUBRANGE:
	os <<"ERROR:SUBRANGE:not supported in Simplify\n";
	break;
      case IS_INTEGER:
	os <<"ERROR:IS_INTEGER:not supported in Simplify\n";
	break;
      case PLUS:  {
	int i=0, iend=e.arity();
	os << "(+ "; 
	if(i!=iend) os << e[i];
	++i;
	for(; i!=iend; ++i) os << " " << e[i];
	os <<  ")";
	break;
      }
      case MINUS:
	os << "(- " << e[0] << " " << e[1]<< ")";
	break;
      case UMINUS:
	os << "-" << e[0] ;
	break;
      case MULT:  {
	int i=0, iend=e.arity();
	os << "(* " ;
	if(i!=iend) os << e[i];
	++i;
	for(; i!=iend; ++i) os << " " << e[i];
	os <<  ")";
	break;
      }
      case POW:
          os << "(" << push << e[1] << space << "^ " << e[0] << push << ")";
          break;
      case DIVIDE:
	os << "(" << push << e[0] << space << "/ " << e[1] << push << ")";
	break;
      case LT:
	if (isInt(e[0].getType()) || isInt(e[1].getType())) {
	}
	os << "(< " << e[0] << " " << e[1] <<")";
	break;
      case LE:
          os << "(<= " << e[0]  << " " << e[1] << ")";
          break;
      case GT:
	os << "(> " << e[0] << " " << e[1] << ")";
	break;
      case GE:
	os << "(>= " << e[0] << " " << e[1]  << ")";
	break;
      case DARK_SHADOW:
      case GRAY_SHADOW:
	os <<"ERROR:SHADOW:not supported in Simplify\n";
	break;
      default:
	// Print the top node in the default LISP format, continue with
	// pretty-printing for children.
          e.print(os);
	  
          break;
      } 
      break; // end of case SIMPLIFY_LANG


    case TPTP_LANG:
      switch(e.getKind()) {
      case RATIONAL_EXPR:
	e.print(os);
	break;
      case SUBRANGE:
	os <<"ERROR:SUBRANGE:not supported in TPTP\n";
	break;
      case IS_INTEGER:
	os <<"ERROR:IS_INTEGER:not supported in TPTP\n";
	break;
      case PLUS:  {
	if(!isInteger(e[0])){
	  os<<"ERRPR:plus only supports inteters now in TPTP\n";
	  break;
	}
	
	int i=0, iend=e.arity();
	if(iend <=1){
	  os<<"ERROR,plus must have more than two numbers in TPTP\n";
	  break;
	}

	for(i=0; i <= iend-2; ++i){
	  os << "$plus_int("; 
	  os << e[i] << ",";
	}

	os<< e[iend-1];

	for(i=0 ; i <= iend-2; ++i){
	  os << ")"; 
	}

	break;
      }
      case MINUS:
	os << "(- " << e[0] << " " << e[1]<< ")";
	break;
      case UMINUS:
	os << "-" << e[0] ;
	break;
      case MULT:  {
	int i=0, iend=e.arity();
	os << "(* " ;
	if(i!=iend) os << e[i];
	++i;
	for(; i!=iend; ++i) os << " " << e[i];
	os <<  ")";
	break;
      }
      case POW:
          os << "(" << push << e[1] << space << "^ " << e[0] << push << ")";
          break;
      case DIVIDE:
	os << "(" << push << e[0] << space << "/ " << e[1] << push << ")";
	break;
      case LT:
	if (isInt(e[0].getType()) || isInt(e[1].getType())) {
	}
	os << "(< " << e[0] << " " << e[1] <<")";
	break;
      case LE:
          os << "(<= " << e[0]  << " " << e[1] << ")";
          break;
      case GT:
	os << "(> " << e[0] << " " << e[1] << ")";
	break;
      case GE:
	os << "(>= " << e[0] << " " << e[1]  << ")";
	break;
      case DARK_SHADOW:
      case GRAY_SHADOW:
	os <<"ERROR:SHADOW:not supported in TPTP\n";
	break;
      default:
	// Print the top node in the default LISP format, continue with
	// pretty-printing for children.
          e.print(os);
	  
          break;
      } 
      break; // end of case TPTP_LANG

      
    case PRESENTATION_LANG:
      switch(e.getKind()) {
        case REAL:
        case INT:
        case RATIONAL_EXPR:
        case NEGINF:
        case POSINF:
          e.print(os);
          break;
        case SUBRANGE:
          if(e.arity() != 2) e.printAST(os);
          else 
            os << "[" << push << e[0] << ".." << e[1] << push << "]";
          break;
        case IS_INTEGER:
	  if(e.arity() == 1)
	    os << "IS_INTEGER(" << push << e[0] << push << ")";
	  else
	    e.printAST(os);
	  break;
        case PLUS:  {
          int i=0, iend=e.arity();
          os << "(" << push;
          if(i!=iend) os << e[i];
          ++i;
          for(; i!=iend; ++i) os << space << "+ " << e[i];
          os << push << ")";
          break;
        }
        case MINUS:
          os << "(" << push << e[0] << space << "- " << e[1] << push << ")";
          break;
        case UMINUS:
          os << "-(" << push << e[0] << push << ")";
          break;
        case MULT:  {
          int i=0, iend=e.arity();
          os << "(" << push;
          if(i!=iend) os << e[i];
          ++i;
          for(; i!=iend; ++i) os << space << "* " << e[i];
          os << push << ")";
          break;
        }
        case POW:
          os << "(" << push << e[1] << space << "^ " << e[0] << push << ")";
          break;
        case DIVIDE:
          os << "(" << push << e[0] << space << "/ " << e[1] << push << ")";
          break;
        case LT:
          if (isInt(e[0].getType()) || isInt(e[1].getType())) {
          }
          os << "(" << push << e[0] << space << "< " << e[1] << push << ")";
          break;
        case LE:
          os << "(" << push << e[0] << space << "<= " << e[1] << push << ")";
          break;
        case GT:
          os << "(" << push << e[0] << space << "> " << e[1] << push << ")";
          break;
        case GE:
          os << "(" << push << e[0] << space << ">= " << e[1] << push << ")";
          break;
        case DARK_SHADOW:
	  os << "DARK_SHADOW(" << push << e[0] << ", " << space << e[1] << push << ")";
	  break;
        case GRAY_SHADOW:
	  os << "GRAY_SHADOW(" << push << e[0] << ","  << space << e[1]
	     << "," << space << e[2] << "," << space << e[3] << push << ")";
	  break;
        default:
          // Print the top node in the default LISP format, continue with
          // pretty-printing for children.
          e.printAST(os);

          break;
      } 
      break; // end of case PRESENTATION_LANG
    case SMTLIB_LANG:
    case SMTLIB_V2_LANG: {
      switch(e.getKind()) {
        case REAL_CONST:
          printRational(os, e[0].getRational(), true);
          break;
        case RATIONAL_EXPR:
          printRational(os, e.getRational());
          break;
        case REAL:
          os << "Real";
          break;
        case INT:
          os << "Int";
          break;
        case SUBRANGE:
          throw SmtlibException("TheoryArithNew::print: SMTLIB: SUBRANGE not implemented");
//           if(e.arity() != 2) e.print(os);
//           else 
//             os << "(" << push << "SUBRANGE" << space << e[0]
// 	       << space << e[1] << push << ")";
          break;
        case IS_INTEGER:
 	  if(e.arity() == 1)
 	    os << "(" << push << "IsInt" << space << e[0] << push << ")";
 	  else
            throw SmtlibException("TheoryArithNew::print: SMTLIB: IS_INTEGER used unexpectedly");
	  break;
        case PLUS:  {
          if(e.arity() == 1 && os.lang() == SMTLIB_V2_LANG) {
            os << e[0];
          } else {
            os << "(" << push << "+";
            Expr::iterator i = e.begin(), iend = e.end();
            for(; i!=iend; ++i) {
              os << space << (*i);
            }
            os << push << ")";
          }
          break;
        }
        case MINUS: {
          os << "(" << push << "- " << e[0] << space << e[1] << push << ")";
          break;
        }
        case UMINUS: {
          os << "(" << push << "-" << space << e[0] << push << ")";
          break;
        }
        case MULT:  {
          int i=0, iend=e.arity();
          if(iend == 1 && os.lang() == SMTLIB_V2_LANG) {
            os << e[0];
          } else {
            for(; i!=iend; ++i) {
              if (i < iend-1) {
                os << "(" << push << "*";
              }
              os << space << e[i];
            }
            for (i=0; i < iend-1; ++i) os << push << ")";
          }
          break;
        }
        case POW:
          throw SmtlibException("TheoryArithNew::print: SMTLIB: POW not supported");
          //          os << "(" << push << "^ " << e[1] << space << e[0] << push << ")";
          break;
        case DIVIDE: {
          throw SmtlibException("TheoryArithNew::print: SMTLIB: unexpected use of DIVIDE");
          break;
        }
        case LT: {
          Rational r;
          os << "(" << push << "<" << space;
          os << e[0] << space << e[1] << push << ")";
          break;
        }
        case LE: {
          Rational r;
          os << "(" << push << "<=" << space;
          os << e[0] << space << e[1] << push << ")";
          break;
        }
        case GT: {
          Rational r;
          os << "(" << push << ">" << space;
          os << e[0] << space << e[1] << push << ")";
          break;
        }
        case GE: {
          Rational r;
          os << "(" << push << ">=" << space;
          os << e[0] << space << e[1] << push << ")";
          break;
        }
        case DARK_SHADOW:
          throw SmtlibException("TheoryArithNew::print: SMTLIB: DARK_SHADOW not supported");
	  os << "(" << push << "DARK_SHADOW" << space << e[0]
	     << space << e[1] << push << ")";
	  break;
        case GRAY_SHADOW:
          throw SmtlibException("TheoryArithNew::print: SMTLIB: GRAY_SHADOW not supported");
	  os << "GRAY_SHADOW(" << push << e[0] << ","  << space << e[1]
	     << "," << space << e[2] << "," << space << e[3] << push << ")";
	  break;
        default:
          throw SmtlibException("TheoryArithNew::print: SMTLIB: default not supported");
          // Print the top node in the default LISP format, continue with
          // pretty-printing for children.
          e.printAST(os);

          break;
      } 
      break; // end of case SMTLIB_LANG
    }
    case LISP_LANG:
      switch(e.getKind()) {
        case REAL:
        case INT:
        case RATIONAL_EXPR:
        case NEGINF:
        case POSINF:
          e.print(os);
          break;
        case SUBRANGE:
          if(e.arity() != 2) e.printAST(os);
          else 
            os << "(" << push << "SUBRANGE" << space << e[0]
	       << space << e[1] << push << ")";
          break;
        case IS_INTEGER:
	  if(e.arity() == 1)
	    os << "(" << push << "IS_INTEGER" << space << e[0] << push << ")";
	  else
	    e.printAST(os);
	  break;
        case PLUS:  {
          int i=0, iend=e.arity();
          os << "(" << push << "+";
          for(; i!=iend; ++i) os << space << e[i];
          os << push << ")";
          break;
        }
        case MINUS:
        //os << "(" << push << e[0] << space << "- " << e[1] << push << ")";
	  os << "(" << push << "- " << e[0] << space << e[1] << push << ")";
          break;
        case UMINUS:
          os << "(" << push << "-" << space << e[0] << push << ")";
          break;
        case MULT:  {
          int i=0, iend=e.arity();
          os << "(" << push << "*";
          for(; i!=iend; ++i) os << space << e[i];
          os << push << ")";
          break;
        }
        case POW:
          os << "(" << push << "^ " << e[1] << space << e[0] << push << ")";
          break;
        case DIVIDE:
          os << "(" << push << "/ " << e[0] << space << e[1] << push << ")";
          break;
        case LT:
          os << "(" << push << "< " << e[0] << space << e[1] << push << ")";
          break;
        case LE:
          os << "(" << push << "<= " << e[0] << space << e[1] << push << ")";
          break;
        case GT:
          os << "(" << push << "> " << e[1]  << space << e[0] << push << ")";
          break;
        case GE:
          os << "(" << push << ">= " << e[0] << space << e[1] << push << ")";
          break;
        case DARK_SHADOW:
	  os << "(" << push << "DARK_SHADOW" << space << e[0]
	     << space << e[1] << push << ")";
	  break;
        case GRAY_SHADOW:
	  os << "(" << push << "GRAY_SHADOW" << space << e[0] << space
	     << e[1] << space << e[2] << space << e[3] << push << ")";
	  break;
        default:
          // Print the top node in the default LISP format, continue with
          // pretty-printing for children.
          e.printAST(os);

          break;
      } 
      break; // end of case LISP_LANG
    default:
     // Print the top node in the default LISP format, continue with
     // pretty-printing for children.
       e.printAST(os);
  }
  return os;
}

///////////////////////////////////////////////////////////////////////////////
// SIMPLEX SOLVER                                                            //
///////////////////////////////////////////////////////////////////////////////

bool TheoryArithNew::isBasic(const Expr& x) const {
	// If it is on the right side of the tableaux the it is basic, non-basic otherwise
	return (tableaux.find(x) != tableaux.end());
}

void TheoryArithNew::pivot(const Expr& x_r, const Expr& x_s) {
	
	// Check that the variable is non-basic
	DebugAssert(isBasic(x_r), "TheoryArithNew::pivot, given variable should be basic" + x_r.toString());
	DebugAssert(!isBasic(x_s), "TheoryArithNew::pivot, given variable should be non-basic" + x_s.toString());

	// If trace is on for the simplex, print it out
	TRACE("simplex", "TheoryArithNew::pivot(", x_r.toString() + ", " + x_s.toString(), ")");

	// Get the iterator that points to the expression of x_r
	TebleauxMap::iterator it = tableaux.find(x_r); 
	
	// Get the expresiion of x_r
	Theorem x_r_Theorem = (*it).second;  
	
	// Erase the x_r expression from the tableaux
	tableaux.erase(x_r); // TODO: Add erase by iterator to ExprHashMap
	
	// Update the dependencies
	updateDependenciesRemove(x_r, x_r_Theorem.getExpr()[1]);
	
	// Construct the expresison (theorem) of x_s
	const Theorem& x_s_Theorem = pivotRule(x_r_Theorem, x_s);	
		
	// Replace all occurances of x_s with x_s_Expression
	substAndCanonizeTableaux(x_s_Theorem);
	
	// Update the dependencies
	updateDependenciesAdd(x_s, x_s_Theorem.getExpr()[1]);
	
	// Add the expression of x_s to the map
	tableaux[x_s] = x_s_Theorem;
}

void TheoryArithNew::update(const Expr& x_i, const EpsRational& v) {
	
	// Check that the variable is non-basic
	DebugAssert(tableaux.find(x_i) == tableaux.end(), "TheoryArithNew::update, given variable should be non-basic" + x_i.toString());

	// If trace is on for the simplex, print it out
	TRACE("simplex", "TheoryArithNew::update(", x_i.toString() + ", " + v.toString(), ")");

	// Remember the value of the x_i variable
	EpsRational old_value = getBeta(x_i);

	// If there are dependent variables then do the work 
	DependenciesMap::iterator find = dependenciesMap.find(x_i);
	if (find != dependenciesMap.end()) {
	
		// Go through all the variables that depend on x_i
		const set<Expr>& dependent = (*find).second;
		set<Expr>::const_iterator it     = dependent.begin();
		set<Expr>::const_iterator it_end = dependent.end(); 		
		// Fix the values of all the variables
		while (it != it_end) {
			
			// Get the current variable
			const Expr& x_j = *it;
			
			// Get the tableaux coefficient of the of x_i in the row of x_j (the right side ofg the tableaux expression)
			const Rational& a_ji = getTableauxEntry(x_j, x_i);
			
			// Update the beta valuation
			EpsRational b(getBeta(x_j)); // TODO: not necessary, beta's are all setup now
			EpsRational x_j_new = beta[x_j] = b + (v - old_value) * a_ji;
			
			// Check if the variable is sat or unsat under the new assignment 
			if (x_j_new < getLowerBound(x_j) || getUpperBound(x_j) < x_j_new)
				unsatBasicVariables.insert(x_j);
			else
				unsatBasicVariables.erase(x_j);
			
			// Go to the next one
			it ++;
		}
	}
	
	// Set the new value to x_i (x_i) is non_basic, no need to add to unsat set)
	beta[x_i] = v;
}
  		
void TheoryArithNew::pivotAndUpdate(const Expr& x_i, const Expr& x_j, const EpsRational& v) {
	
	// Variable x_i should be a basic variable (left side of the tableaux) and x_j should be non_basic
	DebugAssert(tableaux.find(x_i) != tableaux.end(), "TheoryArithNew::pivotAndUpdate, " + x_i.toString() + " should be a basic variable");
	DebugAssert(tableaux.find(x_j) == tableaux.end(), "TheoryArithNew::pivotAndUpdate, " + x_j.toString() + " should be a non-basic variable");

	// If trace is on for the simplex, print it out
	TRACE("simplex", "TheoryArithNew::pivotAndUpdate(", x_i.toString() + ", " + x_j.toString() + ", " + v.toString(), ")");

	// The a_ij coefficient of the tableaux
	const Rational& a_ij = getTableauxEntry(x_i, x_j);
	
	// Let theta be the adjustment coefficient
	EpsRational theta((v - getBeta(x_i))/a_ij);
	
	// Set the new value to x_i (x_i becomes non-basic, hance sat)
	beta[x_i] = v;
	// x_i becomes non-basic, no need ==> it is sat
	unsatBasicVariables.erase(x_i);
	
	// Set the new value to x_j 
	EpsRational b = getBeta(x_j);
	EpsRational new_x_j = beta[x_j] = b + theta;
	
	// Check if the variable is sat or unsat under the new assignment 
	if (new_x_j < getLowerBound(x_j) || getUpperBound(x_j) < new_x_j)
		unsatBasicVariables.insert(x_j);
	else
		unsatBasicVariables.erase(x_j);
	
	// Go through all the variables that depend on x_j, and update their value (there will be at least one, i.e. x_i) // TODO: maybe optimise
	const set<Expr>& dependent = (*dependenciesMap.find(x_j)).second;
	set<Expr>::const_iterator it     = dependent.begin();
	set<Expr>::const_iterator it_end = dependent.end(); 		
	// Go throught all the basic variables
	while (it != it_end) {
		
		// Get the current variable
		const Expr& x_k = *it; 
		
		// If the basic variable is different from x_i update its value
		if (x_k != x_i) {
		
			// Get the a_kj coefficient from the tableaux
			const Rational& a_kj = getTableauxEntry(x_k, x_j);
			
			// Adjust the value (check fort sat/unsat, x_k is basic)
			b = getBeta(x_k);
			EpsRational x_k_new = beta[x_k] = b + theta * a_kj; 
			
			// Check if the variable is sat or unsat under the new assignment 
			if (x_k_new < getLowerBound(x_k) || getUpperBound(x_k) < x_k_new)
				unsatBasicVariables.insert(x_k);
			else
				unsatBasicVariables.erase(x_k);
		}
	
		// Go to the next one
		it ++;
	}
	
	// Last thing to do, pivot x_i and x_j
	pivot(x_i, x_j);
}
  		
QueryResult TheoryArithNew::assertUpper(const Expr& x_i, const EpsRational& c, const Theorem& thm) {
	
	// If trace is on for the simplex, print it out
	TRACE("simplex", "TheoryArithNew::assertUpper(", x_i.toString() + ", " + c.toString(), ")");

	// Check if the given expression is actually a variable
	DebugAssert(isLeaf(x_i), "TheoryArithNew::assertUpper wrong kind, expected an arithmetic leaf (variable) got " + x_i.toString());
	
	// Check if the upper bound is worse then the last one
	if (getUpperBound(x_i) <= c) return (consistent == UNKNOWN? UNKNOWN : SATISFIABLE); 
	
	// If the new bound is lower then the lower bound */
	if (c < getLowerBound(x_i)) {
		// Create the explaining theorem
		explanation = d_rules->clashingBounds(getLowerBoundThm(x_i), thm);
		// Return unsatisfiable
		return UNSATISFIABLE;
	}
	
	// Since it is a tighter bound, propagate what can be 
	propagate = true;

	// Set the new upper bound */
	upperBound[x_i] = BoundInfo(c, thm);

	// If within the new bounds, return the previous state 
	if (getBeta(x_i) <= c) return (consistent == UNKNOWN? UNKNOWN : SATISFIABLE);
	
	// Otherwise, if the variable is non-basic then update it's value
	if (!isBasic(x_i)) update(x_i, c);
	// Else its basic, and non-sat, add to the unsat set
	else unsatBasicVariables.insert(x_i);
	
	// Everything went fine, return OK (not complete, means not UNSAT)
	return UNKNOWN;
}

QueryResult TheoryArithNew::assertLower(const Expr& x_i, const EpsRational& c, const Theorem& thm) {

	// Check if the given expression is actually a variable
	DebugAssert(isLeaf(x_i), "TheoryArithNew::assertLower wrong kind, expected an arithmetic leaf (variable) got " + x_i.toString());

	// If trace is on for the simplex, print it out
	TRACE("simplex", "TheoryArithNew::assertLower(", x_i.toString() + ", " + c.toString(), ")");
	
	// Check if the upper bound is worse then the last one
	if (c <= getLowerBound(x_i)) return (consistent == UNKNOWN? UNKNOWN : SATISFIABLE); 
	
	// Since it is a tighter bound, propagate what can be 
	propagate = true;
	
	// If the new bound is lower then the  bound */
	if (c > getUpperBound(x_i)) { 
		// Create the explaining theorem
		explanation = d_rules->clashingBounds(thm, getUpperBoundThm(x_i));
		// Return unsatisfiable
		return UNSATISFIABLE;
	}
	
	// Set the new upper bound */
	lowerBound[x_i] = BoundInfo(c, thm);
	
	// If within the new bounds, return the previous state 
	if (c <= getBeta(x_i)) return (consistent == UNKNOWN? UNKNOWN : SATISFIABLE);
	
	// Otherwise, if the variable is non-basic then update it's value
	if (!isBasic(x_i)) update(x_i, c);
	// Else its basic, and non-sat, add to the unsat set
	else unsatBasicVariables.insert(x_i);
	
	// Everything went fine, return OK (not complete, means not UNSAT)
	return UNKNOWN;
}
  		
QueryResult TheoryArithNew::assertEqual(const Expr& x_i, const EpsRational& c, const Theorem& thm) {
	
	// Assert the upper bound
	consistent = assertUpper(x_i, c, thm); // TODO: thm: = |- <=
	
	// If the return value is UNSAT return UNSAT
	if (consistent == UNSATISFIABLE) return UNSATISFIABLE;
	
	// Assert the lower bound
	consistent = assertLower(x_i, c, thm); // TODO: thm: = |- >=
	
	// Return the consistency
	return consistent;
}


void TheoryArithNew::checkSat(bool fullEffort)
{	
	// We should not be here if inconsistent
	DebugAssert(consistent != UNSATISFIABLE, "TheoryArithNew::checkSat : we are UNSAT before entering?!?!");

	// Trace the check sat if simplex flag is on
  	TRACE("simplex", "TheoryArithNew::checkSat(fullEffort=",fullEffort? "true" : "false", ")");
  
  	// Check if by backtracking we have more fresh variables than we expect
	if (assertedExprCount < assertedExpr.size()) 
		updateFreshVariables();
  
  	// Do the simplex search if the database is not satisfiable (if inconsistent, we will not be here);
  	if (consistent != SATISFIABLE || fullEffort)
  		consistent = checkSatSimplex();
  		  		
  	// If the result is inconsistent set the inconsistent flag
  	if (consistent == UNSATISFIABLE)
  		setInconsistent(explanation);
  	
  	// If we are not - consistent, check the integer satisfiability
//   	if (consistent == SATISFIABLE) {
// 		// If we asserted a lemma and it hasn't been processed yet, we just don't do anything
// 		Theorem integer_lemma_thm = integer_lemma;
// 		if (!integer_lemma_thm.isNull()) {
// 			if (simplify(integer_lemma_thm.getExpr()).getRHS() == getEM()->trueExpr())
// 				consistent = checkSatInteger();
// 			else 
// 				consistent = UNKNOWN;
// 		} else
// 			// Lemma was not asserted, check integer sat
// 			consistent = checkSatInteger();		
//   	}
  	
  	// Trace the check sat if simplex flag is on
  	TRACE("simplex", "TheoryArithNew::checkSat ==> ", consistent == UNSATISFIABLE? "UNSATISFIABLE" : "SATISFIABLE", "");
}

QueryResult TheoryArithNew::checkSatInteger() {
	
	// Trace the check sat if simplex flag is on
  	TRACE("simplex", "TheoryArithNew::checkSatInteger()", "", "");
  	
  	// At this point we are REAL satisfiable, so we have to check the integers
	set<Expr>::iterator x_i_it     = intVariables.begin();
	set<Expr>::iterator x_i_it_end = intVariables.end();
//	cerr << "Integer vars: ";
//	while (x_i_it != x_i_it_end) {
//		cerr << *x_i_it << " ";
//		++ x_i_it;
//	}
//	cerr << endl;
//	
//	x_i_it     = intVariables.begin();
//	x_i_it_end = intVariables.end();
	while (x_i_it != x_i_it_end) {
		
		// Get the left-hand variable of the tableaux
		const Expr& x_i = (*x_i_it);
		
		// Only do work for unsat integer variables
		if (isInteger(x_i)) {
			
			// Get the current assignment of x_i
			const EpsRational& beta = getBeta(x_i);
			
			// Check if it is an integer
			if (beta.isInteger()) { ++ x_i_it; continue; }
			
			// Since the variable is not an integer, split on it being <= [beta] and >= [beta] + 1
			integer_lemma = d_rules->integerSplit(x_i, beta.getFloor()); 
			TRACE("integer", "TheoryArithNew::checkSatInteger ==> lemma : ", integer_lemma, "");
			enqueueFact(integer_lemma);
			
			// One split should be enough, return unknown
			return UNKNOWN;			 
		}
		
		// Go to the next row
		++ x_i_it;
	} 
	
	// We came through, huh, we are sat
	return SATISFIABLE;	
}

QueryResult TheoryArithNew::checkSatSimplex() {
	
	Expr x_i;                         // The basic variable we will use
	EpsRational x_i_Value;            // The current value of the variable x_i
	Expr x_j;                         // The non-basic variable we will use
	EpsRational x_j_Value;            // The current value of the variable x_j
	Rational a_ij;                    // The coefficient wwhen expanding x_i using x_j in the tableaux
	
	bool x_j_Found;                   // Did we find a suitable one
	EpsRational l_i;                  // Lower bound of x_i
	EpsRational u_i;                  // Upper bound of x_i

	// Trace the size of the tableaux and the unsat 
  	TRACE("arith_atoms", "Tableaux size: ", tableaux.size(), "");
	TRACE("arith_atoms", "UNSAT vars: ", unsatBasicVariables.size(), "");
	
	// The main loop
	while (unsatBasicVariables.size()) {
	 
	 	// The first unsat variable information
		x_i        = *unsatBasicVariables.begin();
		TebleauxMap::iterator it = tableaux.find(x_i); 
		x_i_Value  = getBeta(x_i);
		l_i        = getLowerBound(x_i);
		u_i        = getUpperBound(x_i);
		
		// If the variable doesn't obey the lower bound 
		if (l_i > x_i_Value) {
			
			// Did we find a suitable x_j, NOT YET
			x_j_Found = false; 
					
			// Find the smalles non-basic x_j that can improve x_i
			const Expr& x_i_RightSide = (*it).second.getExpr()[1];
			int non_basics_i_end     = x_i_RightSide.arity();
			for(int non_basics_i = 0; non_basics_i < non_basics_i_end; ++ non_basics_i) {
				
				// Get the info on the current variable
				x_j        = x_i_RightSide[non_basics_i][1]; 
				a_ij       = x_i_RightSide[non_basics_i][0].getRational(); 
				x_j_Value  = getBeta(x_j);           
				
				// If there is slack for improving x_i using x_j then do it       				
				if (a_ij > 0) {
					if (x_j_Value < getUpperBound(x_j)) {
						x_j_Found = true;
						break;
					}
				} else {
					if (x_j_Value > getLowerBound(x_j)) {
						x_j_Found = true;
						break;
					}
				} 		
			}
			
			// If none of the variables allows for slack, the tableaux is unsatisfiable
			if (!x_j_Found) {
				// Generate the explanation
				explanation = getLowerBoundExplanation(it);
				// Return unsat
				return UNSATISFIABLE;
			}
			
			// Otherwise do pivotAndUpdate and continue with the loop
			pivotAndUpdate(x_i, x_j, l_i); 			 
		} else
		// If the variable doesn't obey the upper bound 
		if (x_i_Value > u_i) {
			
			// Did we find a suitable x_j, NOT YET
			x_j_Found = false; 
					
			// Find the smalles non-basic x_j that can improve x_i
			const Expr& x_i_RightSide = (*it).second.getExpr()[1];
			int non_basics_i_end     = x_i_RightSide.arity();
			for(int non_basics_i = 0; non_basics_i < non_basics_i_end; ++ non_basics_i) {
				
				// Get the info on the current variable
				x_j        = x_i_RightSide[non_basics_i][1]; 
				a_ij       = x_i_RightSide[non_basics_i][0].getRational(); 
				x_j_Value  = getBeta(x_j);           
				
				// If there is slack for improving x_i using x_j then do it
				if (a_ij < 0) {
					if (x_j_Value < getUpperBound(x_j)) {
						x_j_Found = true;
						break;
					}
				} else 
					if (x_j_Value > getLowerBound(x_j)) {
						x_j_Found = true;
						break;
					} 		
			}
			
			// If none of the variables allows for slack, the tableaux is unsatisfiable
			if (!x_j_Found) {
				// Generate the explanation
				explanation = getUpperBoundExplanation(it);
				// Return unsat
				return UNSATISFIABLE;	
			}
			
			// Otherwise do pivotAndUpdate and continue with the loop
			pivotAndUpdate(x_i, x_j, u_i); 			 
		} else
			// Due to backtracking a unsat might become sat, just erase it
			unsatBasicVariables.erase(x_i);
			
		
		// If trace is on, printout the current valuation and the tableaux
		TRACE("simplex", "TheoryArithNew::checkSatSimplex ==> new tableaux : \n", tableauxAsString(), "");
		TRACE("simplex", "TheoryArithNew::checkSatSimplex ==> new bounds   : \n", boundsAsString(), "");
		TRACE("simplex", "TheoryArithNew::checkSatSimplex ==> unsat   : \n", unsatAsString(), "");
		
	};

	// Since there is no more unsat constraints we are satisfiable
	return SATISFIABLE;
}  		

Rational TheoryArithNew::getTableauxEntry(const Expr& x_i, const Expr& x_j) {
	return findCoefficient(x_j, tableaux[x_i].getExpr()[1]);
}


const Rational& TheoryArithNew::findCoefficient(const Expr& var, const Expr& expr) {

	// The zero coefficient 
	static Rational zeroCoefficient(0);

    // The given expression must be a sum
    DebugAssert(isPlus(expr), "TheoryArithNew::findCoefficient : expression must be a sum : " + expr.toString());
	
	// Go through the sum and find the coefficient
	int left = 0;
	int right = expr.arity() - 1;
	int i;
	while (left <= right) {
		
		// Take the middle one
		i = (left + right ) / 2;
		
		// Current expression
		const Expr& mult = expr[i];
		
		// Every summand must be a multiplication with a rational
		DebugAssert(isMult(mult) && isRational(mult[0]), "TheoryArithNew::findCoefficient : expression must be a sum of multiplications: " + expr.toString()); 
		
		// If the variable is the same return the coefficient
		int cmp = compare(mult[1], var);
		if (cmp == 0) 
			return mult[0].getRational();
		else 
			if (cmp > 0) 
				left = i + 1;
			else 
				right = i - 1;		
	}
		
	// Not found, return 0
	return zeroCoefficient;	
}


TheoryArithNew::EpsRational TheoryArithNew::getLowerBound(const Expr& x) const {
	// Try and find the lower bound in the map
	CDMap<Expr, BoundInfo>::iterator find = lowerBound.find(x);
	// If not found return +infinity as the default value, othervise return the value
	if (find == lowerBound.end()) return EpsRational::MinusInfinity;
	else return (*find).second.bound;
}

TheoryArithNew::EpsRational TheoryArithNew::getUpperBound(const Expr& x) const {
	// Try and find the upper bound in the map
	CDMap<Expr, BoundInfo>::iterator find = upperBound.find(x);
	// If not found return -infinity as the default value, othervise return the value
	if (find == upperBound.end()) return EpsRational::PlusInfinity;
	else return (*find).second.bound;
}

Theorem TheoryArithNew::getLowerBoundThm(const Expr& x) const {
	// Try and find the upper bound in the map
	CDMap<Expr, BoundInfo>::iterator find = lowerBound.find(x);
	// It has to be found
	DebugAssert(find != lowerBound.end(), "TheoryArithNew::getLowerBoundThm, theorem not found for " + x.toString());	
	// Return the bound theorem 
	return (*find).second.theorem;
}

Theorem TheoryArithNew::getUpperBoundThm(const Expr& x) const {
	// Try and find the upper bound in the map
	CDMap<Expr, BoundInfo>::iterator find = upperBound.find(x);
	// It has to be found
	DebugAssert(find != upperBound.end(), "TheoryArithNew::getUpperBoundThm, theorem not found for " + x.toString());	
	// Return the bound theorem 
	return (*find).second.theorem;
}

  		
TheoryArithNew::EpsRational TheoryArithNew::getBeta(const Expr& x) {
	
	// Try to find the beta value in the map
	CDMap<Expr, EpsRational>::iterator find = beta.find(x);
	
	if (find == beta.end()) {
		// If not found return 0 (no need for sat/unsat, it's allways sat) 
		return beta[x] = EpsRational::Zero;
	
		// Check if the variable is sat or unsat under the new assignment 
		if (EpsRational::Zero < getLowerBound(x) || getUpperBound(x) < EpsRational::Zero)
			unsatBasicVariables.insert(x);
		else
			unsatBasicVariables.erase(x);
	}
	else 
		// If found, just return it
		return (*find).second;
}


void TheoryArithNew::assertFact(const Theorem& assertThm)
{
	// Get the expression to be asserted
	const Expr& expr = assertThm.getExpr();

	// If tracing arithmetic, print out the expression to be asserted
	TRACE("simplex", "TheoryArithNew::assertFact(", expr, ")");
	TRACE("simplex", "asserted: ", assertedExpr.size(), "");
	TRACE("simplex", "counted: ", assertedExprCount, "");
	TRACE("arith_atoms", "Assert: ", expr.toString(), "");
						
	// Check if by backtracking we have more fresh variables than we expect
	if (assertedExprCount < assertedExpr.size()) 
		updateFreshVariables();
	
	// Get the constraint partsreturn 
	const Expr& leftSide   = expr[0];          // The left side of the constraint  
	const Expr& rightSide  = expr[1];          // The right side of the constraint
	int kind        = expr.getKind();   // The relational symbol, should be one of LT, LE, GT, GE. EQ was rewritten as LE and GE so its not here
	
	// The expression must be an inequality (sum a_1*x_1 .. a_n*x_n) @ b
	DebugAssert(isIneq(expr)         , "TheoryArithNew::assertFact wrong kind, expected inequality"                 + expr.toString());
	DebugAssert(isPlus(rightSide) || (isMult(rightSide) && isRational(rightSide[0]) && isLeaf(rightSide[1])), "TheoryArithNew::assertFact wrong kind, expected sum on the right side opr a simple 1*x"      + expr.toString());
	DebugAssert(isRational(leftSide), "TheoryArithNew::assertFact wrong kind, expected rational on the right side" + expr.toString());

	// Get the rational value on the right side	
	Rational leftSideValue = leftSide.getRational(); 
	
	// The rational bound on the constraint
	Rational c = leftSideValue;
	
	// The variable to be constrained
	Expr var;       
	
	// Theorem of the assertion
	Theorem assert = assertThm;                                 
	
	// For now we have that leftSide @ (c1x1 + c2x2 + ... cnxn) = rightSide
	// If rightSide is not a sum constraint is atomic (leftSide @ a*x)
	if (!isPlus(rightSide)) {
		
		// Tee left side in this case should be 1*x
		DebugAssert(rightSide[0].isRational() && rightSide[0].getRational() == 1, "TheoryArithNew::assertFact, left side should be multiplication by one");
		
		// Change the assert theorem to remove the 1*x to x
		assert = iffMP(assert, substitutivityRule(expr, reflexivityRule(leftSide), d_rules->oneElimination(rightSide)));
		
		// The variable will just be x1 (if var is not already present in the tableaux, it will be non-basic)
		var = rightSide[1]; // IMPORTANT!!!, when giving explanations, it should be of the same form
		
		// If an integer, add it to the integer set
		if (isInteger(var)) intVariables.insert(var);
					
	} else {
		// Get the theorem that corresponds to the introduction of the new variable var = leftSide 
		const Theorem& introductionThm = getVariableIntroThm(rightSide);
		
		// Take the new variable out
		var = introductionThm.getExpr()[0];

		// Change the theorem for the assertion so that it involves the new variable, i.e.  c < rightSide, var = rightSide |- c < var
		assert = iffMP(assertThm, substitutivityRule(expr, 1, symmetryRule(introductionThm)));
		
		// Insert all the integer variables into the integer set
		if (isInteger(var)) {
			intVariables.insert(var);
			int i_end = rightSide.arity();
			for(int i = 0; i < i_end; ++ i)
				intVariables.insert(rightSide[i][1]);
		} else {
			int i_end = rightSide.arity();
			for(int i = 0; i < i_end; ++ i)
				if (isInteger(rightSide[i][1])) intVariables.insert(rightSide[i][1]);
		}
	}
	
	// Make the BoundInfo object for theory propagation
	EpsRational bound;
	
	// By default we don't propagate
	propagate = false;
	
	// Remember the old bound
	EpsRational oldBound;
	
	// Finnaly assert the right constraint
	switch (kind) {
		case LT: 
			oldBound    = getLowerBound(var);
			// c < var, convert to c + epsilon <= var and assert it
			consistent = assertLower(var, bound = EpsRational(c, +1), assert);
			break;					
		case LE:
			oldBound    = getLowerBound(var);
			// c <= var, assert the lower bound
			consistent = assertLower(var, bound = c, assert);
			break;
		case GT: 
			oldBound    = getUpperBound(var);
			// c > var, convert to c - epsilon >= var and assert it
			consistent = assertUpper(var, bound = EpsRational(c, -1), assert);
			break;
		case GE:
			oldBound    = getUpperBound(var);
			// c >= var, assert the upper bound
			consistent = assertUpper(var, bound = c, assert);
			break;
		case EQ:
			// c == var, assert the equality
			consistent = assertEqual(var, bound = c, assert);
			// For now, don't propagate anything
			propagate = false; // TODO: some propagation is in place here (negations)			
			break;
		default:
			//How did we get here
      		FatalAssert(false, "Theory_Arith::assertFact, control should not reach here");
      		break;
	} 
	
	// If tracing arithmetic, print out the new tableaux and the current bounds
	TRACE("simplex", "TheoryArithNew::assertFact ==> ", consistent == UNSATISFIABLE? "UNSATISFIABLE" : consistent == UNKNOWN? "UNKNOWN" : "SATISFIABLE", "");
	TRACE("simplex", "TheoryArithNew::assertFact ==> new tableaux : \n", tableauxAsString(), "");
	TRACE("simplex", "TheoryArithNew::assertFact ==> new bounds   : \n", boundsAsString(), "");
	TRACE("simplex", "TheoryArithNew::assertFact ==> unsat   : \n", unsatAsString(), "");
	
	// If the result is inconsistent set the inconsistent flag
  	if (consistent == UNSATISFIABLE)
  		setInconsistent(explanation);
  		
  	// Not inconsistent, propagate all from this assertion
  	if (propagate) 
  		propagateTheory(assertThm.getExpr(), bound, oldBound);  	
}


Theorem TheoryArithNew::getVariableIntroThm(const Expr& rightSide) {
	
	// Try to find the expression in the map
	TebleauxMap::iterator find = freshVariables.find(rightSide);
	
	// If not in tableaux, add it and assign it a new variable
	if (find == freshVariables.end()) {
	
		// Get the common rules
		CommonProofRules* c_rules = getCommonRules();
	
		// Create a new variable (\exists x . rightSide = x)
		Theorem thm = c_rules->varIntroRule(rightSide);
  		
  		// Skolemise it, to get an equality (\exists x . rightSide = x) <==> rightSide = c, then infer |- rightSide = c
  		thm = c_rules->iffMP(thm, c_rules->skolemizeRewrite(thm.getExpr())); 		
  		
  		// Reverse the equality into standard form
  		thm = symmetryRule(thm);
  		
  		// Add the theorem to the variable introduction map (this is the theorem we return)
  		Theorem returnThm = freshVariables[rightSide] = thm;
  		
  		// Now, flatten the equality modulo tableaux
  		thm = substAndCanonizeModTableaux(thm);
  		
  		// Get the skolem constant that was introduced (|- c = leftSide)
  		const Expr& var = thm.getExpr()[0];
  		  		
  		// Also add it to the tableaux
  		tableaux[var] = thm;

		// Update the dependencies
		updateDependenciesAdd(var, thm.getExpr()[1]);

		// Add it to the expressions map
		assertedExpr.push_back(Expr(EQ, var, rightSide));
		assertedExprCount = assertedExprCount + 1;
  		
  		// Compute the value of the new variable using the tableaux
		updateValue(var, rightSide);
  		  		
  		// Return the variable
  		return returnThm;
	}
	
	// Otherwise we have it, so return it
	return (*find).second;
}

void TheoryArithNew::updateValue(const Expr& var, const Expr& e) {
	
  	// The initial value
  	EpsRational varValue(0);
  	
  	// Go through the sum and compute the value
  	int i_end = e.arity();
  	for (int i = 0; i < i_end; ++ i)
  		varValue += getBeta(e[i][1]) * e[i][0].getRational();
  	
  	// Update the beta  
  	beta[var] = varValue;
  	
  	// Check if the variable is sat or unsat under the new assignment 
	if (varValue < getLowerBound(var) || getUpperBound(var) < varValue)
		unsatBasicVariables.insert(var);
	else
		unsatBasicVariables.erase(var);
}

string TheoryArithNew::tableauxAsString() const {

	// The string we are building 
	string str; 

	// Start from the begining
	TebleauxMap::const_iterator row     = tableaux.begin();
	TebleauxMap::const_iterator row_end = tableaux.end(); 
	
	// Print all the rows
	while (row != tableaux.end()) {
		// Print the equality
		str = str + ((*row).second).getExpr().toString() + "\n";
		
		// Continue to the next row
		row ++;
	}
	
	// Return the string representation 
	return str;
}

string TheoryArithNew::unsatAsString() const {

	// The string we are building 
	string str; 

	// Start from the begining
	set<Expr>::const_iterator it     = unsatBasicVariables.begin();
	set<Expr>::const_iterator it_end = unsatBasicVariables.end(); 
	
	// Print all the rows
	while (it != it_end) {
		// Print the equality
		str = str + (*it).toString() + " ";
		
		// Continue to the next row
		it ++;
	}
	
	// Return the string representation 
	return str;
}


string TheoryArithNew::boundsAsString() {

	// The string we are building 
	string str; 

	// Set containing all the variables
	set<Expr> all_variables;
	
	// Go throught the tableaux and pick up all the variables
	TebleauxMap::const_iterator it     = tableaux.begin();
	TebleauxMap::const_iterator it_end = tableaux.end();
	for(; it != it_end; it ++) {
	
		// Add the basic variable to the set
		all_variables.insert((*it).first);
		
		// Go through all the expression variables and add them to the set
		const Expr& rightSide = (*it).second.getExpr()[1];
		int term_i_end = rightSide.arity();
		for(int term_i = 0; term_i < term_i_end; ++ term_i)
			all_variables.insert(rightSide[term_i][1]);	
	} 
	
	// Go throught the bounds map and pickup all the variables
	CDMap<Expr, BoundInfo>::iterator bounds_it;
	for (bounds_it = lowerBound.begin(); bounds_it != lowerBound.end(); bounds_it ++)
		all_variables.insert((*bounds_it).first);
	for (bounds_it = upperBound.begin(); bounds_it != upperBound.end(); bounds_it ++)
		all_variables.insert((*bounds_it).first);
		
	// Start from the begining
	set<Expr>::iterator var_it     = all_variables.begin();
	set<Expr>::iterator var_it_end = all_variables.end(); 
	
	// Print all the rows
	while (var_it != var_it_end) {
		
		// The current variable
		const Expr& var = *var_it;
		
		// Print the equality
		str += getLowerBound(var).toString() + " <= " + var.toString() + "(" + getBeta(var).toString() + ") <= " + getUpperBound(var).toString() + "\n";
			
		// Continue to the next variable
		var_it ++;
	}
	
	// Return the string representation 
	return str;
}

// The infinity constant 
const TheoryArithNew::EpsRational TheoryArithNew::EpsRational::PlusInfinity(PLUS_INFINITY);
// The negative infinity constant
const TheoryArithNew::EpsRational TheoryArithNew::EpsRational::MinusInfinity(MINUS_INFINITY);
// The negative infinity constant
const TheoryArithNew::EpsRational TheoryArithNew::EpsRational::Zero;


Theorem TheoryArithNew::substAndCanonizeModTableaux(const Theorem& eq) {

	// If subst is empty, just return
  	if(tableaux.empty()) return eq;

	// Get the expression of the equality
	const Expr& eqExpr = eq.getExpr();

	// Check if the equality if in the canonic form
	DebugAssert(eqExpr.getKind() == EQ, "TheoryArithNew::substAndCanonize, expected equality " + eqExpr.toString());
	
	// Get the left side of the equality
	const Expr& rightSide = eqExpr[1];

  	// Do the actual substitution in the eqExpr
  	Theorem thm = substAndCanonizeModTableaux(rightSide);
  
  	// If the substitution had no result just return the original equation
  	if(thm.getRHS() == rightSide) return eq;
  	
  	// Return the theorem 
  	return iffMP(eq, substitutivityRule(eq.getExpr(), 1, thm));
}

Theorem TheoryArithNew::substAndCanonizeModTableaux(const Expr& sum) {
  	
  	Theorem res;                      // The resulting theorem   	
  	vector<Theorem> thms;             // The theorems of the changed terms for the substitution
  	vector<unsigned> changed;         // The indices of the changed terms for the substitution
	
	// Trace the canonisation
	TRACE("simplex", "TheoryArithNew::substAndCanonizeModTableaux(", sum, ")");
	
	// Check if the equality if in the canonic form
	DebugAssert(sum.getKind() == PLUS, "TheoryArithNew::substAndCanonize, expected sum " + sum.toString());
   
  	// Go throught the sum and try to substitute the variables
  	int term_index_end = sum.arity();
  	for(int term_index = 0; term_index < term_index_end; ++ term_index) {

		const Expr& term = sum[term_index]; // The current term expression (a*x)
		const Expr& var  = term[1];         // The variable of the current term
  
  		// Find the variable in the map
  		TebleauxMap::iterator find = tableaux.find(var);
  		
  		// If found, substitute it
  		if (find != tableaux.end()) {
  			
  			// Substitute the variable
  			Theorem termTheorem = canonThm(substitutivityRule(term, 1, (*find).second));
  			
  			// Check that the result is not trivial 
    		DebugAssert(termTheorem.getExpr() != term, "substAndCanonizeModTableaux: got the same term in substitution");
      		
			// Push it to the theorems vector
      		thms.push_back(termTheorem);
      		
      		// Add the index to the changed vector
      		changed.push_back(term_index);  		
  		}    	
  	}
  
  	// Do the actual substitution and canonize the result
  	if(thms.size() > 0) {
    	// Substitute the changed subterms into the term
    	res = substitutivityRule(sum, changed, thms);
    	// Canonise the result
    	res = canonThm(res);
  	} else
  		// Nothing happened, just return the reflexivity
    	res = reflexivityRule(sum);			
  
  	// Return the result
  	return res;
}

void TheoryArithNew::substAndCanonizeTableaux(const Theorem& eq) {

	Theorem result;	// The explaining theorem
		
	// Trace 
	TRACE("simplex", "TheoryArithNew::substAndCanonizeTableaux(", eq.getExpr(), ")");
		
	// Get the expression of the equality
	const Expr& eqExpr = eq.getExpr();

	// Check if the equality if in the canonic form
	DebugAssert(eqExpr.getKind() == EQ, "TheoryArithNew::substAndCanonize, expected equality " + eqExpr.toString());
	
	// Get the variable of the substitution
	const Expr& var = eqExpr[0];

	// Check if there are variables that depend on x_j
	DependenciesMap::iterator find = dependenciesMap.find(var);
	if (find != dependenciesMap.end()) {
			
		// Go through all the variables that depend on x_j, and update their value
		set<Expr>& dependent = (*find).second;
		set<Expr>::iterator it     = dependent.begin();
		set<Expr>::iterator it_end = dependent.end(); 		
		for(; it != it_end; ++ it) {
			
			// Get the expression and the right side of the row from the tableaux
			const Expr& leftSide      = *it;
			TebleauxMap::iterator row = tableaux.find(leftSide);
			const Expr& rowExpr       = (*row).second.getExpr();
			const Expr& rowRightSide  = rowExpr[1];
			
			// Go through the sum and try to substitute
			int right = rowRightSide.arity() - 1;
			int left  = 0;
			int term_i;
			while (left <= right) {	
				
				// Get the middle one
				term_i = (left + right) / 2;
				
				// Get the comparison of the variables
				int cmp = compare(rowRightSide[term_i][1], var);
						 	
				// If the variable is found
				if (cmp == 0) {
					
					// Do the substitution and canonise
					result = canonThm(substitutivityRule(rowRightSide[term_i], 1, eq));
					// Do the substitution and canonise in the sum
					result = canonThm(substitutivityRule(rowRightSide, term_i, result));
					// Do the substitution
					result = substitutivityRule(rowExpr, 1, result);
					
					// Get the new expression
					const Expr& newRowRightSide = result.getRHS()[1];				
					// Update the dependencies of the varriables in the expression
					updateDependencies(rowRightSide, newRowRightSide, leftSide, var); 
					
					// That's it, remember the new row
					(*row).second = iffMP((*row).second, result);				
					
					// Variables don't repeat, we can just break out				
					break;
				} else if (cmp > 0) 
					left = term_i + 1;
				else 
					right = term_i - 1;
			}
		}
		
		// Now nobody depends on var anymore, just erase it
	    dependent.clear();
	}	
}

Theorem TheoryArithNew::pivotRule(const Theorem& eq, const Expr& var) {

	Theorem result;  // The theorem explaining the result

	// Get the expression
	const Expr& eqExpr = eq.getExpr();
	const Expr& right_side = eqExpr[1];
	const Expr& left_side = eqExpr[0];

	// Trace if askedTheorem canonLeft  = d_rules->canonMult(thm.getExpr()[0]);
			
	TRACE("simplex", "TheoryArithNew::pivotRule(", eqExpr.toString() + ", ", var.toString() + ")"); 

	// Eq must be an equation with the sum on the left side and a leaf on the right side (variable)
	DebugAssert(eqExpr.getKind() == EQ, "TheoryArithNew::pivotRule, expected an equality : " + eqExpr.toString());
	DebugAssert(right_side.getKind() == PLUS, "TheoryArithNew::pivotRule, expected a sum on the left-hand side : " + eqExpr.toString());
	DebugAssert(isLeaf(left_side), "TheoryArithNew::pivotRule, expected a leaf (variable) on the right-hand side : " + eqExpr.toString());

	// Find the term of var in the left-hand side of eq
	int term_i_end = right_side.arity();
	for(int term_i = 0; term_i < term_i_end; ++ term_i)
		// If found do the stuff
		if (right_side[term_i][1] == var) {
	
			// This is the term we need and the rational we need
			const Expr& termExpr = right_side[term_i];
			const Expr& termVar = termExpr[1]; 
			const Rational& termRat = termExpr[0].getRational();
			
			// Construct the expression we will add to the equality
			const Expr& minusTermExpr = multExpr(rat(-termRat), termVar);
			const Expr& minusVarExpr  = multExpr(rat(-1), left_side); 
		
			// Add the above expressions to the to the equality
			result = iffMP(eq, d_rules->plusPredicate(left_side, right_side, plusExpr(minusTermExpr, minusVarExpr), EQ));
			// Canonise the right-hand side
			result = transitivityRule(result, canon(result.getExpr()[1]));
			// Canonise the left-hand side 
			result = transitivityRule(symmetryRule(canon(result.getExpr()[0])), result);
			// Multiply by the inverse of the rational constant (negated and ^-1)
			result = iffMP(result, d_rules->multEqn(result.getExpr()[0], result.getExpr()[1], rat(-1/termRat)));
			// Canonise the left-hand side
			result = transitivityRule(result, canon(result.getExpr()[1]));
			// Canonise the right=hand side 
			result = transitivityRule(symmetryRule(canon(result.getExpr()[0])), result);
			// Rewrite 1*x => x in the left-hand side
			result = transitivityRule(symmetryRule(d_rules->oneElimination(result.getExpr()[0])), result);
			
			// Trace the result
			TRACE("simplex", "TheoryArithNew::pivotRule ==> ", result.getExpr().toString(), "");
			
			// We are done, there is just one variable there
			return result;
		}
	
	// If not found, there is something wrong
	DebugAssert(false, "TheoryArithNew::pivotRule, " + var.toString() + " does not occur in " + eqExpr.toString());

	// Dummy return	
	return result;
}

Theorem TheoryArithNew::getLowerBoundExplanation(const TebleauxMap::iterator& var_it) {

	vector<Theorem> upperBounds; // Vector of the upper-bound theorems 
	
	// Get the tableaux theorem explaining the leftside = var
	Theorem tableauxTheorem = (*var_it).second;
	
	// Get the variable on the right side
	const Expr& var = (*var_it).first;

	// Get the expression involved (leftSide = var)
	const Expr& rightSide = tableauxTheorem.getExpr()[1];
	
	// Go through the left side and pick up the apropriate lower and upper bounds
	int leftSide_i_end = rightSide.arity();
	for(int leftSide_i = 0; leftSide_i < leftSide_i_end; ++ leftSide_i) {

		// Get the rational
		const Expr& a = rightSide[leftSide_i][0];
		
		// Get the variable
		const Expr& x = rightSide[leftSide_i][1];
		
		// The positive ones make up the upper bounds (x < u => a * x < a * u)
		if (a.getRational() > 0) {
			// Get the upper bound x < u
			Theorem thm = getUpperBoundThm(x);
			
			// Multiply if by a ==> u_i * a > x * a
			thm = iffMP(thm, d_rules->multIneqn(thm.getExpr(), a));
		
			// Canonise the left and the right side
			Theorem canonRight  = d_rules->canonMultTermConst(thm.getExpr()[1][1], thm.getExpr()[1][0]);
			Theorem canonLeft = d_rules->canonMultConstConst(thm.getExpr()[0][0], thm.getExpr()[0][1]); 
			
			// Substitute the canonised to the inequality
			thm = iffMP(thm, substitutivityRule(thm.getExpr(), canonLeft, canonRight));
			
			// Add the bound to the vector of upper bounds (|- c_x > a * x) 
			upperBounds.push_back(thm);
		} 
		// The negative ones make up the lower bounds (x > l => a * x < a * l)
		else {
			// Get the lower bound l < x
			Theorem thm = getLowerBoundThm(x);
			
			// Multiply if by a |- l * a < x * a  
			thm = iffMP(thm, d_rules->multIneqn(thm.getExpr(), a));
		
			// Canonise the left and the right side
			Theorem canonRight  = d_rules->canonMultTermConst(thm.getExpr()[1][1], thm.getExpr()[1][0]);
			Theorem canonLeft = d_rules->canonMultConstConst(thm.getExpr()[0][0], thm.getExpr()[0][1]); 
			
			// Substitute the canonised to the inequality
			thm = iffMP(thm, substitutivityRule(thm.getExpr(), canonLeft, canonRight));
			
			// Add the bound to the vector of upper bounds (|- c_x > a * x)
			upperBounds.push_back(thm);
		}
	} 
	
	// Add up all the inequalities to get a C = \sum c_i > rightSide 
	Theorem sumInequalities = upperBounds[0];
	for(unsigned int i = 1; i < upperBounds.size(); i ++) {	
		// Add the inequalities
		sumInequalities = d_rules->addInequalities(sumInequalities, upperBounds[i]);
		
		// Canonise the left and the right side
		Theorem canonLeft  = d_rules->canonPlus(sumInequalities.getExpr()[0]);
		Theorem canonRight = d_rules->canonPlus(sumInequalities.getExpr()[1]);
		
		// Substitute the canonised to the inequality
		sumInequalities = iffMP(sumInequalities, substitutivityRule(sumInequalities.getExpr(), canonLeft, canonRight));		
	}
	
	// Substitute to get C > rightSide ==> C > var
	Theorem varUpperBound = substitutivityRule(sumInequalities.getExpr(), 1, symmetryRule(tableauxTheorem));  
	// MP to get C > var
	varUpperBound = iffMP(sumInequalities, varUpperBound);
	
	// Get the lower bound on the rigth side variable (l_var < var)
	Theorem varLowerBound = getLowerBoundThm(var);

	// Return the clashing bound theorem 
	return d_rules->clashingBounds(varLowerBound, varUpperBound);
}

Theorem TheoryArithNew::getUpperBoundExplanation(const TebleauxMap::iterator& var_it) {

	vector<Theorem> lowerBounds; // Vector of the upper-bound theorems 
	
	// Get the tableaux theorem explaining the leftside = var
	Theorem tableauxTheorem = (*var_it).second;
	
	// Get the variable on the right side
	const Expr& var = (*var_it).first;

	// Get the expression involved (var = rightSide)
	const Expr& rightSide = tableauxTheorem.getExpr()[1];
	
	// Trace if requested
	TRACE("explanations", "Generating explanation for the tableaux row ", tableauxTheorem.getExpr(), "");
	
	// Go through the right side and pick up the apropriate lower and upper bounds
	int rightSide_i_end = rightSide.arity();
	for(int rightSide_i = 0; rightSide_i < rightSide_i_end; ++ rightSide_i) {

		// Get the rational
		const Expr& a = rightSide[rightSide_i][0];
		
		// Get the variable
		const Expr& x = rightSide[rightSide_i][1];
		
		// The positive ones make up the lower bounds (x > l => a * x > a * l)
		if (a.getRational() > 0) {
			// Get the lower bound l < x
			Theorem thm = getLowerBoundThm(x);
			TRACE("explanations", "Got ", thm.getExpr(), "");
			
			// Multiply if by a ==> l * a < x * a
			thm = iffMP(thm, d_rules->multIneqn(thm.getExpr(), a));
			TRACE("explanations", "Got ", thm.getExpr(), "");
		
			// Canonise the left and the right side
			Theorem canonRight  = d_rules->canonMultTermConst(thm.getExpr()[1][1], thm.getExpr()[1][0]);
			Theorem canonLeft = d_rules->canonMultConstConst(thm.getExpr()[0][0], thm.getExpr()[0][1]); 
			
			// Substitute the canonised to the inequality
			thm = iffMP(thm, substitutivityRule(thm.getExpr(), canonLeft, canonRight));
			TRACE("explanations", "Got ", thm.getExpr(), "");
			
			// Add the bound to the vector of upper bounds (|- c_x < a * x) 
			lowerBounds.push_back(thm);
		} 
		// The negative ones make up the upper bounds (x < u => a * x > a * u)
		else {
			// Get the upper bound u > x
			Theorem thm = getUpperBoundThm(x);
			TRACE("explanations", "Got ", thm.getExpr(), "");
		
			// Multiply it by a |- u * a > x * a 
			thm = iffMP(thm, d_rules->multIneqn(thm.getExpr(), a));
			TRACE("explanations", "Got ", thm.getExpr(), "");
		
			// Canonise the left and the right side
			Theorem canonRight = d_rules->canonMultTermConst(thm.getExpr()[1][1], thm.getExpr()[1][0]);
			Theorem canonLeft  = d_rules->canonMultConstConst(thm.getExpr()[0][0], thm.getExpr()[0][1]); 
			
			// Substitute the canonised to the inequality
			thm = iffMP(thm, substitutivityRule(thm.getExpr(), canonLeft, canonRight));
			TRACE("explanations", "Got ", thm.getExpr(), "");
			
			// Add the bound to the vector of upper bounds (|- c_x < a * x)
			lowerBounds.push_back(thm);
		}
	} 
	
	// Add up all the inequalities to get a \sum c_i = C > rightSide
	Theorem sumInequalities = lowerBounds[0];
	for(unsigned int i = 1; i < lowerBounds.size(); i ++) {	
		// Add the inequalities
		sumInequalities = d_rules->addInequalities(sumInequalities, lowerBounds[i]);
		
		TRACE("explanations", "Got sum ", sumInequalities.getExpr(), "");
		
		// Canonise the left and the right side
		Theorem canonLeft  = d_rules->canonPlus(sumInequalities.getExpr()[0]);
		Theorem canonRight = d_rules->canonPlus(sumInequalities.getExpr()[1]);
		
		// Substitute the canonised to the inequality
		sumInequalities = iffMP(sumInequalities, substitutivityRule(sumInequalities.getExpr(), canonLeft, canonRight));		
	}
	
	// Trace if requested
	TRACE("explanations", "Got sum ", sumInequalities.getExpr(), "");

	// Substitute to get C < leftSide ==> C < var
	Theorem varLowerBound = substitutivityRule(sumInequalities.getExpr(), 1, symmetryRule(tableauxTheorem));  
	
	// MP to get C < var
	varLowerBound = iffMP(sumInequalities, varLowerBound);

	// Trace if requested
	TRACE("explanations", "Got lower bound ", varLowerBound.getExpr(), "");
	
	// Get the lower bound on the rigth side variable (var > l_var)
	Theorem varUpperBound = getUpperBoundThm(var);

	// Trace if requested
	TRACE("explanations", "Got upper bound ", varUpperBound.getExpr(), "");

	TRACE("explanations", "The var value (", var, ")" + getBeta(var).toString());

	// Return the clashing bound theorem 
	return d_rules->clashingBounds(varLowerBound, varUpperBound);
}

void TheoryArithNew::updateFreshVariables() {

	unsigned int size = assertedExpr.size();
	unsigned int i;

	for (i = assertedExprCount; i < size; ++ i)
		//Update the value
		updateValue(assertedExpr[i][0], assertedExpr[i][1]);

	// Update the asserted count to be the size of the vector
	assertedExprCount = i;

}

void TheoryArithNew::updateDependenciesAdd(const Expr& var, const Expr& sum) {
	
	// Trace it
	TRACE("tableaux_dep", "updateDependenciesAdd(", var.toString() + ", ", sum.toString() + ")");
	
	// Go through the sum and add var to the dependencies of that term variable
	Expr::iterator term = sum.begin();
	Expr::iterator term_end = sum.end();
	for(; term != term_end; term ++)
		dependenciesMap[(*term)[1]].insert(var);

}

void TheoryArithNew::updateDependenciesRemove(const Expr& var, const Expr& sum) {
	
	// Trace it
	TRACE("tableaux_dep", "updateDependenciesRemove(", var.toString() + ", ", sum.toString() + ")");
		
	// Go through the sum and remove var to the dependencies of that term variable
	Expr::iterator term = sum.begin();
	Expr::iterator term_end = sum.end();
	for(; term != term_end; term ++)
		dependenciesMap[(*term)[1]].erase(var);

}

void TheoryArithNew::updateDependencies(const Expr& oldSum, const Expr& newSum, const Expr& dependentVar, const Expr& skipVar) {

	// Trace it
	TRACE("tableaux_dep", "updateDependencies(", oldSum.toString() + ", " + newSum.toString() + ", " + dependentVar.toString(), ")");
	
	// Since the sums are ordered by variables, we can just to a "merge sort"
	int oldSum_i = 0, newSum_i = 0;
	int oldSum_end = oldSum.arity(), newSum_end = newSum.arity();
	// Get the first variables
	while (oldSum_i < oldSum_end && newSum_i < newSum_end) {
		
		// Get the variable references
		const Expr oldVar = oldSum[oldSum_i][1];
		const Expr newVar = newSum[newSum_i][1];
		
		// If variables equal, just skip, everything is ok
		if (oldVar == newVar) {
			++ oldSum_i; ++ newSum_i; continue;	
		} 
		
		// Otherwise do the work with the smaller one
		if (oldVar > newVar) {
			// Old variable has dissapeared, remove dependent from its list 
			if (oldVar != skipVar)
				dependenciesMap[oldVar].erase(dependentVar);
			// Move the old variable forward
			++ oldSum_i; 
		} else { 
			// New variable has appeared, insert dependent to its list
			if (newVar != skipVar)
				dependenciesMap[newVar].insert(dependentVar);
			// Move the new variable forward
			++ newSum_i;
		}
	} 

	// If there is leftovers in the old sum, just do the removals
	while (oldSum_i < oldSum_end) {
		// Get the var, and increase the index
		const Expr& var = oldSum[oldSum_i ++][1];
		// Update the dependency
		if (var != skipVar) 
			dependenciesMap[var].erase(dependentVar);
	}
	
	while (newSum_i < newSum_end) {
		// Get the var, and increase the index
		const Expr& var = newSum[newSum_i ++][1];
		// Update the dependency
		if (var != skipVar) 
			dependenciesMap[var].insert(dependentVar);
	}
}

void TheoryArithNew::registerAtom(const Expr& e) {
	
	// Trace it
	TRACE("propagate_arith", "registerAtom(", e.toString(), ")");
	TRACE("arith_atoms", "", e.toString(), "");
	
	// If it is a atomic formula, add it to the map	
	if (e.isAbsAtomicFormula()) {
		Expr rightSide    = e[1];
		int kind          = e.getKind();
		Rational leftSide = e[0].getRational();
		
		// The eps bound we'll be using
		EpsRational bound; 
		
		// Depending on the type of the inequality define the bound
		switch (kind) {
			case LT: 
				bound = EpsRational(leftSide, +1);
				break;					
			case LE:
				bound = leftSide;
				break;
			case GT: 
				bound = EpsRational(leftSide, -1);
				break;
			case GE:
				bound = leftSide;
				break;			
			default:
				// How did we get here
      			FatalAssert(false, "TheoryArithNew::registerAtom: control should not reach here" + e.toString());	
		}
		
		// Bound has been set, now add the
		allBounds.insert(ExprBoundInfo(bound, e));		
	}	

//	// Printout the current set of atoms in the set
//	cout << "ALL BOUNDS:" << endl;
//	BoundInfoSet::iterator it = allBounds.begin();
//	while (it != allBounds.end()) {
//		cout << (*it).e << endl;
//		++ it;
//	}
}

void TheoryArithNew::propagateTheory(const Expr& assertExpr, const EpsRational& bound, const EpsRational& oldBound) {

	// Trace it
	TRACE("propagate_arith", "propagateTheory(", assertExpr.toString() + ", " + bound.toString(), ")");

	// Make the bound info object, so that we can search for it
	ExprBoundInfo boundInfo(bound, assertExpr);
	
		// Get the exression on the right side hand
	Expr rightSide = assertExpr[1];
	
	// Get the kid of the disequality
	int kind = assertExpr.getKind();
	
	// Check wheather the kind is one of LT, LE, GT, GE
	DebugAssert(kind == LT || kind == LE || kind == GT || kind == GE , "TheoryArithNew::propagateTheory : expected an inequality");
	
	// If the bound is of the type LT or LE we go up
	if (kind == LT || kind == LE) {
		// Find the asserted fact in the set (it must be there)
		BoundInfoSet::iterator find      = allBounds.lower_bound(boundInfo);
		BoundInfoSet::iterator find_end  = allBounds.lower_bound(ExprBoundInfo(oldBound, assertExpr));
		
		// If we are at the begining, or not found, just exit
		if (find == find_end) return;
		
		// Now, go up until reached wrong right side (skip the first one, its the same as given)
		while (find != find_end) {
			
			// Go up;
			-- find;
		
			// Get the theorem of the find
			const Expr& findExpr = (*find).e;
			
			// Get the bound of the find
			const EpsRational findRat = (*find).bound; 
		
			// Get the kind of the expression in the theorem
			int findExprKind = findExpr.getKind();
			
			// Check if the right sides are the same
			if (rightSide != findExpr[1]) break;
		
			// Construct the theorem object
			Theorem lemma;
		
			// Check the type and equeue the lemma 
			if (findExprKind == LT || findExprKind == LE)
				// Imply the weaker inequality
				lemma = d_rules->implyWeakerInequality(assertExpr, findExpr);
			else
				// Imply the negation of the impossible inequality
				lemma = d_rules->implyNegatedInequality(assertExpr, findExpr);
				
		
			TRACE("propagate_arith", "lemma ==>", lemma.toString(), "");
			TRACE("arith_atoms", "Propagate: ", lemma.getExpr().toString(), "");
		
			// Put it across
			enqueueFact(lemma);
		}
	}	 
	// If the bound is of the type GT or GE we go down
	else {
		// Find the asserted fact in the set (it must be there)
		BoundInfoSet::iterator find          = allBounds.upper_bound(boundInfo);
		BoundInfoSet::iterator find_end      = allBounds.upper_bound(ExprBoundInfo(oldBound, assertExpr));
		
		// Now, go down until reached wrong right side (skip the first one, its the same as given)
		while (find != find_end) {
							
			// Get the bound of the find
			const EpsRational findRat = (*find).bound; 
		
			// Get the expression in the theorem
			const Expr& findExpr = (*find).e;
			int findExprKind = findExpr.getKind();
			
			// Check if the right sides are the same
			if (rightSide != findExpr[1]) break;
		
			// Construct the theorem object
			Theorem lemma;
		
			// Check the type and equeue the lemma 
			if (findExprKind == GT || findExprKind == GE)
				// Imply the weaker inequality
				lemma = d_rules->implyWeakerInequality(assertExpr, findExpr);
			else
				// Imply the negation of the impossible inequality (use oposite than above)
				lemma = d_rules->implyNegatedInequality(assertExpr, findExpr);
						
			TRACE("propagate_arith", "lemma ==>", lemma.toString(), "");
			TRACE("arith_atoms", "Propagate: ", lemma.getExpr().toString(), "");
				
			// Put it across
			enqueueFact(lemma);
			
			// Go to the next one
			++ find;
		}
	}	
}

Theorem TheoryArithNew::deriveGomoryCut(const Expr& x_i) {

	Theorem res;

	// CHECK IF APPLICABLE
	DebugAssert(isBasic(x_i), "TheoryArithNew::deriveGomoryCut variable must be a basic variable : " + x_i.toString());	
	DebugAssert(intVariables.count(x_i) > 0, "TheoryArithNew::deriveGomoryCut variable must be a basic variable : " + x_i.toString());

	// Get the rational value of x_i
	Rational x_i_Value = getBeta(x_i).getRational();
	
	// Compute f_0
	Rational f_0 = x_i_Value - floor(x_i_Value);
		
	return res;
}
