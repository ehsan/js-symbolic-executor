/*****************************************************************************/
/*!
 * \file theory_arith_old.cpp
 *
 * Author: Clark Barrett, Vijay Ganesh.
 *
 * Created: Fri Jan 17 18:39:18 2003
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


#include "theory_arith_old.h"
#include "arith_proof_rules.h"
//#include "arith_expr.h"
#include "arith_exception.h"
#include "typecheck_exception.h"
#include "eval_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
#include "theory_core.h"
#include "command_line_flags.h"
//TODO: remove this dependency
#include "../theory_core/core_proof_rules.h"


using namespace std;
using namespace CVC3;


///////////////////////////////////////////////////////////////////////////////
// TheoryArithOld::FreeConst Methods                                            //
///////////////////////////////////////////////////////////////////////////////

namespace CVC3 {

ostream& operator<<(ostream& os, const TheoryArithOld::FreeConst& fc) {
  os << "FreeConst(r=" << fc.getConst() << ", "
     << (fc.strict()? "strict" : "non-strict") << ")";
  return os;
}

///////////////////////////////////////////////////////////////////////////////
// TheoryArithOld::Ineq Methods                                                 //
///////////////////////////////////////////////////////////////////////////////

ostream& operator<<(ostream& os, const TheoryArithOld::Ineq& ineq) {
  os << "Ineq(" << ineq.ineq().getExpr() << ", isolated on "
     << (ineq.varOnRHS()? "RHS" : "LHS") << ", const = "
     << ineq.getConst() << ")";
  return os;
}
} // End of namespace CVC3


///////////////////////////////////////////////////////////////////////////////
// TheoryArithOld Private Methods                                               //
///////////////////////////////////////////////////////////////////////////////


Theorem TheoryArithOld::isIntegerThm(const Expr& e) {
  // Quick checks
  Type t = e.getType();
  if (isReal(t)) return Theorem();
  if (isInt(t)) return typePred(e);

  // Try harder
  return isIntegerDerive(Expr(IS_INTEGER, e), typePred(e));
}


Theorem TheoryArithOld::isIntegerDerive(const Expr& isIntE, const Theorem& thm) {
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

const Rational& TheoryArithOld::freeConstIneq(const Expr& ineq, bool varOnRHS) {
  DebugAssert(isIneq(ineq), "TheoryArithOld::freeConstIneq("+ineq.toString()+")");
  const Expr& e = varOnRHS? ineq[0] : ineq[1];

  switch(e.getKind()) {
  case PLUS:
    return e[0].getRational();
  case RATIONAL_EXPR:
    return e.getRational();
  default: { // MULT, DIV, or Variable
    static Rational zero(0);
    return zero;
  }
  }
}


const TheoryArithOld::FreeConst&
TheoryArithOld::updateSubsumptionDB(const Expr& ineq, bool varOnRHS,
				 bool& subsumed) {
  TRACE("arith ineq", "TheoryArithOld::updateSubsumptionDB(", ineq,
	", var isolated on "+string(varOnRHS? "RHS" : "LHS")+")");
  DebugAssert(isLT(ineq) || isLE(ineq), "TheoryArithOld::updateSubsumptionDB("
	      +ineq.toString()+")");
  // Indexing expression: same as ineq only without the free const
  Expr index;
  const Expr& t = varOnRHS? ineq[0] : ineq[1];
  bool strict(isLT(ineq));
  Rational c(0);
  if(isPlus(t)) {
    DebugAssert(t.arity() >= 2, "TheoryArithOld::updateSubsumptionDB("
		+ineq.toString()+")");
    c = t[0].getRational(); // Extract the free const in ineq
    Expr newT;
    if(t.arity() == 2) {
      newT = t[1];
    } else {
      vector<Expr> kids;
      Expr::iterator i=t.begin(), iend=t.end();
      kids.push_back(rat(0));
      for(++i; i!=iend; ++i) kids.push_back(*i);
      DebugAssert(kids.size() > 0, "kids.size = "+int2string(kids.size())
		  +", ineq = "+ineq.toString());
      newT = plusExpr(kids);
    }
    if(varOnRHS)
      index = leExpr(rat(0), canonSimplify(ineq[1] - newT).getRHS());
    else
      index = leExpr(canonSimplify(ineq[0]-newT).getRHS(), rat(0));
  } else if(isRational(t)) {
    c = t.getRational();
    if(varOnRHS)
      index = leExpr(rat(0), ineq[1]);
    else
      index = leExpr(ineq[0], rat(0));
  } else if(isLT(ineq))
    index = leExpr(ineq[0], ineq[1]);
  else
    index = ineq;
  // Now update the database, check for subsumption, and extract the constant
  CDMap<Expr, FreeConst>::iterator i=d_freeConstDB.find(index),
    iend=d_freeConstDB.end();
  if(i == iend) {
    subsumed = false;
    // Create a new entry
    CDOmap<Expr,FreeConst>& obj = d_freeConstDB[index];
    obj = FreeConst(c,strict);
    TRACE("arith ineq", "freeConstDB["+index.toString()+"] := ", obj, "");
    return obj.get();
  } else {
    CDOmap<Expr,FreeConst>& obj = d_freeConstDB[index];
    const FreeConst& fc = obj.get();
    if(varOnRHS) {
      subsumed = (c < fc.getConst() ||
		  (c == fc.getConst() && (!strict || fc.strict())));
    } else {
      subsumed = (c > fc.getConst() ||
		  (c == fc.getConst() && (strict || !fc.strict())));
    }
    if(!subsumed) {
      obj = FreeConst(c,strict);
      TRACE("arith ineq", "freeConstDB["+index.toString()+"] := ", obj, "");
    }
    return obj.get();
  }
}


bool TheoryArithOld::kidsCanonical(const Expr& e) {
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


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// Function: TheoryArithOld::canon                                              //
// Author: Clark Barrett, Vijay Ganesh.                                      //
// Created: Sat Feb  8 14:46:32 2003                                         //
// Description: Compute a canonical form for expression e and return a       //
//              theorem that e is equal to its canonical form.               //
// Note that canonical form for arith expressions is one of the following:   //
// 1. rational constant                                                      //
// 2. arithmetic leaf                                                        //
//    (i.e. variable or term from some other theory)                         //
// 3. (MULT rat leaf)                                                        //
//    where rat is a non-zero rational constant, leaf is an arithmetic leaf  //
// 4. (PLUS const term_0 term_1 ... term_n)                                  //
//    where each term_i is either a leaf or (MULT rat leaf)                  //
//    and each leaf in term_i must be strictly greater than the leaf in      //
//    term_{i+1}.                                                            //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
Theorem TheoryArithOld::canon(const Expr& e)
{
  TRACE("arith canon","canon(",e,") {");
  DebugAssert(kidsCanonical(e), "TheoryArithOld::canon("+e.toString()+")");
  Theorem result;
  switch (e.getKind()) {
    case UMINUS: {
      Theorem thm = d_rules->uMinusToMult(e[0]);
      Expr e2 = thm.getRHS();
      result = transitivityRule(thm, canon(e2));
    }
      break;
    case PLUS: /* {
      Theorem plusThm, plusThm1;
      plusThm = d_rules->canonFlattenSum(e);
      plusThm1 = d_rules->canonComboLikeTerms(plusThm.getRHS());
      result = transitivityRule(plusThm,plusThm1);
    }
             */
      result = d_rules->canonPlus(e);
      break;
    case MINUS: {
      DebugAssert(e.arity() == 2,"");
      Theorem minus_eq_sum = d_rules->minusToPlus(e[0], e[1]);
      // this produces e0 + (-1)*e1; we have to canonize it in 2 steps
      Expr sum(minus_eq_sum.getRHS());
      Theorem thm(canon(sum[1]));
      if(thm.getLHS() == thm.getRHS())
        result = canonThm(minus_eq_sum);
      // The sum changed; do the work
      else {
        vector<unsigned> changed;
        vector<Theorem> thms;
        changed.push_back(1);
        thms.push_back(thm);
        Theorem sum_eq_canon = canonThm(substitutivityRule(sum, changed, thms));
        result = transitivityRule(minus_eq_sum, sum_eq_canon);
      }
      break;
    }

    case MULT:
      result = d_rules->canonMult(e);
      break;
  /*
    case MULT: {
      Theorem thmMult, thmMult1;
      Expr exprMult;
      Expr e0 = e[0];
      Expr e1 = e[1];
      if(e0.isRational()) {
        if(rat(0) == e0)
        result = d_rules->canonMultZero(e1);
        else if (rat(1) == e0)
        result = d_rules->canonMultOne(e1);
        else
        switch(e1.getKind()) {
        case RATIONAL_EXPR :
          result = d_rules->canonMultConstConst(e0,e1);
          break;
        case MULT:
          DebugAssert(e1[0].isRational(),
                      "theory_arith::canon:\n  "
                      "canon:MULT:MULT child is not canonical: "
                      + e1[0].toString());

          thmMult = d_rules->canonMultConstTerm(e0,e1[0],e1[1]);
          result = transitivityRule(thmMult,canon(thmMult.getRHS()));
          break;
        case PLUS:{
          Theorem thmPlus, thmPlus1;
          Expr ePlus;
          std::vector<Theorem> thmPlusVector;
          thmPlus = d_rules->canonMultConstSum(e0,e1);
          ePlus = thmPlus.getRHS();
          Expr::iterator i = ePlus.begin();
          for(;i != ePlus.end();++i)
            thmPlusVector.push_back(canon(*i));
          thmPlus1 = substitutivityRule(PLUS, thmPlusVector);
          result = transitivityRule(thmPlus, thmPlus1);
          break;
        }
        default:
          result = reflexivityRule(e);
          break;
        }
      }
      else {
          if(e1.isRational()){

          // canonMultTermConst just reverses the order of the const and the
            // term.  Then canon is called again.
        Theorem t1 = d_rules->canonMultTermConst(e1,e0);
        result = transitivityRule(t1,canon(t1.getRHS()));
        }
        else

              // This is where the assertion for non-linear multiplication is
              // produced.
            result =  d_rules->canonMultTerm1Term2(e0,e1);
      }
      break;
      }

  */
    case DIVIDE:{
  /*
      case DIVIDE:{
        if (e[1].isRational()) {
          if (e[1].getRational() == 0)
            throw ArithException("Divide by 0 error in "+e.toString());
          Theorem thm = d_rules->canonDivideVar(e[0], e[1]);
          Expr e2 = thm.getRHS();
          result =  transitivityRule(thm, canon(e2));
        }
        else
        {
        // TODO: to be handled
        throw ArithException("Divide by a non-const not handled in "+e.toString());
        }
      break;
      }
  */

      // Division by 0 is OK (total extension, protected by TCCs)
      //      if (e[1].isRational() && e[1].getRational() == 0)
      //        throw ArithException("Divide by 0 error in "+e.toString());
      if (e[1].getKind() == PLUS)
        throw ArithException("Divide by a PLUS expression not handled in"+e.toString());
      result = d_rules->canonDivide(e);
      break;
    }
  case POW:
    if(e[1].isRational())
      result = d_rules->canonPowConst(e);
    else {
      // x ^ 1 --> x
      if (e[0].isRational() && e[0].getRational() == 1) {
    	  result = d_rules->powerOfOne(e);
      } else
    	  result = reflexivityRule(e);
    }
    break;
  default:
      result = reflexivityRule(e);
      break;
    }
  TRACE("arith canon","canon => ",result," }");
  return result;
}


Theorem
TheoryArithOld::canonSimplify(const Expr& e) {
  TRACE("arith simplify", "canonSimplify(", e, ") {");
  DebugAssert(kidsCanonical(e),
	      "TheoryArithOld::canonSimplify("+e.toString()+")");
  DebugAssert(leavesAreSimp(e), "Expected leaves to be simplified");
  Expr tmp(e);
  Theorem thm = canon(e);
  if(thm.getRHS().hasFind())
    thm = transitivityRule(thm, find(thm.getRHS()));
  // We shouldn't rely on simplification in this function anymore
  DebugAssert(thm.getRHS() == simplifyExpr(thm.getRHS()),
	      "canonSimplify("+e.toString()+")\n"
	      +"canon(e) = "+thm.getRHS().toString()
	      +"\nsimplify(canon(e)) = "+simplifyExpr(thm.getRHS()).toString());
//   if(tmp != thm.getRHS())
//     thm = transitivityRule(thm, simplifyThm(thm.getRHS()));
//   while(tmp != thm.getRHS()) {
//     tmp = thm.getRHS();
//     thm = canon(thm);
//     if(tmp != thm.getRHS())
//       thm = transitivityRule(thm, simplifyThm(thm.getRHS()));
//   }
  TRACE("arith", "canonSimplify =>", thm, " }");
  return thm;
}

/*! accepts a theorem, canonizes it, applies iffMP and substituvity to
 *  derive the canonized thm
 */
Theorem
TheoryArithOld::canonPred(const Theorem& thm) {
  vector<Theorem> thms;
  DebugAssert(thm.getExpr().arity() == 2,
              "TheoryArithOld::canonPred: bad theorem: "+thm.toString());
  Expr e(thm.getExpr());
  thms.push_back(canonSimplify(e[0]));
  thms.push_back(canonSimplify(e[1]));
  Theorem result = iffMP(thm, substitutivityRule(e.getOp(), thms));

  return result;
}

/*! accepts an equivalence theorem, canonizes it, applies iffMP and
 *  substituvity to derive the canonized thm
 */
Theorem
TheoryArithOld::canonPredEquiv(const Theorem& thm) {
  vector<Theorem> thms;
  DebugAssert(thm.getRHS().arity() == 2,
              "TheoryArithOld::canonPredEquiv: bad theorem: "+thm.toString());
  Expr e(thm.getRHS());
  thms.push_back(canonSimplify(e[0]));
  thms.push_back(canonSimplify(e[1]));
  Theorem result = transitivityRule(thm, substitutivityRule(e.getOp(), thms));

  return result;
}

/*! accepts an equivalence theorem whose RHS is a conjunction,
 *  canonizes it, applies iffMP and substituvity to derive the
 *  canonized thm
 */
Theorem
TheoryArithOld::canonConjunctionEquiv(const Theorem& thm) {
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
Theorem TheoryArithOld::doSolve(const Theorem& thm)
{
  const Expr& e = thm.getExpr();
  if (e.isTrue() || e.isFalse()) return thm;
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
  TRACE("arith eq","doSolve => ",eqnThm.getExpr()," }");
  right = eqnThm.getRHS();

  //eqn is of the form 0 = e' and is normalized where 'right' denotes e'
  //FIXME: change processRealEq to accept equations as well instead of theorems

  try {
    if (isMult(right)) {
      DebugAssert(right.arity() > 1, "Expected arity > 1");
      if (right[0].isRational()) {
        Rational r = right[0].getRational();
        if (r == 0) return getCommonRules()->trueTheorem();
        else if (r == 1) {
          enqueueFact(iffMP(eqnThm, d_rules->multEqZero(eqnThm.getExpr())));
          return getCommonRules()->trueTheorem();
        }
        Theorem res = iffMP(eqnThm,
                            d_rules->multEqn(eqnThm.getLHS(),
                                             right, rat(1/r)));
        res = canonPred(res);
        return doSolve(res);
      }
      else {
        enqueueFact(iffMP(eqnThm, d_rules->multEqZero(eqnThm.getExpr())));
        return getCommonRules()->trueTheorem();
      }
    }
    else if (isPow(right)) {
      DebugAssert(right.arity() == 2, "Expected arity 2");
      if (right[0].isRational()) {
        return doSolve(iffMP(eqnThm, d_rules->powEqZero(eqnThm.getExpr())));
      }
      throw ArithException("Can't solve exponential eqn: "+eqnThm.toString());
    }
    else {
      if(!isInteger(right)) {
        return processRealEq(eqnThm);
      }
      else {
        return processIntEq(eqnThm);
      }
    }
  } catch(ArithException& e) {
	  FatalAssert(false, "We should never get here!!! : " + e.toString());

//	  // Nonlinear bail out
//    Theorem res;
//    if (isPlus(right)) {
//      // Solve for something
//    	// Try to simulate groebner basis by picking the highest term
//    	Expr isolated = right[1];
//    	int isolated_degree = termDegree(isolated);
//    	for (int i = 2; i < right.arity(); i ++) {
//    		int degree = termDegree(right[i]);
//    		if (degree > isolated_degree) {
//    			isolated = right[i];
//    			isolated_degree = degree;
//    		}
//    	}
//      Rational coeff;
//      if (isMult(isolated) && isolated[0].isRational()) {
//        coeff = isolated[0].getRational();
//        DebugAssert(coeff != 0, "Expected nonzero coeff");
//        isolated = canon(isolated / rat(coeff)).getRHS();
//      } else coeff = 1;
//      res = iffMP(eqnThm, d_rules->multEqn(rat(0), right, rat(-1/coeff)));
//      res = canonPred(res);
//      res = iffMP(res, d_rules->plusPredicate(res.getLHS(), res.getRHS(), isolated, EQ));
//      res = canonPred(res);
//      TRACE("arith nonlinear", "solved for: ", res.getExpr(), "");
//    } else
//      res = symmetryRule(eqnThm); // Flip to e' = 0
//    TRACE("arith eq", "doSolve: failed to solve an equation: ", e, "");
//    IF_DEBUG(debugger.counter("FAILED to solve equalities")++;)
//    setIncomplete("Non-linear arithmetic equalities");
//
//    // Since we are forgetting about this equation, setup for updates
//    TRACE("arith nonlinear", "adding setup to ", eqnThm.getExpr(), "");
//    setupRec(eqnThm.getExpr());
//    return getCommonRules()->trueTheorem();
  }
  FatalAssert(false, "");
  return Theorem();
}

/*! pick a monomial for the input equation. This function is used only
 *  if the equation is an integer equation. Choose the monomial with
 *  the smallest absolute value of coefficient.
 */
bool TheoryArithOld::pickIntEqMonomial(const Expr& right, Expr& isolated, bool& nonlin)
{
  DebugAssert(isPlus(right) && right.arity() > 1,
              "TheoryArithOld::pickIntEqMonomial right is wrong :-): " +
              right.toString());
  DebugAssert(right[0].isRational(),
              "TheoryArithOld::pickIntEqMonomial. right[0] must be const" +
              right.toString());
//  DebugAssert(isInteger(right),
//              "TheoryArithOld::pickIntEqMonomial: right is of type int: " +
//              right.toString());
  //right is of the form "C + a1x1 + ... + anxn". min is initialized
  //to a1
  Expr::iterator istart = right.begin(), iend = right.end();
  istart++;
  Expr::iterator i = istart, j;
  bool found = false;
  nonlin = false;
  Rational min, coeff;
  Expr leaf;
  for(; i != iend; ++i) {
    if (isLeaf(*i)) {
      leaf = *i;
      coeff = 1;
    }
    else if (isMult(*i) && (*i).arity() == 2 && (*i)[0].isRational() && isLeaf((*i)[1])) {
      leaf = (*i)[1];
      coeff = abs((*i)[0].getRational());
    }
    else {
      nonlin = true;
      continue;
    }
    for (j = istart; j != iend; ++j) {
      if (j != i && isLeafIn(leaf, *j)) break;
    }
    if (j == iend) {
      if (!found || min > coeff) {
        min = coeff;
        isolated = *i;
        found = true;
      }
    }
  }
  return found;
}

/*! input is 0=e' Theorem and some of the vars in e' are of
 * type REAL. isolate one of them and send back to framework. output
 * is "var = e''" Theorem.
 */
Theorem
TheoryArithOld::processRealEq(const Theorem& eqn)
{
  DebugAssert(eqn.getLHS().isRational() &&
              eqn.getLHS().getRational() == 0,
              "processRealEq invariant violated");
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
    DebugAssert(right[0].isRational(), "Expected first term to be rational");
    for(int i = 1, iend = right.arity(); i < iend; ++i) {
      Expr c = right[i];
      DebugAssert(!isRational(c), "Expected non-rational");
      if(!isInteger(c))  {
        if (isLeaf(c) ||
            ((isMult(c) && c.arity() == 2 && isLeaf(c[1])))) {
          Expr leaf = isLeaf(c) ? c : c[1];
          int j;
          for (j = 1; j < iend; ++j) {
            if (j!= i
		&& isLeafIn(leaf, right[j])
		) {
              break;
            }
          }
          if (j == iend) {
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
    // The only way we can not get an isolated in the reals is if all of them
    // are non-linear. In this case we might have some integers to solve for
    // so we try that. The integer solver shouldn't be able to solve for the
    // reals, as they are not solvable and we should be safe. One of such 
    // examples is if some constant ITE got skolemized and we have an equation
    // like SKOLEM = x^2 (bug79), in which case we should solve for the SKOLEM
	// where skolem is an INT variable.
    if (isNonlinearEq(eqn.getExpr()))
      return processIntEq(eqn);
    else throw
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
              "TheoryArithOld::ProcessRealEq: left is integer:\n left = "
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


void TheoryArithOld::getFactors(const Expr& e, set<Expr>& factors)
{
  switch (e.getKind()) {
    case RATIONAL_EXPR: break;
    case MULT: {
      Expr::iterator i = e.begin(), iend = e.end();
      for (; i != iend; ++i) {
        getFactors(*i, factors);
      }
      break;
    }
    case POW: {
      DebugAssert(e.arity() == 2, "invariant violated");
      if (!isIntegerConst(e[0]) || e[0].getRational() <= 0) {
        throw ArithException("not positive integer exponent in "+e.toString());
      }
      if (isLeaf(e[1])) factors.insert(e[1]);
      break;
    }
    default: {
      DebugAssert(isLeaf(e), "expected leaf");
      DebugAssert(factors.find(e) == factors.end(), "expected new entry");
      factors.insert(e);
      break;
    }
  }
}


/*!
 * \param eqn is a single equation 0 = e
 * \return an equivalent Theorem (x = t AND 0 = e'), or just x = t
 */
Theorem
TheoryArithOld::processSimpleIntEq(const Theorem& eqn)
{
  TRACE("arith eq", "processSimpleIntEq(", eqn.getExpr(), ") {");
  DebugAssert(eqn.isRewrite(),
              "TheoryArithOld::processSimpleIntEq: eqn must be equality" +
              eqn.getExpr().toString());

  Expr right = eqn.getRHS();

  DebugAssert(eqn.getLHS().isRational() && 0 == eqn.getLHS().getRational(),
              "TheoryArithOld::processSimpleIntEq: LHS must be 0:\n" +
              eqn.getExpr().toString());

  DebugAssert(!isMult(right) && !isPow(right), "should have been handled above");
  if (isPlus(right)) {
    if (2 == right.arity() &&
        (isLeaf(right[1]) ||
         (isMult(right[1]) && right[1].arity() == 2 && right[1][0].isRational() && isLeaf(right[1][1])))) {
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
    // Pick a suitable monomial. isolated can be of the form x, a.x, -a.x
    Expr isolated;
    bool nonlin;
    if (pickIntEqMonomial(right, isolated, nonlin)) {
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
      } else if (!nonlin) {
        DebugAssert(isMult(isolated) && isolated[0].getRational() >= 2,
                    "TheoryArithOld::processSimpleIntEq: isolated must be mult "
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
    }
    throw
      ArithException("Can't find a leaf for solve in "+eqn.toString());
  } else {
    // eqn is 0 = x.  Flip it and return
    Theorem result = symmetryRule(eqn);
    TRACE("arith eq", "processSimpleIntEq[x = 0] => ", result, " }");
    return result;
  }
}

/*! input is 0=e' Theorem and all of the vars in e' are of
 * type INT. isolate one of them and send back to framework. output
 * is "var = e''" Theorem and some associated equations in
 * solved form.
 */
Theorem
TheoryArithOld::processIntEq(const Theorem& eqn)
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
    else if (result.getExpr().isBoolConst()) {
      done = true;
    }
    else {
      DebugAssert(result.getExpr().isAnd() && result.getExpr().arity() == 2,
		  "TheoryArithOld::processIntEq("+eqn.getExpr().toString()
		  +")\n result = "+result.getExpr().toString());
      solvedAndNewEqs.push_back(getCommonRules()->andElim(result, 0));
      newEq = getCommonRules()->andElim(result, 1);
    }
  } while(!done);
  Theorem res;
  if (result.getExpr().isFalse()) res = result;
  else if (solvedAndNewEqs.size() > 0)
    res = solvedForm(solvedAndNewEqs);
  else res = result;
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
TheoryArithOld::solvedForm(const vector<Theorem>& solvedEqs)
{
  DebugAssert(solvedEqs.size() > 0, "TheoryArithOld::solvedForm()");

  // Trace code
  TRACE_MSG("arith eq", "TheoryArithOld::solvedForm:solvedEqs(\n  [");
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
		  "TheoryArithOld::solvedForm: an element of solvedEqs must "
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

  if (thms.size() > 1) return getCommonRules()->andIntro(thms);
  else return thms.back();
}


/*!
 * ASSUMPTION: 't' is a fully canonized arithmetic term, and every
 * element of subst is a fully canonized equation of the form x=e,
 * indexed by the LHS variable.
 */

Theorem
TheoryArithOld::substAndCanonize(const Expr& t, ExprMap<Theorem>& subst)
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
TheoryArithOld::substAndCanonize(const Theorem& eq, ExprMap<Theorem>& subst)
{
  // Quick and dirty check: return immediately if subst is empty
  if(subst.empty()) return eq;

  DebugAssert(eq.isRewrite(), "TheoryArithOld::substAndCanonize: t = "
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

void TheoryArithOld::processBuffer()
{
  // Process the inequalities in the buffer
  bool varOnRHS;

  // If we are in difference logic only, just return
  if (diffLogicOnly) return;

  while (!inconsistent() && (d_bufferIdx_0 < d_buffer_0.size() || d_bufferIdx_1 < d_buffer_1.size() || d_bufferIdx_2 < d_buffer_2.size() ||  d_bufferIdx_3 < d_buffer_3.size())) {

	  // Get the unprojected inequality
	  Theorem ineqThm;
	  if (d_bufferIdx_0 < d_buffer_0.size()) {
		  ineqThm = d_buffer_0[d_bufferIdx_0];
	  	  d_bufferIdx_0 = d_bufferIdx_0 + 1;
	  } else if (d_bufferIdx_1 < d_buffer_1.size()) {
		  ineqThm = d_buffer_1[d_bufferIdx_1];
		  d_bufferIdx_1 = d_bufferIdx_1 + 1;
	  } else if (d_bufferIdx_2 < d_buffer_2.size()) {
		  ineqThm = d_buffer_2[d_bufferIdx_2];
		  d_bufferIdx_2 = d_bufferIdx_2 + 1;
	  } else {
		  ineqThm = d_buffer_3[d_bufferIdx_3];
		  d_bufferIdx_3 = d_bufferIdx_3 + 1;
	  }

//    // Skip this inequality if it is stale
//    if(isStale(ineqThm.getExpr())) {
//    	TRACE("arith buffer", "processBuffer(", ineqThm.getExpr(), ")... skipping stale");
//    	continue;
//    }
    // Dejan: project the finds, not the originals (if not projected already)
    const Expr& inequality = ineqThm.getExpr();
    Theorem inequalityFindThm = inequalityToFind(ineqThm, true);
    Expr inequalityFind = inequalityFindThm.getExpr();
//    if (inequality != inequalityFind)
//    	enqueueFact(inequalityFindThm);

    TRACE("arith buffer", "processing: ", inequality, "");
    TRACE("arith buffer", "with find : ", inequalityFind, "");

    if (!isIneq(inequalityFind)) {
    	TRACE("arith buffer", "find not an inequality... ", "", "skipping");
    	continue;
    }

    if (alreadyProjected.find(inequalityFind) != alreadyProjected.end()) {
    	TRACE("arith buffer", "already projected ... ", "", "skipping");
    	continue;
    }


    // We put the dummy for now, isolate variable will set it properly (or the find's one)
    // This one is just if the find is different. If the find is different
    // We will not check it again in update, so we're fine
	Expr dummy;
    alreadyProjected[inequality] = dummy;
    if (inequality != inequalityFind) {

    	alreadyProjected[inequalityFind] = dummy;

    	Expr rhs = inequalityFind[1];

    	// Collect the statistics about variables
    	if(isPlus(rhs)) {
    	    for(Expr::iterator i=rhs.begin(), iend=rhs.end(); i!=iend; ++i) {
    	    	Expr monomial = *i;
    	    	updateStats(monomial);
    	    }
    	} else // It's a monomial
    	    updateStats(rhs);
    }

    // See if this one is subsumed by a stronger inequality
    // c1 <= t1, t2 <= c2
    Rational c1, c2;
    Expr t1, t2;
    // Every term in the buffer has to have a lower bound set!!!
    // Except for the ones that changed the find
    extractTermsFromInequality(inequalityFind, c1, t1, c2, t2);
    if (termLowerBound.find(t1) != termLowerBound.end() && c1 != termLowerBound[t1]) {
    	TRACE("arith ineq", "skipping because stronger bounds asserted ", inequalityFind.toString(), ":" + t1.toString());
    	DebugAssert(termLowerBoundThm.find(t1) != termLowerBoundThm.end(), "No lower bound on asserted atom!!! " + t1.toString());
	   	Theorem strongerBound = termLowerBoundThm[t1];
	   	//enqueueFact(d_rules->implyWeakerInequality(strongerBound.getExpr(), inequalityFindThm.getExpr()));
	   	continue;
    }

    Theorem thm1 = isolateVariable(inequalityFindThm, varOnRHS);
    const Expr& ineq = thm1.getExpr();
    if (ineq.isFalse())
      setInconsistent(thm1);
    else
    	if(!ineq.isTrue()) {

    		// Check that the variable is indeed isolated correctly
    		DebugAssert(varOnRHS? !isPlus(ineq[1]) : !isPlus(ineq[0]), "TheoryArithOld::processBuffer(): bad result from isolateVariable:\nineq = "+ineq.toString());
    		// and project the inequality
    		projectInequalities(thm1, varOnRHS);
    	}
  	}
}


void TheoryArithOld::updateStats(const Rational& c, const Expr& v)
{
  TRACE("arith stats", "updateStats("+c.toString()+", ", v, ")");

  // we can get numbers as checking for variables is not possible (nonlinear stuff)
  if (v.isRational()) return;

  if (v.getType() != d_realType) {
	  // Dejan: update the max coefficient of the variable
	  if (c < 0) {
		  // Goes to the left side
		  ExprMap<Rational>::iterator maxFind = maxCoefficientLeft.find(v);
		  if (maxFind == maxCoefficientLeft.end()) {
			  maxCoefficientLeft[v] = - c;
			  TRACE("arith stats", "max left", "", "");
		  }
		  else
			  if ((*maxFind).second < -c) {
				  TRACE("arith stats", "max left", "", "");
				  maxCoefficientLeft[v] = -c;
			  }
	  } else {
		  // Stays on the right side
		  ExprMap<Rational>::iterator maxFind = maxCoefficientRight.find(v);
		  if (maxFind == maxCoefficientRight.end()) {
			  maxCoefficientRight[v] = c;
			  TRACE("arith stats", "max right", "", "");
		  }
		  else
			  if((*maxFind).second < c) {
				  TRACE("arith stats", "max right", "", "");
				  maxCoefficientRight[v] = c;
			  }
	  }
  }

  if(c > 0) {
    if(d_countRight.count(v) > 0) d_countRight[v] = d_countRight[v] + 1;
    else d_countRight[v] = 1;
  }
  else
    if(d_countLeft.count(v) > 0) d_countLeft[v] = d_countLeft[v] + 1;
    else d_countLeft[v] = 1;
}


void TheoryArithOld::updateStats(const Expr& monomial)
{
  Expr c, m;
  separateMonomial(monomial, c, m);
  updateStats(c.getRational(), m);
}

int TheoryArithOld::extractTermsFromInequality(const Expr& inequality,
		Rational& c1, Expr& t1,
		Rational& c2, Expr& t2) {

	TRACE("arith extract", "extract(", inequality.toString(), ")");

	DebugAssert(isIneq(inequality), "extractTermsFromInequality: expexting an inequality got: " + inequality.getString() + ")");

	Expr rhs = inequality[1];

	c1 = 0;

	// Extract the non-constant term (both sides)
	vector<Expr> positive_children, negative_children;
	if (isPlus(rhs)) {
		  int start_i = 0;
		  if (rhs[0].isRational()) {
			  start_i = 1;
			  c1 = -rhs[0].getRational();
		  }
		  int end_i   = rhs.arity();
		    for(int i = start_i; i < end_i; i ++) {
		  	  const Expr& term = rhs[i];
		  	  positive_children.push_back(term);
		  	  negative_children.push_back(canon(multExpr(rat(-1),term)).getRHS());
		    }
	  } else {
	  	  positive_children.push_back(rhs);
		  negative_children.push_back(canon(multExpr(rat(-1), rhs)).getRHS());
	  }

	  int num_vars = positive_children.size();

	  // c1 <= t1
	  t1 = (num_vars > 1 ? canon(plusExpr(positive_children)).getRHS() : positive_children[0]);

	  // c2 is the upper bound on t2 : t2 <= c2
	  c2 = -c1;
	  t2 = (num_vars > 1 ? canon(plusExpr(negative_children)).getRHS() : negative_children[0]);

	  TRACE("arith extract", "extract: ", c1.toString() + " <= ", t1.toString());

	  return num_vars;
}

bool TheoryArithOld::addToBuffer(const Theorem& thm, bool priority) {

  TRACE("arith buffer", "addToBuffer(", thm.getExpr().toString(), ")");

  Expr ineq = thm.getExpr();
  const Expr& rhs = thm.getExpr()[1];

  bool nonLinear = false;
  Rational nonLinearConstant = 0;
  Expr compactNonLinear;
  Theorem compactNonLinearThm;

  // Collect the statistics about variables and check for non-linearity
  if(isPlus(rhs)) {
    for(Expr::iterator i=rhs.begin(), iend=rhs.end(); i!=iend; ++i) {
    	Expr monomial = *i;
    	updateStats(monomial);
    	// check for non-linear
    	if (isMult(monomial)) {
    		if ((monomial[0].isRational() && monomial.arity() >= 3) ||
    			(!monomial[0].isRational() && monomial.arity() >= 2) ||
    			(monomial.arity() == 2 && isPow(monomial[1])))
    			nonLinear = true;
    	}
    }
    if (nonLinear) {
    	compactNonLinearThm = d_rules->compactNonLinearTerm(rhs);
    	compactNonLinear = compactNonLinearThm.getRHS();
    }
  }
  else // It's a monomial
  {
    updateStats(rhs);
	if (isMult(rhs))
		if ((rhs[0].isRational() && rhs.arity() >= 3)
				|| (!rhs[0].isRational() && rhs.arity() >= 2)
				|| (rhs.arity() == 2 && isPow(rhs[1]))) {
			nonLinear = true;
			compactNonLinear = rhs;
			compactNonLinearThm = reflexivityRule(compactNonLinear);
		}
  }

  if (bufferedInequalities.find(ineq) != bufferedInequalities.end()) {
	  TRACE("arith buffer", "addToBuffer()", "", "... already in db");
	  if (formulaAtoms.find(ineq) != formulaAtoms.end()) {
		  TRACE("arith buffer", "it's a formula atom, enqueuing.", "", "");
		  enqueueFact(thm);
	  }
	  return false;
  }

  if (nonLinear && (isMult(rhs) || compactNonLinear != rhs)) {
	  TRACE("arith nonlinear", "compact version of ", rhs, " is " + compactNonLinear.toString());
	  // Replace the rhs with the compacted nonlinear term
	  Theorem thm1 = (compactNonLinear != rhs ?
			  iffMP(thm, substitutivityRule(ineq, 1, compactNonLinearThm)) : thm);
	  // Now, try to deduce the signednes of multipliers
	  Rational c = (isMult(rhs) ? 0 : compactNonLinear[0].getRational());
	  // We can deduct the signs if the constant is not bigger than 0
	  if (c <= 0) {
		  thm1 = d_rules->nonLinearIneqSignSplit(thm1);
		  TRACE("arith nonlinear", "spliting on signs : ", thm1.getExpr(), "");
		  enqueueFact(thm1);
	  }
  }

  // Get c1, c2, t1, t2 such that c1 <= t1 and t2 <= c2
  Expr t1, t2;
  Rational c1, c2;
  int num_vars = extractTermsFromInequality(ineq, c1, t1, c2, t2);

  // If 2 variable, do add to difference logic (allways, just in case)
  bool factIsDiffLogic = false;
  if (num_vars <= 2) {

	  TRACE("arith diff", t2, " < ", c2);
  	  // c1 <= t1, check if difference logic
  	  // t1 of the form 0 + ax + by
  	  Expr ax = (num_vars == 2 ? t2[1] : t2);
  	  Expr a_expr, x;
  	  separateMonomial(ax, a_expr, x);
  	  Rational a = a_expr.getRational();
  	  Expr by = (num_vars == 2 ? t2[2] : (a < 0 ? zero : rat(-1)*zero));
  	  Expr b_expr, y;
  	  separateMonomial(by, b_expr, y);
  	  Rational b = b_expr.getRational();

  	  // Check for non-linear
  	  if (!isLeaf(x) || !isLeaf(y))
  		  setIncomplete("Non-linear arithmetic inequalities");

  	  if (a == 1 && b == -1) {
  		  diffLogicGraph.addEdge(x, y, c2, thm);
  		  factIsDiffLogic = true;
  	  }
  	  else if (a == -1 && b == 1) {
  		  diffLogicGraph.addEdge(y, x, c2, thm);
  		  factIsDiffLogic = true;
  	  }
  	  // Not difference logic, put it in the 3 or more vars buffer
  	  else {
  		  diffLogicOnly = false;
  		  TRACE("arith diff", "not diff logic", thm.getExpr().toString(), "");
  	  }

  	  if (diffLogicGraph.isUnsat()) {
  		  TRACE("diff unsat", "UNSAT", " : ", diffLogicGraph.getUnsatTheorem());
  		  setInconsistent(diffLogicGraph.getUnsatTheorem());
  		  return false;
  	  }
  } else {
	  diffLogicOnly = false;
	  TRACE("arith diff", "not diff logic", thm.getExpr().toString(), "");
  }

  // For now we treat all the bound as LE, weaker
  CDMap<Expr, Rational>::iterator find_lower = termLowerBound.find(t1);
  if (find_lower != termLowerBound.end()) {
	  // found bound c <= t1
	  Rational found_c = (*find_lower).second;
	  // If found c is bigger than the new one, we are done
	  if (c1 <= found_c && !(found_c == c1 && ineq.getKind() == LT)) {
		  TRACE("arith buffer", "addToBuffer()", "", "... lower_bound subsumed");
		  // Removed assert. Can happen that an atom is not asserted yet, and get's implied as
		  // a formula atom and then asserted here. it's fine
		  //DebugAssert(!thm.isAssump(), "Should have been propagated: " + ineq.toString() + "");
		  return false;
	  } else {
		  Theorem oldLowerBound = termLowerBoundThm[t1];
		  Expr oldIneq = oldLowerBound.getExpr();
		  if (formulaAtoms.find(oldIneq) != formulaAtoms.end())
			  enqueueFact(getCommonRules()->implMP(thm, d_rules->implyWeakerInequality(ineq, oldIneq)));
		  termLowerBound[t1] = c1;
		  termLowerBoundThm[t1] = thm;
	  }
  } else {
	  termLowerBound[t1] = c1;
	  termLowerBoundThm[t1] = thm;
  }

  CDMap<Expr, Rational>::iterator find_upper = termUpperBound.find(t2);
  if (find_upper != termUpperBound.end()) {
	  // found bound t2 <= c
	  Rational found_c = (*find_upper).second;
	  // If found c is smaller than the new one, we are done
	  if (found_c <= c2 && !(found_c == c2 && ineq.getKind() == LT)) {
		  TRACE("arith buffer", "addToBuffer()", "", "... upper_bound subsumed");
		  //DebugAssert(!thm.isAssump(), "Should have been propagated: " + ineq.toString() + "");
		  return false;
	  } else {
		  termUpperBound[t2] = c2;
		  termUpperBoundThm[t2] = thm;
	  }
  } else {
	  termUpperBound[t2] = c2;
	  termUpperBoundThm[t2] = thm;
  }

  // See if the bounds on the term can infer conflict or equality
  if (termUpperBound.find(t1) != termUpperBound.end() &&
      termLowerBound.find(t1) != termLowerBound.end() &&
      termUpperBound[t1] <= termLowerBound[t1]) {
	  Theorem thm1 = termUpperBoundThm[t1];
	  Theorem thm2 = termLowerBoundThm[t1];
	  TRACE("arith propagate", "adding inequalities: ", thm1.getExpr().toString(), " with " + thm2.getExpr().toString());
	  enqueueFact(d_rules->addInequalities(thm1, thm2));
  } else
  if (termUpperBound.find(t2) != termUpperBound.end() &&
        termLowerBound.find(t2) != termLowerBound.end() &&
        termUpperBound[t2] <= termLowerBound[t2]) {
	  Theorem thm1 = termUpperBoundThm[t2];
	  Theorem thm2 = termLowerBoundThm[t2];
	  TRACE("arith propagate", "adding inequalities: ", thm1.getExpr().toString(), " with " + thm2.getExpr().toString());
  	  enqueueFact(d_rules->addInequalities(thm1, thm2));
  }

  if (true) {
	  // See if we can propagate anything to the formula atoms
	  // c1 <= t1 ===> c <= t1 for c < c1
	  AtomsMap::iterator find     = formulaAtomLowerBound.find(t1);
	  AtomsMap::iterator find_end = formulaAtomLowerBound.end();
	  if (find != find_end) {
	  	  set< pair<Rational, Expr> >::iterator bounds     = (*find).second.begin();
	  	  set< pair<Rational, Expr> >::iterator bounds_end = (*find).second.end();
	  	  while (bounds != bounds_end) {
	  		  TRACE("arith atoms", "trying propagation", ineq, (*bounds).second);
	  		  const Expr& implied = (*bounds).second;
	  		  // Try to do some theory propagation
	  		  if ((*bounds).first < c1 || (!(ineq.getKind() == LE && implied.getKind() == LT) && (*bounds).first == c1)) {
	  			  // c1 <= t1 => c <= t1 (for c <= c1)
	  			  // c1 < t1  => c <= t1 (for c <= c1)
	  			  // c1 <= t1 => c < t1  (for c < c1)
	  			  Theorem impliedThm = getCommonRules()->implMP(thm, d_rules->implyWeakerInequality(ineq, implied));
	  			  enqueueFact(impliedThm);
	  		  }
	  		  bounds ++;
	  	  }
	  }

	  //
	  // c1 <= t1 ==> !(t1 <= c) for c < c1
	  //          ==> !(-c <= t2)
	  // i.e. all coefficient in in the implied are opposite of t1
	  find     = formulaAtomUpperBound.find(t1);
	  find_end = formulaAtomUpperBound.end();
	  if (find != find_end) {
	   	  set< pair<Rational, Expr> >::iterator bounds     = (*find).second.begin();
	   	  set< pair<Rational, Expr> >::iterator bounds_end = (*find).second.end();
	   	  while (bounds != bounds_end) {
	   		  TRACE("arith atoms", "trying propagation", ineq, (*bounds).second);
	   		  const Expr& implied = (*bounds).second;
	   		  // Try to do some theory propagation
	   		  if ((*bounds).first < c1) {
	   			  Theorem impliedThm = getCommonRules()->implMP(thm, d_rules->implyNegatedInequality(ineq, implied));
	   			  enqueueFact(impliedThm);
	   		  }
	   		  bounds ++;
	   	  }
	  }
  }

  // Register this as a resource
  theoryCore()->getResource();

  // If out of resources, bail out
  if (theoryCore()->outOfResources()) return false;

  // Checking because we could have projected it as a find of some other
  // equation
  if (alreadyProjected.find(ineq) == alreadyProjected.end()) {
	  // We buffer it if it's not marked for not buffering
	  if (dontBuffer.find(ineq) == dontBuffer.end()) {
		  // We give priority to the one that can produce a conflict
		  if (priority)
			  d_buffer_0.push_back(thm);
		  else {
			  // Push it into the buffer (one var)
			  if (num_vars == 1) d_buffer_1.push_back(thm);
			  else if (num_vars == 2) d_buffer_2.push_back(thm);
			  else d_buffer_3.push_back(thm);
		  }

		  if (factIsDiffLogic) diff_logic_size = diff_logic_size + 1;
	  }
  }

  // Remember that it's in the buffer
  bufferedInequalities[ineq] = thm;

  // Since we care about this atom, lets set it up
  if (!ineq.hasFind())
	  theoryCore()->setupTerm(ineq, this, thm);

  return true;
}


Theorem TheoryArithOld::isolateVariable(const Theorem& inputThm,
                                     bool& isolatedVarOnRHS)
{
  Theorem result(inputThm);
  const Expr& e = inputThm.getExpr();
  TRACE("arith","isolateVariable(",e,") {");
  TRACE("arith ineq", "isolateVariable(", e, ") {");
  //we assume all the children of e are canonized
  DebugAssert(isLT(e)||isLE(e),
              "TheoryArithOld::isolateVariable: " + e.toString() +
              " wrong kind");
  int kind = e.getKind();
  DebugAssert(e[0].isRational() && e[0].getRational() == 0,
              "TheoryArithOld::isolateVariable: theorem must be of "
              "the form 0 < rhs: " + inputThm.toString());

  const Expr& zero = e[0];
  Expr right = e[1];
  // Check for trivial in-equation.
  if (right.isRational()) {
    result = iffMP(result, d_rules->constPredicate(e));
    TRACE("arith ineq","isolateVariable => ",result.getExpr()," }");
    TRACE("arith","isolateVariable => ",result," }");
    return result;
  }

  // Normalization of inequality to make coefficients integer and
  // relatively prime.

  Expr factor(computeNormalFactor(right, false));
  TRACE("arith", "isolateVariable: factor = ", factor, "");
  DebugAssert(factor.getRational() > 0,
              "isolateVariable: factor="+factor.toString());
  // Now multiply the inequality by the factor, unless it is 1
  if(factor.getRational() != 1) {
    result = iffMP(result, d_rules->multIneqn(e, factor));
    // And canonize the result
    result = canonPred(result);
    result = rafineInequalityToInteger(result);
    right = result.getExpr()[1];
  }

  // Find monomial to isolate and store it in isolatedMonomial
  Expr isolatedMonomial = right;

  if (isPlus(right))
    isolatedMonomial = pickMonomial(right);

  TRACE("arith ineq", "isolatedMonomial => ",isolatedMonomial,"");

  // Set the correct isolated monomial
  // Now, if something gets updated, but this monomial is not changed, we don't
  // Have to rebuffer it as the projection will still be accurate when updated
  alreadyProjected[e] = isolatedMonomial;

  Rational r = -1;
  isolatedVarOnRHS = true;
  if (isMult(isolatedMonomial)) {
	  r = ((isolatedMonomial[0].getRational()) >= 0)? -1 : 1;
	  isolatedVarOnRHS =
		  ((isolatedMonomial[0].getRational()) >= 0)? true : false;
  }
  isolatedMonomial = canon(rat(-1)*isolatedMonomial).getRHS();
  TRACE("arith ineq", "-(isolatedMonomial) => ",isolatedMonomial,"");
    // Isolate isolatedMonomial on to the LHS
  result = iffMP(result, d_rules->plusPredicate(zero, right,
                                                isolatedMonomial, kind));
  // Canonize the resulting inequality
  TRACE("arith ineq", "resutl => ",result,"");
    result = canonPred(result);
  if(1 != r) {
    result = iffMP(result, d_rules->multIneqn(result.getExpr(), rat(r)));
    result = canonPred(result);
  }
  TRACE("arith ineq","isolateVariable => ",result.getExpr()," }");
  TRACE("arith","isolateVariable => ",result," }");
  return result;
}

Expr
TheoryArithOld::computeNormalFactor(const Expr& right, bool normalizeConstants) {
  // Strategy: compute f = lcm(d1...dn)/gcd(c1...cn), where the RHS is
  // of the form c1/d1*x1 + ... + cn/dn*xn
  Rational factor;
  if(isPlus(right)) {
    vector<Rational> nums, denoms;
    for(int i=0, iend=right.arity(); i<iend; ++i) {
      switch(right[i].getKind()) {
      case RATIONAL_EXPR:
      if (normalizeConstants)  {
        Rational c(abs(right[i].getRational()));
        nums.push_back(c.getNumerator());
        denoms.push_back(c.getDenominator());
        break;
        }
    	  break;
      case MULT: {
        Rational c(abs(right[i][0].getRational()));
        nums.push_back(c.getNumerator());
        denoms.push_back(c.getDenominator());
        break;
        }
      default: // it's a variable
        nums.push_back(1);
        denoms.push_back(1);
        break;
      }
    }
    Rational gcd_nums = gcd(nums);
    // x/0 == 0 in our model, as a total extension of arithmetic.  The
    // particular value of x/0 is irrelevant, since the DP is guarded
    // by the top-level TCCs, and it is safe to return any value in
    // cases when terms are undefined.
    factor = (gcd_nums==0)? 0 : (lcm(denoms) / gcd_nums);
  } else if(isMult(right)) {
    const Rational& r = right[0].getRational();
    factor = (r==0)? 0 : (1/abs(r));
  }
  else
    factor = 1;
  return rat(factor);
}


bool TheoryArithOld::lessThanVar(const Expr& isolatedMonomial, const Expr& var2)
{
  DebugAssert(!isRational(var2) && !isRational(isolatedMonomial),
              "TheoryArithOld::findMaxVar: isolatedMonomial cannot be rational" +
              isolatedMonomial.toString());
  Expr c, var0, var1;
  separateMonomial(isolatedMonomial, c, var0);
  separateMonomial(var2, c, var1);
  return var0 < var1;
}

/*! "Stale" means it contains non-simplified subexpressions.  For
 *  terms, it checks the expression's find pointer; for formulas it
 *  checks the children recursively (no caching!).  So, apply it with
 *  caution, and only to simple atomic formulas (like inequality).
 */
bool TheoryArithOld::isStale(const Expr& e) {
  if(e.isTerm())
    return e != find(e).getRHS();
  // It's better be a simple predicate (like inequality); we check the
  // kids recursively
  bool stale=false;
  for(Expr::iterator i=e.begin(), iend=e.end(); !stale && i!=iend; ++i)
    stale = isStale(*i);
  return stale;
}


bool TheoryArithOld::isStale(const TheoryArithOld::Ineq& ineq) {
  TRACE("arith stale", "isStale(", ineq, ") {");
  const Expr& ineqExpr = ineq.ineq().getExpr();
  const Rational& c = freeConstIneq(ineqExpr, ineq.varOnRHS());
  bool strict(isLT(ineqExpr));
  const FreeConst& fc = ineq.getConst();

  bool subsumed;

  if (ineqExpr.hasFind() && find(ineqExpr[1]).getRHS() != ineqExpr[1])
	  return true;

  if(ineq.varOnRHS()) {
    subsumed = (c < fc.getConst() ||
		(c == fc.getConst() && !strict && fc.strict()));
  } else {
    subsumed = (c > fc.getConst() ||
		(c == fc.getConst() && strict && !fc.strict()));
  }

  bool res;
  if(subsumed) {
    res = true;
    TRACE("arith ineq", "isStale[subsumed] => ", res? "true" : "false", " }");
  }
  else {
    res = isStale(ineqExpr);
    TRACE("arith ineq", "isStale[updated] => ", res? "true" : "false", " }");
  }
  return res;
}


void TheoryArithOld::separateMonomial(const Expr& e, Expr& c, Expr& var) {
  TRACE("separateMonomial", "separateMonomial(", e, ")");
  DebugAssert(!isPlus(e),
	      "TheoryArithOld::separateMonomial(e = "+e.toString()+")");
  if(isMult(e)) {
    DebugAssert(e.arity() >= 2,
		"TheoryArithOld::separateMonomial(e = "+e.toString()+")");
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
  DebugAssert(c.isRational(), "TheoryArithOld::separateMonomial(e = "
	      +e.toString()+", c = "+c.toString()+")");
  DebugAssert(!isMult(var) || (var[0].isRational() && var[0].getRational()==1),
	      "TheoryArithOld::separateMonomial(e = "
	      +e.toString()+", var = "+var.toString()+")");
}


void TheoryArithOld::projectInequalities(const Theorem& theInequality,
                                      bool isolatedVarOnRHS)
{

	TRACE("arith project", "projectInequalities(", theInequality.getExpr(),
        ", isolatedVarOnRHS="+string(isolatedVarOnRHS? "true" : "false")
        +") {");
	DebugAssert(isLE(theInequality.getExpr()) ||
              isLT(theInequality.getExpr()),
              "TheoryArithOld::projectIsolatedVar: "\
              "theInequality is of the wrong form: " +
              theInequality.toString());

	//TODO: DebugAssert to check if the isolatedMonomial is of the right
	//form and the whether we are indeed getting inequalities.
	Theorem theIneqThm(theInequality);
	Expr theIneq = theIneqThm.getExpr();

	// If the inequality is strict and integer, change it to non-strict
	if(isLT(theIneq)) {
		Theorem isIntLHS(isIntegerThm(theIneq[0]));
		Theorem isIntRHS(isIntegerThm(theIneq[1]));
		if ((!isIntLHS.isNull() && !isIntRHS.isNull())) {
			Theorem thm = d_rules->lessThanToLE(theInequality, isIntLHS, isIntRHS, !isolatedVarOnRHS);
			theIneqThm = canonPred(iffMP(theIneqThm, thm));
			theIneq = theIneqThm.getExpr();
		}
	}

	Expr isolatedMonomial = isolatedVarOnRHS ? theIneq[1] : theIneq[0];

	Expr monomialVar, a;
	separateMonomial(isolatedMonomial, a, monomialVar);

	bool subsumed;
	const FreeConst& bestConst = updateSubsumptionDB(theIneq, isolatedVarOnRHS, subsumed);

	if(subsumed) {
		IF_DEBUG(debugger.counter("subsumed inequalities")++;)
		TRACE("arith ineq", "subsumed inequality: ", theIneq, "");
	} else {
		// If the isolated variable is actually a non-linear term, we are
		// incomplete
		if(isMult(monomialVar) || isPow(monomialVar))
			setIncomplete("Non-linear arithmetic inequalities");

		// First, we need to make sure the isolated inequality is
		// setup properly.
		//    setupRec(theIneq[0]);
		//    setupRec(theIneq[1]);
		theoryCore()->setupTerm(theIneq[0], this, theIneqThm);
		theoryCore()->setupTerm(theIneq[1], this, theIneqThm);
		// Add the inequality into the appropriate DB.
		ExprMap<CDList<Ineq> *>& db1 = isolatedVarOnRHS ? d_inequalitiesRightDB : d_inequalitiesLeftDB;
		ExprMap<CDList<Ineq> *>::iterator it1 = db1.find(monomialVar);
		if(it1 == db1.end()) {
			CDList<Ineq> * list = new(true) CDList<Ineq>(theoryCore()->getCM()->getCurrentContext());
			list->push_back(Ineq(theIneqThm, isolatedVarOnRHS, bestConst));
			db1[monomialVar] = list;
		}
		else
			((*it1).second)->push_back(Ineq(theIneqThm, isolatedVarOnRHS, bestConst));

		ExprMap<CDList<Ineq> *>& db2 = isolatedVarOnRHS ? d_inequalitiesLeftDB : d_inequalitiesRightDB;
		ExprMap<CDList<Ineq> *>::iterator it = db2.find(monomialVar);
		if(it == db2.end()) {
			TRACE_MSG("arith ineq", "projectInequalities[not in DB] => }");
			return;
		}

		CDList<Ineq>& listOfDBIneqs = *((*it).second);
		Theorem betaLTt, tLTalpha, thm;
		for(int i = listOfDBIneqs.size() - 1; !inconsistent() && i >= 0; --i) {
			const Ineq& ineqEntry = listOfDBIneqs[i];
			const Theorem& ineqThm = ineqEntry.ineq(); //inequalityToFind(ineqEntry.ineq(), isolatedVarOnRHS);

			// ineqExntry might be stale

			if(!isStale(ineqEntry)) {
				betaLTt = isolatedVarOnRHS ? theIneqThm : ineqThm;
				tLTalpha = isolatedVarOnRHS ? ineqThm : theIneqThm;

				thm = normalizeProjectIneqs(betaLTt, tLTalpha);
				if (thm.isNull()) continue;

				IF_DEBUG(debugger.counter("real shadows")++;)

				// Check for TRUE and FALSE theorems
				Expr e(thm.getExpr());

				if(e.isFalse()) {
					setInconsistent(thm);
					TRACE_MSG("arith ineq", "projectInequalities[inconsistent] => }");
					return;
				}
				else {
					if(!e.isTrue() && !e.isEq()) {
						// setup the term so that it comes out in updates
						addToBuffer(thm, false);
					}
					else if(e.isEq())
						enqueueFact(thm);
				}
			} else {
				IF_DEBUG(debugger.counter("stale inequalities")++;)
			}
		}
	}

	TRACE_MSG("arith ineq", "projectInequalities => }");
}

Theorem TheoryArithOld::normalizeProjectIneqs(const Theorem& ineqThm1,
                                           const Theorem& ineqThm2)
{
  //ineq1 is of the form beta < b.x  or beta < x  [ or with <= ]
  //ineq2 is of the form a.x < alpha   or x < alpha.
  Theorem betaLTt = ineqThm1, tLTalpha = ineqThm2;
  Expr ineq1 = betaLTt.getExpr();
  Expr ineq2 = tLTalpha.getExpr();
  Expr c,x;
  separateMonomial(ineq2[0], c, x);
  Theorem isIntx(isIntegerThm(x));
  Theorem isIntBeta(isIntegerThm(ineq1[0]));
  Theorem isIntAlpha(isIntegerThm(ineq2[1]));
  bool isInt = !(isIntx.isNull() || isIntBeta.isNull() || isIntAlpha.isNull());

  TRACE("arith ineq", "normalizeProjectIneqs(", ineq1,
        ", "+ineq2.toString()+") {");
  DebugAssert((isLE(ineq1) || isLT(ineq1)) &&
              (isLE(ineq2) || isLT(ineq2)),
              "TheoryArithOld::normalizeProjectIneqs: Wrong Kind inputs: " +
              ineq1.toString() + ineq2.toString());
  DebugAssert(!isPlus(ineq1[1]) && !isPlus(ineq2[0]),
              "TheoryArithOld::normalizeProjectIneqs: Wrong Kind inputs: " +
              ineq1.toString() + ineq2.toString());

  //compute the factors to multiply the two inequalities with
  //so that they get the form beta < t and t < alpha.
  Rational factor1 = 1, factor2 = 1;
  Rational b = isMult(ineq1[1]) ? (ineq1[1])[0].getRational() : 1;
  Rational a = isMult(ineq2[0]) ? (ineq2[0])[0].getRational() : 1;
  if(b != a) {
    factor1 = a;
    factor2 = b;
  }

  //if the ineqs are of type int then apply one of the gray
  //dark shadow rules.
  // FIXME: intResult should also be checked for immediate
  // optimizations, as those below for 'result'.  Also, if intResult
  // is a single inequality, we may want to handle it similarly to the
  // 'result' rather than enqueuing directly.
  if(isInt && (a >= 2 || b >= 2)) {
    Theorem intResult;
    if(a <= b)
      intResult = d_rules->darkGrayShadow2ab(betaLTt, tLTalpha,
					     isIntAlpha, isIntBeta, isIntx);
    else
      intResult = d_rules->darkGrayShadow2ba(betaLTt, tLTalpha,
					     isIntAlpha, isIntBeta, isIntx);
	enqueueFact(intResult);
    // Fetch dark and gray shadows
    const Expr& DorG = intResult.getExpr();
    DebugAssert(DorG.isOr() && DorG.arity()==2, "DorG = "+DorG.toString());
    const Expr& G = DorG[1];
    DebugAssert(G.getKind()==GRAY_SHADOW, "G = "+G.toString());
    // Set the higher splitter priority for dark shadow
//    Expr tmp = simplifyExpr(D);
//    if (!tmp.isBoolConst())
//      addSplitter(tmp, 5);
    // Also set a higher priority to the NEGATION of GRAY_SHADOW
    Expr tmp = simplifyExpr(!G);
    if (!tmp.isBoolConst())
      addSplitter(tmp, 1);
    IF_DEBUG(debugger.counter("dark+gray shadows")++;)

    // Dejan: Let's forget about the real shadow, we are doing integers
//    /return intResult;
  }

  //actually normalize the inequalities
  if(1 != factor1) {
    Theorem thm2 = iffMP(betaLTt, d_rules->multIneqn(ineq1, rat(factor1)));
    betaLTt = canonPred(thm2);
    ineq1 = betaLTt.getExpr();
  }
  if(1 != factor2) {
    Theorem thm2 = iffMP(tLTalpha, d_rules->multIneqn(ineq2, rat(factor2)));
    tLTalpha = canonPred(thm2);
    ineq2 = tLTalpha.getExpr();
  }

  //IF_DEBUG(debugger.counter("real shadows")++;)

  Expr beta(ineq1[0]);
  Expr alpha(ineq2[1]);
  // In case of alpha <= t <= alpha, we generate t = alpha
  if(isLE(ineq1) && isLE(ineq2) && alpha == beta) {
    Theorem result = d_rules->realShadowEq(betaLTt, tLTalpha);
    TRACE("arith ineq", "normalizeProjectIneqs => ", result, " }");
    return result;
  }

  // Check if this inequality is a finite interval
//  if(isInt)
//    processFiniteInterval(betaLTt, tLTalpha);

//  // Only do the real shadow if a and b = 1
//  if (isInt && a > 1 && b > 1)
//	  return Theorem();

  //project the normalized inequalities.

  Theorem result = d_rules->realShadow(betaLTt, tLTalpha);

  // FIXME: Clark's changes.  Is 'rewrite' more or less efficient?
//   result = iffMP(result, rewrite(result.getExpr()));
//   TRACE("arith ineq", "normalizeProjectIneqs => ", result, " }");

  // Now, transform the result into 0 < rhs and see if rhs is a const
  Expr e(result.getExpr());
  // int kind = e.getKind();
  if(!(e[0].isRational() && e[0].getRational() == 0))
    result = iffMP(result, d_rules->rightMinusLeft(e));
  result = canonPred(result);

  //result is "0 kind e'". where e' is equal to canon(e[1]-e[0])
  Expr right = result.getExpr()[1];
  // Check for trivial inequality
  if (right.isRational())
    result = iffMP(result, d_rules->constPredicate(result.getExpr()));
  else
	result = normalize(result);
  TRACE("arith ineq", "normalizeProjectIneqs => ", result, " }");
  return result;
}

Rational TheoryArithOld::currentMaxCoefficient(Expr var)
{
	// We prefer real variables
	if (var.getType() == d_realType) return -100;

	// Find the biggest left side coefficient
	ExprMap<Rational>::iterator findMaxLeft = maxCoefficientLeft.find(var);
	Rational leftMax = -1;
	if (findMaxLeft != maxCoefficientLeft.end())
		leftMax = (*findMaxLeft).second;

	//
	ExprMap<Rational>::iterator findMaxRight = maxCoefficientRight.find(var);
	Rational rightMax = -1;
	if (findMaxRight != maxCoefficientRight.end())
		rightMax = (*findMaxRight).second;

	// What is the max coefficient
	// If one is undefined, dont take it. My first thought was to project away unbounded
	// ones, but it happens that you get another constraint on it later and the hell breaks
	// loose if they have big coefficients.
	Rational returnValue;
	if (leftMax == -1) returnValue = rightMax;
	else if (rightMax == -1) returnValue = leftMax;
	else if (leftMax < rightMax) returnValue = rightMax;
	else returnValue = leftMax;

	TRACE("arith stats", "max coeff of ", var.toString(), ": " + returnValue.toString() + "(left=" + leftMax.toString() + ",right=" + rightMax.toString());

	return returnValue;
}

void TheoryArithOld::fixCurrentMaxCoefficient(Expr var, Rational max) {
	fixedMaxCoefficient[var] = max;
}

void TheoryArithOld::selectSmallestByCoefficient(const vector<Expr>& input, vector<Expr>& output) {

	// Clear the output vector
	output.clear();

	// Get the first variable, and set it as best
	Expr best_variable = input[0];
	Rational best_coefficient = currentMaxCoefficient(best_variable);
	output.push_back(best_variable);

	for(unsigned int i = 1; i < input.size(); i ++) {

		// Get the current variable
		Expr current_variable = input[i];
		// Get the current variable's max coefficient
		Rational current_coefficient = currentMaxCoefficient(current_variable);

		// If strictly better than the current best, remember it
		if ((current_coefficient < best_coefficient)) {
			best_variable = current_variable;
			best_coefficient = current_coefficient;
			output.clear();
		}

		// If equal to the current best, push it to the stack (in 10% range)
		if (current_coefficient == best_coefficient)
			  output.push_back(current_variable);
	}

    // Fix the selected best coefficient
	//fixCurrentMaxCoefficient(best_variable, best_coefficient);
}

Expr TheoryArithOld::pickMonomial(const Expr& right)
{
  DebugAssert(isPlus(right), "TheoryArithOld::pickMonomial: Wrong Kind: " +
              right.toString());
  if(theoryCore()->getFlags()["var-order"].getBool()) {
    Expr::iterator i = right.begin();
    Expr isolatedMonomial = right[1];
    //PLUS always has at least two elements and the first element is
    //always a constant. hence ++i in the initialization of the for
    //loop.
    for(++i; i != right.end(); ++i)
      if(lessThanVar(isolatedMonomial,*i))
        isolatedMonomial = *i;
    return isolatedMonomial;
  }

  ExprMap<Expr> var2monomial;
  vector<Expr> vars;
  Expr::iterator i = right.begin(), iend = right.end();
  for(;i != iend; ++i) {
    if(i->isRational())
      continue;
    Expr c, var;
    separateMonomial(*i, c, var);
    var2monomial[var] = *i;
    vars.push_back(var);
  }

  vector<Expr> largest;
  d_graph.selectLargest(vars, largest);
  DebugAssert(0 < largest.size(),
              "TheoryArithOld::pickMonomial: selectLargest: failed!!!!");

  // DEJAN: Rafine the largest by coefficient values
  vector<Expr> largest_small_coeff;
  selectSmallestByCoefficient(largest, largest_small_coeff);
  DebugAssert(0 < largest_small_coeff.size(), "TheoryArithOld::pickMonomial: selectLargestByCOefficient: failed!!!!");

  size_t pickedVar = 0;
    // Pick the variable which will generate the fewest number of
    // projections

  size_t size = largest_small_coeff.size();
  int minProjections = -1;
  if (size > 1)
	for(size_t k=0; k< size; ++k) {
      const Expr& var(largest_small_coeff[k]), monom(var2monomial[var]);
      // Grab the counters for the variable
      int nRight = (d_countRight.count(var) > 0)? d_countRight[var] : 0;
      int nLeft = (d_countLeft.count(var) > 0)? d_countLeft[var] : 0;
      int n(nRight*nLeft);
      TRACE("arith ineq", "pickMonomial: var=", var,
            ", nRight="+int2string(nRight)+", nLeft="+int2string(nLeft));
      if(minProjections < 0 || minProjections > n) {
        minProjections = n;
        pickedVar = k;
      }
      TRACE("arith ineq", "Number of projections for "+var.toString()+" = ", n, "");
	}


  const Expr& largestVar = largest_small_coeff[pickedVar];
  // FIXME: TODO: update the counters (subtract counts for the vars
  // other than largestVar

  // Update the graph (all edges to the largest in the graph, not just the small coefficients).
  for(size_t k = 0; k < vars.size(); ++k) {
    if(vars[k] != largestVar)
      d_graph.addEdge(largestVar, vars[k]);
  }

  TRACE("arith buffer", "picked var : ", var2monomial[largestVar].toString(), "");

  return var2monomial[largestVar];
}

void TheoryArithOld::VarOrderGraph::addEdge(const Expr& e1, const Expr& e2)
{
  TRACE("arith var order", "addEdge("+e1.toString()+" > ", e2, ")");
  DebugAssert(e1 != e2, "TheoryArithOld::VarOrderGraph::addEdge("
	      +e1.toString()+", "+e2.toString()+")");
  d_edges[e1].push_back(e2);
}

//returns true if e1 < e2, else false(i.e e2 < e1 or e1,e2 are not
//comparable)
bool TheoryArithOld::VarOrderGraph::lessThan(const Expr& e1, const Expr& e2)
{
  d_cache.clear();
  //returns true if e1 is in the subtree rooted at e2 implying e1 < e2
  return dfs(e1,e2);
}

//returns true if e1 is in the subtree rooted at e2 implying e1 < e2
bool TheoryArithOld::VarOrderGraph::dfs(const Expr& e1, const Expr& e2)
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

void TheoryArithOld::VarOrderGraph::dfs(const Expr& v, vector<Expr>& output_list)
{
	TRACE("arith shared", "dfs(", v.toString(), ")");

	// If visited already we are done
	if (d_cache.count(v) > 0) return;

	// Dfs further
	if(d_edges.count(v) != 0) {
		// We have edges, so lets dfs it further
		vector<Expr>& vEdges = d_edges[v];
		vector<Expr>::iterator e = vEdges.begin();
		vector<Expr>::iterator e_end = vEdges.end();
		while (e != e_end) {
			dfs(*e, output_list);
			e ++;
		}
	}

	// Mark as visited and add to the output list
	d_cache[v] = true;
	output_list.push_back(v);
}

void TheoryArithOld::VarOrderGraph::getVerticesTopological(vector<Expr>& output_list)
{
	// Clear the cache
	d_cache.clear();
	output_list.clear();

	// Go through all the vertices and run a dfs from them
	ExprMap< vector<Expr> >::iterator v_it     = d_edges.begin();
	ExprMap< vector<Expr> >::iterator v_it_end = d_edges.end();
	while (v_it != v_it_end)
	{
		// Run dfs from this vertex
		dfs(v_it->first, output_list);
		// Go to the next one
		v_it ++;
	}
}

void TheoryArithOld::VarOrderGraph::selectSmallest(vector<Expr>& v1,
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


void TheoryArithOld::VarOrderGraph::selectLargest(const vector<Expr>& v1,
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
// TheoryArithOld Public Methods                                                //
///////////////////////////////////////////////////////////////////////////////


TheoryArithOld::TheoryArithOld(TheoryCore* core)
  : TheoryArith(core, "ArithmeticOld"),
    d_diseq(core->getCM()->getCurrentContext()),
    d_diseqIdx(core->getCM()->getCurrentContext(), 0, 0),
    diseqSplitAlready(core->getCM()->getCurrentContext()),
    d_inModelCreation(core->getCM()->getCurrentContext(), false, 0),
    d_freeConstDB(core->getCM()->getCurrentContext()),
    d_buffer_0(core->getCM()->getCurrentContext()),
    d_buffer_1(core->getCM()->getCurrentContext()),
    d_buffer_2(core->getCM()->getCurrentContext()),
    d_buffer_3(core->getCM()->getCurrentContext()),
        // Initialize index to 0 at scope 0
    d_bufferIdx_0(core->getCM()->getCurrentContext(), 0, 0),
    d_bufferIdx_1(core->getCM()->getCurrentContext(), 0, 0),
    d_bufferIdx_2(core->getCM()->getCurrentContext(), 0, 0),
    d_bufferIdx_3(core->getCM()->getCurrentContext(), 0, 0),
    diff_logic_size(core->getCM()->getCurrentContext(), 0, 0),
    d_bufferThres(&(core->getFlags()["ineq-delay"].getInt())),
    d_splitSign(&(core->getFlags()["nonlinear-sign-split"].getBool())),
    d_grayShadowThres(&(core->getFlags()["grayshadow-threshold"].getInt())),
    d_countRight(core->getCM()->getCurrentContext()),
    d_countLeft(core->getCM()->getCurrentContext()),
    d_sharedTerms(core->getCM()->getCurrentContext()),
    d_sharedTermsList(core->getCM()->getCurrentContext()),
    d_sharedVars(core->getCM()->getCurrentContext()),
    bufferedInequalities(core->getCM()->getCurrentContext()),
    termLowerBound(core->getCM()->getCurrentContext()),
    termLowerBoundThm(core->getCM()->getCurrentContext()),
    termUpperBound(core->getCM()->getCurrentContext()),
    termUpperBoundThm(core->getCM()->getCurrentContext()),
    alreadyProjected(core->getCM()->getCurrentContext()),
    dontBuffer(core->getCM()->getCurrentContext()),
    diffLogicOnly(core->getCM()->getCurrentContext(), true, 0),
    diffLogicGraph(0, core, 0, core->getCM()->getCurrentContext()),
    shared_index_1(core->getCM()->getCurrentContext(), 0, 0),
    shared_index_2(core->getCM()->getCurrentContext(), 0, 0),
    termUpperBounded(core->getCM()->getCurrentContext()),
    termLowerBounded(core->getCM()->getCurrentContext()),
    termConstrainedBelow(core->getCM()->getCurrentContext()),
    termConstrainedAbove(core->getCM()->getCurrentContext())
{
  IF_DEBUG(d_diseq.setName("CDList[TheoryArithOld::d_diseq]");)
  IF_DEBUG(d_buffer_0.setName("CDList[TheoryArithOld::d_buffer_0]");)
  IF_DEBUG(d_buffer_1.setName("CDList[TheoryArithOld::d_buffer_1]");)
  IF_DEBUG(d_buffer_2.setName("CDList[TheoryArithOld::d_buffer_2]");)
  IF_DEBUG(d_buffer_3.setName("CDList[TheoryArithOld::d_buffer_3]");)
  IF_DEBUG(d_bufferIdx_1.setName("CDList[TheoryArithOld::d_bufferIdx_0]");)
  IF_DEBUG(d_bufferIdx_1.setName("CDList[TheoryArithOld::d_bufferIdx_1]");)
  IF_DEBUG(d_bufferIdx_2.setName("CDList[TheoryArithOld::d_bufferIdx_2]");)
  IF_DEBUG(d_bufferIdx_3.setName("CDList[TheoryArithOld::d_bufferIdx_3]");)

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

  d_kinds.push_back(REAL);
  d_kinds.push_back(INT);
  d_kinds.push_back(SUBRANGE);
  d_kinds.push_back(IS_INTEGER);
  d_kinds.push_back(UMINUS);
  d_kinds.push_back(PLUS);
  d_kinds.push_back(MINUS);
  d_kinds.push_back(MULT);
  d_kinds.push_back(DIVIDE);
  d_kinds.push_back(POW);
  d_kinds.push_back(INTDIV);
  d_kinds.push_back(MOD);
  d_kinds.push_back(LT);
  d_kinds.push_back(LE);
  d_kinds.push_back(GT);
  d_kinds.push_back(GE);
  d_kinds.push_back(RATIONAL_EXPR);
  d_kinds.push_back(NEGINF);
  d_kinds.push_back(POSINF);
  d_kinds.push_back(DARK_SHADOW);
  d_kinds.push_back(GRAY_SHADOW);
  d_kinds.push_back(REAL_CONST);

  registerTheory(this, d_kinds, true);

  d_rules = createProofRulesOld();
  diffLogicGraph.setRules(d_rules);
  diffLogicGraph.setArith(this);

  d_realType = Type(getEM()->newLeafExpr(REAL));
  d_intType  = Type(getEM()->newLeafExpr(INT));

  // Make the zero variable
  Theorem thm_exists_zero = getCommonRules()->varIntroSkolem(rat(0));
  zero = thm_exists_zero.getExpr()[1];
}


// Destructor: delete the proof rules class if it's present
TheoryArithOld::~TheoryArithOld() {
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
  unregisterTheory(this, d_kinds, true);
}

void TheoryArithOld::collectVars(const Expr& e, vector<Expr>& vars,
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
TheoryArithOld::processFiniteInterval
(const Theorem& alphaLEax,
				   const Theorem& bxLEbeta) {
  const Expr& ineq1(alphaLEax.getExpr());
  const Expr& ineq2(bxLEbeta.getExpr());
  DebugAssert(isLE(ineq1), "TheoryArithOld::processFiniteInterval: ineq1 = "
	      +ineq1.toString());
  DebugAssert(isLE(ineq2), "TheoryArithOld::processFiniteInterval: ineq2 = "
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
	      "TheoryArithOld::processFiniteInterval:\n ax = "+ax.toString());
  DebugAssert(!isPlus(bx) && !isRational(bx),
	      "TheoryArithOld::processFiniteInterval:\n bx = "+bx.toString());
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
    if (d_sharedTerms.find(thm1.getExpr()[1]) != d_sharedTerms.end())
    	enqueueFact(d_rules->finiteInterval(thm1, tLEac, isInta, isIntt));
  }
}


void
TheoryArithOld::processFiniteIntervals(const Expr& x) {
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
TheoryArithOld::setupRec(const Expr& e) {
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


void TheoryArithOld::addSharedTerm(const Expr& e) {
  return;
  if (d_sharedTerms.find(e) == d_sharedTerms.end()) {
	  d_sharedTerms[e] = true;
	  d_sharedTermsList.push_back(e);
  }
}


void TheoryArithOld::assertFact(const Theorem& e)
{
	TRACE("arith assert", "assertFact(", e.getExpr().toString(), ")");

    // Pick up any multiplicative case splits and enqueue them
    for (unsigned i = 0; i < multiplicativeSignSplits.size(); i ++)
  	  enqueueFact(multiplicativeSignSplits[i]);
    multiplicativeSignSplits.clear();

  const Expr& expr = e.getExpr();
  if (expr.isNot() && expr[0].isEq()) {
    IF_DEBUG(debugger.counter("[arith] received disequalities")++;)

//    Expr eq = expr[0];
//
//    // We want to expand on difference logic disequalities as soon as possible
//    bool diff_logic = false;
//    if (eq[1].isRational() && eq[1].getRational() == 0) {
//    	if (!isPlus(eq[0])) {
//    		if (isLeaf(eq[0])) diff_logic = true;
//    	}
//    	else {
//    		int arity = eq[0].arity();
//    		if (arity <= 2) {
//    			if (eq[0][0].isRational())
//    				diff_logic = true;
//    			else {
//    				Expr ax = eq[0][0], a, x;
//    				Expr by = eq[0][1], b, y;
//    				separateMonomial(ax, a, x);
//    				separateMonomial(by, b, y);
//    				if (isLeaf(x) && isLeaf(y))
//    					if ((a.getRational() == 1 && b.getRational() == -1) ||
//    						(a.getRational() == -1 && b.getRational() == 1))
//    						diff_logic = true;
//    			}
//    		}
//    		if (arity == 3 && eq[0][0].isRational()) {
//    			Expr ax = eq[0][1], a, x;
//				Expr by = eq[0][2], b, y;
//				separateMonomial(ax, a, x);
//				separateMonomial(by, b, y);
//				if (isLeaf(x) && isLeaf(y))
//					if ((a.getRational() == 1 && b.getRational() == -1) ||
//						(a.getRational() == -1 && b.getRational() == 1))
//						diff_logic = true;
//    		}
//    	}
//    }
//
//    if (diff_logic)
//    	enqueueFact(d_rules->diseqToIneq(e));
//    else
    	d_diseq.push_back(e);
  }
  else if (!expr.isEq()){
    if (expr.isNot()) {
      // If expr[0] is asserted to *not* be an integer, we track it
      // so we will detect if it ever becomes equal to an integer.
      if (expr[0].getKind() == IS_INTEGER) {
        expr[0][0].addToNotify(this, expr[0]);
      }
      // This can only be negation of dark or gray shadows, or
      // disequalities, which we ignore.  Negations of inequalities
      // are handled in rewrite, we don't even receive them here.

//      if (isGrayShadow(expr[0])) {
//    	  TRACE("arith gray", "expanding ", expr.toString(), "");
//    	  Theorem expand = d_rules->expandGrayShadowRewrite(expr[0]);
//    	  enqueueFact(iffMP(e, substitutivityRule(expr, 0, expand)));
//      }

    }
    else if(isDarkShadow(expr)) {
      enqueueFact(d_rules->expandDarkShadow(e));
      IF_DEBUG(debugger.counter("received DARK_SHADOW")++;)
    }
    else if(isGrayShadow(expr)) {
      IF_DEBUG(debugger.counter("received GRAY_SHADOW")++;)
      const Rational& c1 = expr[2].getRational();
      const Rational& c2 = expr[3].getRational();

      // If gray shadow bigger than the treshold, we are done
      if (*d_grayShadowThres > -1 && (c2 - c1 > *d_grayShadowThres)) {
    	  setIncomplete("Some gray shadows ignored due to threshold");
    	  return;
      }

      const Expr& v = expr[0];
      const Expr& ee = expr[1];
      if(c1 == c2)
    	  enqueueFact(d_rules->expandGrayShadow0(e));
      else {
    	  Theorem gThm(e);
    	  // Check if we can reduce the number of cases in G(ax,c,c1,c2)
    	  if(ee.isRational() && isMult(v)
    			  && v[0].isRational() && v[0].getRational() >= 2) {
    		  IF_DEBUG(debugger.counter("reduced const GRAY_SHADOW")++;)
    		  gThm = d_rules->grayShadowConst(e);
    	  }
    	  // (Possibly) new gray shadow
    	  const Expr& g = gThm.getExpr();
    	  if(g.isFalse())
    		  setInconsistent(gThm);
    	  else if(g[2].getRational() == g[3].getRational())
    		  enqueueFact(d_rules->expandGrayShadow0(gThm));
    	  else if(g[3].getRational() - g[2].getRational() <= 5) {
    		  // Assert c1+e <= v <= c2+e
    		  enqueueFact(d_rules->expandGrayShadow(gThm));
    		  // Split G into 2 cases x = l_bound and the other
    		  Theorem thm2 = d_rules->splitGrayShadowSmall(gThm);
    		  enqueueFact(thm2);
    	  }
    	  else {
    		  // Assert c1+e <= v <= c2+e
    		  enqueueFact(d_rules->expandGrayShadow(gThm));
    		  // Split G into 2 cases (binary search b/w c1 and c2)
    		  Theorem thm2 = d_rules->splitGrayShadow(gThm);
    		  enqueueFact(thm2);
    		  // Fetch the two gray shadows
//    		  DebugAssert(thm2.getExpr().isAnd() && thm2.getExpr().arity()==2,
//    				  "thm2 = "+thm2.getExpr().toString());
//    		  const Expr& G1orG2 = thm2.getExpr()[0];
//    		  DebugAssert(G1orG2.isOr() && G1orG2.arity()==2,
//    				  "G1orG2 = "+G1orG2.toString());
//    		  const Expr& G1 = G1orG2[0];
//    		  const Expr& G2 = G1orG2[1];
//    		  DebugAssert(G1.getKind()==GRAY_SHADOW, "G1 = "+G1.toString());
//    		  DebugAssert(G2.getKind()==GRAY_SHADOW, "G2 = "+G2.toString());
//    		  // Split on the left disjunct first (keep the priority low)
//    		  Expr tmp = simplifyExpr(G1);
//    		  if (!tmp.isBoolConst())
//    			  addSplitter(tmp, 1);
//    		  tmp = simplifyExpr(G2);
//    		  if (!tmp.isBoolConst())
//    			  addSplitter(tmp, -1);
    	  }
      }
    }
    else {
      DebugAssert(isLE(expr) || isLT(expr) || isIntPred(expr),
		  "expected LE or LT: "+expr.toString());
      if(isLE(expr) || isLT(expr)) {
	IF_DEBUG(debugger.counter("recevied inequalities")++;)

//        // Assert the equivalent negated inequality
//        Theorem thm;
//        if (isLE(expr)) thm = d_rules->negatedInequality(!gtExpr(expr[0],expr[1]));
//        else thm = d_rules->negatedInequality(!geExpr(expr[0],expr[1]));
//        thm = symmetryRule(thm);
//        Theorem thm2 = simplify(thm.getRHS()[0]);
//        DebugAssert(thm2.getLHS() != thm2.getRHS(), "Expected rewrite");
//        thm2 = getCommonRules()->substitutivityRule(thm.getRHS(), thm2);
//        thm = transitivityRule(thm, thm2);
//        enqueueFact(iffMP(e, thm));

	// Buffer the inequality
	addToBuffer(e);

	unsigned total_buf_size = d_buffer_0.size() + d_buffer_1.size() + d_buffer_2.size() + d_buffer_3.size();
	unsigned processed      = d_bufferIdx_0 + d_bufferIdx_1 + d_bufferIdx_2 + d_bufferIdx_3;
	TRACE("arith ineq", "buffer.size() = ", total_buf_size,
		      ", index="+int2string(processed)
		      +", threshold="+int2string(*d_bufferThres));

	if(!diffLogicOnly && *d_bufferThres >= 0 && (total_buf_size > *d_bufferThres + processed) && !d_inModelCreation) {
	  processBuffer();
	}
      } else {
	IF_DEBUG(debugger.counter("arith IS_INTEGER")++;)
        if (!isInteger(expr[0])) {
          enqueueFact(d_rules->IsIntegerElim(e));
        }
      }
    }
  }
  else {
    IF_DEBUG(debugger.counter("[arith] received 	t1=t2")++;)

//    const Expr lhs = e.getExpr()[0];
//    const Expr rhs = e.getExpr()[1];
//
//    CDMap<Expr, Rational>::iterator l_bound_find = termLowerBound[lhs];
//    if (l_bound_find != termLowerBound.end()) {
//    	Rational lhs_bound = (*l_bound_find).second;
//    	CDMap<Expr, Rational>::iterator l_bound_find_rhs = termLowerBound[rhs];
//    	if (l_bound_find_rhs != termLowerBound.end()) {
//
//    	} else {
//    		// Add the new bound for the rhs
//    		termLowerBound[rhs] = lhs_bound;
//    		termLowerBoundThm =
//    	}
//
//    }


  }
}


void TheoryArithOld::checkSat(bool fullEffort)
{
  //  vector<Expr>::const_iterator e;
  //  vector<Expr>::const_iterator eEnd;
  // TODO: convert back to use iterators
  TRACE("arith checksat", "checksat(fullEffort = ", fullEffort? "true, modelCreation = " : "false, modelCreation = ", (d_inModelCreation ? "true)" : "false)"));
  TRACE("arith ineq", "TheoryArithOld::checkSat(fullEffort=",
        fullEffort? "true" : "false", ")");
  if (fullEffort) {

	  // Process the buffer if necessary
    if (!inconsistent())
        processBuffer();

    // Expand the needded inequalitites
    int total_buffer_size = d_buffer_0.size() + d_buffer_1.size() + d_buffer_2.size() + d_buffer_3.size();

    int constrained_vars = 0;
    if (!inconsistent() && total_buffer_size > 0)
    	constrained_vars = computeTermBounds();

    bool something_enqueued = false;

    if (d_inModelCreation || (!inconsistent() && total_buffer_size > 0 && constrained_vars > 0)) {
      // If in model creation we might have to reconsider some of the dis-equalities
      if (d_inModelCreation) d_diseqIdx = 0;

      // Now go and try to split
      for(; d_diseqIdx < d_diseq.size(); d_diseqIdx = d_diseqIdx+1) {
    	  TRACE("model", "[arith] refining diseq: ", d_diseq[d_diseqIdx].getExpr() , "");

    	  // Get the disequality theorem and the expression
    	  Theorem diseqThm = d_diseq[d_diseqIdx];
    	  Expr diseq = diseqThm.getExpr();

    	  // If we split on this one already
    	  if (diseqSplitAlready.find(diseq) != diseqSplitAlready.end()) continue;

    	  // Get the equality
    	  Expr eq = diseq[0];

    	  // Get the left-hand-side and the right-hands side
    	  Expr lhs = eq[0];
    	  Expr rhs = eq[1];
    	  DebugAssert(lhs.hasFind() && rhs.hasFind(), "Part of dis-equality has no find!");
    	  lhs = find(lhs).getRHS();
    	  rhs = find(rhs).getRHS();

    	  // If the value of the equality is already determined by instantiation, we just skip it
    	  // This can happen a lot as we infer equalities in difference logic
    	  if (lhs.isRational() && rhs.isRational()) {
    		  TRACE("arith diseq", "disequality already evaluated : ", diseq.toString(), "");
    		  continue;
    	  }

    	  // We can allow ourselfs not to care about specific values if we are
    	  // not in model creation
    	  if (!d_inModelCreation) {
    		  // If the left or the right hand side is unbounded, we don't care right now
    		  if (!isConstrained(lhs) || !isConstrained(rhs)) continue;
    		  if (getUpperBound(lhs) < getLowerBound(rhs)) continue;
    		  if (getUpperBound(rhs) < getLowerBound(lhs)) continue;
    	  }

    	  TRACE("arith ineq", "[arith] refining diseq: ", d_diseq[d_diseqIdx].getExpr() , "");

    	  // We don't know the value of the disequlaity, split on it (for now)
    	  enqueueFact(d_rules->diseqToIneq(diseqThm));
    	  something_enqueued = true;

    	  // Mark it as split already
    	  diseqSplitAlready[diseq] = true;
      }
    }

    IF_DEBUG(
            {
              bool dejans_printouts = false;
              if (dejans_printouts) {
    		cerr << "Disequalities after CheckSat" << endl;
    		for (unsigned i = 0; i < d_diseq.size(); i ++) {
    			Expr diseq = d_diseq[i].getExpr();
    			Expr d_find = find(diseq[0]).getRHS();
    			cerr << diseq.toString() << ":" << d_find.toString() << endl;
    		}
    		cerr << "Arith Buffer after CheckSat (0)" << endl;
    		for (unsigned i = 0; i < d_buffer_0.size(); i ++) {
    			Expr ineq = d_buffer_0[i].getExpr();
    			Expr rhs = find(ineq[1]).getRHS();
    			cerr << ineq.toString() << ":" << rhs.toString() << endl;
    		}
    		cerr << "Arith Buffer after CheckSat (1)" << endl;
    		for (unsigned i = 0; i < d_buffer_1.size(); i ++) {
    			Expr ineq = d_buffer_1[i].getExpr();
    			Expr rhs = find(ineq[1]).getRHS();
    			cerr << ineq.toString() << ":" << rhs.toString() << endl;
    		}
    		cerr << "Arith Buffer after CheckSat (2)" << endl;
    		for (unsigned i = 0; i < d_buffer_2.size(); i ++) {
    			Expr ineq = d_buffer_2[i].getExpr();
    			Expr rhs = find(ineq[1]).getRHS();
    			cerr << ineq.toString() << ":" << rhs.toString() << endl;
    		}
    		cerr << "Arith Buffer after CheckSat (3)" << endl;
    		for (unsigned i = 0; i < d_buffer_3.size(); i ++) {
    			Expr ineq = d_buffer_3[i].getExpr();
    			Expr rhs = find(ineq[1]).getRHS();
    			cerr << ineq.toString() << ":" << rhs.toString() << endl;
       		}
              }
            }
    )
  }
}



void TheoryArithOld::refineCounterExample()
{
  d_inModelCreation = true;
  TRACE("model", "refineCounterExample[TheoryArithOld] ", "", "{");
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
		  "TheoryArithOld::refineCounterExample: e1 = "+e1.toString()
		  +"\n type(e1) = "+e1.getType().toString());
      if(findExpr(e1) != findExpr(e2)) {
	DebugAssert(isReal(getBaseType(e2)),
		    "TheoryArithOld::refineCounterExample: e2 = "+e2.toString()
		    +"\n type(e2) = "+e2.getType().toString());
	Expr eq = simplifyExpr(e1.eqExpr(e2));
        if (!eq.isBoolConst()) {
          addSplitter(eq);
        }
      }
    }
  }
  TRACE("model", "refineCounterExample[Theory::Arith] ", "", "}");
}


void
TheoryArithOld::findRationalBound(const Expr& varSide, const Expr& ratSide,
			       const Expr& var,
			       Rational &r)
{
  Expr c, x;
  separateMonomial(varSide, c, x);

  if (!findExpr(ratSide).isRational() && isNonlinearEq(ratSide.eqExpr(rat(0))))
      throw ArithException("Could not generate the model due to non-linear arithmetic");

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
TheoryArithOld::findBounds(const Expr& e, Rational& lub, Rational&  glb)
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

void TheoryArithOld::assignVariables(std::vector<Expr>&v)
{
  int count = 0;

  if (diffLogicOnly)
  {
	  // Compute the model
	  diffLogicGraph.computeModel();
	  // Get values for the variables
	  for (unsigned i = 0; i < v.size(); i ++) {
		  Expr x = v[i];
		  assignValue(x, rat(diffLogicGraph.getValuation(x)));
	  }
	  // Done
	  return;
  }

  while (v.size() > 0)
  {
	  std::vector<Expr> bottom;
	  d_graph.selectSmallest(v, bottom);
	  TRACE("model", "Finding variables to assign. Iteration # ", count, "");
	  for(unsigned int i = 0; i<bottom.size(); i++)
	  {
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

void TheoryArithOld::computeModelBasic(const std::vector<Expr>& v)
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
void TheoryArithOld::computeModel(const Expr& e, vector<Expr>& vars) {
  DebugAssert(findExpr(e).isRational(), "TheoryArithOld::computeModel("
	      +e.toString()+")\n e is not assigned concrete value.\n"
	      +" find(e) = "+findExpr(e).toString());
  assignValue(simplify(e));
  vars.push_back(e);
}

Theorem TheoryArithOld::checkIntegerEquality(const Theorem& thm) {

	// Check if this is a rewrite theorem
	bool rewrite = thm.isRewrite();

	// If it's an integer theorem, then rafine it to integer domain
	Expr eq = (rewrite ? thm.getRHS() : thm.getExpr());

	TRACE("arith rafine", "TheoryArithOld::checkIntegerEquality(", eq, ")");
	DebugAssert(eq.getKind() == EQ, "checkIntegerEquality: must be an equality");

	// Trivial equalities, we don't care
	if (!isPlus(eq[1]) && !isPlus(eq[0])) return thm;
	Expr old_sum = (isPlus(eq[1]) ? eq[1] : eq[0]);

	// Get the sum part
	vector<Expr> children;
	bool const_is_integer = true; // Assuming only one constant is present (canon called before this)
	for (int i = 0; i < old_sum.arity(); i ++)
		 if (!old_sum[i].isRational())
			 children.push_back(old_sum[i]);
		 else
			 const_is_integer = old_sum[i].getRational().isInteger();

	// If the constants are integers, we don't care
	if (const_is_integer) return thm;

	Expr sum = (children.size() > 1 ? plusExpr(children) : children[0]);
	// Check for integer of the remainder of the sum
	Theorem isIntegerEquality = isIntegerThm(sum);
	// If it is an integer, it's unsat
	if (!isIntegerEquality.isNull()) {
		  Theorem false_thm = d_rules->intEqualityRationalConstant(isIntegerEquality, eq);
	  	  if (rewrite) return transitivityRule(thm, false_thm);
	   	  else return iffMP(thm, false_thm);
	}
	else return thm;
}


Theorem TheoryArithOld::rafineInequalityToInteger(const Theorem& thm) {

	// Check if this is a rewrite theorem
	bool rewrite = thm.isRewrite();

	// If it's an integer theorem, then rafine it to integer domain
	Expr ineq = (rewrite ? thm.getRHS() : thm.getExpr());

	TRACE("arith rafine", "TheoryArithOld::rafineInequalityToInteger(", ineq, ")");
	DebugAssert(isIneq(ineq), "rafineInequalityToInteger: must be an inequality");

	// Trivial inequalities are rafined
	// if (!isPlus(ineq[1])) return thm;

	// Get the sum part
	vector<Expr> children;
	if (isPlus(ineq[1])) {
		for (int i = 0; i < ineq[1].arity(); i ++)
			if (!ineq[1][i].isRational())
				children.push_back(ineq[1][i]);
	} else children.push_back(ineq[1]);

	Expr sum = (children.size() > 1 ? plusExpr(children) : children[0]);
	// Check for integer of the remainder of the sum
	Theorem isIntegerInequality = isIntegerThm(sum);
	// If it is an integer, do rafine it
	if (!isIntegerInequality.isNull()) {
	  	  Theorem rafine = d_rules->rafineStrictInteger(isIntegerInequality, ineq);
	  	  TRACE("arith rafine", "TheoryArithOld::rafineInequalityToInteger()", "=>", rafine.getRHS());
	   	  if (rewrite) return canonPredEquiv(transitivityRule(thm, rafine));
	   	  else return canonPred(iffMP(thm, rafine));
	}
	else return thm;
}



/*! accepts a rewrite theorem over eqn|ineqn and normalizes it
 *  and returns a theorem to that effect. assumes e is non-trivial
 *  i.e. e is not '0=const' or 'const=0' or '0 <= const' etc.
 */
Theorem TheoryArithOld::normalize(const Expr& e) {
  //e is an eqn or ineqn. e is not a trivial eqn or ineqn
  //trivial means 0 = const or 0 <= const.
  TRACE("arith normalize", "normalize(", e, ") {");
  DebugAssert(e.isEq() || isIneq(e),
	      "normalize: input must be Eq or Ineq: " + e.toString());
  DebugAssert(!isIneq(e) || (0 == e[0].getRational()),
	      "normalize: if (e is ineq) then e[0] must be 0" +
	      e.toString());
  if(e.isEq()) {
    if(e[0].isRational()) {
      DebugAssert(0 == e[0].getRational(),
		  "normalize: if e is Eq and e[0] is rat then e[0]==0");
    }
    else {
      //if e[0] is not rational then e[1] must be rational.
      DebugAssert(e[1].isRational() && 0 == e[1].getRational(),
		  "normalize: if e is Eq and e[1] is rat then e[1]==0\n"
		  " e = "+e.toString());
    }
  }

  Expr factor;
  if(e[0].isRational())
    factor = computeNormalFactor(e[1], false);
  else
    factor = computeNormalFactor(e[0], false);

  TRACE("arith normalize", "normalize: factor = ", factor, "");
  DebugAssert(factor.getRational() > 0,
              "normalize: factor="+ factor.toString());

  Theorem thm(reflexivityRule(e));
  // Now multiply the equality by the factor, unless it is 1
  if(factor.getRational() != 1) {
    int kind = e.getKind();
    switch(kind) {
    case EQ:
      //TODO: DEJAN FIX
      thm = d_rules->multEqn(e[0], e[1], factor);
      // And canonize the result
      thm = canonPredEquiv(thm);

      // If this is an equation of the form 0 = c + sum, c is not integer, but sum is
      // then equation has no solutions
      thm = checkIntegerEquality(thm);

      break;
    case LE:
    case LT:
    case GE:
    case GT: {
    	 thm = d_rules->multIneqn(e, factor);
    	 // And canonize the result
    	 thm = canonPredEquiv(thm);
    	 // Try to rafine to integer domain
    	 thm = rafineInequalityToInteger(thm);
    	 break;
    }

    default:
      // MS .net doesn't accept "..." + int
      ostringstream ss;
      ss << "normalize: control should not reach here " << kind;
      DebugAssert(false, ss.str());
      break;
    }
  } else
	  if (e.getKind() == EQ)
		  thm = checkIntegerEquality(thm);

  TRACE("arith normalize", "normalize => ", thm, " }");
  return(thm);
}


Theorem TheoryArithOld::normalize(const Theorem& eIffEqn) {
	if (eIffEqn.isRewrite()) return transitivityRule(eIffEqn, normalize(eIffEqn.getRHS()));
	else return iffMP(eIffEqn, normalize(eIffEqn.getExpr()));
}


Theorem TheoryArithOld::rewrite(const Expr& e)
{
  DebugAssert(leavesAreSimp(e), "Expected leaves to be simplified");
  TRACE("arith", "TheoryArithOld::rewrite(", e, ") {");
  Theorem thm;
  if (!e.isTerm()) {
    if (!e.isAbsLiteral()) {
      if (e.isPropAtom() && leavesAreNumConst(e)) {
        if (e.getSize() < 200) {
          Expr eNew = e;
          thm = reflexivityRule(eNew);
          while (eNew.containsTermITE()) {
            thm = transitivityRule(thm, getCommonRules()->liftOneITE(eNew));
            DebugAssert(!thm.isRefl(), "Expected non-reflexive");
            thm = transitivityRule(thm, theoryCore()->getCoreRules()->rewriteIteCond(thm.getRHS()));
            thm = transitivityRule(thm, simplify(thm.getRHS()));
            eNew = thm.getRHS();
          }
        }
        else {
          thm = d_rules->rewriteLeavesConst(e);
          if (thm.isRefl()) {
            e.setRewriteNormal();
          }
          else {
            thm = transitivityRule(thm, simplify(thm.getRHS()));
          }
        }
//         if (!thm.getRHS().isBoolConst()) {
//           e.setRewriteNormal();
//           thm = reflexivityRule(e);
//         }
      }
      else {
        e.setRewriteNormal();
        thm = reflexivityRule(e);
      }
      TRACE("arith", "TheoryArithOld::rewrite[non-literal] => ", thm, " }");
      return thm;
    }
    switch(e.getKind()) {
    case EQ:
    {
      // canonical form for an equality of two leaves
      // is just l == r instead of 0 + (-1 * l) + r = 0.
      if (isLeaf(e[0]) && isLeaf(e[1]))
    	  thm = reflexivityRule(e);
      else { // Otherwise, it is "lhs = 0"
    	  //first convert e to the form 0=e'
    	  if((e[0].isRational() && e[0].getRational() == 0)
    			  || (e[1].isRational() && e[1].getRational() == 0))
    		  //already in 0=e' or e'=0 form
    		  thm = reflexivityRule(e);
    	  else {
    		  thm = d_rules->rightMinusLeft(e);
    		  thm = canonPredEquiv(thm);
    	  }
    	  // Check for trivial equation
    	  if ((thm.getRHS())[0].isRational() && (thm.getRHS())[1].isRational()) {
    		  thm = transitivityRule(thm, d_rules->constPredicate(thm.getRHS()));
    	  } else {
    		  //else equation is non-trivial
    		  thm = normalize(thm);
    		  // Normalization may yield non-simplified terms
    		  if (!thm.getRHS().isBoolConst())
    			  thm = canonPredEquiv(thm);
    	  }
      }

      // Equations must be oriented such that lhs >= rhs as Exprs;
      // this ordering is given by operator<(Expr,Expr).
      const Expr& eq = thm.getRHS();
      if(eq.isEq() && eq[0] < eq[1])
    	  thm = transitivityRule(thm, getCommonRules()->rewriteUsingSymmetry(eq));

      // Check if the equation is nonlinear
      Expr nonlinearEq = thm.getRHS();
      if (nonlinearEq.isEq() && isNonlinearEq(nonlinearEq)) {

    	  TRACE("arith nonlinear", "nonlinear eq rewrite: ", nonlinearEq, "");

    	  Expr left = nonlinearEq[0];
    	  Expr right = nonlinearEq[1];

		  // Check for multiplicative equations, i.e. x*y = 0
		  if (isNonlinearSumTerm(left) && right.isRational() && right.getRational() == 0) {
			  Theorem eq_thm = d_rules->multEqZero(nonlinearEq);
			  thm = transitivityRule(thm, eq_thm);
			  thm = transitivityRule(thm, theoryCore()->simplify(thm.getRHS()));
			  break;
		  }

		  // Heuristics for a sum
		  if (isPlus(left)) {

		      // Search for common factor
		      if (left[0].getRational() == 0) {
		        Expr::iterator i = left.begin(), iend = left.end();
		        ++ i;
		        set<Expr> factors;
		        set<Expr>::iterator is, isend;
		        getFactors(*i, factors);
		        for (++i; i != iend; ++i) {
		          set<Expr> factors2;
		          getFactors(*i, factors2);
		          for (is = factors.begin(), isend = factors.end(); is != isend;) {
		            if (factors2.find(*is) == factors2.end()) {
		              factors.erase(is ++);
		            } else
		            	++ is;
		          }
		          if (factors.empty()) break;
		        }
		        if (!factors.empty()) {
		          thm = transitivityRule(thm, d_rules->divideEqnNonConst(left, rat(0), *(factors.begin())));
		          // got (factor != 0) OR (left / factor = right / factor), need to simplify
		          thm = transitivityRule(thm, simplify(thm.getRHS()));
		          TRACE("arith nonlinear", "nonlinear eq rewrite (factoring): ", thm.getRHS(), "");
		          break;
		        }
		      }

		      // Look for equal powers (eq in the form of c + pow1 - pow2 = 0)
		      Rational constant;
		      Expr power1;
		      Expr power2;
		      if (isPowersEquality(nonlinearEq, power1, power2)) {
		    	  // Eliminate the powers
		    	  thm = transitivityRule(thm, d_rules->elimPower(nonlinearEq));
		    	  thm = transitivityRule(thm, simplify(thm.getRHS()));
		    	  TRACE("arith nonlinear", "nonlinear eq rewrite (equal powers): ", thm.getRHS(), "");
		    	  break;
		      } else
		      // Look for one power equality (c - pow = 0);
		      if (isPowerEquality(nonlinearEq, constant, power1)) {
		    	  Rational pow1 = power1[0].getRational();
		    	  if (pow1 % 2 == 0 && constant < 0) {
		    		  thm = transitivityRule(thm, d_rules->evenPowerEqNegConst(nonlinearEq));
		    		  TRACE("arith nonlinear", "nonlinear eq rewrite (even power = negative): ", thm.getRHS(), "");
		    		  break;
		    	  }
		    	  DebugAssert(constant != 0, "Expected nonzero const");
			      Rational root = ratRoot(constant, pow1.getUnsigned());
				  if (root != 0) {
					  thm = transitivityRule(thm, d_rules->elimPowerConst(nonlinearEq, root));
					  thm = transitivityRule(thm, simplify(thm.getRHS()));
					  TRACE("arith nonlinear", "nonlinear eq rewrite (rational root): ", thm.getRHS(), "");
					  break;
				  } else {
					  Theorem isIntPower(isIntegerThm(left));
					  if (!isIntPower.isNull()) {
						  thm = transitivityRule(thm, d_rules->intEqIrrational(nonlinearEq, isIntPower));
						  TRACE("arith nonlinear", "nonlinear eq rewrite (irational root): ", thm.getRHS(), "");
						  break;
					  }
				  }
		      }
		  }

		  // Non-solvable nonlinear equations are rewritten as conjunction of inequalities
		  if (!canPickEqMonomial(nonlinearEq[0])) {
			  thm = transitivityRule(thm, d_rules->eqToIneq(nonlinearEq));
			  thm = transitivityRule(thm, simplify(thm.getRHS()));
			  TRACE("arith nonlinear", "nonlinear eq rewrite (not solvable): ", thm.getRHS(), "");
			  break;
		  }
      }
    }
    break;
    case GRAY_SHADOW:
    case DARK_SHADOW:
      thm = reflexivityRule(e);
      break;
    case IS_INTEGER: {
      Theorem res(isIntegerDerive(e, typePred(e[0])));
      if(!res.isNull())
	thm = getCommonRules()->iffTrue(res);
      else
	thm = reflexivityRule(e);
      break;
    }
    case NOT:
      if (!isIneq(e[0]))
	//in this case we have "NOT of DARK or GRAY_SHADOW."
	thm = reflexivityRule(e);
      else {
	//In this case we have the "NOT of ineq". get rid of NOT
	//and then treat like an ineq
	thm = d_rules->negatedInequality(e);
	DebugAssert(isGE(thm.getRHS()) || isGT(thm.getRHS()),
		    "Expected GE or GT");
	thm = transitivityRule(thm, d_rules->flipInequality(thm.getRHS()));
	thm = transitivityRule(thm, d_rules->rightMinusLeft(thm.getRHS()));
	thm = canonPredEquiv(thm);

    // If the inequality is strict and integer, change it to non-strict
	Expr theIneq = thm.getRHS();
    if(isLT(theIneq)) {
    	// Check if integer
    	Theorem isIntLHS(isIntegerThm(theIneq[0]));
    	Theorem isIntRHS(isIntegerThm(theIneq[1]));
    	bool isInt = (!isIntLHS.isNull() && !isIntRHS.isNull());
    	  	if (isInt) {
    	  		thm = canonPredEquiv(
    	 			  transitivityRule(thm, d_rules->lessThanToLERewrite(theIneq, isIntLHS, isIntRHS, true)));
    	}
    }

	// Check for trivial inequation
	if ((thm.getRHS())[1].isRational())
	  thm = transitivityRule(thm, d_rules->constPredicate(thm.getRHS()));
	else {
	  //else ineq is non-trivial
	  thm = normalize(thm);
	  // Normalization may yield non-simplified terms
	  thm = canonPredEquiv(thm);
	}
      }
      break;
    case LT:
    case GT:
    case LE:
    case GE: {

      if (isGE(e) || isGT(e)) {
    	  thm = d_rules->flipInequality(e);
    	  thm = transitivityRule(thm, d_rules->rightMinusLeft(thm.getRHS()));
      }
      else
    	  thm = d_rules->rightMinusLeft(e);

      thm = canonPredEquiv(thm);

      // If the inequality is strict and integer, change it to non-strict
      Expr theIneq = thm.getRHS();
      if(isLT(theIneq)) {
      	// Check if integer
      	Theorem isIntLHS(isIntegerThm(theIneq[0]));
      	Theorem isIntRHS(isIntegerThm(theIneq[1]));
      	bool isInt = (!isIntLHS.isNull() && !isIntRHS.isNull());
      	  	if (isInt) {
      	  		thm = canonPredEquiv(
      	 			  transitivityRule(thm, d_rules->lessThanToLERewrite(theIneq, isIntLHS, isIntRHS, true)));
      	}
      }

      // Check for trivial inequation
      if ((thm.getRHS())[1].isRational())
    	  thm = transitivityRule(thm, d_rules->constPredicate(thm.getRHS()));
      else { // ineq is non-trivial
    	  thm = normalize(thm);
    	  thm = canonPredEquiv(thm);
    	  if (thm.getRHS()[1].isRational())
    		  thm = transitivityRule(thm, d_rules->constPredicate(thm.getRHS()));
      }
      break;
      }
    default:
      DebugAssert(false,
		  "Theory_Arith::rewrite: control should not reach here");
      break;
    }
  }
  else {
    if (e.isAtomic())
      thm = canon(e);
    else
      thm = reflexivityRule(e);
  }
  // TODO: this needs to be reviewed, esp for non-linear case
  // Arith canonization is idempotent
  if (theoryOf(thm.getRHS()) == this)
    thm.getRHS().setRewriteNormal();
  TRACE("arith", "TheoryArithOld::rewrite => ", thm, " }");
  return thm;
}


void TheoryArithOld::setup(const Expr& e)
{
  if (!e.isTerm()) {
    if (e.isNot()) return;
    //    if(e.getKind() == IS_INTEGER) {
    //      e[0].addToNotify(this, e);
    //      return;
    //    }
    if (isIneq(e)) {
    	DebugAssert((isLT(e)||isLE(e)) &&
                e[0].isRational() && e[0].getRational() == 0,
                "TheoryArithOld::setup: expected 0 < rhs:" + e.toString());
    	e[1].addToNotify(this, e);
    } else {
//    	if (e.isEq()) {
//    		// Nonlinear solved equations
//    		if (isNonlinearEq(e) && e[0].isRational() && e[0].getRational() == 0)
//    			e[0].addToNotify(this, e);
//    	}
//
//    	DebugAssert(isGrayShadow(e), "TheoryArithOld::setup: expected grayshadow" + e.toString());
//
//    	// Do not add the variable, just the subterm e[0].addToNotify(this, e);
//    	e[1].addToNotify(this, e);
    }
    return;
  }
  int k(0), ar(e.arity());
  for ( ; k < ar; ++k) {
    e[k].addToNotify(this, e);
    TRACE("arith setup", "e["+int2string(k)+"]: ", *(e[k].getNotify()), "");
  }
}


void TheoryArithOld::update(const Theorem& e, const Expr& d)
{
	TRACE("arith update", "update on " + d.toString() + " with ", e.getRHS().toString(), ".");

  if (inconsistent()) return;

  // We accept atoms without find, but only inequalities (they come from the buffer)
  DebugAssert(d.hasFind() || isIneq(d), "update on a non-inequality term/atom");

  IF_DEBUG(debugger.counter("arith update total")++;)
//  if (isGrayShadow(d)) {
//		TRACE("shadow update", "updating index of " + d.toString() + " with ", e.getRHS().toString(), ".");
//
//	    // Substitute e[1] for e[0] in d and enqueue new shadow
//	    DebugAssert(e.getLHS() == d[1], "Mismatch");
//	    Theorem thm = find(d);
//
//	    //    DebugAssert(thm.getRHS() == trueExpr(), "Expected find = true");
//	    vector<unsigned> changed;
//	    vector<Theorem> children;
//	    changed.push_back(1);
//	    children.push_back(e);
//	    Theorem thm2 = substitutivityRule(d, changed, children);
//	    if (thm.getRHS() == trueExpr()) {
//	      enqueueFact(iffMP(getCommonRules()->iffTrueElim(thm), thm2));
//	    }
//	    else {
//	      enqueueFact(getCommonRules()->iffFalseElim(
//	        transitivityRule(symmetryRule(thm2), thm)));
//	    }
//	    IF_DEBUG(debugger.counter("arith update ineq")++;)
//  }
//  else
  if (isIneq(d)) {

    // Substitute e[1] for e[0] in d and enqueue new inequality
    DebugAssert(e.getLHS() == d[1], "Mismatch");
    Theorem thm;
    if (d.hasFind()) thm = find(d);

//    bool diff_logic = false;
//    Expr new_rhs = e.getRHS();
//    if (!isPlus(new_rhs)) {
//    	if (isLeaf(new_rhs)) diff_logic = true;
//    }
//    else {
//    	int arity = new_rhs.arity();
//    	if (arity == 2)  {
//    		if (new_rhs[0].isRational()) diff_logic = true;
//    		else {
//    			Expr ax = new_rhs[0], a, x;
//    			Expr by = new_rhs[1], b, y;
//    			separateMonomial(ax, a, x);
//    			separateMonomial(by, b, y);
//    			if ((a.getRational() == 1 && b.getRational() == -1) ||
//    					(a.getRational() == -1 && b.getRational() == 1))
//    				diff_logic = true;
//    		}
//    	} else {
//    		if (arity == 3 && new_rhs[0].isRational()) {
//    			Expr ax = new_rhs[1], a, x;
//    			Expr by = new_rhs[2], b, y;
//    			separateMonomial(ax, a, x);
//    			separateMonomial(by, b, y);
//    			if ((a.getRational() == 1 && b.getRational() == -1) ||
//    					(a.getRational() == -1 && b.getRational() == 1))
//    							diff_logic = true;
//    		}
//    	}
//    }

    //    DebugAssert(thm.getRHS() == trueExpr(), "Expected find = true");
    vector<unsigned> changed;
    vector<Theorem> children;
    changed.push_back(1);
    children.push_back(e);
    Theorem thm2 = substitutivityRule(d, changed, children);
    Expr newIneq = thm2.getRHS();

  	// If this inequality is bufferred but not yet projected, just wait for it
   	// but don't add the find to the buffer as it will be projected as a find
   	// We DO want it to pass through all the buffer stuff but NOT get into the buffer
   	// NOTE: this means that the difference logic WILL get processed
   	if ((thm.isNull() || thm.getRHS() != falseExpr()) &&
   			bufferedInequalities.find(d) != bufferedInequalities.end() &&
   			alreadyProjected.find(d) == alreadyProjected.end()) {
   		TRACE("arith update", "simplified but not projected : ", thm2.getRHS(), "");
   		dontBuffer[thm2.getRHS()] = true;
   	}

   	if (thm.isNull()) {
   		// This hy is in the buffer, not in the core
   		// if it has been projected, than it's parent has been projected and will get reprojected
   		// accuratlz. If it has not been projected, we don't care it's still there
   		TRACE("arith update", "in udpate, but no find", "", "");
   		if (bufferedInequalities.find(d) != bufferedInequalities.end()) {
   			if (thm2.getRHS()[1].isRational()) enqueueFact(iffMP(bufferedInequalities[d], thm2));
   			else if (alreadyProjected.find(d) != alreadyProjected.end()) {
   				// the parent will get reprojected
   				alreadyProjected[d] = d;
   			}
   		}
   	}
   	else if (thm.getRHS() == trueExpr()) {
   		if (!newIneq[1].isRational() || newIneq[1].getRational() <= 0)
   			enqueueFact(iffMP(getCommonRules()->iffTrueElim(thm), thm2));
    }
    else {
      enqueueFact(getCommonRules()->iffFalseElim(
        transitivityRule(symmetryRule(thm2), thm)));
    }
    IF_DEBUG(debugger.counter("arith update ineq")++;)
  }
  else if (d.isEq()) {
	  TRACE("arith nonlinear", "TheoryArithOld::update() on equality ", d, "");
	  // We get equalitites from the non-solve nonlinear equations
	  // only the right hand sides get updated
	  vector<unsigned> changed;
	  vector<Theorem> children;
	  changed.push_back(0);
	  children.push_back(e);
	  Theorem thm = substitutivityRule(d, changed, children);
	  Expr newEq = thm.getRHS();

	  Theorem d_find = find(d);
	  if (d_find.getRHS() == trueExpr()) enqueueFact(iffMP(getCommonRules()->iffTrueElim(d_find), thm));
      else enqueueFact(getCommonRules()->iffFalseElim(transitivityRule(symmetryRule(thm), d_find)));
  }
  else if (d.getKind() == IS_INTEGER) {
    // This should only happen if !d has been asserted
    DebugAssert(e.getRHS() == findExpr(d[0]), "Unexpected");
    if (isInteger(e.getRHS())) {
      Theorem thm = substitutivityRule(d, find(d[0]));
      thm = transitivityRule(symmetryRule(find(d)), thm);
      thm = iffMP(thm, simplify(thm.getExpr()));
      setInconsistent(thm);
    }
    else {
      e.getRHS().addToNotify(this, d);
    }
  }
  else if (find(d).getRHS() == d) {
//     Theorem thm = canonSimp(d);
//     TRACE("arith", "TheoryArithOld::update(): thm = ", thm, "");
//     DebugAssert(leavesAreSimp(thm.getRHS()), "updateHelper error: "
//  		+thm.getExpr().toString());
//     assertEqualities(transitivityRule(thm, rewrite(thm.getRHS())));
//     IF_DEBUG(debugger.counter("arith update find(d)=d")++;)
    Theorem thm = simplify(d);
    // If the original is was a shared term, add this one as as a shared term also
    if (d_sharedTerms.find(d) != d_sharedTerms.end()) addSharedTerm(thm.getRHS());
    DebugAssert(thm.getRHS().isAtomic(), "Expected atomic");
    assertEqualities(thm);
  }
}


Theorem TheoryArithOld::solve(const Theorem& thm)
{
  DebugAssert(thm.isRewrite() && thm.getLHS().isTerm(), "");
  const Expr& lhs = thm.getLHS();
  const Expr& rhs = thm.getRHS();

  // Check for already solved equalities.

  // Have to be careful about the types: integer variable cannot be
  // assigned a real term.  Also, watch for e[0] being a subexpression
  // of e[1]: this would create an unsimplifiable expression.
  if (isLeaf(lhs) && !isLeafIn(lhs, rhs)
      && (!isInteger(lhs) || isInteger(rhs))
      // && !e[0].subExprOf(e[1])
      )
    return thm;

  // Symmetric version is already solved
  if (isLeaf(rhs) && !isLeafIn(rhs, lhs)
      && (!isInteger(rhs) || isInteger(lhs))
      // && !e[1].subExprOf(e[0])
      )
    return symmetryRule(thm);

  return doSolve(thm);
}


void TheoryArithOld::computeModelTerm(const Expr& e, std::vector<Expr>& v) {
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
      TRACE("model", "TheoryArithOld::computeModelTerm(", e, "): a variable");
      // Leave it alone (it has no descendants)
      // v.push_back(e);
    } else {
      TRACE("model", "TheoryArithOld::computeModelTerm("+e.toString()
	    +"): has find pointer to ", e2, "");
      v.push_back(e2);
    }
  }
  }
}


Expr TheoryArithOld::computeTypePred(const Type& t, const Expr& e) {
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


void TheoryArithOld::checkAssertEqInvariant(const Theorem& e)
{
  if (e.isRewrite()) {
    DebugAssert(e.getLHS().isTerm(), "Expected equation");
    if (isLeaf(e.getLHS())) {
      // should be in solved form
      DebugAssert(!isLeafIn(e.getLHS(),e.getRHS()),
                  "Not in solved form: lhs appears in rhs");
    }
    else {
      DebugAssert(e.getLHS().hasFind(), "Expected lhs to have find");
      DebugAssert(!leavesAreSimp(e.getLHS()),
                  "Expected at least one unsimplified leaf on lhs");
    }
    DebugAssert(canonSimp(e.getRHS()).getRHS() == e.getRHS(),
                "Expected canonSimp(rhs) = canonSimp(rhs)");
  }
  else {
    Expr expr = e.getExpr();
    if (expr.isFalse()) return;

    vector<Theorem> eqs;
    Theorem thm;
    int index, index2;

    for (index = 0; index < expr.arity(); ++index) {
      thm = getCommonRules()->andElim(e, index);
      eqs.push_back(thm);
      if (thm.getExpr().isFalse()) return;
      DebugAssert(eqs[index].isRewrite() &&
                  eqs[index].getLHS().isTerm(), "Expected equation");
    }

    // Check for solved form
    for (index = 0; index < expr.arity(); ++index) {
      DebugAssert(isLeaf(eqs[index].getLHS()), "expected leaf on lhs");
      DebugAssert(canonSimp(eqs[index].getRHS()).getRHS() == eqs[index].getRHS(),
                  "Expected canonSimp(rhs) = canonSimp(rhs)");
      DebugAssert(recursiveCanonSimpCheck(eqs[index].getRHS()),
                  "Failed recursive canonSimp check");
      for (index2 = 0; index2 < expr.arity(); ++index2) {
        DebugAssert(index == index2 ||
                    eqs[index].getLHS() != eqs[index2].getLHS(),
                    "Not in solved form: repeated lhs");
        DebugAssert(!isLeafIn(eqs[index].getLHS(),eqs[index2].getRHS()),
                    "Not in solved form: lhs appears in rhs");
      }
    }
  }
}


void TheoryArithOld::checkType(const Expr& e)
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
      DebugAssert(false, "Unexpected kind in TheoryArithOld::checkType"
                  +getEM()->getKindName(e.getKind()));
  }
}


Cardinality TheoryArithOld::finiteTypeInfo(Expr& e, Unsigned& n,
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


void TheoryArithOld::computeType(const Expr& e)
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
      DebugAssert(false,"TheoryArithOld::computeType: unexpected expression:\n "
                  +e.toString());
      break;
  }
}


Type TheoryArithOld::computeBaseType(const Type& t) {
  IF_DEBUG(int kind = t.getExpr().getKind();)
  DebugAssert(kind==INT || kind==REAL || kind==SUBRANGE,
	      "TheoryArithOld::computeBaseType("+t.toString()+")");
  return realType();
}


Expr
TheoryArithOld::computeTCC(const Expr& e) {
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
Expr
TheoryArithOld::parseExprOp(const Expr& e) {
  TRACE("parser", "TheoryArithOld::parseExprOp(", e, ")");
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
	      "TheoryArithOld::parseExprOp:\n e = "+e.toString());

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
      if(e.arity() == 2) {
        if (false && (getEM()->getInputLang() == SMTLIB_LANG
                      || getEM()->getInputLang() == SMTLIB_V2_LANG)) {
          throw ParserException("Unary Minus should use '~' instead of '-' in SMT-LIB expr:"
                                +e.toString());
        }
        else {
          return uminusExpr(parseExpr(e[1]));
        }
      }
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
	  	  "TheoryArithOld::parseExprOp: invalid input " + e.toString());
      break;
  }
  return e;
}

///////////////////////////////////////////////////////////////////////////////
// Pretty-printing                                                           //
///////////////////////////////////////////////////////////////////////////////


ExprStream&
TheoryArithOld::print(ExprStream& os, const Expr& e) {
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
	if(!isInteger(e[0])){
	  os<<"ERRPR:arithmetic operations only support inteters now in TPTP\n";
	  break;
	}

	os << "$minus_int(" << e[0] << "," << e[1]<< ")";
	break;
      case UMINUS:
	if(!isInteger(e[0])){
	  os<<"ERRPR:arithmetic operations only support inteters now in TPTP\n";
	  break;
	}

	os << "$uminus_int(" << e[0] <<")" ;
	break;
      case MULT:  {
	if(!isInteger(e[0])){
	  os<<"ERRPR:times only supports inteters now in TPTP\n";
	  break;
	}

	int i=0, iend=e.arity();
	if(iend <=1){
	  os<<"ERROR:times must have more than two numbers in TPTP\n";
	  break;
	}

	for(i=0; i <= iend-2; ++i){
	  os << "$times_int(";
	  os << e[i] << ",";
	}

	os<< e[iend-1];

	for(i=0 ; i <= iend-2; ++i){
	  os << ")";
	}

	break;
      }
      case POW:

	if(!isInteger(e[0])){
	  os<<"ERRPR:arithmetic operations only support inteters now in TPTP\n";
	  break;
	}

	os << "$power_int(" << push << e[1] << space << "^ " << e[0] << push << ")";
	break;

      case DIVIDE:
	if(!isInteger(e[0])){
	  os<<"ERRPR:arithmetic operations only support inteters now in TPTP\n";
	  break;
	}

	os << "divide_int(" <<e[0]  << "," << e[1] << ")";
	break;

      case LT:
	if(!isInteger(e[0])){
	  os<<"ERRPR:arithmetic operations only support inteters now in TPTP\n";
	  break;
	}
	os << "$less_int(" << e[0] << "," << e[1] <<")";
	break;

      case LE:
	if(!isInteger(e[0])){
	  os<<"ERRPR:arithmetic operations only support inteters now in TPTP\n";
	  break;
	}

          os << "$lesseq_int(" << e[0]  << "," << e[1] << ")";
          break;

      case GT:
	if(!isInteger(e[0])){
	  os<<"ERRPR:arithmetic operations only support inteters now in TPTP\n";
	  break;
	}

	os << "$greater_int(" << e[0] << "," << e[1] << ")";
	break;

      case GE:
	if(!isInteger(e[0])){
	  os<<"ERRPR:arithmetic operations only support inteters now in TPTP\n";
	  break;
	}

	os << "$greatereq_int(" << e[0] << "," << e[1]  << ")";
	break;
      case DARK_SHADOW:
      case GRAY_SHADOW:
	os <<"ERROR:SHADOW:not supported in TPTP\n";
	break;

      case INT:
	os <<"$int";
	break;
      case REAL:
	os <<"ERROR:REAL not supported in TPTP\n";
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
          os << "REAL";
          break;
        case INT:
          os << "INT";
          break;
        case RATIONAL_EXPR:
          e.print(os);
          break;
        case NEGINF:
          os << "NEGINF";
          break;
        case POSINF:
          os << "POSINF";
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
 case SPASS_LANG: {
      switch(e.getKind()) {
        case REAL_CONST:
          printRational(os, e[0].getRational(), true);
          break;
        case RATIONAL_EXPR:
          printRational(os, e.getRational());
          break;
        case REAL:
          throw SmtlibException("TheoryArithOld::print: SPASS: REAL not implemented");
          break;
        case INT:
          throw SmtlibException("TheoryArithOld::print: SPASS: INT not implemented");
          break;
        case SUBRANGE:
          throw SmtlibException("TheoryArithOld::print: SPASS: SUBRANGE not implemented");
          break;
        case IS_INTEGER:
          throw SmtlibException("TheoryArithOld::print: SPASS: IS_INTEGER not implemented");
        case PLUS: {
	  int arity = e.arity();
	  if(2 == arity) {
	    os << push << "plus("
               << e[0] << "," << space << e[1]
               << push << ")";
	  }
	  else if(2 < arity) {
	    for (int i = 0 ; i < arity - 2; i++){
	      os << push << "plus(";
	      os << e[i] << "," << space;
	    }
	    os << push << "plus("
               << e[arity - 2] << "," << space << e[arity - 1]
               << push << ")";
	    for (int i = 0 ; i < arity - 2; i++){
	      os << push << ")";
	    }
	  }
	  else {
	    throw SmtlibException("TheoryArithOld::print: SPASS: Less than two arguments for plus");
	  }
          break;
        }
        case MINUS: {
          os << push << "plus(" << e[0]
             << "," << space << push << "mult(-1,"
             << space << e[1] << push << ")" << push << ")";
          break;
        }
        case UMINUS: {
          os << push << "plus(0,"
             << space << push << "mult(-1,"
             << space << e[0] << push << ")" << push << ")";
          break;
        }
        case MULT: {
	  int arity = e.arity();
	  if (2 == arity){
	    os << push << "mult("
               << e[0] << "," << space << e[1]
               << push << ")";
	  }
	  else if (2 < arity){
	    for (int i = 0 ; i < arity - 2; i++){
	      os << push << "mult(";
	      os << e[i] << "," << space;
	    }
	    os << push << "mult("
               << e[arity - 2] << "," << space << e[arity - 1]
               << push << ")";
	    for (int i = 0 ; i < arity - 2; i++){
	      os << push << ")";
	    }
	  }
	  else{
	    throw SmtlibException("TheoryArithOld::print: SPASS: Less than two arguments for mult");
	  }
          break;
        }
        case POW:
          if (e[0].isRational() && e[0].getRational().isInteger()) {
            int i=0, iend=e[0].getRational().getInt();
              for(; i!=iend; ++i) {
                if (i < iend-2) {
                  os << push << "mult(";
                }
                os << e[1] << "," << space;
              }
	      os << push << "mult("
                 << e[1] << "," << space << e[1];
              for (i=0; i < iend-1; ++i) {
                os << push << ")";
              }
          }
          else {
            throw SmtlibException("TheoryArithOld::print: SPASS: POW not supported: " + e.toString(PRESENTATION_LANG));
          }
          break;
        case DIVIDE: {
	  os << "ERROR "<< endl;break;
          throw SmtlibException("TheoryArithOld::print: SPASS: unexpected use of DIVIDE");
          break;
        }
        case LT: {
          Rational r;
          os << push << "ls(" << space;
          os << e[0] << "," << space << e[1] << push << ")";
          break;
        }
        case LE: {
          Rational r;
          os << push << "le(" << space;
          os << e[0] << "," << space << e[1] << push << ")";
          break;
        }
        case GT: {
          Rational r;
          os << push << "gs(" << space;
          os << e[0] << "," << space << e[1] << push << ")";
          break;
        }
        case GE: {
          Rational r;
          os << push << "ge(" << space;
          os << e[0] << "," << space << e[1] << push << ")";
          break;
        }

        default:
          throw SmtlibException("TheoryArithOld::print: SPASS: default not supported");
      }
      break; // end of case SPASS_LANG
    }
    case SMTLIB_LANG:
    case SMTLIB_V2_LANG: {
      switch(e.getKind()) {
        case REAL_CONST:
          printRational(os, e[0].getRational(), (os.lang() == SMTLIB_LANG));
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
          throw SmtlibException("TheoryArithOld::print: SMTLIB: SUBRANGE not implemented");
//           if(e.arity() != 2) e.print(os);
//           else
//             os << "(" << push << "SUBRANGE" << space << e[0]
// 	       << space << e[1] << push << ")";
          break;
        case IS_INTEGER:
 	  if(e.arity() == 1)
 	    os << "(" << push << "IsInt" << space << e[0] << push << ")";
 	  else
            throw SmtlibException("TheoryArithOld::print: SMTLIB: IS_INTEGER used unexpectedly");
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
          if (os.lang() == SMTLIB_LANG) {
            os << "(" << push << "~" << space << e[0] << push << ")";
          }
          else {
            os << "(" << push << "-" << space << e[0] << push << ")";
          }
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
          if (e[0].isRational() && e[0].getRational().isInteger()) {
            int i=0, iend=e[0].getRational().getInt();
              for(; i!=iend; ++i) {
                if (i < iend-1) {
                  os << "(" << push << "*";
                }
                os << space << e[1];
              }
              for (i=0; i < iend-1; ++i) os << push << ")";
          }
          else
            throw SmtlibException("TheoryArithOld::print: SMTLIB: POW not supported: " + e.toString(PRESENTATION_LANG));
          //          os << "(" << push << "^ " << e[1] << space << e[0] << push << ")";
          break;
        case DIVIDE: {
          throw SmtlibException("TheoryArithOld::print: SMTLIB: unexpected use of DIVIDE");
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
          throw SmtlibException("TheoryArithOld::print: SMTLIB: DARK_SHADOW not supported");
	  os << "(" << push << "DARK_SHADOW" << space << e[0]
	     << space << e[1] << push << ")";
	  break;
        case GRAY_SHADOW:
          throw SmtlibException("TheoryArithOld::print: SMTLIB: GRAY_SHADOW not supported");
	  os << "GRAY_SHADOW(" << push << e[0] << ","  << space << e[1]
	     << "," << space << e[2] << "," << space << e[3] << push << ")";
	  break;
        default:
          throw SmtlibException("TheoryArithOld::print: SMTLIB: default not supported");
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

Theorem TheoryArithOld::inequalityToFind(const Theorem& inequalityThm, bool normalizeRHS) {

	// Which side of the inequality
	int index = (normalizeRHS ? 1 : 0);

	TRACE("arith find", "inequalityToFind(", int2string(index) + ", " + inequalityThm.getExpr().toString(), ")");

	// Get the inequality expression
	const Expr& inequality = inequalityThm.getExpr();

	// The theorem we will return
	Theorem inequalityFindThm;

	// If the inequality side has a find
	if (inequality[index].hasFind()) {
		// Get the find of the rhs (lhs)
	 	Theorem rhsFindThm = inequality[index].getFind();
	 	// Get the theorem simplifys the find (in case the updates haven't updated all the finds yet
	    // Fixed with d_theroyCore.inUpdate()
        rhsFindThm = transitivityRule(rhsFindThm, simplify(rhsFindThm.getRHS()));
	    // If not the same as the original
	    Expr rhsFind = rhsFindThm.getRHS();
	    if (rhsFind != inequality[index]) {
	    	// Substitute in the inequality
	    	vector<unsigned> changed;
	    	vector<Theorem> children;
	    	changed.push_back(index);
	    	children.push_back(rhsFindThm);
	    	rhsFindThm = iffMP(inequalityThm, substitutivityRule(inequality, changed, children));
	    	// If on the left-hand side, we are done
	    	if (index == 0)
	    		inequalityFindThm = rhsFindThm;
	    	else
	    		// If on the right-hand side and left-hand side is 0, normalize it
	    		if (inequality[0].isRational() && inequality[0].getRational() == 0)
	    			inequalityFindThm =	normalize(rhsFindThm);
	    		else
	    			inequalityFindThm = rhsFindThm;
	    } else
	    	inequalityFindThm = inequalityThm;
	} else
	    inequalityFindThm = inequalityThm;


	TRACE("arith find", "inequalityToFind ==>", inequalityFindThm.getExpr(), "");

	return inequalityFindThm;
}

void TheoryArithOld::registerAtom(const Expr& e) {
	// Trace it
	TRACE("arith atoms", "registerAtom(", e.toString(), ")");

	// Mark it
	formulaAtoms[e] = true;

	// If it is a atomic formula, add it to the map
	if (e.isAbsAtomicFormula() && isIneq(e)) {
		Expr rightSide    = e[1];
		Rational leftSide = e[0].getRational();

		//Get the terms for : c1 op t1 and t2 -op c2
		Expr t1, t2;
		Rational c1, c2;
		extractTermsFromInequality(e, c1, t1, c2, t2);

		if (true) {
			TRACE("arith atoms", "registering lower bound for ", t1.toString(), " = " + c1.toString() + ")");
			formulaAtomLowerBound[t1].insert(pair<Rational, Expr>(c1, e));

			// See if the bounds on the registered term can infered from already asserted facts
			CDMap<Expr, Rational>::iterator lowerBoundFind = termLowerBound.find(t1);
			if (lowerBoundFind != termLowerBound.end()) {
				Rational boundValue = (*lowerBoundFind).second;
				Theorem boundThm = termLowerBoundThm[t1];
				Expr boundIneq = boundThm.getExpr();
				if (boundValue > c1 || (boundValue == c1 && !(boundIneq.getKind() == LE && e.getKind() == LT))) {
					enqueueFact(getCommonRules()->implMP(boundThm, d_rules->implyWeakerInequality(boundIneq, e)));
				}
			}

			// See if the bounds on the registered term can falsified from already asserted facts
			CDMap<Expr, Rational>::iterator upperBoundFind = termUpperBound.find(t1);
			if (upperBoundFind != termUpperBound.end()) {
				Rational boundValue = (*upperBoundFind).second;
				Theorem boundThm = termUpperBoundThm[t1];
				Expr boundIneq = boundThm.getExpr();
				if (boundValue < c1 || (boundValue == c1 && boundIneq.getKind() == LT && e.getKind() == LT)) {
					enqueueFact(getCommonRules()->implMP(boundThm, d_rules->implyNegatedInequality(boundIneq, e)));
				}
			}

			TRACE("arith atoms", "registering upper bound for ", t2.toString(), " = " + c2.toString() + ")");
			formulaAtomUpperBound[t2].insert(pair<Rational, Expr>(c2, e));
		}
	}
}

TheoryArithOld::DifferenceLogicGraph::DifferenceLogicGraph(TheoryArithOld* arith, TheoryCore* core, ArithProofRules* rules, Context* context)
	: d_pathLenghtThres(&(core->getFlags()["pathlength-threshold"].getInt())),
	  arith(arith),
	  core(core),
	  rules(rules),
	  unsat_theorem(context),
	  biggestEpsilon(context, 0, 0),
	  smallestPathDifference(context, 1, 0),
	  leGraph(context),
	  varInCycle(context)
{
}

Theorem TheoryArithOld::DifferenceLogicGraph::getUnsatTheorem() {
	return unsat_theorem;
}

bool TheoryArithOld::DifferenceLogicGraph::isUnsat() {
	return !getUnsatTheorem().isNull();
}

bool TheoryArithOld::DifferenceLogicGraph::existsEdge(const Expr& x, const Expr& y) {
	Expr index = x - y;

	Graph::iterator find_le = leGraph.find(index);
	if (find_le != leGraph.end()) {
		EdgeInfo edge_info = (*find_le).second;
		if (edge_info.isDefined()) return true;
	}

	return false;
}

bool TheoryArithOld::DifferenceLogicGraph::inCycle(const Expr& x) {
	return (varInCycle.find(x) != varInCycle.end());
}

TheoryArithOld::DifferenceLogicGraph::Graph::ElementReference TheoryArithOld::DifferenceLogicGraph::getEdge(const Expr& x, const Expr& y) {
	Expr index = x - y;
	Graph::ElementReference edge_info = leGraph[index];

	// If a new edge and x != y, then add vertices to the apropriate lists
	if (x != y && !edge_info.get().isDefined()) {

		// Adding a new edge, take a resource
		core->getResource();

		EdgesList::iterator y_it = incomingEdges.find(y);
		if (y_it == incomingEdges.end() || (*y_it).second == 0) {
			CDList<Expr>* list = new(true) CDList<Expr>(core->getCM()->getCurrentContext());
			list->push_back(x);
			incomingEdges[y] = list;
		} else
			((*y_it).second)->push_back(x);

		EdgesList::iterator x_it = outgoingEdges.find(x);
		if (x_it == outgoingEdges.end() || (*x_it).second == 0) {
			CDList<Expr>* list = new(true) CDList<Expr>(core->getCM()->getCurrentContext());
			list->push_back(y);
			outgoingEdges[x] = list;
		} else
			((*x_it).second)->push_back(y);
	}

	return edge_info;
}

TheoryArithOld::DifferenceLogicGraph::EpsRational TheoryArithOld::DifferenceLogicGraph::getEdgeWeight(const Expr& x, const Expr& y) {
	if (!existsEdge(x, y))
		return EpsRational::PlusInfinity;
	else {
		EdgeInfo edgeInfo = getEdge(x, y).get();
		return edgeInfo.length;
	}
}


void TheoryArithOld::DifferenceLogicGraph::addEdge(const Expr& x, const Expr& y, const Rational& bound, const Theorem& edge_thm) {

	TRACE("arith diff", x, " --> ", y);
	DebugAssert(x != y, "addEdge, given two equal expressions!");

	if (isUnsat()) return;

    // If out of resources, bail out
	if (core->outOfResources()) return;

	// Get the kind of the inequality (NOTE isNull -- for model computation we add a vertex with no theorem)
	// FIXME: Later, add a debug assert for the theorem that checks that this variable is cvc3diffLogicSource
	int kind = (edge_thm.isNull() ? LE : edge_thm.getExpr().getKind());
	DebugAssert(kind == LT || kind == LE, "addEdge, not an <= or <!");

	// Get the EpsRational bound
	Rational k = (kind == LE ? 0 : -1);
	EpsRational c(bound, k);

	// Get the current (or a fresh new edge info)
	Graph::ElementReference edgeInfoRef = getEdge(x, y);
	// If uninitialized, or smaller length (we prefer shorter paths, so one edge is better)
	EdgeInfo edgeInfo = edgeInfoRef.get();
	// If the edge changed to the better, do the work
	if (!edgeInfo.isDefined() || c <= edgeInfo.length) {

		// Update model generation data
		if (edgeInfo.isDefined()) {
			EpsRational difference = edgeInfo.length - c;
			Rational rationalDifference = difference.getRational();
			if (rationalDifference > 0 && rationalDifference < smallestPathDifference) {
				smallestPathDifference = rationalDifference;
				TRACE("diff model", "smallest path difference : ", smallestPathDifference, "");
			}
		}
		Rational newEpsilon = - c.getEpsilon();
		if (newEpsilon > biggestEpsilon) {
			biggestEpsilon = newEpsilon;
			TRACE("diff model", "biggest epsilon : ", biggestEpsilon, "");
		}

		// Set the edge info
		edgeInfo.length = c;
		edgeInfo.explanation = edge_thm;
		edgeInfo.path_length_in_edges = 1;
		edgeInfoRef = edgeInfo;


		// Try simple cycle x --> y --> x, to keep invariants (no cycles or one negative)
		if (existsEdge(y, x)) {
			varInCycle[x] = true;
			varInCycle[y] = true;
			tryUpdate(x, y, x);
			if (isUnsat())
				return;
		}

	    // For all edges coming into x, z ---> x,  update z ---> y and add updated ones to the updated_in_y vector
		CDList<Expr>* in_x = incomingEdges[x];
		vector<Expr> updated_in_y;
		updated_in_y.push_back(x);

		// If there
		if (in_x) {
			IF_DEBUG(int total = 0; int updated = 0;);
			for (unsigned it = 0; it < in_x->size() && !isUnsat(); it ++) {
				const Expr& z = (*in_x)[it];
				if (z != arith->zero && z.hasFind() && core->find(z).getRHS() != z) continue;
				if (z != y && z != x && x != y) {
					IF_DEBUG(total ++;);
					TRACE("diff update", "trying with ", z.toString() + " --> ", x.toString());
					if (tryUpdate(z, x, y)) {
						updated_in_y.push_back(z);
						IF_DEBUG(updated++;);
					}
				}
			}
			TRACE("diff updates", "Updates : ", int2string(updated), " of " + int2string(total));
		}

		// For all edges coming into y, z_1 ---> y, and all edges going out of y, y ---> z_2, update z1 --> z_2
		CDList<Expr>* out_y = outgoingEdges[y];
		if (out_y)
			for (unsigned it_z1 = 0; it_z1 < updated_in_y.size() && !isUnsat(); it_z1 ++) {
				for (unsigned it_z2 = 0; it_z2 < out_y->size() && !isUnsat(); it_z2 ++) {
					const Expr& z1 = updated_in_y[it_z1];
					const Expr& z2 = (*out_y)[it_z2];
					if (z2 != arith->zero && z2.hasFind() && core->find(z2).getRHS() != z2) continue;
					if (z1 != z2 && z1 != y && z2 != y)
						tryUpdate(z1, y, z2);
				}
			}

	} else {
		TRACE("arith propagate", "could have propagated ", edge_thm.getExpr(), edge_thm.isAssump() ? " ASSUMPTION " : "not assumption");

	}

}

void TheoryArithOld::DifferenceLogicGraph::getEdgeTheorems(const Expr& x, const Expr& z, const EdgeInfo& edgeInfo, std::vector<Theorem>& outputTheorems) {
	TRACE("arith diff", "Getting theorems from ", x, " to " + z.toString() + " length = " + edgeInfo.length.toString() + ", edge_length = " + int2string(edgeInfo.path_length_in_edges));

	if (edgeInfo.path_length_in_edges == 1) {
		DebugAssert(x == sourceVertex || z == sourceVertex || !edgeInfo.explanation.isNull(), "Edge from " + x.toString() + " to " + z.toString() + " has no theorem!");
		if (x != sourceVertex && z != sourceVertex)
			outputTheorems.push_back(edgeInfo.explanation);
	}
	else {
		const Expr& y = edgeInfo.in_path_vertex;
		EdgeInfo x_y = getEdge(x, y);
		DebugAssert(x_y.isDefined(), "getEdgeTheorems: the cycle edge is not defined!");
		EdgeInfo y_z = getEdge(y, z);
		DebugAssert(y_z.isDefined(), "getEdgeTheorems: the cycle edge is not defined!");
		getEdgeTheorems(x, y, x_y, outputTheorems);
		getEdgeTheorems(y, z, y_z, outputTheorems);
	}
}

void TheoryArithOld::DifferenceLogicGraph::analyseConflict(const Expr& x, int kind) {

	// Get the cycle info
	Graph::ElementReference x_x_cycle_ref = getEdge(x, x);
	EdgeInfo x_x_cycle = x_x_cycle_ref.get();

	DebugAssert(x_x_cycle.isDefined(), "analyseConflict: the cycle edge is not defined!");

	// Vector to keep the theorems in
	vector<Theorem> inequalities;

	// Get the theorems::analyse
	getEdgeTheorems(x, x, x_x_cycle, inequalities);

	// Set the unsat theorem
	unsat_theorem = rules->cycleConflict(inequalities);

	TRACE("diff unsat", "negative cycle : ", int2string(inequalities.size()), " vertices.");
}

bool TheoryArithOld::DifferenceLogicGraph::tryUpdate(const Expr& x, const Expr& y, const Expr& z) {

	// x -> y -> z, if z -> x they are all in a cycle
	if (existsEdge(z, x)) {
		varInCycle[x] = true;
		varInCycle[y] = true;
		varInCycle[z] = true;
	}

	//Get all the edges
	Graph::ElementReference x_y_le_ref = getEdge(x, y);
	EdgeInfo x_y_le = x_y_le_ref;
	if (*d_pathLenghtThres >= 0 && x_y_le.path_length_in_edges > *d_pathLenghtThres) return false;

	Graph::ElementReference y_z_le_ref = getEdge(y, z);
	EdgeInfo y_z_le = y_z_le_ref;
	if (*d_pathLenghtThres >= 0 && y_z_le.path_length_in_edges > *d_pathLenghtThres) return false;

	Graph::ElementReference x_z_le_ref = getEdge(x, z);
	EdgeInfo x_z_le = x_z_le_ref;

	bool cycle = (x == z);
	bool updated = false;

	// Try <= + <= --> <=
	if (!isUnsat() && x_y_le.isDefined() && y_z_le.isDefined()) {
		EpsRational combined_length = x_y_le.length + y_z_le.length;
		int combined_edge_length = x_y_le.path_length_in_edges + y_z_le.path_length_in_edges;

		if (!x_z_le.isDefined() || combined_length < x_z_le.length ||
				(combined_length == x_z_le.length && (combined_edge_length < x_z_le.path_length_in_edges))) {

			if (!cycle || combined_length <= EpsRational::Zero) {

				if (!cycle || combined_length < EpsRational::Zero) {

					// Remember the path differences
					if (!cycle) {
						EpsRational difference = x_z_le.length - combined_length;
						Rational rationalDifference = difference.getRational();
						Rational newEpsilon = - x_z_le.length.getEpsilon();
						if (rationalDifference > 0 && rationalDifference < smallestPathDifference) {
							smallestPathDifference = rationalDifference;
							TRACE("diff model", "smallest path difference : ", smallestPathDifference, "");
						}
						if (newEpsilon > biggestEpsilon) {
							biggestEpsilon = newEpsilon;
							TRACE("diff model", "biggest epsilon : ", biggestEpsilon, "");
						}
					}

					// If we have a constraint among two integers variables strenghten it
					bool addAndEnqueue = false;
					if (core->okToEnqueue() && !combined_length.isInteger())
						if (x.getType() == arith->intType() && z.getType() == arith->intType())
							addAndEnqueue = true;

					x_z_le.length = combined_length;
					x_z_le.path_length_in_edges = combined_edge_length;
					x_z_le.in_path_vertex = y;
					x_z_le_ref = x_z_le;

					if (addAndEnqueue) {
						vector<Theorem> pathTheorems;
						getEdgeTheorems(x, z, x_z_le, pathTheorems);
						core->enqueueFact(rules->addInequalities(pathTheorems));
					}

					TRACE("arith diff", x.toString() + " -- > " + z.toString(), " : ", combined_length.toString());
					updated = true;
				} else
					if (core->okToEnqueue()) {
						// 0 length cycle
						vector<Theorem> antecedentThms;
						getEdgeTheorems(x, y, x_y_le, antecedentThms);
						getEdgeTheorems(y, z, y_z_le, antecedentThms);
						core->enqueueFact(rules->implyEqualities(antecedentThms));
					}

				// Try to propagate somthing in the original formula
				if (updated && !cycle && x != sourceVertex && z != sourceVertex && core->okToEnqueue())
					arith->tryPropagate(x, z, x_z_le, LE);

			}

			if (cycle && combined_length < EpsRational::Zero)
				analyseConflict(x, LE);
		}
	}

	return updated;
}

void TheoryArithOld::DifferenceLogicGraph::expandSharedTerm(const Expr& x) {

}

TheoryArithOld::DifferenceLogicGraph::~DifferenceLogicGraph() {
	for (EdgesList::iterator it = incomingEdges.begin(), it_end = incomingEdges.end(); it != it_end; it ++) {
		if ((*it).second) {
			delete (*it).second;
			free ((*it).second);
		}
	}
	for (EdgesList::iterator it = outgoingEdges.begin(), it_end = outgoingEdges.end(); it != it_end; it ++) {
		if ((*it).second) {
			delete (*it).second;
			free ((*it).second);
		}
	}
}

void TheoryArithOld::tryPropagate(const Expr& x, const Expr& y, const DifferenceLogicGraph::EdgeInfo& x_y_edge, int kind) {

	TRACE("diff atoms", "trying propagation", " x = " + x.toString(), " y = " + y.toString());

	// bail on non representative terms (we don't pass non-representative terms)
//	if (x.hasFind() && find(x).getRHS() != x) return;
//	if (y.hasFind() && find(y).getRHS() != y) return;

	// given edge x - z (kind) lenth

	// Make the index (c1 <= y - x)
	vector<Expr> t1_summands;
	t1_summands.push_back(rat(0));
	if (y != zero) t1_summands.push_back(y);
	// We have to canonize in case it is nonlinear
	// nonlinear terms are canonized with a constants --> 1*x*y, hence (-1)*1*x*y will not be canonical
	if (x != zero) t1_summands.push_back(canon(rat(-1)*x).getRHS());
	Expr t1 = canon(plusExpr(t1_summands)).getRHS();

	TRACE("diff atoms", "trying propagation", " t1 = " + t1.toString(), "");

	// The constant c1 <= y - x
	Rational c1 = - x_y_edge.length.getRational();

	// See if we can propagate anything to the formula atoms
	// c1 <= t1 ===> c <= t1 for c < c1
	AtomsMap::iterator find     = formulaAtomLowerBound.find(t1);
	AtomsMap::iterator find_end = formulaAtomLowerBound.end();
	if (find != find_end) {
  	  	set< pair<Rational, Expr> >::iterator bounds     = (*find).second.begin();
  	  	set< pair<Rational, Expr> >::iterator bounds_end = (*find).second.end();
  	  	while (bounds != bounds_end) {
  	  		const Expr& implied = (*bounds).second;
  	  		// Try to do some theory propagation
  	  		if ((*bounds).first < c1 || (implied.getKind() == LE && (*bounds).first == c1)) {
  	  			TRACE("diff atoms", "found propagation", "", "");
  	  		  	  			// c1 <= t1 => c <= t1 (for c <= c1)
  	  			// c1 < t1  => c <= t1 (for c <= c1)
  	  			// c1 <= t1 => c < t1  (for c < c1)
  	  			vector<Theorem> antecedentThms;
  	  			diffLogicGraph.getEdgeTheorems(x, y, x_y_edge, antecedentThms);
  	  			Theorem impliedThm = d_rules->implyWeakerInequalityDiffLogic(antecedentThms, implied);
  	  			enqueueFact(impliedThm);
  	  		}
  	  		bounds ++;
  	  	}
	}

	//
	// c1 <= t1 ==> !(t1 <= c) for c < c1
	//          ==> !(-c <= t2)
	// i.e. all coefficient in in the implied are opposite of t1
	find     = formulaAtomUpperBound.find(t1);
	find_end = formulaAtomUpperBound.end();
	if (find != find_end) {
		set< pair<Rational, Expr> >::iterator bounds     = (*find).second.begin();
   	  	set< pair<Rational, Expr> >::iterator bounds_end = (*find).second.end();
   	  	while (bounds != bounds_end) {
   	  		const Expr& implied = (*bounds).second;
   	  		// Try to do some theory propagation
   	  		if ((*bounds).first < c1) {
   	  			TRACE("diff atoms", "found negated propagation", "", "");
   	  			vector<Theorem> antecedentThms;
	  			diffLogicGraph.getEdgeTheorems(x, y, x_y_edge, antecedentThms);
	  			Theorem impliedThm = d_rules->implyNegatedInequalityDiffLogic(antecedentThms, implied);
	  			enqueueFact(impliedThm);
   	  		}
   	  		bounds ++;
   	  	}
	}
}

void TheoryArithOld::DifferenceLogicGraph::computeModel() {

	// If source vertex is null, create it
	if (sourceVertex.isNull()) {
		Theorem thm_exists_zero = arith->getCommonRules()->varIntroSkolem(arith->zero);
		sourceVertex = thm_exists_zero.getExpr()[1];
	}

	// The empty theorem to pass around
	Theorem thm;

	// Add an edge to all the vertices
	EdgesList::iterator vertexIt    = incomingEdges.begin();
	EdgesList::iterator vertexItEnd = incomingEdges.end();
	for (; vertexIt != vertexItEnd; vertexIt ++) {
		Expr vertex = (*vertexIt).first;
		if (core->find(vertex).getRHS() != vertex) continue;
		if (vertex != sourceVertex && !existsEdge(sourceVertex, vertex))
			addEdge(sourceVertex, vertex, 0, thm);
	}
	vertexIt    = outgoingEdges.begin();
	vertexItEnd = outgoingEdges.end();
	for (; vertexIt != vertexItEnd; vertexIt ++) {
		Expr vertex = (*vertexIt).first;
		if (core->find(vertex).getRHS() != vertex) continue;
		if (vertex != sourceVertex && !existsEdge(sourceVertex, vertex))
			addEdge(sourceVertex, vertex, 0, thm);
	}

	// Also add an edge to cvcZero
	if (!existsEdge(sourceVertex, arith->zero))
		addEdge(sourceVertex, arith->zero, 0, thm);

	// For the < edges we will have a small enough epsilon to add
	// So, we will upper-bound the number of vertices and then divide
	// the smallest edge with that number so as to not be able to bypass

}

Rational TheoryArithOld::DifferenceLogicGraph::getValuation(const Expr& x) {

	// For numbers, return it's value
	if (x.isRational()) return x.getRational();

	// For the source vertex, we don't care
	if (x == sourceVertex) return 0;

	// The path from source to targer vertex
	Graph::ElementReference x_le_c_ref = getEdge(sourceVertex, x);
	EdgeInfo x_le_c = x_le_c_ref;

	// The path from source to zero (adjusment)
	Graph::ElementReference zero_le_c_ref = getEdge(sourceVertex, arith->zero);
	EdgeInfo zero_le_c = zero_le_c_ref;

	TRACE("diff model", "zero adjustment: ", zero_le_c.length.getRational(), "");
	TRACE("diff model", "zero adjustment (eps): ", zero_le_c.length.getEpsilon(), "");

	// Value adjusted with the epsilon
	Rational epsAdjustment = (biggestEpsilon > 0 ? (x_le_c.length.getEpsilon() - zero_le_c.length.getEpsilon()) * smallestPathDifference / (2 * (biggestEpsilon + 1)) : 0);
	Rational value = x_le_c.length.getRational() + epsAdjustment;

	TRACE("diff model" , "biggest epsilon: ", biggestEpsilon, "");
	TRACE("diff model" , "smallestPathDifference: ", smallestPathDifference, "");
	TRACE("diff model" , "x_le_c.getEpsilon: ", x_le_c.length.getEpsilon(), "");
	TRACE("diff model" , "x_le_c.length: ", x_le_c.length.getRational(), "");

	// Value adjusted with the shift for zero
	value = zero_le_c.length.getRational() - value;

	TRACE("diff model", "Value of ", x, " : " + value.toString());

	// Return it
	return value;
}

// The infinity constant
const TheoryArithOld::DifferenceLogicGraph::EpsRational TheoryArithOld::DifferenceLogicGraph::EpsRational::PlusInfinity(PLUS_INFINITY);
// The negative infinity constant
const TheoryArithOld::DifferenceLogicGraph::EpsRational TheoryArithOld::DifferenceLogicGraph::EpsRational::MinusInfinity(MINUS_INFINITY);
// The negative infinity constant
const TheoryArithOld::DifferenceLogicGraph::EpsRational TheoryArithOld::DifferenceLogicGraph::EpsRational::Zero;

void TheoryArithOld::addMultiplicativeSignSplit(const Theorem& case_split_thm) {
	multiplicativeSignSplits.push_back(case_split_thm);
}

bool TheoryArithOld::addPairToArithOrder(const Expr& smaller, const Expr& bigger) {
	TRACE("arith var order", "addPairToArithOrder(" + smaller.toString(), ", ", bigger.toString() + ")");
	// We only accept arithmetic terms
	if (!isReal(smaller.getType()) && !isInt(smaller.getType())) return false;
	if (!isReal(bigger.getType()) && !isInt(bigger.getType())) return false;
	// We don't want to introduce loops
	FatalAssert(!d_graph.lessThan(smaller, bigger), "The pair (" + bigger.toString() + "," + smaller.toString() + ") is already in the order");
	// Update the graph
	d_graph.addEdge(smaller, bigger);
	return true;
}

bool TheoryArithOld::isNonlinearSumTerm(const Expr& term) {
	if (isPow(term)) return true;
	if (!isMult(term)) return false;
	int vars = 0;
	for (int j = 0; j < term.arity(); j ++)
		if (isPow(term[j])) return true;
		else if (isLeaf(term[j])) {
			vars ++;
			if (vars > 1) return true;
		}
	return false;
}

bool TheoryArithOld::isNonlinearEq(const Expr& e) {

	DebugAssert(e.isEq(), "TheoryArithOld::isNonlinear: expecting an equation" + e.toString());

	const Expr& lhs = e[0];
	const Expr& rhs = e[1];

	if (isNonlinearSumTerm(lhs) || isNonlinearSumTerm(rhs)) return true;

	// Check the right-hand side
	for (int i = 0; i < lhs.arity(); i ++)
		if (isNonlinearSumTerm(lhs[i])) return true;

	// Check the left hand side
	for (int i = 0; i < rhs.arity(); i ++)
		if (isNonlinearSumTerm(rhs[i])) return true;

	return false;
}


bool TheoryArithOld::isPowersEquality(const Expr& eq, Expr& power1, Expr& power2) {
	// equality should be in the form 0 + x1^n - x2^n = 0
	DebugAssert(eq.isEq(), "TheoryArithOld::isPowersEquality, expecting an equality got " + eq.toString());

	if (!isPlus(eq[0])) return false;
	if (eq[0].arity() != 3) return false;
	if (!(eq[0][0].isRational()) || !(eq[0][0].getRational() == 0)) return false;

	// Process the first term
	Expr term1 = eq[0][1];
	Rational term1_c;
	if (isPow(term1)) {
		term1_c = 1;
		power1 = term1;
	} else
		if (isMult(term1) && term1.arity() == 2) {
			if (term1[0].isRational()) {
				term1_c = term1[0].getRational();
				if (isPow(term1[1])) {
					if (term1_c == 1) power1 = term1[1];
					else if (term1_c == -1) power2 = term1[1];
					else return false;
				} else return false;
			} else return false;
		} else return false;

	// Process the second term
	Expr term2 = eq[0][2];
	Rational term2_c;
	if (isPow(term2)) {
		term2_c = 1;
		power1 = term2;
	} else
		if (isMult(term2) && term2.arity() == 2) {
			if (term2[0].isRational()) {
				term2_c = term2[0].getRational();
				if (isPow(term2[1])) {
					if (term2_c == 1) power1 = term2[1];
					else if (term2_c == -1) power2 = term2[1];
					else return false;
				} else return false;
			} else return false;
		} else return false;

	// Check that they are of opposite signs
	if (term1_c == term2_c) return false;

	// Check that the powers are equal numbers
	if (!power1[0].isRational()) return false;
	if (!power2[0].isRational()) return false;
	if (power1[0].getRational() != power2[0].getRational()) return false;

	// Everything is fine
	return true;
}

bool TheoryArithOld::isPowerEquality(const Expr& eq, Rational& constant, Expr& power1) {
	DebugAssert(eq.isEq(), "TheoryArithOld::isPowerEquality, expecting an equality got " + eq.toString());

	if (!isPlus(eq[0])) return false;
	if (eq[0].arity() != 2) return false;
	if (!eq[0][0].isRational()) return false;

	constant = eq[0][0].getRational();

	Expr term = eq[0][1];
	if (isPow(term)) {
		power1 = term;
		constant = -constant;
	} else
		if (isMult(term) && term.arity() == 2) {
			if (term[0].isRational() && isPow(term[1])) {
				Rational term2_c = term[0].getRational();
				if (term2_c == 1) {
					power1 = term[1];
					constant = -constant;
				} else if (term2_c == -1) {
					power1 = term[1];
					return true;
				} else return false;
			} else return false;
		} else return false;

	// Check that the power is an integer
	if (!power1[0].isRational()) return false;
	if (!power1[0].getRational().isInteger()) return false;

	return true;
}

int TheoryArithOld::termDegree(const Expr& e) {
	if (isLeaf(e)) return 1;
	if (isPow(e)) return termDegree(e[1]) * e[0].getRational().getInt();
	if (isMult(e)) {
		int degree = 0;
		for (int i = 0; i < e.arity(); i ++) degree += termDegree(e[i]);
		return degree;
	}
	return 0;
}

bool TheoryArithOld::canPickEqMonomial(const Expr& right)
{
	Expr::iterator istart = right.begin();
	Expr::iterator iend   = right.end();

	// Skip the first one
	istart++;
	for(Expr::iterator i = istart; i != iend; ++i) {

		Expr leaf;
		Rational coeff;

		// Check if linear term
		if (isLeaf(*i)) {
			leaf = *i;
			coeff = 1;
		} else if (isMult(*i) && (*i).arity() == 2 && (*i)[0].isRational() && isLeaf((*i)[1])) {
			leaf = (*i)[1];
			coeff = abs((*i)[0].getRational());
		} else
			continue;

		// If integer, must be coeff 1/-1
		if (!isIntegerThm(leaf).isNull())
			if (coeff != 1 && coeff != -1)
				continue;

		// Check if a leaf in other ones
		Expr::iterator j;
		for (j = istart; j != iend; ++j)
			if (j != i && isLeafIn(leaf, *j))
				break;
		if (j == iend)
			return true;
	}

	return false;
}

bool TheoryArithOld::isBounded(const Expr& t, BoundsQueryType queryType) {
	TRACE("arith shared", "isBounded(", t.toString(), ")");
	return hasUpperBound(t, queryType) && hasLowerBound(t, queryType);
}

TheoryArithOld::DifferenceLogicGraph::EpsRational TheoryArithOld::getUpperBound(const Expr& t, BoundsQueryType queryType)
{
	TRACE("arith shared", "getUpperBound(", t.toString(), ")");

	// If t is a constant it's bounded
	if (t.isRational()) {
		TRACE("arith shared", "getUpperBound(", t.toString(), ") ==> " + t.getRational().toString());
		return t.getRational();
	}

	// If buffered, just return it
	CDMap<Expr, DifferenceLogicGraph::EpsRational>::iterator find_t = termUpperBounded.find(t);
	if (find_t != termUpperBounded.end()) {
		TRACE("arith shared", "getUpperBound(", t.toString(), ") ==> " + (*find_t).second.toString());
		return (*find_t).second;
	} else if (queryType == QueryWithCacheAll) {
		// Asked for cache query, so no bound is found
		TRACE("arith shared", "getUpperBound(", t.toString(), ") ==> +inf");
		return DifferenceLogicGraph::EpsRational::PlusInfinity;
	}

	// Assume it's not bounded
	DifferenceLogicGraph::EpsRational upperBound = DifferenceLogicGraph::EpsRational::PlusInfinity;

	// We always buffer the leaves, so all that's left are the terms
	if (!isLeaf(t)) {
		if (isMult(t)) {
			// We only handle linear terms
			if (!isNonlinearSumTerm(t)) {
				// Separate the multiplication
				Expr c, v;
				separateMonomial(t, c, v);
				// Get the upper-bound for the variable
				if (c.getRational() > 0) upperBound = getUpperBound(v);
				else upperBound = getLowerBound(v);
				if (upperBound.isFinite()) upperBound = upperBound * c.getRational();
				else upperBound = DifferenceLogicGraph::EpsRational::PlusInfinity;
			}
		} else if (isPlus(t)) {
			// If one of them is unconstrained then the term itself is unconstrained
			upperBound = DifferenceLogicGraph::EpsRational::Zero;
			for (int i = 0; i < t.arity(); i ++) {
				Expr t_i = t[i];
				DifferenceLogicGraph::EpsRational t_i_upperBound = getUpperBound(t_i, queryType);
				if (t_i_upperBound.isFinite()) upperBound = upperBound + t_i_upperBound;
				else {
					upperBound = DifferenceLogicGraph::EpsRational::PlusInfinity;
					// Not-bounded, check for constrained
					if (queryType == QueryWithCacheLeavesAndConstrainedComputation) {
						for(; i < t.arity() && isConstrainedAbove(t[i], QueryWithCacheLeaves); i ++);
						if (i == t.arity())	{
							TRACE("arith shared", "getUpperBound(", t.toString(), ") ==> constrained");
							termConstrainedAbove[t] = true;
						}
						break;
					} else break;
				}
			}
		}
	}

	// Buffer it
	if (upperBound.isFinite()) {
		termUpperBounded[t] = upperBound;
		termConstrainedAbove[t] = true;
	}

	// Return if bounded or not
	TRACE("arith shared", "getUpperBound(", t.toString(), ") ==> " + upperBound.toString());
	return upperBound;
}

TheoryArithOld::DifferenceLogicGraph::EpsRational TheoryArithOld::getLowerBound(const Expr& t, BoundsQueryType queryType)
{
	TRACE("arith shared", "getLowerBound(", t.toString(), ")");

	// If t is a constant it's bounded
	if (t.isRational()) {
		TRACE("arith shared", "getLowerBound(", t.toString(), ") ==> " + t.getRational().toString());
		return t.getRational();
	}

	// If buffered, just return it
	CDMap<Expr, DifferenceLogicGraph::EpsRational>::iterator t_find = termLowerBounded.find(t);
	if (t_find != termLowerBounded.end()) {
		TRACE("arith shared", "getLowerBound(", t.toString(), ") ==> " + (*t_find).second.toString());
		return (*t_find).second;
	} else if (queryType == QueryWithCacheAll) {
		// Asked for cache query, so no bound is found
		TRACE("arith shared", "getLowerBound(", t.toString(), ") ==> -inf");
		return DifferenceLogicGraph::EpsRational::MinusInfinity;
	}

	// Assume it's not bounded
	DifferenceLogicGraph::EpsRational lowerBound = DifferenceLogicGraph::EpsRational::MinusInfinity;

	// Leaves are always buffered
	if (!isLeaf(t)) {
		if (isMult(t)) {
			// We only handle linear terms
			if (!isNonlinearSumTerm(t)) {
				// Separate the multiplication
				Expr c, v;
				separateMonomial(t, c, v);
				// Get the upper-bound for the variable
				if (c.getRational() > 0) lowerBound = getLowerBound(v);
				else lowerBound = getUpperBound(v);
				if (lowerBound.isFinite()) lowerBound = lowerBound * c.getRational();
				else lowerBound = DifferenceLogicGraph::EpsRational::MinusInfinity;
			}
		} else if (isPlus(t)) {
			// If one of them is unconstrained then the term itself is unconstrained
			lowerBound = DifferenceLogicGraph::EpsRational::Zero;
			for (int i = 0; i < t.arity(); i ++) {
				Expr t_i = t[i];
				DifferenceLogicGraph::EpsRational t_i_lowerBound = getLowerBound(t_i, queryType);
				if (t_i_lowerBound.isFinite()) lowerBound = lowerBound + t_i_lowerBound;
				else {
					lowerBound = DifferenceLogicGraph::EpsRational::MinusInfinity;
					// Not-bounded, check for constrained
					if (queryType == QueryWithCacheLeavesAndConstrainedComputation) {
						for(; i < t.arity() && isConstrainedBelow(t[i], QueryWithCacheLeaves); i ++);
						if (i == t.arity())	{
							TRACE("arith shared", "getLowerBound(", t.toString(), ") ==> constrained");
							termConstrainedBelow[t] = true;
						}
						break;
					} else break;
				}
			}
		}
	}

	// Buffer it
	if (lowerBound.isFinite()) {
		termLowerBounded[t] = lowerBound;
		termConstrainedBelow[t] = true;
	}

	// Return if bounded or not
	TRACE("arith shared", "getLowerBound(", t.toString(), ") ==> " + lowerBound.toString());
	return lowerBound;
}

int TheoryArithOld::computeTermBounds()
{
	int computeTermBoundsConstrainedCount = 0;

	vector<Expr> sorted_vars;
	// Get the variables in the topological order
	if (!diffLogicOnly) d_graph.getVerticesTopological(sorted_vars);
	// Or if difference logic only, just get them
	else {
		diffLogicGraph.getVariables(sorted_vars);
		IF_DEBUG(
				diffLogicGraph.writeGraph(cerr);
		)
	}

	// Go in the reverse topological order and try to see if the vats are constrained/bounded
	for (int i = sorted_vars.size() - 1; i >= 0; i --)
	{
		// Get the variable
		Expr v = sorted_vars[i];

		// If the find is not identity, skip it
		if (v.hasFind() && find(v).getRHS() != v) continue;

		TRACE("arith shared", "processing: ", v.toString(), "");

		// If the variable is not an integer, it's unconstrained, unless we are in model generation
		if (isIntegerThm(v).isNull() && !d_inModelCreation) continue;

		// We only do the computation if the variable is not already constrained
		if (!isConstrained(v, QueryWithCacheAll)) {

			// Recall if we already computed the constraint
			bool constrainedAbove = isConstrained(v, QueryWithCacheAll);

			// See if it's bounded from above in the difference graph
			DifferenceLogicGraph::EpsRational upperBound = diffLogicGraph.getEdgeWeight(v, zero);
			if (!constrainedAbove) constrainedAbove = upperBound.isFinite();

			// Try to refine the bound by checking projected inequalities
			if (!diffLogicOnly) {
				ExprMap<CDList<Ineq> *>::iterator v_left_find = d_inequalitiesLeftDB.find(v);
				// If not constraint from one side, it's unconstrained
				if (v_left_find != d_inequalitiesLeftDB.end()) {
					// Check right hand side for an unconstrained variable
					CDList<Ineq>*& left_list = (*v_left_find).second;
					if (left_list && left_list->size() > 0) {
						for (unsigned ineq_i = 0; ineq_i < left_list->size(); ineq_i ++) {
							// Get the inequality
							Ineq ineq = (*left_list)[ineq_i];
							// Get the right-hand side (v <= rhs)
							Expr rhs = ineq.ineq().getExpr()[1];
							// If rhs changed, skip it
							if (rhs.hasFind() && find(rhs).getRHS() != rhs) continue;
							// Compute the upper bound while
							DifferenceLogicGraph::EpsRational currentUpperBound = getUpperBound(rhs, (constrainedAbove ? QueryWithCacheLeaves : QueryWithCacheLeavesAndConstrainedComputation));
							if (currentUpperBound.isFinite() && (!upperBound.isFinite() || currentUpperBound < upperBound)) {
								upperBound = currentUpperBound;
								constrainedAbove = true;
							}
							// If not constrained, check if right-hand-side is constrained
							if (!constrainedAbove) constrainedAbove = isConstrainedAbove(rhs, QueryWithCacheAll);
						}
					}
				}
			}
			// Difference logic case (no projections)
			else if (!constrainedAbove) {
				// If there is no incoming edges, then the variable is not constrained
				if (!diffLogicGraph.hasIncoming(v)) constrainedAbove =  false;
				// If there is a cycle from t to t, all the variables
				// in the graph are constrained by each-other (we could
				// choose one, but it's too complicated)
				else if (diffLogicGraph.inCycle(v)) constrainedAbove = true;
				// Otherwise, since there is no bounds, and the cycles
				// can be shifted (since one of them can be taken as
				// unconstrained), we can assume that the variables is
				// not constrained. Conundrum here is that when in model-generation
				// we actually should take it as constrained so that it's
				// split on and we are on the safe side
				else constrainedAbove = d_inModelCreation;
			}

			// Cache the upper bound and upper constrained computation
			if (constrainedAbove) termConstrainedAbove[v] = true;
			if (upperBound.isFinite()) termUpperBounded[v] = upperBound;

			// Recall the below computation if it's there
			bool constrainedBelow = isConstrainedBelow(v, QueryWithCacheAll);

			// See if it's bounded from below in the difference graph
			DifferenceLogicGraph::EpsRational lowerBound = diffLogicGraph.getEdgeWeight(zero, v);
			if (lowerBound.isFinite()) lowerBound = -lowerBound;
			else lowerBound = DifferenceLogicGraph::EpsRational::MinusInfinity;
			if (!constrainedBelow) constrainedBelow = lowerBound.isFinite();

			// Try to refine the bound by checking projected inequalities
			if (!diffLogicOnly) {
				ExprMap<CDList<Ineq> *>::iterator v_right_find = d_inequalitiesRightDB.find(v);
				// If not constraint from one side, it's unconstrained
				if (v_right_find != d_inequalitiesRightDB.end()) {
					// Check right hand side for an unconstrained variable
					CDList<Ineq>*& right_list = (*v_right_find).second;
					if (right_list && right_list->size() > 0) {
						for (unsigned ineq_i = 0; ineq_i < right_list->size(); ineq_i ++) {
							// Get the inequality
							Ineq ineq = (*right_list)[ineq_i];
							// Get the right-hand side (lhs <= 0)
							Expr lhs = ineq.ineq().getExpr()[0];
							// If lhs has changed, skip it
							if (lhs.hasFind() && find(lhs).getRHS() != lhs) continue;
							// Compute the lower bound
							DifferenceLogicGraph::EpsRational currentLowerBound = getLowerBound(lhs, (constrainedBelow ? QueryWithCacheLeaves : QueryWithCacheLeavesAndConstrainedComputation));
							if (currentLowerBound.isFinite() && (!lowerBound.isFinite() || currentLowerBound > lowerBound)) {
								lowerBound = currentLowerBound;
								constrainedBelow = true;
							}
							// If not constrained, check if right-hand-side is constrained
							if (!constrainedBelow) constrainedBelow = isConstrainedBelow(lhs, QueryWithCacheAll);
						}
					}
				}
			}
			// Difference logic case (no projections)
			else if (!constrainedBelow) {
				// If there is no incoming edges, then the variable is not constrained
				if (!diffLogicGraph.hasOutgoing(v)) constrainedBelow = false;
				// If there is a cycle from t to t, all the variables
				// in the graph are constrained by each-other (we could
				// choose one, but it's too complicated)
				else if (diffLogicGraph.inCycle(v)) constrainedBelow = true;
				// Otherwise, since there is no bounds, and the cycles
				// can be shifted (since one of them can be taken as
				// unconstrained), we can assume that the variables is
				// not constrained. Conundrum here is that when in model-generation
				// we actually should take it as constrained so that it's
				// split on and we are on the safe side
				else constrainedBelow = d_inModelCreation;
			}

			// Cache the lower bound and lower constrained computation
			if (constrainedBelow) termConstrainedBelow[v] = true;
			if (lowerBound.isFinite()) termLowerBounded[v] = lowerBound;

			// Is this variable constrained
			if (constrainedAbove && constrainedBelow) computeTermBoundsConstrainedCount ++;

			TRACE("arith shared", (constrainedAbove && constrainedBelow ? "constrained " : "unconstrained "), "", "");
		} else
			computeTermBoundsConstrainedCount ++;
	}

	TRACE("arith shared", "number of constrained variables : ", int2string(computeTermBoundsConstrainedCount), " of " + int2string(sorted_vars.size()));

	return computeTermBoundsConstrainedCount;
}

bool TheoryArithOld::isConstrainedAbove(const Expr& t, BoundsQueryType queryType)
{
	TRACE("arith shared", "isConstrainedAbove(", t.toString(), ")");

	// Rational numbers are constrained
	if (t.isRational()) {
		TRACE("arith shared", "isConstrainedAbove() ==> true", "", "");
		return true;
	}

	// Look it up in the cache
	CDMap<Expr, bool>::iterator t_find = termConstrainedAbove.find(t);
	if (t_find != termConstrainedAbove.end()) {
		TRACE("arith shared", "isConstrainedAbove() ==> true", "", "");
		return true;
	}
	else if (queryType == QueryWithCacheAll) {
		TRACE("arith shared", "isConstrainedAbove() ==> false", "", "");
		return false;
	}

	bool constrainedAbove = true;

	if (isLeaf(t)) {
		// Leaves are always cached
		constrainedAbove = false;
	} else {
		if (isMult(t)) {
			// Non-linear terms are constrained by default
			// we only deal with the linear stuff
			if (!isNonlinearSumTerm(t)) {
				// Separate the multiplication
				Expr c, v;
				separateMonomial(t, c, v);
				// Check if the variable is constrained
				if (c.getRational() > 0) constrainedAbove = isConstrainedAbove(v, queryType);
				else constrainedAbove = isConstrainedBelow(v, queryType);
			}
		} else if (isPlus(t)) {
			// If one of them is unconstrained then the term itself is unconstrained
			for (int i = 0; i < t.arity() && constrainedAbove; i ++)
				if (!isConstrainedAbove(t[i])) constrainedAbove = false;
		}
	}

	// Remember it
	if (constrainedAbove) termConstrainedAbove[t] = true;

	TRACE("arith shared", "isConstrainedAbove() ==> ", constrainedAbove ? "true" : "false", "");

	// Return in
	return constrainedAbove;
}

bool TheoryArithOld::isConstrainedBelow(const Expr& t, BoundsQueryType queryType)
{
	TRACE("arith shared", "isConstrainedBelow(", t.toString(), ")");

	// Rational numbers are constrained
	if (t.isRational()) return true;

	// Look it up in the cache
	CDMap<Expr, bool>::iterator t_find = termConstrainedBelow.find(t);
	if (t_find != termConstrainedBelow.end()) {
		TRACE("arith shared", "isConstrainedBelow() ==> true", "", "");
		return true;
	}
	else if (queryType == QueryWithCacheAll) {
		TRACE("arith shared", "isConstrainedBelow() ==> false", "", "");
		return false;
	}

	bool constrainedBelow = true;

	if (isLeaf(t)) {
		// Leaves are always cached
		constrainedBelow = false;
	} else {
		if (isMult(t)) {
			// Non-linear terms are constrained by default
			// we only deal with the linear stuff
			if (!isNonlinearSumTerm(t)) {
				// Separate the multiplication
				Expr c, v;
				separateMonomial(t, c, v);
				// Check if the variable is constrained
				if (c.getRational() > 0) constrainedBelow = isConstrainedBelow(v, queryType);
				else constrainedBelow = isConstrainedAbove(v, queryType);
			}
		} else if (isPlus(t)) {
			// If one of them is unconstrained then the term itself is unconstrained
			constrainedBelow = true;
			for (int i = 0; i < t.arity() && constrainedBelow; i ++)
				if (!isConstrainedBelow(t[i]))
					constrainedBelow = false;
		}
	}

	// Cache it
	if (constrainedBelow) termConstrainedBelow[t] = true;

	TRACE("arith shared", "isConstrainedBelow() ==> ", constrainedBelow ? "true" : "false", "");

	// Return it
	return constrainedBelow;
}

bool TheoryArithOld::isConstrained(const Expr& t, bool intOnly, BoundsQueryType queryType)
{
	TRACE("arith shared", "isConstrained(", t.toString(), ")");
	// For the reals we consider them unconstrained if not asked for full check
	if (intOnly && isIntegerThm(t).isNull()) return false;
	bool result = (isConstrainedAbove(t, queryType) && isConstrainedBelow(t, queryType));
	TRACE("arith shared", "isConstrained(", t.toString(), (result ? ") ==>  true " : ") ==>  false ") );
	return result;
}

bool TheoryArithOld::DifferenceLogicGraph::hasIncoming(const Expr& x)
{
	EdgesList::iterator find_x = incomingEdges.find(x);

	// No edges at all meaning no incoming
	if (find_x == incomingEdges.end()) return false;

	// The pointer being null, also no incoming
	CDList<Expr>*& list = (*find_x).second;
	if (!list) return false;

	// If in model creation, source vertex goes to all vertices
	if (sourceVertex.isNull())
		return list->size() > 0;
	else
		return list->size() > 1;
}

bool TheoryArithOld::DifferenceLogicGraph::hasOutgoing(const Expr& x)
{
	EdgesList::iterator find_x = outgoingEdges.find(x);

	// No edges at all meaning no incoming
	if (find_x == outgoingEdges.end()) return false;

	// The pointer being null, also no incoming
	CDList<Expr>*& list = (*find_x).second;
	if (!list) return false;

	// If the list is not empty we have outgoing edges
	return list->size() > 0;
}

void TheoryArithOld::DifferenceLogicGraph::getVariables(vector<Expr>& variables)
{
	set<Expr> vars_set;

	EdgesList::iterator incoming_it     = incomingEdges.begin();
	EdgesList::iterator incoming_it_end = incomingEdges.end();
	while (incoming_it != incoming_it_end) {
		Expr var = (*incoming_it).first;
		if (var != sourceVertex)
			vars_set.insert(var);
		incoming_it ++;
	}

	EdgesList::iterator outgoing_it     = outgoingEdges.begin();
	EdgesList::iterator outgoing_it_end = outgoingEdges.end();
	while (outgoing_it != outgoing_it_end) {
		Expr var = (*outgoing_it).first;
		if (var != sourceVertex)
			vars_set.insert(var);
		outgoing_it ++;
	}

	set<Expr>::iterator set_it     = vars_set.begin();
	set<Expr>::iterator set_it_end = vars_set.end();
	while (set_it != set_it_end) {
		variables.push_back(*set_it);
		set_it ++;
	}
}

void TheoryArithOld::DifferenceLogicGraph::writeGraph(ostream& out) {
  return;
        out << "digraph G {" << endl;

	EdgesList::iterator incoming_it     = incomingEdges.begin();
	EdgesList::iterator incoming_it_end = incomingEdges.end();
	while (incoming_it != incoming_it_end) {

		Expr var_u = (*incoming_it).first;

		CDList<Expr>* edges = (*incoming_it).second;
		if (edges)
			for (unsigned edge_i = 0; edge_i < edges->size(); edge_i ++) {
				Expr var_v = (*edges)[edge_i];
				out << var_u.toString() << " -> " << var_v.toString() << endl;
			}

		incoming_it ++;
	}

	out << "}" << endl;
}
