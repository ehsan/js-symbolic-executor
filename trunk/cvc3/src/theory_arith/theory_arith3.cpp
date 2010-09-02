/*****************************************************************************/
/*!
 * \file theory_arith3.cpp
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


#include "theory_arith3.h"
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
// TheoryArith3::FreeConst Methods                                            //
///////////////////////////////////////////////////////////////////////////////

namespace CVC3 {

ostream& operator<<(ostream& os, const TheoryArith3::FreeConst& fc) {
  os << "FreeConst(r=" << fc.getConst() << ", "
     << (fc.strict()? "strict" : "non-strict") << ")";
  return os;
}

///////////////////////////////////////////////////////////////////////////////
// TheoryArith3::Ineq Methods                                                 //
///////////////////////////////////////////////////////////////////////////////

ostream& operator<<(ostream& os, const TheoryArith3::Ineq& ineq) {
  os << "Ineq(" << ineq.ineq().getExpr() << ", isolated on "
     << (ineq.varOnRHS()? "RHS" : "LHS") << ", const = "
     << ineq.getConst() << ")";
  return os;
}
} // End of namespace CVC3


///////////////////////////////////////////////////////////////////////////////
// TheoryArith3 Private Methods                                               //
///////////////////////////////////////////////////////////////////////////////


Theorem TheoryArith3::isIntegerThm(const Expr& e) {
  // Quick check
  if(isReal(e.getType())) return Theorem();
  // Try harder
  return isIntegerDerive(Expr(IS_INTEGER, e), typePred(e));
}


Theorem TheoryArith3::isIntegerDerive(const Expr& isIntE, const Theorem& thm) {
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

const Rational& TheoryArith3::freeConstIneq(const Expr& ineq, bool varOnRHS) {
  DebugAssert(isIneq(ineq), "TheoryArith3::freeConstIneq("+ineq.toString()+")");
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


const TheoryArith3::FreeConst&
TheoryArith3::updateSubsumptionDB(const Expr& ineq, bool varOnRHS,
				 bool& subsumed) {
  TRACE("arith ineq", "TheoryArith3::updateSubsumptionDB(", ineq,
	", var isolated on "+string(varOnRHS? "RHS" : "LHS")+")");
  DebugAssert(isLT(ineq) || isLE(ineq), "TheoryArith3::updateSubsumptionDB("
	      +ineq.toString()+")");
  // Indexing expression: same as ineq only without the free const
  Expr index;
  const Expr& t = varOnRHS? ineq[0] : ineq[1];
  bool strict(isLT(ineq));
  Rational c(0);
  if(isPlus(t)) {
    DebugAssert(t.arity() >= 2, "TheoryArith3::updateSubsumptionDB("
		+ineq.toString()+")");
    c = t[0].getRational(); // Extract the free const in ineq
    Expr newT;
    if(t.arity() == 2) {
      newT = t[1];
    } else {
      vector<Expr> kids;
      Expr::iterator i=t.begin(), iend=t.end();
      for(++i; i!=iend; ++i) kids.push_back(*i);
      DebugAssert(kids.size() > 0, "kids.size = "+int2string(kids.size())
		  +", ineq = "+ineq.toString());
      newT = plusExpr(kids);
    }
    if(varOnRHS)
      index = leExpr(newT, ineq[1]);
    else
      index = leExpr(ineq[0], newT);
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


bool TheoryArith3::kidsCanonical(const Expr& e) {
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
// Function: TheoryArith3::canon                                              //
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
Theorem TheoryArith3::canon(const Expr& e)
{
  TRACE("arith canon","canon(",e,") {");
  DebugAssert(kidsCanonical(e), "TheoryArith3::canon("+e.toString()+")");
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
//       if (e[1].isRational() && e[1].getRational() == 0)
//         throw ArithException("Divide by 0 error in "+e.toString());
      if (e[1].getKind() == PLUS)
        throw ArithException("Divide by a PLUS expression not handled in"+e.toString());
      result = d_rules->canonDivide(e);
      break;
    }
  case POW:
    if(e[1].isRational())
      result = d_rules->canonPowConst(e);
    else
      result = reflexivityRule(e);
    break;
  default:
      result = reflexivityRule(e);
      break;
    }
  TRACE("arith canon","canon => ",result," }");
  return result;
}


Theorem
TheoryArith3::canonSimplify(const Expr& e) {
  TRACE("arith", "canonSimplify(", e, ") {");
  DebugAssert(kidsCanonical(e),
	      "TheoryArith3::canonSimplify("+e.toString()+")");
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
TheoryArith3::canonPred(const Theorem& thm) {
  vector<Theorem> thms;
  DebugAssert(thm.getExpr().arity() == 2,
              "TheoryArith3::canonPred: bad theorem: "+thm.toString());
  Expr e(thm.getExpr());
  thms.push_back(canonSimplify(e[0]));
  thms.push_back(canonSimplify(e[1]));
  return iffMP(thm, substitutivityRule(e.getOp(), thms));
}

/*! accepts an equivalence theorem, canonizes it, applies iffMP and
 *  substituvity to derive the canonized thm
 */
Theorem
TheoryArith3::canonPredEquiv(const Theorem& thm) {
  vector<Theorem> thms;
  DebugAssert(thm.getRHS().arity() == 2,
              "TheoryArith3::canonPredEquiv: bad theorem: "+thm.toString());
  Expr e(thm.getRHS());
  thms.push_back(canonSimplify(e[0]));
  thms.push_back(canonSimplify(e[1]));
  return transitivityRule(thm, substitutivityRule(e.getOp(), thms));
}

/*! accepts an equivalence theorem whose RHS is a conjunction,
 *  canonizes it, applies iffMP and substituvity to derive the
 *  canonized thm
 */
Theorem
TheoryArith3::canonConjunctionEquiv(const Theorem& thm) {
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
Theorem TheoryArith3::doSolve(const Theorem& thm)
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

    // Nonlinear heuristics
    Theorem res;
    if (isPlus(right)) {

      // Search for common factor
      if (right[0].getRational() == 0) {
        Expr::iterator i = right.begin(), iend = right.end();
        ++i;
        set<Expr> factors;
        set<Expr>::iterator is, isend;
        getFactors(*i, factors);
        for (++i; i != iend; ++i) {
          set<Expr> factors2;
          getFactors(*i, factors2);
          for (is = factors.begin(), isend = factors.end(); is != isend; ++is) {
            if (factors2.find(*is) == factors2.end()) {
              factors.erase(is);
            }
          }
          if (factors.empty()) break;
        }
        if (!factors.empty()) {
          enqueueFact(iffMP(eqnThm, d_rules->divideEqnNonConst(rat(0), right, *(factors.begin()))));
          return getCommonRules()->trueTheorem();
        }
      }

      // Solve for something
      Expr isolated = right[1];
      Rational coeff;
      if (isMult(isolated) && isolated[0].isRational()) {
        coeff = isolated[0].getRational();
        DebugAssert(coeff != 0, "Expected nonzero coeff");
        isolated = canon(isolated / rat(coeff)).getRHS();
      } else coeff = 1;
      res = iffMP(eqnThm, d_rules->multEqn(rat(0), right, rat(-1/coeff)));
      res = canonPred(res);
      res = iffMP(res, d_rules->plusPredicate(res.getLHS(), res.getRHS(),
                                              isolated, EQ));
      res = canonPred(res);

      // Look for equal powers
      if (isPow(res.getLHS())) {
        Expr left = res.getLHS();
        if (isInteger(left[0])) {
          Rational pow = left[0].getRational();
          if (pow > 1) {
            right = res.getRHS();
            if (isPow(right) && right[0] == left[0]) {
              enqueueFact(iffMP(res, d_rules->elimPower(res.getExpr())));
              return getCommonRules()->trueTheorem();
            }
            else if (right.isRational()) {
              Rational r = right.getRational();
              if (pow % 2 == 0 && r < 0) {
                return iffMP(res, d_rules->evenPowerEqNegConst(res.getExpr()));
              }
              DebugAssert(r != 0, "Expected nonzero const");
              Rational root = ratRoot(r, pow.getUnsigned());
              if (root != 0) {
                enqueueFact(iffMP(res, d_rules->elimPowerConst(res.getExpr(), root)));
                return getCommonRules()->trueTheorem();
              }
              else if (isInt(left[1].getType())) {
                Theorem isIntx(isIntegerThm(left[1]));
                DebugAssert(!isIntx.isNull(), "left = "+left.toString());
                return iffMP(res, d_rules->intEqIrrational(res.getExpr(), isIntx));
              }
            }
          }
        }
      }
    }
    else {
      res = symmetryRule(eqnThm); // Flip to e' = 0
    }
    TRACE("arith eq", "doSolve: failed to solve an equation: ", e, "");
    IF_DEBUG(debugger.counter("FAILED to solve equalities")++;)
    setIncomplete("Non-linear arithmetic equalities");
    return res;
  }
  FatalAssert(false, "");
  return Theorem();
}

/*! pick a monomial for the input equation. This function is used only
 *  if the equation is an integer equation. Choose the monomial with
 *  the smallest absolute value of coefficient.
 */
bool TheoryArith3::pickIntEqMonomial(const Expr& right, Expr& isolated, bool& nonlin)
{
  DebugAssert(isPlus(right) && right.arity() > 1,
              "TheoryArith3::pickIntEqMonomial right is wrong :-): " +
              right.toString());
  DebugAssert(right[0].isRational(),
              "TheoryArith3::pickIntEqMonomial. right[0] must be const" +
              right.toString());
  DebugAssert(isInteger(right),
              "TheoryArith3::pickIntEqMonomial: right is of type int: " +
              right.toString());
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
TheoryArith3::processRealEq(const Theorem& eqn)
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
              "TheoryArith3::ProcessRealEq: left is integer:\n left = "
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


void TheoryArith3::getFactors(const Expr& e, set<Expr>& factors)
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
TheoryArith3::processSimpleIntEq(const Theorem& eqn)
{
  TRACE("arith eq", "processSimpleIntEq(", eqn.getExpr(), ") {");
  DebugAssert(eqn.isRewrite(),
              "TheoryArith3::processSimpleIntEq: eqn must be equality" +
              eqn.getExpr().toString());

  Expr right = eqn.getRHS();

  DebugAssert(eqn.getLHS().isRational() && 0 == eqn.getLHS().getRational(),
              "TheoryArith3::processSimpleIntEq: LHS must be 0:\n" +
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
                    "TheoryArith3::processSimpleIntEq: isolated must be mult "
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
TheoryArith3::processIntEq(const Theorem& eqn)
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
		  "TheoryArith3::processIntEq("+eqn.getExpr().toString()
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
TheoryArith3::solvedForm(const vector<Theorem>& solvedEqs)
{
  DebugAssert(solvedEqs.size() > 0, "TheoryArith3::solvedForm()");

  // Trace code
  TRACE_MSG("arith eq", "TheoryArith3::solvedForm:solvedEqs(\n  [");
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
		  "TheoryArith3::solvedForm: an element of solvedEqs must "
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
TheoryArith3::substAndCanonize(const Expr& t, ExprMap<Theorem>& subst)
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
TheoryArith3::substAndCanonize(const Theorem& eq, ExprMap<Theorem>& subst)
{
  // Quick and dirty check: return immediately if subst is empty
  if(subst.empty()) return eq;

  DebugAssert(eq.isRewrite(), "TheoryArith3::substAndCanonize: t = "
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


void TheoryArith3::processBuffer()
{
  // Process the inequalities in the buffer
  bool varOnRHS;

  for(; !inconsistent() && d_bufferIdx < d_buffer.size();
      d_bufferIdx = d_bufferIdx+1) {
    const Theorem& ineqThm = d_buffer[d_bufferIdx];
    // Skip this inequality if it is stale
    if(isStale(ineqThm.getExpr())) continue;
    Theorem thm1 = isolateVariable(ineqThm, varOnRHS);
    const Expr& ineq = thm1.getExpr();
    if((ineq).isFalse())
      setInconsistent(thm1);
    else if(!ineq.isTrue()) {
      // Check that the variable is indeed isolated correctly
      DebugAssert(varOnRHS? !isPlus(ineq[1]) : !isPlus(ineq[0]),
		  "TheoryArith3::processBuffer(): bad result from "
		  "isolateVariable:\nineq = "+ineq.toString());
      // and project the inequality
      projectInequalities(thm1, varOnRHS);
    }
  }
}


void TheoryArith3::updateStats(const Rational& c, const Expr& v)
{
  TRACE("arith ineq", "updateStats("+c.toString()+", ", v, ")");

  // Dejan: update the max coefficient of the variable
  if (c < 0) {
	  // Goes to the left side
	  CDMap<Expr, Rational>::iterator maxFind = maxCoefficientLeft.find(v);
	  if (maxFind == maxCoefficientLeft.end())
		  maxCoefficientLeft[v] = - c;
	  else
		  if ((*maxFind).second < -c)
			  (*maxFind).second = -c;
  } else {
	  // Stays on the right side
	  CDMap<Expr, Rational>::iterator maxFind = maxCoefficientRight.find(v);
	  if (maxFind == maxCoefficientRight.end())
		  maxCoefficientRight[v] = c;
	  else
		  if((*maxFind).second < c)
			  (*maxFind).second = c;
  }

  if(c > 0) {
    if(d_countRight.count(v) > 0) d_countRight[v] = d_countRight[v] + 1;
    else d_countRight[v] = 1;
  }
  else
    if(d_countLeft.count(v) > 0) d_countLeft[v] = d_countLeft[v] + 1;
    else d_countLeft[v] = 1;
}


void TheoryArith3::updateStats(const Expr& monomial)
{
  Expr c, m;
  separateMonomial(monomial, c, m);
  updateStats(c.getRational(), m);
}


void TheoryArith3::addToBuffer(const Theorem& thm) {
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


Theorem TheoryArith3::isolateVariable(const Theorem& inputThm,
                                     bool& isolatedVarOnRHS)
{
  Theorem result(inputThm);
  const Expr& e = inputThm.getExpr();
  TRACE("arith","isolateVariable(",e,") {");
  TRACE("arith ineq", "isolateVariable(", e, ") {");
  //we assume all the children of e are canonized
  DebugAssert(isLT(e)||isLE(e),
              "TheoryArith3::isolateVariable: " + e.toString() +
              " wrong kind");
  int kind = e.getKind();
  DebugAssert(e[0].isRational() && e[0].getRational() == 0,
              "TheoryArith3::isolateVariable: theorem must be of "
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

  Expr factor(computeNormalFactor(right));
  TRACE("arith", "isolateVariable: factor = ", factor, "");
  DebugAssert(factor.getRational() > 0,
              "isolateVariable: factor="+factor.toString());
  // Now multiply the inequality by the factor, unless it is 1
  if(factor.getRational() != 1) {
    result = iffMP(result, d_rules->multIneqn(e, factor));
    // And canonize the result
    result = canonPred(result);
    right = result.getExpr()[1];
  }

  // Find monomial to isolate and store it in isolatedMonomial
  Expr isolatedMonomial = right;

  if (isPlus(right))
    isolatedMonomial = pickMonomial(right);

  Rational r = -1;
  isolatedVarOnRHS = true;
  if (isMult(isolatedMonomial)) {
    r = ((isolatedMonomial[0].getRational()) >= 0)? -1 : 1;
    isolatedVarOnRHS =
      ((isolatedMonomial[0].getRational()) >= 0)? true : false;
  }
  isolatedMonomial = canon(rat(-1)*isolatedMonomial).getRHS();
  // Isolate isolatedMonomial on to the LHS
  result = iffMP(result, d_rules->plusPredicate(zero, right,
                                                isolatedMonomial, kind));
  // Canonize the resulting inequality
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
TheoryArith3::computeNormalFactor(const Expr& right) {
  // Strategy: compute f = lcm(d1...dn)/gcd(c1...cn), where the RHS is
  // of the form c1/d1*x1 + ... + cn/dn*xn
  Rational factor;
  if(isPlus(right)) {
    vector<Rational> nums, denoms;
    for(int i=0, iend=right.arity(); i<iend; ++i) {
      switch(right[i].getKind()) {
      case RATIONAL_EXPR: {
        Rational c(abs(right[i].getRational()));
        nums.push_back(c.getNumerator());
        denoms.push_back(c.getDenominator());
        break;
        }
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


bool TheoryArith3::lessThanVar(const Expr& isolatedMonomial, const Expr& var2)
{
  DebugAssert(!isRational(var2) && !isRational(isolatedMonomial),
              "TheoryArith3::findMaxVar: isolatedMonomial cannot be rational" +
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
bool TheoryArith3::isStale(const Expr& e) {
  if(e.isTerm())
    return e != find(e).getRHS();
  // It's better be a simple predicate (like inequality); we check the
  // kids recursively
  bool stale=false;
  for(Expr::iterator i=e.begin(), iend=e.end(); !stale && i!=iend; ++i)
    stale = isStale(*i);
  return stale;
}


bool TheoryArith3::isStale(const TheoryArith3::Ineq& ineq) {
  TRACE("arith ineq", "isStale(", ineq, ") {");
  const Expr& ineqExpr = ineq.ineq().getExpr();
  const Rational& c = freeConstIneq(ineqExpr, ineq.varOnRHS());
  bool strict(isLT(ineqExpr));
  const FreeConst& fc = ineq.getConst();

  bool subsumed;

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


void TheoryArith3::separateMonomial(const Expr& e, Expr& c, Expr& var) {
  TRACE("separateMonomial", "separateMonomial(", e, ")");
  DebugAssert(!isPlus(e),
	      "TheoryArith3::separateMonomial(e = "+e.toString()+")");
  if(isMult(e)) {
    DebugAssert(e.arity() >= 2,
		"TheoryArith3::separateMonomial(e = "+e.toString()+")");
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
  DebugAssert(c.isRational(), "TheoryArith3::separateMonomial(e = "
	      +e.toString()+", c = "+c.toString()+")");
  DebugAssert(!isMult(var) || (var[0].isRational() && var[0].getRational()==1),
	      "TheoryArith3::separateMonomial(e = "
	      +e.toString()+", var = "+var.toString()+")");
}


void TheoryArith3::projectInequalities(const Theorem& theInequality,
                                      bool isolatedVarOnRHS)
{
  TRACE("arith ineq", "projectInequalities(", theInequality.getExpr(),
        ", isolatedVarOnRHS="+string(isolatedVarOnRHS? "true" : "false")
        +") {");
  DebugAssert(isLE(theInequality.getExpr()) ||
              isLT(theInequality.getExpr()),
              "TheoryArith3::projectIsolatedVar: "\
              "theInequality is of the wrong form: " +
              theInequality.toString());
  //TODO: DebugAssert to check if the isolatedMonomial is of the right
  //form and the whether we are indeed getting inequalities.
  Theorem theIneqThm(theInequality);
  Expr theIneq = theIneqThm.getExpr();

  Theorem isIntLHS(isIntegerThm(theIneq[0]));
  Theorem isIntRHS(isIntegerThm(theIneq[1]));
  bool isInt = (!isIntLHS.isNull() && !isIntRHS.isNull());
  // If the inequality is strict and integer, change it to non-strict
  if(isLT(theIneq) && isInt) {
    Theorem thm = d_rules->lessThanToLE(theInequality, isIntLHS, isIntRHS,
					!isolatedVarOnRHS);
    theIneqThm = canonPred(iffMP(theIneqThm, thm));
    theIneq = theIneqThm.getExpr();
  }
  Expr isolatedMonomial =
    isolatedVarOnRHS ? theIneq[1] : theIneq[0];

  Expr monomialVar, a;
  separateMonomial(isolatedMonomial, a, monomialVar);

  bool subsumed;
  const FreeConst& bestConst =
    updateSubsumptionDB(theIneq, isolatedVarOnRHS, subsumed);

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
    ExprMap<CDList<Ineq> *>& db1 =
      isolatedVarOnRHS ? d_inequalitiesRightDB : d_inequalitiesLeftDB;
    ExprMap<CDList<Ineq> *>::iterator it1 = db1.find(monomialVar);
    if(it1 == db1.end()) {
      CDList<Ineq> * list = new(true) CDList<Ineq>(theoryCore()->getCM()->getCurrentContext());
      list->push_back(Ineq(theIneqThm, isolatedVarOnRHS, bestConst));
      db1[monomialVar] = list;
    }
    else
      ((*it1).second)->push_back(Ineq(theIneqThm, isolatedVarOnRHS, bestConst));

    ExprMap<CDList<Ineq> *>& db2 =
      isolatedVarOnRHS ? d_inequalitiesLeftDB : d_inequalitiesRightDB;
    ExprMap<CDList<Ineq> *>::iterator it = db2.find(monomialVar);
    if(it == db2.end()) {
      TRACE_MSG("arith ineq", "projectInequalities[not in DB] => }");
      return;
    }

    CDList<Ineq>& listOfDBIneqs = *((*it).second);
    Theorem betaLTt, tLTalpha, thm;
    for(size_t i = 0, iend=listOfDBIneqs.size(); i!=iend; ++i) {
      const Ineq& ineqEntry = listOfDBIneqs[i];
      const Theorem& ineqThm = ineqEntry.ineq();
      if(!isStale(ineqEntry)) {
	betaLTt = isolatedVarOnRHS ? theIneqThm : ineqThm;
	tLTalpha = isolatedVarOnRHS ? ineqThm : theIneqThm;
	thm = normalizeProjectIneqs(betaLTt, tLTalpha);

	IF_DEBUG(debugger.counter("real shadows")++;)

	// Check for TRUE and FALSE theorems
	Expr e(thm.getExpr());	if(e.isFalse()) {
	  setInconsistent(thm);
	  TRACE_MSG("arith ineq", "projectInequalities[inconsistent] => }");
	  return;
	}
	else {
	  if(!e.isTrue() && !e.isEq())
	    addToBuffer(thm);
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

Theorem TheoryArith3::normalizeProjectIneqs(const Theorem& ineqThm1,
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
              "TheoryArith3::normalizeProjectIneqs: Wrong Kind inputs: " +
              ineq1.toString() + ineq2.toString());
  DebugAssert(!isPlus(ineq1[1]) && !isPlus(ineq2[0]),
              "TheoryArith3::normalizeProjectIneqs: Wrong Kind inputs: " +
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
    const Expr& D = DorG[0];
    const Expr& G = DorG[1];
    DebugAssert(D.getKind()==DARK_SHADOW, "D = "+D.toString());
    DebugAssert(G.getKind()==GRAY_SHADOW, "G = "+G.toString());
    // Set the higher splitter priority for dark shadow
    Expr tmp = simplifyExpr(D);
    if (!tmp.isBoolConst())
      addSplitter(tmp, 5);
    // Also set a higher priority to the NEGATION of GRAY_SHADOW
    tmp = simplifyExpr(!G);
    if (!tmp.isBoolConst())
      addSplitter(tmp, 1);
    IF_DEBUG(debugger.counter("dark+gray shadows")++;)
  }

  //actually normalize the inequalities
  if(1 != factor1) {
    std::vector<Theorem> thms1;
    Theorem thm2 = iffMP(betaLTt, d_rules->multIneqn(ineq1, rat(factor1)));
    betaLTt = canonPred(thm2);
    ineq1 = betaLTt.getExpr();
  }
  if(1 != factor2) {
    std::vector<Theorem> thms1;
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
  if(isInt)
    processFiniteInterval(betaLTt, tLTalpha);

  //project the normalized inequalities.

  Theorem result = d_rules->realShadow(betaLTt, tLTalpha);

  // FIXME: Clark's changes.  Is 'rewrite' more or less efficient?
//   result = iffMP(result, rewrite(result.getExpr()));
//   TRACE("arith ineq", "normalizeProjectIneqs => ", result, " }");

  // Now, transform the result into 0 < rhs and see if rhs is a const
  Expr e(result.getExpr());
  // int kind = e.getKind();
  if(!(e[0].isRational() && e[0].getRational() == 0)) {
    result = iffMP(result, d_rules->rightMinusLeft(e));
    result = canonPred(result);
  }

  //result is "0 kind e'". where e' is equal to canon(e[1]-e[0])
  Expr right = result.getExpr()[1];
  // Check for trivial inequality
  if (right.isRational())
    result = iffMP(result, d_rules->constPredicate(result.getExpr()));
  TRACE("arith ineq", "normalizeProjectIneqs => ", result, " }");
  return result;
}

Rational TheoryArith3::currentMaxCoefficient(Expr var)
{
	bool foundLeft = false;
	bool foundRight = false;
	Rational leftMax = 1;
	Rational rightMax = 1;

	// If the coefitient was found earlier and fixed, just return it
	CDMap<Expr, Rational>::iterator findFixed = fixedMaxCoefficient.find(var);
	if (findFixed != fixedMaxCoefficient.end())
		return (*findFixed).second;

	// Find the biggest left side coefficient
	CDMap<Expr, Rational>::iterator findMaxLeft = maxCoefficientLeft.find(var);
	if (findMaxLeft != maxCoefficientLeft.end()) {
		foundLeft = true;
		leftMax = (*findMaxLeft).second;
	}

	//
	CDMap<Expr, Rational>::iterator findMaxRight = maxCoefficientRight.find(var);
	if (findMaxRight != maxCoefficientRight.end()) {
		foundRight = true;
		rightMax = (*findMaxRight).second;
	}

	if (foundLeft && foundRight) {
		if (leftMax < rightMax) return rightMax;
		else return leftMax;
	}

	return Rational(1) / (leftMax * rightMax);
}

void TheoryArith3::fixCurrentMaxCoefficient(Expr var, Rational max) {
	fixedMaxCoefficient[var] = max;
}

void TheoryArith3::selectSmallestByCoefficient(vector<Expr> input, vector<Expr>& output) {

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

		// If equal to the current best, push it to the stack
		if (current_coefficient == best_coefficient)
			  output.push_back(current_variable);
	}

    // Fix the selected best coefficient
	fixCurrentMaxCoefficient(best_variable, best_coefficient);
}

Expr TheoryArith3::pickMonomial(const Expr& right)
{
  DebugAssert(isPlus(right), "TheoryArith3::pickMonomial: Wrong Kind: " +
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
              "TheoryArith3::pickMonomial: selectLargest: failed!!!!");

  // DEJAN: Rafine the largest by coefficient values
  vector<Expr> largest_small_coeff;
  selectSmallestByCoefficient(largest, largest_small_coeff);
  DebugAssert(0 < largest_small_coeff.size(), "TheoryArith3::pickMonomial: selectLargestByCOefficient: failed!!!!");

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

  return var2monomial[largestVar];
}

void TheoryArith3::VarOrderGraph::addEdge(const Expr& e1, const Expr& e2)
{
  TRACE("arith var order", "addEdge("+e1.toString()+" > ", e2, ")");
  DebugAssert(e1 != e2, "TheoryArith3::VarOrderGraph::addEdge("
	      +e1.toString()+", "+e2.toString()+")");
  d_edges[e1].push_back(e2);
}

//returns true if e1 < e2, else false(i.e e2 < e1 or e1,e2 are not
//comparable)
bool TheoryArith3::VarOrderGraph::lessThan(const Expr& e1, const Expr& e2)
{
  d_cache.clear();
  //returns true if e1 is in the subtree rooted at e2 implying e1 < e2
  return dfs(e1,e2);
}

//returns true if e1 is in the subtree rooted at e2 implying e1 < e2
bool TheoryArith3::VarOrderGraph::dfs(const Expr& e1, const Expr& e2)
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


void TheoryArith3::VarOrderGraph::selectSmallest(vector<Expr>& v1,
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


void TheoryArith3::VarOrderGraph::selectLargest(const vector<Expr>& v1,
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
// TheoryArith3 Public Methods                                                //
///////////////////////////////////////////////////////////////////////////////


TheoryArith3::TheoryArith3(TheoryCore* core)
  : TheoryArith(core, "Arithmetic3"),
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
    maxCoefficientLeft(core->getCM()->getCurrentContext()),
    maxCoefficientRight(core->getCM()->getCurrentContext()),
    fixedMaxCoefficient(core->getCM()->getCurrentContext())
{
  IF_DEBUG(d_diseq.setName("CDList[TheoryArith3::d_diseq]");)
  IF_DEBUG(d_buffer.setName("CDList[TheoryArith3::d_buffer]");)
  IF_DEBUG(d_bufferIdx.setName("CDList[TheoryArith3::d_bufferIdx]");)

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

  d_rules = createProofRules3();

  d_realType = Type(getEM()->newLeafExpr(REAL));
  d_intType  = Type(getEM()->newLeafExpr(INT));
}


// Destructor: delete the proof rules class if it's present
TheoryArith3::~TheoryArith3() {
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

void TheoryArith3::collectVars(const Expr& e, vector<Expr>& vars,
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
TheoryArith3::processFiniteInterval(const Theorem& alphaLEax,
				   const Theorem& bxLEbeta) {
  const Expr& ineq1(alphaLEax.getExpr());
  const Expr& ineq2(bxLEbeta.getExpr());
  DebugAssert(isLE(ineq1), "TheoryArith3::processFiniteInterval: ineq1 = "
	      +ineq1.toString());
  DebugAssert(isLE(ineq2), "TheoryArith3::processFiniteInterval: ineq2 = "
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
	      "TheoryArith3::processFiniteInterval:\n ax = "+ax.toString());
  DebugAssert(!isPlus(bx) && !isRational(bx),
	      "TheoryArith3::processFiniteInterval:\n bx = "+bx.toString());
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
TheoryArith3::processFiniteIntervals(const Expr& x) {
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
TheoryArith3::setupRec(const Expr& e) {
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


void TheoryArith3::addSharedTerm(const Expr& e) {
  d_sharedTerms[e] = true;
}


void TheoryArith3::assertFact(const Theorem& e)
{
	TRACE("arith assert", "assertFact(", e.getExpr().toString(), ")");
  const Expr& expr = e.getExpr();
  if (expr.isNot() && expr[0].isEq()) {
    IF_DEBUG(debugger.counter("[arith] received disequalities")++;)
    d_diseq.push_back(e);
  }
  else if (!expr.isEq()){
    if (expr.isNot()) {
      // This can only be negation of dark or gray shadows, or
      // disequalities, which we ignore.  Negations of inequalities
      // are handled in rewrite, we don't even receive them here.
    }
    else if(isDarkShadow(expr)) {
      enqueueFact(d_rules->expandDarkShadow(e));
      IF_DEBUG(debugger.counter("received DARK_SHADOW")++;)
    }
    else if(isGrayShadow(expr)) {
      IF_DEBUG(debugger.counter("received GRAY_SHADOW")++;)
      const Rational& c1 = expr[2].getRational();
      const Rational& c2 = expr[3].getRational();
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
	else {
	  // Assert c1+e <= v <= c2+e
	  enqueueFact(d_rules->expandGrayShadow(gThm));
	  // Split G into 2 cases (binary search b/w c1 and c2)
	  Theorem thm2 = d_rules->splitGrayShadow(gThm);
	  enqueueFact(thm2);
	  // Fetch the two gray shadows
	  DebugAssert(thm2.getExpr().isAnd() && thm2.getExpr().arity()==2,
		      "thm2 = "+thm2.getExpr().toString());
	  const Expr& G1orG2 = thm2.getExpr()[0];
	  DebugAssert(G1orG2.isOr() && G1orG2.arity()==2,
		      "G1orG2 = "+G1orG2.toString());
	  const Expr& G1 = G1orG2[0];
	  const Expr& G2 = G1orG2[1];
	  DebugAssert(G1.getKind()==GRAY_SHADOW, "G1 = "+G1.toString());
	  DebugAssert(G2.getKind()==GRAY_SHADOW, "G2 = "+G2.toString());
	  // Split on the left disjunct first (keep the priority low)
          Expr tmp = simplifyExpr(G1);
          if (!tmp.isBoolConst())
            addSplitter(tmp, 1);
          tmp = simplifyExpr(G2);
	  if (!tmp.isBoolConst())
            addSplitter(tmp, -1);
	}
      }
    }
    else {
      DebugAssert(isLE(expr) || isLT(expr) || isIntPred(expr),
		  "expected LE or LT: "+expr.toString());
      if(isLE(expr) || isLT(expr)) {
	IF_DEBUG(debugger.counter("recevied inequalities")++;)

        // Assert the equivalent negated inequality
        Theorem thm;
        if (isLE(expr)) thm = d_rules->negatedInequality(!gtExpr(expr[0],expr[1]));
        else thm = d_rules->negatedInequality(!geExpr(expr[0],expr[1]));
        thm = symmetryRule(thm);
        Theorem thm2 = simplify(thm.getRHS()[0]);
        DebugAssert(thm2.getLHS() != thm2.getRHS(), "Expected rewrite");
        thm2 = getCommonRules()->substitutivityRule(thm.getRHS(), thm2);
        thm = transitivityRule(thm, thm2);
        enqueueFact(iffMP(e, thm));

	// Buffer the inequality
	addToBuffer(e);

	TRACE("arith ineq", "buffer.size() = ", d_buffer.size(),
	      ", index="+int2string(d_bufferIdx)
	      +", threshold="+int2string(*d_bufferThres));

	if((((int)d_buffer.size()) - (int)d_bufferIdx > *d_bufferThres)
	   && !d_inModelCreation)
	  processBuffer();
      } else {
	IF_DEBUG(debugger.counter("arith IS_INTEGER")++;)
      }
    }
  }
  else {
    IF_DEBUG(debugger.counter("[arith] received t1=t2")++;)
  }
}


void TheoryArith3::checkSat(bool fullEffort)
{
  //  vector<Expr>::const_iterator e;
  //  vector<Expr>::const_iterator eEnd;
  // TODO: convert back to use iterators
  TRACE("arith checksat", "checksat(", fullEffort? "true" : "false", ")");
  TRACE("arith ineq", "TheoryArith3::checkSat(fullEffort=",
        fullEffort? "true" : "false", ")");
  if (fullEffort) {
    while(!inconsistent() && d_bufferIdx < d_buffer.size())
      processBuffer();
    if(d_inModelCreation) {
      for(; d_diseqIdx < d_diseq.size(); d_diseqIdx = d_diseqIdx+1) {
	TRACE("model", "[arith] refining diseq: ",
	      d_diseq[d_diseqIdx].getExpr() , "");
	enqueueFact(d_rules->diseqToIneq(d_diseq[d_diseqIdx]));
      }
    }
  }
}



void TheoryArith3::refineCounterExample()
{
  d_inModelCreation = true;
  TRACE("model", "refineCounterExample[TheoryArith3] ", "", "{");
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
		  "TheoryArith3::refineCounterExample: e1 = "+e1.toString()
		  +"\n type(e1) = "+e1.getType().toString());
      if(findExpr(e1) != findExpr(e2)) {
	DebugAssert(isReal(getBaseType(e2)),
		    "TheoryArith3::refineCounterExample: e2 = "+e2.toString()
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
TheoryArith3::findRationalBound(const Expr& varSide, const Expr& ratSide,
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
TheoryArith3::findBounds(const Expr& e, Rational& lub, Rational&  glb)
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

void TheoryArith3::assignVariables(std::vector<Expr>&v)
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

void TheoryArith3::computeModelBasic(const std::vector<Expr>& v)
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
void TheoryArith3::computeModel(const Expr& e, vector<Expr>& vars) {
  DebugAssert(findExpr(e).isRational(), "TheoryArith3::computeModel("
	      +e.toString()+")\n e is not assigned concrete value.\n"
	      +" find(e) = "+findExpr(e).toString());
  assignValue(simplify(e));
  vars.push_back(e);
}



/*! accepts a rewrite theorem over eqn|ineqn and normalizes it
 *  and returns a theorem to that effect. assumes e is non-trivial
 *  i.e. e is not '0=const' or 'const=0' or '0 <= const' etc.
 */
Theorem TheoryArith3::normalize(const Expr& e) {
  //e is an eqn or ineqn. e is not a trivial eqn or ineqn
  //trivial means 0 = const or 0 <= const.
  TRACE("arith", "normalize(", e, ") {");
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
    factor = computeNormalFactor(e[1]);
  else
    factor = computeNormalFactor(e[0]);

  TRACE("arith", "normalize: factor = ", factor, "");
  DebugAssert(factor.getRational() > 0,
              "normalize: factor="+ factor.toString());

  Theorem thm(reflexivityRule(e));
  // Now multiply the equality by the factor, unless it is 1
  if(factor.getRational() != 1) {
    int kind = e.getKind();
    switch(kind) {
    case EQ:
      thm = d_rules->multEqn(e[0], e[1], factor);
      // And canonize the result
      thm = canonPredEquiv(thm);
      break;
    case LE:
    case LT:
    case GE:
    case GT:
      thm = d_rules->multIneqn(e, factor);
      // And canonize the result
      thm = canonPredEquiv(thm);
      break;
    default:
      // MS .net doesn't accept "..." + int
      ostringstream ss;
      ss << "normalize: control should not reach here " << kind;
      DebugAssert(false, ss.str());
      break;
    }
  }
  TRACE("arith", "normalize => ", thm, " }");
  return(thm);
}


Theorem TheoryArith3::normalize(const Theorem& eIffEqn) {
  return transitivityRule(eIffEqn, normalize(eIffEqn.getRHS()));
}


Theorem TheoryArith3::rewrite(const Expr& e)
{
  DebugAssert(leavesAreSimp(e), "Expected leaves to be simplified");
  TRACE("arith", "TheoryArith3::rewrite(", e, ") {");
  Theorem thm;
  if (!e.isTerm()) {
    if (!e.isAbsLiteral()) {
      e.setRewriteNormal();
      thm = reflexivityRule(e);
      TRACE("arith", "TheoryArith3::rewrite[non-literal] => ", thm, " }");
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
	  thm = canonPredEquiv(thm);

	}
      }

      // Equations must be oriented such that lhs >= rhs as Exprs;
      // this ordering is given by operator<(Expr,Expr).
      const Expr& eq = thm.getRHS();
      if(eq.isEq() && eq[0] < eq[1])
	thm = transitivityRule(thm, getCommonRules()->rewriteUsingSymmetry(eq));
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
    case LE:
    case LT:
    case GE:
    case GT:
      if (isGE(e) || isGT(e)) {
	thm = d_rules->flipInequality(e);
	thm = transitivityRule(thm, d_rules->rightMinusLeft(thm.getRHS()));
      }
      else
	thm = d_rules->rightMinusLeft(e);
      thm = canonPredEquiv(thm);

      // Check for trivial inequation
      if ((thm.getRHS())[1].isRational())
	thm = transitivityRule(thm, d_rules->constPredicate(thm.getRHS()));
      else { // ineq is non-trivial
	thm = normalize(thm);
	thm = canonPredEquiv(thm);
      }
      break;
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
  // Arith canonization is idempotent
  if (theoryOf(thm.getRHS()) == this)
    thm.getRHS().setRewriteNormal();
  TRACE("arith", "TheoryArith3::rewrite => ", thm, " }");
  return thm;
}


void TheoryArith3::setup(const Expr& e)
{
  if (!e.isTerm()) {
    if (e.isNot() || e.isEq() || isDarkShadow(e) || isGrayShadow(e)) return;
    if(e.getKind() == IS_INTEGER) {
      e[0].addToNotify(this, e);
      return;
    }
    DebugAssert((isLT(e)||isLE(e)) &&
                e[0].isRational() && e[0].getRational() == 0,
                "TheoryArith3::setup: expected 0 < rhs:" + e.toString());
    e[1].addToNotify(this, e);
    return;
  }
  int k(0), ar(e.arity());
  for ( ; k < ar; ++k) {
    e[k].addToNotify(this, e);
    TRACE("arith setup", "e["+int2string(k)+"]: ", *(e[k].getNotify()), "");
  }
}


void TheoryArith3::update(const Theorem& e, const Expr& d)
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
    Theorem thm = canonSimp(d);
    TRACE("arith", "TheoryArith3::update(): thm = ", thm, "");
    DebugAssert(leavesAreSimp(thm.getRHS()), "updateHelper error: "
 		+thm.getExpr().toString());
    assertEqualities(transitivityRule(thm, rewrite(thm.getRHS())));
    IF_DEBUG(debugger.counter("arith update find(d)=d")++;)
  }
}


Theorem TheoryArith3::solve(const Theorem& thm)
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


void TheoryArith3::computeModelTerm(const Expr& e, std::vector<Expr>& v) {
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
      TRACE("model", "TheoryArith3::computeModelTerm(", e, "): a variable");
      // Leave it alone (it has no descendants)
      // v.push_back(e);
    } else {
      TRACE("model", "TheoryArith3::computeModelTerm("+e.toString()
	    +"): has find pointer to ", e2, "");
      v.push_back(e2);
    }
  }
  }
}


Expr TheoryArith3::computeTypePred(const Type& t, const Expr& e) {
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


void TheoryArith3::checkAssertEqInvariant(const Theorem& e)
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


void TheoryArith3::checkType(const Expr& e)
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
      DebugAssert(false, "Unexpected kind in TheoryArith3::checkType"
                  +getEM()->getKindName(e.getKind()));
  }
}


Cardinality TheoryArith3::finiteTypeInfo(Expr& e, Unsigned& n,
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


void TheoryArith3::computeType(const Expr& e)
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
      DebugAssert(false,"TheoryArith3::computeType: unexpected expression:\n "
                  +e.toString());
      break;
  }
}


Type TheoryArith3::computeBaseType(const Type& t) {
  IF_DEBUG(int kind = t.getExpr().getKind();)
  DebugAssert(kind==INT || kind==REAL || kind==SUBRANGE,
	      "TheoryArith3::computeBaseType("+t.toString()+")");
  return realType();
}


Expr
TheoryArith3::computeTCC(const Expr& e) {
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
TheoryArith3::parseExprOp(const Expr& e) {
  TRACE("parser", "TheoryArith3::parseExprOp(", e, ")");
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
	      "TheoryArith3::parseExprOp:\n e = "+e.toString());

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
	  	  "TheoryArith3::parseExprOp: invalid input " + e.toString());
      break;
  }
  return e;
}

///////////////////////////////////////////////////////////////////////////////
// Pretty-printing                                                           //
///////////////////////////////////////////////////////////////////////////////


ExprStream&
TheoryArith3::print(ExprStream& os, const Expr& e) {
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
          throw SmtlibException("TheoryArith3::print: SMTLIB: SUBRANGE not implemented");
//           if(e.arity() != 2) e.print(os);
//           else
//             os << "(" << push << "SUBRANGE" << space << e[0]
// 	       << space << e[1] << push << ")";
          break;
        case IS_INTEGER:
 	  if(e.arity() == 1)
 	    os << "(" << push << "IsInt" << space << e[0] << push << ")";
 	  else
            throw SmtlibException("TheoryArith3::print: SMTLIB: IS_INTEGER used unexpectedly");
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
          throw SmtlibException("TheoryArith3::print: SMTLIB: POW not supported");
          //          os << "(" << push << "^ " << e[1] << space << e[0] << push << ")";
          break;
        case DIVIDE: {
          throw SmtlibException("TheoryArith3::print: SMTLIB: unexpected use of DIVIDE");
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
          throw SmtlibException("TheoryArith3::print: SMTLIB: DARK_SHADOW not supported");
	  os << "(" << push << "DARK_SHADOW" << space << e[0]
	     << space << e[1] << push << ")";
	  break;
        case GRAY_SHADOW:
          throw SmtlibException("TheoryArith3::print: SMTLIB: GRAY_SHADOW not supported");
	  os << "GRAY_SHADOW(" << push << e[0] << ","  << space << e[1]
	     << "," << space << e[2] << "," << space << e[3] << push << ")";
	  break;
        default:
          throw SmtlibException("TheoryArith3::print: SMTLIB: default not supported");
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
