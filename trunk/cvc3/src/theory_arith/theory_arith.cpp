/*****************************************************************************/
/*!
 * \file theory_arith.cpp
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


#include "theory_arith.h"
#include "theory_core.h"
#include "translator.h"


using namespace std;
using namespace CVC3;


Theorem TheoryArith::canonRec(const Expr& e)
{
  if (isLeaf(e)) return reflexivityRule(e);
  int ar = e.arity();
  if (ar > 0) {
    vector<Theorem> newChildrenThm;
    vector<unsigned> changed;
    for(int k = 0; k < ar; ++k) {
      // Recursively canonize the kids
      Theorem thm = canonRec(e[k]);
      if (thm.getLHS() != thm.getRHS()) {
	newChildrenThm.push_back(thm);
	changed.push_back(k);
      }
    }
    if(changed.size() > 0) {
      return canonThm(substitutivityRule(e, changed, newChildrenThm));
    }
  }
  return canon(e);
}


void TheoryArith::printRational(ExprStream& os, const Rational& r,
                                bool printAsReal)
{
  // Print rational
  if (r.isInteger()) {
    if (r < 0) {
      os << "(" << push;
      if (os.lang() == SMTLIB_LANG) {
        os << "~";
      }
      else {
        os << "-";
      }
      os << space << (-r).toString();
      if (printAsReal) os << ".0";
      os << push << ")";
    }
    else {
      os << r.toString();
      if (printAsReal) os << ".0";
    }
  }
  else {
    os << "(" << push << "/ ";
    Rational tmp = r.getNumerator();
    if (tmp < 0) {
      os << "(" << push << "-" << space << (-tmp).toString();
      if (printAsReal) os << ".0";
      os << push << ")";
    }
    else {
      os << tmp.toString();
      if (printAsReal) os << ".0";
    }
    os << space;
    tmp = r.getDenominator();
    DebugAssert(tmp > 0 && tmp.isInteger(), "Unexpected rational denominator");
    os << tmp.toString();
    if (printAsReal) os << ".0";
    os << push << ")";
  }
}


bool TheoryArith::isAtomicArithTerm(const Expr& e)
{
  switch (e.getKind()) {
    case RATIONAL_EXPR:
      return true;
    case ITE:
      return false;
    case UMINUS:
    case PLUS:
    case MINUS:
    case MULT:
    case DIVIDE:
    case POW:
    case INTDIV:
    case MOD: {
      int i=0, iend=e.arity();
      for(; i!=iend; ++i) {
        if (!isAtomicArithTerm(e[i])) return false;
      }
      break;
    }
    default:
      break;
  }
  return true;
}


bool TheoryArith::isAtomicArithFormula(const Expr& e)
{
  switch (e.getKind()) {
    case LT:
    case GT:
    case LE:
    case GE:
    case EQ:
      return isAtomicArithTerm(e[0]) && isAtomicArithTerm(e[1]);
  }
  return false;
}


bool TheoryArith::isSyntacticRational(const Expr& e, Rational& r)
{
  if (e.getKind() == REAL_CONST) {
    r = e[0].getRational();
    return true;
  }
  else if (e.isRational()) {
    r = e.getRational();
    return true;
  }
  else if (isUMinus(e)) {
    if (isSyntacticRational(e[0], r)) {
      r = -r;
      return true;
    }
  }
  else if (isDivide(e)) {
    Rational num;
    if (isSyntacticRational(e[0], num)) {
      Rational den;
      if (isSyntacticRational(e[1], den)) {
        if (den != 0) {
          r = num / den;
          return true;
        }
      }
    }
  }
  return false;
}


Expr TheoryArith::rewriteToDiff(const Expr& e)
{
  Expr tmp = e[0] - e[1];
  tmp = canonRec(tmp).getRHS();
  switch (tmp.getKind()) {
    case RATIONAL_EXPR: {
      Rational r = tmp.getRational();
      switch (e.getKind()) {
        case LT:
          if (r < 0) return trueExpr();
          else return falseExpr();
        case LE:
          if (r <= 0) return trueExpr();
          else return falseExpr();
        case GT:
          if (r > 0) return trueExpr();
          else return falseExpr();
        case GE:
          if (r >= 0) return trueExpr();
          else return falseExpr();
        case EQ:
          if (r == 0) return trueExpr();
          else return falseExpr();
      }
    }
    case MULT:
      DebugAssert(tmp[0].isRational(), "Unexpected term structure from canon");
      if (tmp[0].getRational() != -1) return e;
      return Expr(e.getOp(), theoryCore()->getTranslator()->zeroVar() - tmp[1], rat(0));
    case PLUS: {
      DebugAssert(tmp[0].isRational(), "Unexpected term structure from canon");
      Rational c = tmp[0].getRational();
      Expr x, y;
      if (tmp.arity() == 2) {
        if (tmp[1].getKind() == MULT) {
          x = theoryCore()->getTranslator()->zeroVar();
          y = tmp[1];
        }
        else {
          x = tmp[1];
          y = rat(-1) * theoryCore()->getTranslator()->zeroVar();
        }
      }
      else if (tmp.arity() == 3) {
        if (tmp[1].getKind() == MULT) {
          x = tmp[2];
          y = tmp[1];
        }
        else if (tmp[2].getKind() == MULT) {
          x = tmp[1];
          y = tmp[2];
        }
        else return e;
      }
      else return e;
      if (x.getKind() == MULT) return e;
      DebugAssert(y[0].isRational(), "Unexpected term structure from canon");
      if (y[0].getRational() != -1) return e;
      return Expr(e.getOp(), x - y[1], getEM()->newRatExpr(-c));
    }
    default:
      return Expr(e.getOp(), tmp - theoryCore()->getTranslator()->zeroVar(), rat(0));
      break;
  }
  return e;
}


Theorem TheoryArith::canonSimp(const Expr& e)
{
  DebugAssert(canonRec(e).getRHS() == e, "canonSimp expects input to be canonized");
  int ar = e.arity();
  if (isLeaf(e)) return find(e);
  if (ar > 0) {
    vector<Theorem> newChildrenThm;
    vector<unsigned> changed;
    Theorem thm;
    for (int k = 0; k < ar; ++k) {
      thm = canonSimp(e[k]);
      if (thm.getLHS() != thm.getRHS()) {
        newChildrenThm.push_back(thm);
        changed.push_back(k);
      }
    }
    if(changed.size() > 0) {
      thm = canonThm(substitutivityRule(e, changed, newChildrenThm));
      return transitivityRule(thm, find(thm.getRHS()));
    }
    else return find(e);
  }
  return find(e);
}


bool TheoryArith::recursiveCanonSimpCheck(const Expr& e)
{
  if (e.hasFind()) return true;
  if (e != canonSimp(e).getRHS()) return false;
  Expr::iterator i = e.begin(), iend = e.end();
  for (; i != iend; ++i)
    if (!recursiveCanonSimpCheck(*i)) return false;
  return true;
}


bool TheoryArith::leavesAreNumConst(const Expr& e)
{
  DebugAssert(e.isTerm() ||
              (e.isPropAtom() && theoryOf(e) == this),
              "Expected term or arith prop atom");

  if (e.validTerminalsConstFlag()) {
    return e.getTerminalsConstFlag();
  }

  if (e.isRational()) {
    e.setTerminalsConstFlag(true);
    return true;
  }

  if (e.isAtomic() && isLeaf(e)) {
    e.setTerminalsConstFlag(false);
    return false;
  }

  DebugAssert(e.arity() > 0, "Expected non-zero arity");
  int k = 0;

  if (e.isITE()) {
    k = 1;
  }

  for (; k < e.arity(); ++k) {
    if (!leavesAreNumConst(e[k])) {
      e.setTerminalsConstFlag(false);
      return false;
    }
  }
  e.setTerminalsConstFlag(true);
  return true;
}


