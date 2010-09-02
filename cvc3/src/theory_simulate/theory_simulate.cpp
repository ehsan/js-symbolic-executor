/*****************************************************************************/
/*!
 *\file theory_simulate.cpp
 *\brief Implementation of class TheorySimulate.
 *
 * Author: Sergey Berezin
 *
 * Created: Tue Oct  7 10:28:14 2003
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

#include "theory_simulate.h"
#include "simulate_proof_rules.h"
#include "typecheck_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
// For the type REAL
#include "theory_arith.h"


using namespace std;
using namespace CVC3;


TheorySimulate::TheorySimulate(TheoryCore* core)
  : Theory(core, "Simulate") {
  // Initialize the proof rules
  d_rules = createProofRules();
  // Register the kinds
  vector<int> kinds;
  kinds.push_back(SIMULATE);
  // Register the theory with the core
  registerTheory(this, kinds, false /* no solver */);
}


TheorySimulate::~TheorySimulate() {
  delete d_rules;
}


Theorem
TheorySimulate::rewrite(const Expr& e) {
  switch (e.getKind()) {
  case SIMULATE:
    return d_rules->expandSimulate(e);
    break;
  default:
    return reflexivityRule(e);
  }
}


void
TheorySimulate::computeType(const Expr& e) {
  switch (e.getKind()) {
  case SIMULATE: { // SIMULATE(f, s0, i_1, ..., i_k, N)
    const int arity = e.arity();
    if (!e[arity - 1].isRational() || 
	!e[arity - 1].getRational().isInteger()) {
      throw TypecheckException
	("Number of cycles in SIMULATE (last arg) "
	 "must be an integer constant:\n\n  " + e[arity -1].toString()
	 +"\n\nIn the following expression:\n\n  "
	 +e.toString());
    }

    const Expr& fn(e[0]);
    Type fnType(getBaseType(fn));
    // The arity of function is k+1, which is e.arity()-2.
    // The arity of the type also includes the result type.
    if(fnType.arity() != e.arity()-1)
      throw TypecheckException
	("Wrong number of arguments in SIMULATE:\n\n"
	 +e.toString()
	 +"\n\nExpected "+int2string(fnType.arity()+1)
	 +" arguments, but received "+int2string(e.arity())+".");
    // Build the function type that SIMULATE expects
    vector<Type> argTp;
    // The (initial) state type
    Type resType(getBaseType(e[1]));
    argTp.push_back(resType);
    for(int i=2, iend=e.arity()-1; i<iend; ++i) {
      Type iTp(e[i].getType());
      Type iTpBase(getBaseType(e[i]));
      if(!iTp.isFunction() || iTp.arity() != 2 || !isReal(iTpBase[0]))
	throw TypecheckException
	  ("Type mismatch in SIMULATE:\n\n  "
	   +e.toString()
	   +"\n\nThe input #"+int2string(i-1)
	   +" is expected to be of type:\n\n  REAL -> <something>"
	   "\n\nBut the actual type is:\n\n  "
	   +iTp.toString());
      argTp.push_back(iTpBase[1]);
    }
    Type expectedFnType(Type::funType(argTp, resType));
    if(fnType != expectedFnType)
      throw TypecheckException
	("Type mismatch in SIMULATE:\n\n  "
	 +e.toString()
	 +"\n\nThe transition function is expected to be of type:\n\n  "
	 +expectedFnType.toString()
	 +"\n\nBut the actual type is:\n\n  "
	 +fnType.toString());

    e.setType(resType);
    break;
  }
  default:
    DebugAssert(false,"TheorySimulate::computeType: Unexpected expression: "
		+e.toString());
  }
}

///////////////////////////////////////////////////////////////////////////////
//parseExprOp:
//Recursive call of parseExpr defined in theory_ libaries based on kind of expr 
//being built
///////////////////////////////////////////////////////////////////////////////
Expr
TheorySimulate::parseExprOp(const Expr& e) {
  TRACE("parser", "TheorySimulate::parseExprOp(", e, ")");
  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  if(RAW_LIST != e.getKind()) return e;

  DebugAssert(e.arity() > 0,
	      "TheorySimulate::parseExprOp:\n e = "+e.toString());
  /* The first element of the list (e[0] is an ID of the operator. 
     ID string values are the dirst element of the expression */ 
  const Expr& c1 = e[0][0];
  int kind = getEM()->getKind(c1.getString());
  switch(kind) {
  case SIMULATE: { // Application of SIMULATE to args
    vector<Expr> k;
    Expr::iterator i = e.begin(), iend=e.end();
    // Skip first element of the vector of kids in 'e'.
    // The first element is the operator.
    ++i; 
    // Parse the kids of e and push them into the vector 'k'
    for(; i!=iend; ++i) 
      k.push_back(parseExpr(*i));
    return Expr(SIMULATE, k, e.getEM());
    break;
  }
  default:
    DebugAssert(false, "TheorySimulate::parseExprOp: Unexpected operator: "
		+e.toString());
  }
  return e;
}

Expr
TheorySimulate::computeTCC(const Expr& e) {
  switch (e.getKind()) {
  case SIMULATE: {
    // TCC(SIMULATE(f, s, i1, ..., ik, N)):

    // First, we require that the type of the first argument of f is
    // exactly the same as the type of f's result (otherwise we need
    // to check subtyping relation, which might be undecidable), and
    // whether f is defined on s.
    //
    // Then, we check that the result type of i_j exactly matches the
    // type of the j+1-th argument of f (again, for efficiency and
    // decidability reasons), and that each i_j is defined on every
    // integer from 0..N-1.
    vector<Expr> tccs;
    Type fnType(e[0].getType());
    DebugAssert(fnType.arity() == e.arity()-1,
		"TheorySimulate::computeTCC: SIMULATE() doesn't typecheck: "
		+e.toString());
    Type resType(fnType[fnType.arity()-1]);
    // Check that the state type matches the 1st arg and the result type in f
    if(fnType[0] != resType)
      return getEM()->falseExpr();
    // Compute TCC for f on the initial state
    tccs.push_back(getTypePred(fnType[0], e[1]));

    const Rational& N = e[e.arity()-1].getRational();
    // Now, iterate through the inputs
    for(int i=2, iend=e.arity()-1; i<iend; ++i) {
      Type iTp(e[i].getType());
      DebugAssert(iTp.isFunction() && iTp.arity()==2,
		  "TheorySimulate::computeTCC: SIMULATE() doesn't typecheck: "
		  +e.toString());
      // Match the return type of i-th input with f's argument
      if(iTp[1] != fnType[i-1])
	return getEM()->falseExpr();
      // Compute the TCC for i(0) ... i(N-1)
      for(Rational j=0; j<N; j = j+1)
	tccs.push_back(getTypePred(iTp[0], getEM()->newRatExpr(j)));
    }
    return rewriteAnd(andExpr(tccs)).getRHS();
  }
  default: 
    DebugAssert(false, "TheorySimulate::computeTCC("+e.toString()
		+")\n\nUnknown expression.");
    return getEM()->trueExpr();
  }
}


ExprStream&
TheorySimulate::print(ExprStream& os, const Expr& e) {
  switch(os.lang()) {
  case PRESENTATION_LANG:
    switch(e.getKind()) {
    case SIMULATE:{
      os << "SIMULATE" << "(" << push;
      bool first(true);
      for (int i = 0; i < e.arity(); i++) {
	if (first) first = false;
	else os << push << "," << pop << space;
	os << e[i];
      }
      os << push << ")";
      break;
    }
    default:
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.printAST(os);
      
      break;
    }
    break;
  case SMTLIB_LANG:
  case SMTLIB_V2_LANG:
    d_theoryUsed = true;
    throw SmtlibException("TheorySimulate::print: SMTLIB not supported");
    switch(e.getKind()) {
    case SIMULATE:{
      os << "(" << push << "SIMULATE" << space;
      for (int i = 0; i < e.arity(); i++) {
	os << space << e[i];
      }
      os << push << ")";
      break;
    }
    default:
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.printAST(os);
      
      break;
    }
    break;
  case LISP_LANG:
    switch(e.getKind()) {
    case SIMULATE:{
      os << "(" << push << "SIMULATE" << space;
      for (int i = 0; i < e.arity(); i++) {
	os << space << e[i];
      }
      os << push << ")";
      break;
    }
    default:
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.printAST(os);
      
      break;
    }
    break;
  default:  // Not a known language
    e.printAST(os);
    break;
  }
  return os;
}
