/*****************************************************************************/
/*!
 *\file uf_theorem_producer.cpp
 *\brief TRUSTED implementation of uninterpreted function/predicate rules
 *
 * Author: Clark Barrett
 *
 * Created: Tue Aug 31 23:20:27 2004
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


// This code is trusted
#define _CVC3_TRUSTED_


#include "uf_theorem_producer.h"
#include "theory_uf.h"
#include "theory_core.h"


using namespace std;
using namespace CVC3;


////////////////////////////////////////////////////////////////////
// TheoryUF: trusted method for creating UFTheoremProducer
////////////////////////////////////////////////////////////////////


UFProofRules* TheoryUF::createProofRules() {
  return new UFTheoremProducer(theoryCore()->getTM(), this);
}
  

////////////////////////////////////////////////////////////////////
// Proof rules
////////////////////////////////////////////////////////////////////


#define CLASS_NAME "CVC3::UFTheoremProducer"


Theorem UFTheoremProducer::relToClosure(const Theorem& rel)
{
  const Expr& relExpr = rel.getExpr();

  if(CHECK_PROOFS)
    CHECK_SOUND(relExpr.isApply() && relExpr.arity() == 2,
		CLASS_NAME
		"theorem is not a relation or has wrong arity:\n"
		+ rel.getExpr().toString());

  Proof pf;
  if(withProof()) {
    pf = newPf("rel_closure", rel.getProof());
  }

  const string& name = relExpr.getOp().getExpr().getName();
  Expr tc = d_theoryUF->transClosureExpr(name, relExpr[0], relExpr[1]);

  return newTheorem(tc, rel.getAssumptionsRef(), pf);
}


Theorem UFTheoremProducer::relTrans(const Theorem& t1, const Theorem& t2)
{
  const Expr& e1 = t1.getExpr();
  const Expr& e2 = t2.getExpr();

  if (CHECK_PROOFS) {
    CHECK_SOUND(e1.getOpKind() == TRANS_CLOSURE &&
		e1.arity() == 2,
		(CLASS_NAME
		 "theorem is not a proper trans_closure expr:\n"
		 + e1.toString()).c_str());
    CHECK_SOUND(e2.getOpKind() == TRANS_CLOSURE &&
		e2.arity() == 2,
		(CLASS_NAME
		 "theorem is not a proper trans_closure expr:\n"
		 + e2.toString()).c_str());
  }

  if (CHECK_PROOFS) {
    CHECK_SOUND(e1.getOpExpr().getName() == e2.getOpExpr().getName() &&
		e1[1] == e2[0],
		(CLASS_NAME
		 "Expr's don't match:\n"
		 + e1.toString() + " and " + e2.toString()).c_str());
  }

  Assumptions a(t1, t2);
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(t1.getProof());
    pfs.push_back(t2.getProof());
    pf = newPf("rel_trans", pfs);
  }
  return newTheorem(Expr(e1.getOp(), e1[0], e2[1]), a, pf);
}


Theorem UFTheoremProducer::applyLambda(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isApply() && e.getOpKind() == LAMBDA,
		"applyLambda("+e.toString()
		+"):\n\n  expression is not an APPLY");
  }
  Expr lambda(e.getOpExpr());

  if (CHECK_PROOFS) {
    CHECK_SOUND(lambda.isLambda(),
		"applyLambda:\n"
		"Operator is not LAMBDA: " + lambda.toString());
  }

  Expr body(lambda.getBody());
  const vector<Expr>& vars = lambda.getVars();

  if(CHECK_PROOFS) {
    CHECK_SOUND(vars.size() == (size_t)e.arity(), 
		"wrong number of arguments applied to lambda\n");
  }

  // Use the Expr's efficient substitution
  body = body.substExpr(vars, e.getKids());
//   for (unsigned i = 0; i < vars.size(); i++) {
//     body = substFreeTerm(body, vars[i], e[i]);
//   }

  Proof pf;
  if(withProof())
    pf = newPf("apply_lambda", e);
  return newRWTheorem(e, body, Assumptions::emptyAssump(), pf);
}


Theorem UFTheoremProducer::rewriteOpDef(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isApply(),
		"UFTheoremProducer::rewriteOpDef: 'e' is not a "
		"function application:\n\n "+e.toString());
  }

  Expr op = e.getOpExpr();
  int opKind = op.getKind();

  if(CHECK_PROOFS) {
    CHECK_SOUND(opKind==LETDECL,
		"UFTheoremProducer::rewriteOpDef: operator is not a "
		"named function in:\n\n "+e.toString());
  }
  // Now actually replace the name with the definition
  while(opKind==LETDECL) {
    if(CHECK_PROOFS) {
      CHECK_SOUND(op.arity()==2,
		  "UFTheoremProducer::rewriteOpDef: bad named "
		  "operator in:\n\n "+e.toString());
    }
    op = op[1];
    opKind = op.getKind();
  }
  // ...and construct a Theorem
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_op_def", e);
  return newRWTheorem(e, Expr(op.mkOp(), e.getKids()), Assumptions::emptyAssump(), pf);
}
