
/*****************************************************************************/
/*!
 * \file records_theorem_producer.cpp
 * 
 * Author: Daniel Wichs
 * 
 * Created: Jul 22 22:59:07 GMT 2003
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
#define _CVC3_TRUSTED_

#include "records_theorem_producer.h"
#include "theory_records.h"
#include "theory_core.h"


using namespace std;
using namespace CVC3;


RecordsProofRules* TheoryRecords::createProofRules() {
  return new RecordsTheoremProducer(theoryCore()->getTM(), this);
}
  

#define CLASS_NAME "CVC3::RecordsTheoremProducer"

//! ==> (SELECT (LITERAL  v1 ... vi ...) fi) = vi
Theorem RecordsTheoremProducer::rewriteLitSelect(const Expr &e){
  
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_record_literal_select", e);

  int index=0;
  switch(e.getOpKind())
    {
    case RECORD_SELECT: {
      if(CHECK_PROOFS) {
	CHECK_SOUND(e[0].getOpKind()==RECORD,
		    "expected RECORD child:\n"
		    +e.toString());
      } 
      index = getFieldIndex(e[0], getField(e));
      break;
    }
    case TUPLE_SELECT: {
      if(CHECK_PROOFS) {
	CHECK_SOUND(e[0].getOpKind()==TUPLE,
		    "expected TUPLE child:\n"
		    +e.toString());
      } 
      index = getIndex(e);
      break;
    }
    default: {
      if(CHECK_PROOFS)
	CHECK_SOUND(false, "expected TUPLE_SELECT or RECORD_SELECT kind" 
		    + e.toString());
    }
    } 
  if(CHECK_PROOFS) {
    CHECK_SOUND(index!=-1 && index<e[0].arity(), 
		"selected field did not appear in literal" + e.toString());
  }
  return newRWTheorem(e, e[0][index], Assumptions::emptyAssump(), pf);
}
//! ==> (RECORD_SELECT (RECORD_UPDATE r fi vi) fj) = vi
//iff j=i, r.fj otherwise  (and same for tuples)
Theorem RecordsTheoremProducer::rewriteUpdateSelect(const Expr& e) {
  Proof pf;
  switch(e.getOpKind()) {
  case RECORD_SELECT: {
    if(CHECK_PROOFS)
      CHECK_SOUND(e[0].getOpKind() == RECORD_UPDATE,
		  "expected RECORD_UPDATE child" + e.toString());
    if(withProof())
      pf = newPf("rewrite_record_update_and_select", e);
    if(getField(e) == getField(e[0]))
      return newRWTheorem(e, e[0][1], Assumptions::emptyAssump(), pf);
    else
      return newRWTheorem(e, recordSelect(e[0][0], getField(e)), Assumptions::emptyAssump(), pf);
    break;
  }
  case TUPLE_SELECT: {
    if(CHECK_PROOFS)
      CHECK_SOUND(e[0].getOpKind() == TUPLE_UPDATE,
		  "expected TUPLE_UPDATE child" + e.toString());
    if(withProof())
      pf = newPf("rewrite_record_update_and_select", e);
    if(getIndex(e) == getIndex(e[0]))
      return newRWTheorem(e, e[0][1], Assumptions::emptyAssump(), pf);
    else
      return newRWTheorem(e, tupleSelect(e[0][0], getIndex(e)), Assumptions::emptyAssump(), pf);
    break;
  }
  default:
    if(CHECK_PROOFS)
      CHECK_SOUND(false, "expected RECORD_SELECT or TUPLE_SELECT kind"
		  + e.toString());
    break;
  }
  //to avoid warnings
  return newRWTheorem(e, e, Assumptions::emptyAssump(), pf);
}


//! ==> (RECORD_UPDATE (RECORD (f1 v1) ... (fi vi) ...) fi v') =(RECORD (f1 v1) ... (fi v') ...) and same for tuples.
Theorem RecordsTheoremProducer::rewriteLitUpdate(const Expr& e) {
  int index =0;
  switch(e.getOpKind()) {
  case RECORD_UPDATE: {
    if(CHECK_PROOFS)
      CHECK_SOUND(e[0].getOpKind() == RECORD,
		  "expected a RECORD: e = "+e.toString());
    index = getFieldIndex(e[0], getField(e));
    break;
  }
  case TUPLE_UPDATE: {
    if(CHECK_PROOFS)
      CHECK_SOUND(e[0].getOpKind() == TUPLE,
		  "expected a TUPLE: e = "+ e.toString());
    index = getIndex(e);
    break;
  }
  default:
    if(CHECK_PROOFS)
      CHECK_SOUND(false, "expected RECORD_UPDATE or TUPLE_UPDATE kind"
		  + e.toString());
  }

  vector<Expr> fieldVals= e[0].getKids();
  if(CHECK_PROOFS)
    CHECK_SOUND(index!=-1 && index<e[0].arity(),
		"update field does not appear in literal"
		+ e.toString());
  fieldVals[index] = e[1];
  Proof pf;
  if(withProof())
    pf= newPf("rewrite record_literal_update", e);
  if(e.getOpKind() == RECORD_UPDATE)
    return newRWTheorem(e, recordExpr(getFields(e[0]), fieldVals), Assumptions::emptyAssump(), pf);
  else
    return newRWTheorem(e, tupleExpr(fieldVals), Assumptions::emptyAssump(), pf);
}

Theorem RecordsTheoremProducer::expandNeq(const Theorem& neqThrm)
{
  Expr e = neqThrm.getExpr();
  if(CHECK_PROOFS)
    CHECK_SOUND(e.getKind() == NOT, "expected not expression" + e.toString());
  e=e[0];
  Expr e0 = e[0].getType().getExpr() , e1 = e[1].getType().getExpr();
  if(CHECK_PROOFS)
    {
    CHECK_SOUND(e.getKind() == EQ, 
		"equation expression expected \n" + e.toString());
    CHECK_SOUND(e0.arity()==e1.arity() && e0.getOpKind() == e1.getOpKind(),
		"equation types mismatch \n" + e.toString());
    CHECK_SOUND(e0.getOpKind() == RECORD_TYPE || e0.getOpKind() == TUPLE_TYPE,
		"expected TUPLES or RECORDS \n" + e.toString());
    }
  std::vector<Expr> orChildren;
  for(int i=0; i<e0.arity();i++)
  {
    Expr lhs, rhs;
    switch(e0.getOpKind()) {
    case RECORD_TYPE: {
      const string& field(getField(e0, i));
      DebugAssert(field == getField(e1, i), 	
		  "equation types mismatch \n" + neqThrm.getExpr().toString());
      lhs = recordSelect(e[0], field);
      rhs = recordSelect(e[1], field);
      break;
    }
    case TUPLE_TYPE: {
      lhs = tupleSelect(e[0], i);
      rhs = tupleSelect(e[1], i);
      break;
      }
    default:
      DebugAssert(false, "RecordsTheoremProducer::expandNeq: "
		  "Type must be TUPLE or RECORD: "+e0.toString());
    }
    Expr eq = lhs.getType().isBool()? lhs.iffExpr(rhs) : lhs.eqExpr(rhs);
    orChildren.push_back(!eq);
  }
  Proof pf;
  if(withProof())
    pf= newPf("rewrite_record_literal_update", e, neqThrm.getProof());
  return newTheorem(orExpr(orChildren), neqThrm.getAssumptionsRef(), pf);
}

Theorem RecordsTheoremProducer::expandEq(const Theorem& eqThrm)
{
  Expr lhs(eqThrm.getLHS()), e0 = lhs.getType().getExpr();
  Expr rhs(eqThrm.getRHS()), e1 = rhs.getType().getExpr();
  if(CHECK_PROOFS)
    {
    CHECK_SOUND(eqThrm.isRewrite(), 
		"equation expression expected \n"
		+ eqThrm.getExpr().toString());
    CHECK_SOUND(e0.arity() == e1.arity() && e0.getOpKind() == e1.getOpKind(),
		"equation types mismatch \n" + eqThrm.getExpr().toString());
    CHECK_SOUND(e0.getOpKind() == RECORD_TYPE || e0.getOpKind() == TUPLE_TYPE,
		"expected TUPLES or RECORDS \n" + eqThrm.getExpr().toString());
    }
  std::vector<Expr> andChildren;
  for(int i=0; i<e0.arity();i++)
  {
    Expr lhs1, rhs1;
    switch(e0.getOpKind()) {
    case RECORD_TYPE: {
      const vector<Expr>& fields(getFields(e0));
      DebugAssert(fields[i].getString() == getField(e1, i),
		  "equation types mismatch \n" + eqThrm.getExpr().toString());
      lhs1 = recordSelect(lhs, fields[i].getString());
      rhs1 = recordSelect(rhs, fields[i].getString());
      break;
    }
    case TUPLE_TYPE: {
      lhs1 = tupleSelect(lhs, i);
      rhs1 = tupleSelect(rhs, i);
      break;
      }
    default:
      DebugAssert(false, "RecordsTheoremProducer::expandEq(): "
		  "Type must be TUPLE or RECORD: "+e0.toString());
    }
    Expr eq = lhs1.getType().isBool()? lhs1.iffExpr(rhs1) : lhs1.eqExpr(rhs1);
    andChildren.push_back(eq);
  }
  Proof pf;
  if(withProof())
    pf= newPf("rewrite record_literal_update",
	      eqThrm.getExpr(), eqThrm.getProof());
  return newTheorem(andExpr(andChildren), eqThrm.getAssumptionsRef() , pf);  
}


Theorem RecordsTheoremProducer::expandRecord(const Expr& e) {
  Type tp(d_theoryRecords->getBaseType(e));
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRecordType(tp),
		"expandRecord("+e.toString()+"): not a record type");
  }
  const vector<Expr>& fields = getFields(tp.getExpr());
  vector<Expr> kids;
  for(vector<Expr>::const_iterator i=fields.begin(), iend=fields.end();
      i!=iend; ++i)
    kids.push_back(recordSelect(e, (*i).getString()));
  Proof pf;
  if(withProof()) pf = newPf("expand_record", e);
  return newRWTheorem(e, recordExpr(fields, kids), Assumptions::emptyAssump(), pf);
}


Theorem RecordsTheoremProducer::expandTuple(const Expr& e) {
  Type tp(d_theoryRecords->getBaseType(e));
  if(CHECK_PROOFS) {
    CHECK_SOUND(tp.getExpr().getOpKind() == TUPLE_TYPE,
		"expandTuple("+e.toString()+"): not a tuple type");
  }
  int size(tp.arity());
  vector<Expr> kids;
  for(int i=0; i<size; ++i)
    kids.push_back(tupleSelect(e, i));
  Proof pf;
  if(withProof()) pf = newPf("expand_tuple", e);
  return newRWTheorem(e, tupleExpr(kids), Assumptions::emptyAssump(), pf);
}
