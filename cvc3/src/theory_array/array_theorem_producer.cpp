/*****************************************************************************/
/*!
 * \file array_theorem_producer.cpp
 * \brief Description: TRUSTED implementation of array proof rules.
 * 
 * Author: Clark Barrett
 * 
 * Created: Thu May 29 14:02:16 2003
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


#include "array_theorem_producer.h"
#include "theory_array.h"
#include "theory_core.h"


using namespace std;
using namespace CVC3;


////////////////////////////////////////////////////////////////////
// TheoryArray: trusted method for creating ArrayTheoremProducer
////////////////////////////////////////////////////////////////////


ArrayProofRules* TheoryArray::createProofRules() {
  return new ArrayTheoremProducer(this);
}
  

ArrayTheoremProducer::ArrayTheoremProducer(TheoryArray* theoryArray)
  : TheoremProducer(theoryArray->theoryCore()->getTM()),
    d_theoryArray(theoryArray)
{}


////////////////////////////////////////////////////////////////////
// Proof rules
////////////////////////////////////////////////////////////////////


#define CLASS_NAME "CVC3::ArrayTheoremProducer"


// ==>
// write(store, index_0, v_0, index_1, v_1, ..., index_n, v_n) = store IFF
//
// read(store, index_n) = v_n &
// index_{n-1} != index_n -> read(store, index_{n-1}) = v_{n-1} &
// (index_{n-2} != index_{n-1} & index_{n-2} != index_n) -> read(store, index_{n-2}) = v_{n-2} &
// ...
// (index_1 != index_2 & ... & index_1 != index_n) -> read(store, index_1) = v_1
// (index_0 != index_1 & index_0 != index_2 & ... & index_0 != index_n) -> read(store, index_0) = v_0
Theorem
ArrayTheoremProducer::rewriteSameStore(const Expr& e, int n)
{
  IF_DEBUG(
    DebugAssert(e.isEq(), "EQ expected");
    Expr e1 = e[0];
    int N = 0;
    while (isWrite(e1)) { N++; e1 = e1[0]; }
    DebugAssert(N == n && n > 0, "Counting error");
    DebugAssert(e1 == e[1], "Stores do not match");
  )
    
  Proof pf;
  Expr write_i, write_j, index_i, index_j, hyp, conc, result;
  int i, j;

  write_i = e[0];
  for (i = n-1; i >= 0; --i) {
    index_i = write_i[1];

    // build: [index_i /= index_n && index_i /= index_(n-1) &&
    //         ... && index_i /= index_(i+1)] -> read(store, index_i) = v_i
    write_j = e[0];
    for (j = n - 1; j > i; --j) {
      index_j = write_j[1];
      Expr hyp2(!((index_i.getType().isBool())? 
		   index_i.iffExpr(index_j) : index_i.eqExpr(index_j)));
      if (hyp.isNull()) hyp = hyp2;
      else hyp = hyp && hyp2;
      write_j = write_j[0];
    }
    Expr r1(Expr(READ, e[1], index_i));
    conc = (r1.getType().isBool())? 
      r1.iffExpr(write_i[2]) : r1.eqExpr(write_i[2]);
    if (!hyp.isNull()) conc = hyp.impExpr(conc);

    // And into result
    if (result.isNull()) result = conc;
    else result = result && conc;

    // Prepare for next iteration
    write_i = write_i[0];
    hyp = Expr();
  }
  if (withProof()) pf = newPf("rewriteSameStore", e);
  return newRWTheorem(e, result, Assumptions::emptyAssump(), pf);
}


// ==> write(store, index, value) = write(...) IFF
//       store = write(write(...), index, read(store, index)) &
//       value = read(write(...), index)
Theorem
ArrayTheoremProducer::rewriteWriteWrite(const Expr& e)
{
  IF_DEBUG(
    DebugAssert(e.isEq(), "EQ expected");
    DebugAssert(isWrite(e[0]) && isWrite(e[1]),
		"Expected WRITE = WRITE");
  )
  Proof pf;
  const Expr& left = e[0];
  const Expr& right = e[1];
  const Expr& store = left[0];
  const Expr& index = left[1];
  const Expr& value = left[2];
  Expr e1 = (store.getType().isBool())?
    store.iffExpr(Expr(WRITE, right, index, Expr(READ, store, index)))
    : store.eqExpr(Expr(WRITE, right, index, Expr(READ, store, index)));
  Expr e2 = (value.getType().isBool()) ?
    value.iffExpr(Expr(READ, right, index)) :
    value.eqExpr(Expr(READ, right, index));
  if (withProof()) pf = newPf("rewriteWriteWrite", e);
  return newRWTheorem(e, e1.andExpr(e2), Assumptions::emptyAssump(), pf);
}


// ==> read(write(store, index1, value), index2) =
//   ite(index1 = index2, value, read(store, index2))
Theorem
ArrayTheoremProducer::rewriteReadWrite(const Expr& e)
{
  IF_DEBUG(
    DebugAssert(isRead(e), "Read expected");
    DebugAssert(isWrite(e[0]), "Expected Read(Write)");
  )
  Proof pf;
  const Expr& store = e[0][0];
  const Expr& index1 = e[0][1];
  const Expr& value = e[0][2];
  const Expr& index2 = e[1];
  Expr indexCond = (index1.getType().isBool())?
    index1.iffExpr(index2) : index1.eqExpr(index2);
  if (withProof()) pf = newPf("rewriteReadWrite", e);
  return newRWTheorem(e, indexCond.iteExpr(value,
                                           Expr(READ, store, index2)), Assumptions::emptyAssump(), pf);
}


// e = read(write(store, index1, value), index2):
// ==> ite(index1 = index2,
//         read(write(store, index1, value), index2) = value,
//         read(write(store, index1, value), index2) = read(store, index2))
Theorem
ArrayTheoremProducer::rewriteReadWrite2(const Expr& e)
{
  IF_DEBUG(
    DebugAssert(isRead(e), "Read expected");
    DebugAssert(isWrite(e[0]), "Expected Read(Write)");
  )
  Proof pf;
  const Expr& store = e[0][0];
  const Expr& index1 = e[0][1];
  const Expr& value = e[0][2];
  const Expr& index2 = e[1];
  Expr indexCond = (index1.getType().isBool())?
    index1.iffExpr(index2) : index1.eqExpr(index2);
  if (withProof()) pf = newPf("rewriteReadWrite2", e);
  return newTheorem(indexCond.iteExpr(e.eqExpr(value),
                                      e.eqExpr(Expr(READ, store, index2))),
                    Assumptions::emptyAssump(), pf);
}


// read(store, index) = value ==>
//   write(store, index, value) = store
//
// More general case:
//
// read(store, index_n) = value_n ==>
//   write(store, index_0, v_0, index_1, v_1, ..., index_n, value_n) =
//   write(store, index_0, ite(index_n = index_0, value_n, v_0),
//                index_1, ite(index_n = index_1, value_n, v_1),
//                ...
//                index_{n-1}, ite(index_n = index_{n-1}, value_n, value_{n-1}))
Theorem
ArrayTheoremProducer::rewriteRedundantWrite1(const Theorem& r_eq_v,
					     const Expr& write)
{
  DebugAssert(r_eq_v.isRewrite(), "Expected equation");
  DebugAssert(isRead(r_eq_v.getLHS()), "Expected Read");
  const Expr& index = r_eq_v.getLHS()[1];
  const Expr& value = r_eq_v.getRHS();
  DebugAssert(isWrite(write) &&
	      index == write[1] && value == write[2],
	      "Error in parameters to rewriteRedundantWrite1");

  vector<Expr> indices;
  vector<Expr> values;
  Expr store = write[0];
  while (isWrite(store)) {
    indices.push_back(store[1]);
    values.push_back(store[2]);
    store = store[0];
  }
  DebugAssert(store == r_eq_v.getLHS()[0],
              "Store does not match in rewriteRedundantWrite");
  while (!indices.empty()) {
    store = Expr(WRITE, store, indices.back(),
                 index.eqExpr(indices.back()).iteExpr(value, values.back()));
    indices.pop_back();
    values.pop_back();
  }

  Proof pf;
  if(withProof()) {
    pf = newPf("rewriteRedundantWrite1", write, r_eq_v.getProof());
  }
  return newRWTheorem(write, store, r_eq_v.getAssumptionsRef(), pf);
}


// ==>
//   write(write(store, index, v1), index, v2) = write(store, index, v2)
Theorem
ArrayTheoremProducer::rewriteRedundantWrite2(const Expr& e)
{
  DebugAssert(isWrite(e) && isWrite(e[0]) &&
	      e[0][1] == e[1],
	      "Error in parameters to rewriteRedundantWrite2");

  Proof pf;
  
  if(withProof()) {
    pf = newPf("rewriteRedundantWrite2", e);
  }

  return newRWTheorem(e, Expr(WRITE, e[0][0], e[1], e[2]), Assumptions::emptyAssump(), pf);
}


// ==>
//   write(write(store, index1, v1), index2, v2) =
//   write(write(store, index2, v2), index1, ite(index1 = index2, v2, v1))
Theorem
ArrayTheoremProducer::interchangeIndices(const Expr& e)
{
  DebugAssert(isWrite(e) && isWrite(e[0]),
	      "Error in parameters to interchangeIndices");

  Proof pf;
  
  if(withProof()) {
    pf = newPf("interchangeIndices", e);
  }

  Expr w0 = Expr(WRITE, e[0][0], e[1], e[2]);
  Expr indexCond = (e[0][1].getType().isBool())?
    e[0][1].iffExpr(e[1]) : e[0][1].eqExpr(e[1]);
  Expr w2 = Expr(WRITE, w0, e[0][1], indexCond.iteExpr(e[2], e[0][2]));

  return newRWTheorem(e, w2, Assumptions::emptyAssump(), pf);
}

Theorem
ArrayTheoremProducer::readArrayLiteral(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == READ,
		"ArrayTheoremProducer::readArrayLiteral("+e.toString()
		+"):\n\n  expression is not a READ");
  }

  Expr arrayLit(e[0]);

  if (CHECK_PROOFS) {
    CHECK_SOUND(arrayLit.isClosure() && arrayLit.getKind()==ARRAY_LITERAL,
		"ArrayTheoremProducer::readArrayLiteral("+e.toString()+")");
  }

  Expr body(arrayLit.getBody());
  const vector<Expr>& vars = arrayLit.getVars();

  if(CHECK_PROOFS) {
    CHECK_SOUND(vars.size() == 1, 
		"ArrayTheoremProducer::readArrayLiteral("+e.toString()+"):\n"
		+"wrong number of bound variables");
  }

  // Use the Expr's efficient substitution
  vector<Expr> ind;
  ind.push_back(e[1]);
  body = body.substExpr(vars, ind);

  Proof pf;
  if(withProof())
    pf = newPf("read_array_literal", e);
  return newRWTheorem(e, body, Assumptions::emptyAssump(), pf);
}


Theorem ArrayTheoremProducer::liftReadIte(const Expr& e)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == READ && e[0].getKind() == ITE,
		"ArrayTheoremProducer::liftReadIte("+e.toString()
		+"):\n\n  expression is not READ(ITE...");
  }

  const Expr& ite = e[0];

  Proof pf;
  if (withProof())
    pf = newPf("lift_read_ite",e);
  return newRWTheorem(e, Expr(ITE, ite[0], Expr(READ, ite[1], e[1]),
                              Expr(READ, ite[2], e[1])),
                      Assumptions::emptyAssump(), pf);
}


Theorem ArrayTheoremProducer::arrayNotEq(const Theorem& e)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getExpr().getKind() == NOT &&
                e.getExpr()[0].getKind() == EQ &&
                isArray(d_theoryArray->getBaseType(e.getExpr()[0][0])),
		"ArrayTheoremProducer::arrayNotEq("+e.toString()
		+"):\n\n  expression is ill-formed");
  }

  Expr eq = e.getExpr()[0];

  Proof pf;
  if (withProof())
    pf = newPf("array_not_eq", e.getProof());

  Type arrType = d_theoryArray->getBaseType(eq[0]);
  Type indType = Type(arrType.getExpr()[0]);
  Expr var = d_theoryArray->getEM()->newBoundVarExpr(indType);
  eq = Expr(READ, eq[0], var).eqExpr(Expr(READ, eq[1], var));

  return newTheorem(d_theoryArray->getEM()->newClosureExpr(EXISTS, var, !eq),
                    Assumptions(e), pf);
}

Theorem ArrayTheoremProducer::splitOnConstants(const Expr& a, const std::vector<Expr>& consts) {
  Theorem res;
  Expr result;

  vector<Expr> eq;
  vector<Expr> diseq;
  for (unsigned i = 0; i < consts.size(); ++ i) {
    eq.push_back(a.eqExpr(consts[i]));
    diseq.push_back(a.eqExpr(consts[i]).notExpr());
  }

  if (eq.size() == 1) {
    result = eq[0].orExpr(diseq[0]);
  } else {
    eq.push_back(andExpr(diseq));
    result = orExpr(eq);
  }

  Proof pf;
  if (withProof())
    pf = newPf("splitOnConstants");

  return newTheorem(result, Assumptions::emptyAssump(), pf);
}

Theorem ArrayTheoremProducer::propagateIndexDiseq(const Theorem& read1eqread2isFalse) {
  Expr read1eqread2 = read1eqread2isFalse.getLHS();
  Expr read1 = read1eqread2[0];
  Expr read2 = read1eqread2[1];
  Expr i1 = read1[1];
  Expr i2 = read2[1];

  Proof pf;
  if (withProof())
    pf = newPf("propagateIndexDiseq", read1eqread2isFalse.getProof());

  return newTheorem(i1.eqExpr(i2).notExpr(), Assumptions(read1eqread2isFalse), pf);
}
