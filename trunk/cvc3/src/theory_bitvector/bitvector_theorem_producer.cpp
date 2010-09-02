/*****************************************************************************/
/*!
 * \file bitvector_theorem_producer.cpp
 *
 * Author: Vijay Ganesh
 *
 * Created: Wed May  5 16:19:49 PST 2004
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
// CLASS: BitvectorProofRules
//
// AUTHOR: Vijay Ganesh,   05/30/2003
//
// Description: TRUSTED implementation of bitvector proof rules.
//
///////////////////////////////////////////////////////////////////////////////

// This code is trusted
#define _CVC3_TRUSTED_

#include <cstdio>
#include "bitvector_theorem_producer.h"
#include "common_proof_rules.h"
#include "theory_core.h"
#include "theory_bitvector.h"

using namespace std;
using namespace CVC3;


///////////////////////////////////////////////////////////////////////
// TheoryBitvector:trusted method for creating BitvectorTheoremProducer
///////////////////////////////////////////////////////////////////////
BitvectorProofRules*
TheoryBitvector::createProofRules() {
  return new BitvectorTheoremProducer(this);
}


BitvectorTheoremProducer::BitvectorTheoremProducer(TheoryBitvector* theoryBV)
  : TheoremProducer(theoryBV->theoryCore()->getTM()),
    d_theoryBitvector(theoryBV) {
  // Cache constants 0bin0 and 0bin1
  vector<bool> bits(1);
  bits[0]=false;
  d_bvZero = d_theoryBitvector->newBVConstExpr(bits);
  bits[0]=true;
  d_bvOne = d_theoryBitvector->newBVConstExpr(bits);
}


///////////////////////////////////////////////////////////////////////
// BitBlasting rules for equations
///////////////////////////////////////////////////////////////////////
// |- (BOOLEXTRACT(a,i) <=> BOOLEXTRACT(b,i)) <=> False ==> |- a = b <=> False
Theorem BitvectorTheoremProducer::bitvectorFalseRule(const Theorem& thm) {
  if(CHECK_PROOFS) {
    const Expr e = thm.getExpr();
    CHECK_SOUND(e.isIff() && e[0].isIff(),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be a iff theorem:\n e = "
		+e.toString());
    CHECK_SOUND(e[1].isFalse(),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
    CHECK_SOUND(e[0][0].getOpKind() == BOOLEXTRACT &&
		e[0][1].getOpKind() == BOOLEXTRACT,
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
    CHECK_SOUND(d_theoryBitvector->getBoolExtractIndex(e[0][0]) ==
		d_theoryBitvector->getBoolExtractIndex(e[0][1]),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
  }
  const Expr& e = thm.getExpr();
  const Expr& t1 = e[0][0][0];
  const Expr& t2 = e[0][1][0];

  Proof pf;
  if(withProof())
    pf = newPf("bitvector_false_rule", e, thm.getProof());
  return newRWTheorem(t1.eqExpr(t2), e[1], thm.getAssumptionsRef(), pf);
}

    /*! \param thm input theorem: (~e1[i]<=>e2[i])<=>true
     *
     *  \result (e1!=e2)<=>true
     */
// |- (NOT (BOOLEXTRACT(a,i)) <=> BOOLEXTRACT(b,i)) <=> TRUE ==>
// |- NOT (a = b) <=> TRUE
Theorem BitvectorTheoremProducer::bitvectorTrueRule(const Theorem& thm) {
  if(CHECK_PROOFS) {
    const Expr e = thm.getExpr();
    CHECK_SOUND(e.isIff() && e[0].isIff(),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be a iff theorem:\n e = "
		+e.toString());
    CHECK_SOUND(e[1].isTrue(),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
    CHECK_SOUND(e[0][0].getKind() == NOT &&
		e[0][0][0].getOpKind() == BOOLEXTRACT &&
		e[0][1].getOpKind() == BOOLEXTRACT,
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
    CHECK_SOUND(d_theoryBitvector->getBoolExtractIndex(e[0][0][0]) ==
		d_theoryBitvector->getBoolExtractIndex(e[0][1]),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
  }
  const Expr& e = thm.getExpr();
  //e is (~BE(t1,i)<=>BE(t2,i))<=>true. to extract t1 we have to go 4 level deep
  //FIXME: later
  const Expr& t1 = e[0][0][0][0];
  const Expr& t2 = e[0][1][0];

  Proof pf;
  if(withProof())
    pf = newPf("bitvector_true_rule", e, thm.getProof());
  return newRWTheorem(t1.eqExpr(t2).negate(), e[1], thm.getAssumptionsRef(), pf);
}

// Input: e: a = b
//        f :AND_0^(bvLength-1)(a[bitPosition] <=> b[bitPosition])
// Output: |- e <=> f
Theorem BitvectorTheoremProducer::bitBlastEqnRule(const Expr& e, const Expr& f)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isEq(),
		"TheoryBitvector::bitBlastEqnRule: "
		"premise must be a rewrite theorem:\n e = "
		+e.toString());
    const Expr& lhs = e[0];
    const Expr& rhs = e[1];
    const Type& leftType = lhs.getType();
    const Type& rightType = rhs.getType();
    CHECK_SOUND(BITVECTOR == leftType.getExpr().getOpKind() &&
		BITVECTOR == rightType.getExpr().getOpKind(),
		"TheoryBitvector::bitBlastEqnRule: "
		"lhs & rhs must be bitvectors:\n e ="
		+e.toString());
    int lhsLength = d_theoryBitvector->BVSize(lhs);
    int rhsLength = d_theoryBitvector->BVSize(rhs);
    CHECK_SOUND(lhsLength == rhsLength,
		"TheoryBitvector::bitBlastEqnRule: "
		"lhs & rhs must be bitvectors of same bvLength.\n size(lhs) = "
		+ int2string(lhsLength)
		+"\n size(rhs) = "
		+ int2string(rhsLength)
		+"\n e = "+e.toString());
    int bvLength = d_theoryBitvector->BVSize(leftType.getExpr());
    CHECK_SOUND(f.isAnd(),
		"TheoryBitvector::bitBlastEqnRule: "
		"consequence of the rule must be an AND.\n f = "
		+f.toString());
    CHECK_SOUND(bvLength == f.arity(),
		"TheoryBitvector::bitBlastEqnRule: "
		"the arity of the consequence AND must "
		"equal the bvLength of the bitvector:\n f = "
		+f.toString()+"\n bvLength = "+ int2string(bvLength));
    for (int i=0; i < bvLength; ++i) {
      const Expr& conjunct = f[i];
      CHECK_SOUND(conjunct.isIff() && 2 == conjunct.arity(),
		  "TheoryBitvector::bitBlastEqnRule: "
		  "each conjunct in consequent must be an IFF.\n f = "
		  +f.toString());
      const Expr& leftExtract = conjunct[0];
      const Expr& rightExtract = conjunct[1];
      CHECK_SOUND(BOOLEXTRACT == leftExtract.getOpKind(),
		  "TheoryBitvector::bitBlastEqnRule: "
		  "each conjunct in consequent must be boolextract.\n"
		  " f["+int2string(i)+"] = "+conjunct.toString());
      CHECK_SOUND(BOOLEXTRACT == rightExtract.getOpKind(),
		  "TheoryBitvector::bitBlastEqnRule: "
		  "each conjunct in consequent must be boolextract.\n"
		  " f["+int2string(i)+"] = "+conjunct.toString());
      const Expr& leftBV = leftExtract[0];
      const Expr& rightBV = rightExtract[0];
      CHECK_SOUND(leftBV == lhs && rightBV == rhs,
		  "TheoryBitvector::bitBlastEqnRule: each boolextract"
		  " must be applied to the correct bitvector.\n conjunct = "
		  +conjunct.toString()
		  +"\n leftBV = "+ leftBV.toString()
		  +"\n lhs = "+ lhs.toString()
		  +"\n rightBV = "+rightBV.toString()
		  +"\n rhs = "+rhs.toString());
      int leftBitPosition =
	d_theoryBitvector->getBoolExtractIndex(leftExtract);
      int rightBitPosition =
	d_theoryBitvector->getBoolExtractIndex(rightExtract);
      CHECK_SOUND(leftBitPosition == i && rightBitPosition == i,
		  "TheoryBitvector::bitBlastEqnRule: "
		  "boolextract positions must match i= "+int2string(i)
		  +"\n conjunct = "+conjunct.toString());
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("bit_blast_equations", e, f);
  return newRWTheorem(e, f, Assumptions::emptyAssump(), pf);
}


///////////////////////////////////////////////////////////////////////
// BitBlasting rules for dis-equations: separate rule for disequations
// for efficiency sake
///////////////////////////////////////////////////////////////////////
Theorem BitvectorTheoremProducer::bitBlastDisEqnRule(const Theorem& notE,
						     const Expr& f){

  TRACE("bitvector", "input to bitBlastDisEqnRule(", notE.toString(), ")");
  DebugAssert(notE.getExpr().isNot() && (notE.getExpr())[0].isEq(),
	      "TheoryBitvector::bitBlastDisEqnRule:"
	      "expecting an equation" + notE.getExpr().toString());
  //e is the equation
  const Expr& e = (notE.getExpr())[0];
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isEq(),
		"TheoryBitvector::bitBlastDisEqnRule:"
		"premise must be a rewrite theorem" + e.toString());
    const Expr& lhs = e[0];
    const Expr& rhs = e[1];
    const Type& leftType = lhs.getType();
    const Type& rightType = rhs.getType();
    CHECK_SOUND(BITVECTOR == leftType.getExpr().getOpKind() &&
		BITVECTOR == rightType.getExpr().getOpKind(),
		"TheoryBitvector::bitBlastDisEqnRule:"
		"lhs & rhs must be bitvectors" + e.toString());
    CHECK_SOUND(d_theoryBitvector->BVSize(leftType.getExpr()) ==
		d_theoryBitvector->BVSize(rightType.getExpr()),
		"TheoryBitvector::bitBlastDisEqnRule:"
		"lhs & rhs must be bitvectors of same bvLength");
    int bvLength = d_theoryBitvector->BVSize(leftType.getExpr());
    CHECK_SOUND(f.isOr(),
		"TheoryBitvector::bitBlastDisEqnRule:"
		"consequence of the rule must be an OR" + f.toString());
    CHECK_SOUND(bvLength == f.arity(),
		"TheoryBitvector::bitBlastDisEqnRule:"
		"the arity of the consequence OR must be"
		"equal to the bvLength of the bitvector" +
		f.toString() + int2string(bvLength));
    for(int i=0; i <bvLength; i++) {
      const Expr& disjunct = f[i];
      CHECK_SOUND(disjunct.isIff() &&
		  2 == disjunct.arity() && disjunct[0].isNot(),
		  "TheoryBitvector::bitBlastDisEqnRule:"
		  "each conjunct in consequent must be an Iff"+f.toString());
      const Expr& leftExtract = (disjunct[0])[0];
      const Expr& rightExtract = disjunct[1];
      CHECK_SOUND(BOOLEXTRACT == leftExtract.getOpKind(),
		  "TheoryBitvector::bitBlastDisEqnRule:"
		  "each disjunct in consequent must be boolextract" +
		  disjunct.toString());
      CHECK_SOUND(BOOLEXTRACT == rightExtract.getOpKind(),
		  "TheoryBitvector::bitBlastDisEqnRule:"
		  "each conjunct in consequent must be boolextract" +
		  disjunct.toString());
      const Expr& leftBV = leftExtract[0];
      const Expr& rightBV = rightExtract[0];
      CHECK_SOUND(leftBV == lhs && rightBV == rhs,
		  "TheoryBitvector::bitBlastDisEqnRule:"
		  "each boolextract must be applied to the correct bitvector"+
		  disjunct.toString() + leftBV.toString() + lhs.toString() +
		  rightBV.toString() + rhs.toString());
      int leftBitPosition =
	d_theoryBitvector->getBoolExtractIndex(leftExtract);
      int rightBitPosition =
	d_theoryBitvector->getBoolExtractIndex(rightExtract);
      CHECK_SOUND(leftBitPosition == i && rightBitPosition == i,
		  "TheoryBitvector::bitBlastDisEqnRule:"
		  "boolextract positions must match" + disjunct.toString());
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("bit_blast_disequations", notE.getExpr(), f, notE.getProof());
  return newTheorem(f, notE.getAssumptionsRef(), pf);
}

///////////////////////////////////////////////////////////////////////
// Rules for Inequations
///////////////////////////////////////////////////////////////////////


//! Pad the kids of BVLT/BVLE to make their bvLength equal
Theorem
BitvectorTheoremProducer::padBVLTRule(const Expr& e, int len) {
  if(CHECK_PROOFS) {
    CHECK_SOUND((BVLT == e.getOpKind() || BVLE == e.getOpKind()) &&
		e.arity()==2,
		"BitvectorTheoremProducer::padBVLTRule: "
		"input must e be a BVLT/BVLE: e = " + e.toString());
    CHECK_SOUND(BITVECTOR==e[0].getType().getExpr().getOpKind() &&
		BITVECTOR==e[1].getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::padBVLTRule: "
		"for BVMULT terms e[0],e[1] must be a BV: " + e.toString());
    CHECK_SOUND(0<len,
		"BitvectorTheoremProducer::padBVLTRule: "
		"input len must be >=0 and an integer: len = " +
		int2string(len));
  }
  Expr e0 = pad(len, e[0]);
  Expr e1 = pad(len, e[1]);
  int kind = e.getOpKind();

  Expr output;
  if(kind == BVLT)
    output = d_theoryBitvector->newBVLTExpr(e0,e1);
  else
    output = d_theoryBitvector->newBVLEExpr(e0,e1);

  Proof pf;
  if(withProof())
    pf = newPf("pad_bvlt_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! signExtendRule: pads the input e with topBit to length len
Theorem
BitvectorTheoremProducer::signExtendRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR==e.getType().getExpr().getOpKind(),
		"input must be a bitvector. \n e = " + e.toString());
    CHECK_SOUND(SX == e.getOpKind(),
		"input must be SX(e).\n e = " + e.toString());
    CHECK_SOUND(SX != e[0].getOpKind(),
		"input cannot have nested SX.\n e = " + e.toString());
  }
  Expr input0 = e[0];
  //strip the top level SX applications
  while(SX == input0.getOpKind())
    input0 = input0[0];

  int bvLength = d_theoryBitvector->BVSize(e);
  int bvLength0 = d_theoryBitvector->BVSize(input0);

  Expr output;
  if(bvLength0 == bvLength) {
    output = input0;
  } else if(bvLength0 < bvLength) {
    std::vector<Expr> k;
    int c = bvLength - bvLength0;
    Expr topBit =
      d_theoryBitvector->newBVExtractExpr(input0,bvLength0-1,bvLength0-1);
    while(c--)
      k.push_back(topBit);
    k.push_back(input0);
    output = d_theoryBitvector->newConcatExpr(k);
  } else
    output = d_theoryBitvector->newBVExtractExpr(input0, bvLength-1, 0);

  Proof pf;
  if(withProof())
    pf = newPf("sign_extend_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! bitExtractSXRule
Theorem
BitvectorTheoremProducer::bitExtractSXRule(const Expr& e, int i) {
  //little bit of cheating here. calling a rule from inside a rule.
  //just a shorthand
  Theorem thm = signExtendRule(e);
  Expr e_i = d_theoryBitvector->newBoolExtractExpr(e,i);
  Expr newE_i = d_theoryBitvector->newBoolExtractExpr(thm.getRHS(),i);

  Proof pf;
  if(withProof())
    pf = newPf("bitExtract_SX_rule",e,rat(i));
  Theorem result(newRWTheorem(e_i,newE_i,Assumptions::emptyAssump(),pf));
  return result;
}


//! Pad the kids of SIGN BVLT/SIGN BVLE to make their bvLength equal
Theorem
BitvectorTheoremProducer::padBVSLTRule(const Expr& e, int len) {
  if(CHECK_PROOFS) {
    CHECK_SOUND((BVSLT == e.getOpKind() || BVSLE == e.getOpKind()) &&
		e.arity()==2,
		"BitvectorTheoremProducer::padBVSLTRule: "
		"input must e be a BVSLT/BVSLE: e = " + e.toString());
    CHECK_SOUND(BITVECTOR==e[0].getType().getExpr().getOpKind() &&
		BITVECTOR==e[1].getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::padBVSLTRule: "
		"for BVMULT terms e[0],e[1] must be a BV: " + e.toString());
    CHECK_SOUND(0<=len,
		"BitvectorTheoremProducer::padBVSLTRule: "
		"input len must be >=0 and an integer: len = " +
		int2string(len));
  }
  Expr e0 = d_theoryBitvector->newSXExpr(e[0], len);
  Expr e1 = d_theoryBitvector->newSXExpr(e[1], len);
  int kind = e.getOpKind();

  Expr output;
  if(kind == BVSLT)
    output = d_theoryBitvector->newBVSLTExpr(e0,e1);
  else
    output = d_theoryBitvector->newBVSLEExpr(e0,e1);

  Proof pf;
  if(withProof())
    pf = newPf("pad_bvslt_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

/*! input: e0 <=(s) e1. output depends on whether the topbits(MSB) of
 *  e0 and e1 are constants. If they are constants then optimizations
 *  are done, otherwise the following rule is implemented.
 *
 *  e0 <=(s) e1 <==> (e0[n-1] AND NOT e1[n-1]) OR
 *                   (e0[n-1] = e1[n-1] AND e0[n-2:0] <= e1[n-2:0])
 */
Theorem
BitvectorTheoremProducer::signBVLTRule(const Expr& e,
				       const Theorem& topBit0,
				       const Theorem& topBit1){
  if(CHECK_PROOFS) {
    CHECK_SOUND((BVSLT == e.getOpKind() || BVSLE == e.getOpKind()) &&
		e.arity()==2,
		"BitvectorTheoremProducer::signedBVLTRule: "
		"input must e be a BVSLT/BVSLE: e = " + e.toString());
    CHECK_SOUND(BITVECTOR==e[0].getType().getExpr().getOpKind() &&
		BITVECTOR==e[1].getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::signedBVLTRule: "
		"for BVMULT terms e[0],e[1] must be a BV: " + e.toString());
  }
  const Expr e0 = e[0];
  const Expr e1 = e[1];
  int e0len = d_theoryBitvector->BVSize(e0);
  int e1len = d_theoryBitvector->BVSize(e1);

  if(CHECK_PROOFS) {
    const Expr e0ext =
      d_theoryBitvector->newBVExtractExpr(e0,e0len-1,e0len-1);
    const Expr e1ext =
      d_theoryBitvector->newBVExtractExpr(e1,e1len-1,e1len-1);
    CHECK_SOUND(e0ext == topBit0.getLHS(),
		"BitvectorTheoremProducer::signedBVLTRule: "
		"topBit0.getLHS() is the un-rewritten form of MSB of e0\n"
		"topBit0 is screwed up: topBit0 = " +
		topBit0.getExpr().toString());
    CHECK_SOUND(e1ext == topBit1.getLHS(),
		"BitvectorTheoremProducer::signedBVLTRule: "
		"topBit1.getLHS() is the un-rewritten form of MSB of e1\n"
		"topBit1 is screwed up: topBit1 = " +
		topBit1.getExpr().toString());
    CHECK_SOUND(e0len == e1len,
		"BitvectorTheoremProducer::signedBVLTRule: "
		"both e[0] and e[1] must have the same length\n. e =" +
		e.toString());
  }
  const Expr MSB0 = topBit0.getRHS();
  const Expr MSB1 = topBit1.getRHS();

  int eKind = e.getOpKind();
  Expr output;

  //if both MSBs are constants, then we can optimize the output.  we
  //know precisely the value of the signed comparison in cases where
  //topbit of e0 and e1 are constants. e.g. |-1\@t0 < 0\@t1 is clearly
  //|-TRUE.

  //-1 indicates that both topBits are not known to be BVCONSTS
  Rational b0 = -1;
  Rational b1 = -1;
  if(MSB0.getKind() == BVCONST) b0 = d_theoryBitvector->computeBVConst(MSB0);
  if(MSB1.getKind() == BVCONST) b1 = d_theoryBitvector->computeBVConst(MSB1);

  //useful expressions to be used below
  const Expr tExpr = d_theoryBitvector->trueExpr();
  const Expr fExpr = d_theoryBitvector->falseExpr();
  const Expr MSB0isZero = MSB0.eqExpr(bvZero());
  const Expr MSB0isOne  = MSB0.eqExpr(bvOne());
  const Expr MSB1isZero = MSB1.eqExpr(bvZero());
  const Expr MSB1isOne  = MSB1.eqExpr(bvOne());

  //handle single bit e0 <=(s) e1 in a special way. this is clumsy
  //(i.e. extra and redundant code) but much more efficient and easy
  //to read
  if(e0len == 1) {
    if(b0==0 && b1==0)
      output = eKind==BVSLT ? fExpr      : tExpr;
    else if(b0==0  && b1==1)
      output = fExpr;
    else if(b0==1  && b1==0)
      output = tExpr;
    else if(b0==1  && b1==1)
      output = eKind==BVSLT ? fExpr      : tExpr;
    else if(b0==0  && b1==-1)
      output = eKind==BVSLT ? fExpr      : MSB1isZero;
    else if(b0==1  && b1==-1)
      output = eKind==BVSLT ? MSB1isZero : tExpr;
    else if(b0==-1 && b1==0)
      output = eKind==BVSLT ? MSB0isOne  : tExpr;
    else if(b0==-1 && b1==1)
      output = eKind==BVSLT ? fExpr      : MSB0isOne;
    else
      //both b0 and b1 are -1
      output =
	eKind==BVSLT ?
	MSB0isOne.andExpr(MSB1isZero) :
	MSB0isOne.orExpr(MSB1isZero);
  } else {
    //useful expressions to be used below
    Expr newE0 = d_theoryBitvector->newBVExtractExpr(e0,e0len-2,0);
    Expr newE1 = d_theoryBitvector->newBVExtractExpr(e1,e1len-2,0);
    Expr newBVLT =
      eKind==BVSLT ?
      d_theoryBitvector->newBVLTExpr(newE0,newE1):
      d_theoryBitvector->newBVLEExpr(newE0,newE1);
//     Expr newBVLTreverse =
//       eKind==BVSLT ?
//       d_theoryBitvector->newBVLTExpr(newE1,newE0):
//       d_theoryBitvector->newBVLEExpr(newE1,newE0);


    //both MSBs are simultaneously constants
    if(-1 != b0 && -1 !=b1) {
      //e0 is negative and e1 is positive
      if(b0 == 1 && b1 == 0)
	output = tExpr;
      //e0 is positive and e1 is negative
      else if(b0 == 0 && b1 == 1)
	output = fExpr;
      //e0 = e1, so result is determined by the rest of the bits
      else {
	output = newBVLT;
      }
    }
    else if(-1 != b0 && -1 == b1) {
      //only b0 is a constant. Both topBits are not simultaneously constants.

      //if (b0==0)
      //    e0 <=(s) e1 <==> NOT e1[n-1] AND e0[n-2:0] <= e1[n-2:0])
      //else
      //    e0 <=(s) e1 <==> NOT e1[n-1] OR (e1[n-1] AND e0[n-2:0] <= e1[n-2:0]))

      output =
	(b0==0) ?
	//means that b1 has to be 0 and e0[n-2:0] <= e1[n-2:0]
	MSB1isZero.andExpr(newBVLT) :
	//means that either b1 is 0 or (b1 is 1 and e0[n-2:0] <= e1[n-2:0])
	MSB1isZero.orExpr(MSB1isOne.andExpr(newBVLT));
    }
    else if(-1 == b0 && -1 != b1) {
      //only b1 is a constant. Both topBits are not simultaneously constants.

      //if (b1==0)
      //    e0 <=(s) e1 <==> e0[n-1] OR (NOT e0[n-1] AND e0[n-2:0] <= e1[n-2:0]))
      //else
      //    e0 <=(s) e1 <==> e0[n-1] AND e0[n-2:0] <= e1[n-2:0]))

      output =
	(b1==0) ?
	//means that either b0 must be 1 or (b0 = 0 and e0[n-2:0] <= e1[n-2:0])
	MSB0isOne.orExpr(MSB0isZero.andExpr(newBVLT)) :
	//means that b0 must be 1 and e0[n-2:0] <= e1[n-2:0]
	MSB0isOne.andExpr(newBVLT);
    } else {
      //both top bits are not constants.

      //(e0[n-1] AND NOT e1[n-1])
      Expr k0 = MSB0isOne.andExpr(MSB1isZero);

      //(e0[n-1] = e1[n-1])
      Expr k1 = MSB0.eqExpr(MSB1);

      //e0 <=(s) e1 <==> (e0[n-1] AND NOT e1[n-1]) OR
      //                 (e0[n-1] = e1[n-1] AND e0[n-2:0] <= e1[n-2:0])
      output = k0.orExpr(k1.andExpr(newBVLT));
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("sign_bvlt_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


/*! NOT(e[0][0] = e[0][1]) <==> e[0][0] = ~e[0][1]
 */
Theorem BitvectorTheoremProducer::notBVEQ1Rule(const Expr& e)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == NOT,
		"BitvectorTheoremProducer::notBVEQ1Rule: "
		"input kind must be a NOT:\n e = " + e.toString());
    CHECK_SOUND(e[0].getOpKind() == EQ,
		"BitvectorTheoremProducer::notBVEQ1Rule: "
		"e[0] must be EQ: \n e = " + e.toString());
    CHECK_SOUND(d_theoryBitvector->BVSize(e[0][0]) == 1,
		"BitvectorTheoremProducer::notBVEQ1Rule: "
		"BVSize(e[0][0]) must be 1: \n e = " + e.toString());
  }
  Expr output = e[0][0].eqExpr(d_theoryBitvector->newBVNegExpr(e[0][1]));

  Proof pf;
  if(withProof())
    pf = newPf("not_eq1_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


/*! NOT(e[0][0] < e[0][1]) <==> (e[0][1] <= e[0][0]),
 *  NOT(e[0][0] <= e[0][1]) <==> (e[0][1] < e[0][0])
 */
Theorem BitvectorTheoremProducer::notBVLTRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == NOT,
		"BitvectorTheoremProducer::notBVLTRule: "
		"input kind must be a NOT:\n e = " + e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVLT ||
		e[0].getOpKind() == BVLE,
		"BitvectorTheoremProducer::notBVLTRule: "
		"e[0] must be BVLT or BVLE: \n e = " + e.toString());
  }
  Expr output;

  const Expr& e00 = e[0][0];
  const Expr& e01 = e[0][1];
  if(BVLT == e[0].getOpKind())
    output = d_theoryBitvector->newBVLEExpr(e01,e00);
  else
    output = d_theoryBitvector->newBVLTExpr(e01,e00);

  Proof pf;
  if(withProof())
    pf = newPf("not_bvlt_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! if(lhs==rhs) then we have (lhs < rhs <==> false),(lhs <= rhs <==> true)
Theorem BitvectorTheoremProducer::lhsEqRhsIneqn(const Expr& e, int kind) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVLT == e.getOpKind() || BVLE == e.getOpKind(),
		"BitvectorTheoremProducer::lhsEqRhsIneqn: "
		"input kind must be BVLT or BVLE: e = " + e.toString());
    CHECK_SOUND(kind == e.getOpKind(),
		"BitvectorTheoremProducer::lhsEqRhsIneqn: "
		"input kind must match e.getOpKind(): "
		"\n e = " + e.toString());
    CHECK_SOUND((e.arity()==2) && (e[0]==e[1]),
		"BitvectorTheoremProducer::lhsEqRhsIneqn: "
		"input arity must be 2, and e[0] must be equal to e[1]: "
		"\ne = " + e.toString());
  }
  Expr output;
  if(kind == BVLT)
    output = d_theoryBitvector->falseExpr();
  else
    output = d_theoryBitvector->trueExpr();

  Proof pf;
  if(withProof())
    pf = newPf("lhs_eq_rhs_ineqn", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! |= 0 <= foo <-> TRUE
Theorem BitvectorTheoremProducer::zeroLeq(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVLE == e.getOpKind(),
		"BitvectorTheoremProducer::zeroLeq: "
		"input kind must be BVLE: e = " + e.toString());
    CHECK_SOUND(e.arity()==2 && e[0].getOpKind() == BVCONST &&
                d_theoryBitvector->computeBVConst(e[0]) == 0,
		"BitvectorTheoremProducer::zeroLeq: "
		"unexpected input: e = " + e.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("zeroLeq", e);
  return newRWTheorem(e, d_theoryBitvector->trueExpr(), Assumptions::emptyAssump(), pf);
}


//! if indeed e[0] < e[1] then (e<==>true) else (e<==>false)
Theorem BitvectorTheoremProducer::bvConstIneqn(const Expr& e, int kind) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVLT == e.getOpKind() || BVLE == e.getOpKind(),
		"BitvectorTheoremProducer::bvConstIneqn: "
		"input kind must be BVLT or BVLE: e = " + e.toString());
    CHECK_SOUND(kind == e.getOpKind(),
		"BitvectorTheoremProducer::bvConstIneqn: "
		"input kind must match e.getOpKind(): "
		"\n e = " + e.toString());
    CHECK_SOUND((e.arity()==2),
		"BitvectorTheoremProducer::bvConstIneqn: "
		"input arity must be 2: \ne = " + e.toString());
    CHECK_SOUND(BVCONST == e[0].getKind() && BVCONST == e[1].getKind(),
		"BitvectorTheoremProducer::bvConstIneqn: "
		"e[0] and e[1] must both be constants:\n e = " +
		e.toString());
  }

  int e0len = d_theoryBitvector->BVSize(e[0]);
  int e1len = d_theoryBitvector->BVSize(e[1]);
  if(CHECK_PROOFS)
    CHECK_SOUND(e0len == e1len,
		"BitvectorTheoremProducer::bvConstIneqn: "
		"e[0] and e[1] must have the same bvLength:\ne = " +
		e.toString());

  Rational lhsVal = d_theoryBitvector->computeBVConst(e[0]);
  Rational rhsVal = d_theoryBitvector->computeBVConst(e[1]);
  Expr output;

  if(BVLT == kind) {
    if(lhsVal < rhsVal)
      output = d_theoryBitvector->trueExpr();
    else
      output = d_theoryBitvector->falseExpr();
  } else {
    if(lhsVal <= rhsVal)
      output = d_theoryBitvector->trueExpr();
    else
      output = d_theoryBitvector->falseExpr();
  }

  Proof pf;
  if(withProof())
    pf = newPf("bv_const_ineqn", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


// Input: e: a op b, where op is < or <=
//        lhs_i: BOOLEXTRACT(a,i) <=> b1
//        rhs_i: BOOLEXTRACT(b,i) <=> b2
//        kind: op
//        i = BVSize(a)-1 = BVSize(b)-1
// Output: for i > 0:
//           (lhs_i < rhs_i) OR (lhs_i = rhs_i AND a[i-1:0] op b[i-1:0])
//         for i = 0:
//           (lhs_i op rhs_i)
Theorem BitvectorTheoremProducer::generalIneqn(const Expr& e,
					       const Theorem& lhs_i,
					       const Theorem& rhs_i,
					       int kind) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVLT == e.getOpKind() || BVLE == e.getOpKind(),
		"BitvectorTheoremProducer::generalIneqn: "
		"input kind must be BVLT or BVLE: e = " + e.toString());
    CHECK_SOUND(kind == e.getOpKind(),
		"BitvectorTheoremProducer::generalIneqn: "
		"input kind must match e.getOpKind(): "
		"\n e = " + e.toString());
    CHECK_SOUND((e.arity()==2),
		"BitvectorTheoremProducer::generalIneqn: "
		"input arity must be 2: \ne = " + e.toString());
    CHECK_SOUND(lhs_i.isRewrite() && rhs_i.isRewrite(),
		"BitvectorTheoremProducer::generalIneqn: "
		"lhs_i and rhs_i must be rewrite theorems: "
		"\nlhs_i = " + lhs_i.toString() +
		"\nrhs_i = " + rhs_i.toString());
  }

  int e0len = d_theoryBitvector->BVSize(e[0]);
  int e1len = d_theoryBitvector->BVSize(e[1]);
  const Expr& e0_iBit = lhs_i.getLHS();
  const Expr& e1_iBit = rhs_i.getLHS();
  if(CHECK_PROOFS) {
    CHECK_SOUND(BOOLEXTRACT == e0_iBit.getOpKind() &&
		BOOLEXTRACT == e1_iBit.getOpKind(),
		"BitvectorTheoremProducer::generalIneqn: "
		"lhs_i.getRHS() and rhs_i.getRHS() must be BOOLEXTRACTs:"
		"\nlhs_i = " + lhs_i.toString() +
		"\nrhs_i = " + rhs_i.toString());
    CHECK_SOUND(e[0] == e0_iBit[0],
		"BitvectorTheoremProducer::generalIneqn: "
		"e[0] must be equal to LHS of lhs_i: \nlhs_i = " +
		lhs_i.toString() + "\n e[0] = " + e[0].toString());
    CHECK_SOUND(e[1] == e1_iBit[0],
		"BitvectorTheoremProducer::generalIneqn: "
		"e[1] must be equal to LHS of rhs_i: \nrhs_i = " +
		rhs_i.toString() + "\n e[1] = " + e[1].toString());
    CHECK_SOUND(e0len == e1len,
		"BitvectorTheoremProducer::generalIneqn: "
		"e[0] and e[1] must have the same bvLength:\ne = " +
		e.toString());
    int e0_iBitIndex =
      d_theoryBitvector->getBoolExtractIndex(e0_iBit);
    int e1_iBitIndex =
      d_theoryBitvector->getBoolExtractIndex(e1_iBit);
    CHECK_SOUND(e0_iBitIndex == e1_iBitIndex &&
		e0_iBitIndex == e0len-1,
		"BitvectorTheoremProducer::generalIneqn: "
		"e0_iBit & e1_iBit must have same extract index: "
		"\ne0_iBit = " + e0_iBit.toString() +
		"\ne1_iBit = " + e1_iBit.toString());
  }

  const Expr& b1 = lhs_i.getRHS();
  const Expr& b2 = rhs_i.getRHS();
  const Expr& trueExpression = d_theoryBitvector->trueExpr();
  const Expr& falseExpression = d_theoryBitvector->falseExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(b1.getType().isBool(),
		"BitvectorTheoremProducer::generalIneqn: "
		"b1 must be a boolean type: "
		"\n b1 = " + b1.toString());
    CHECK_SOUND(b2.getType().isBool(),
		"BitvectorTheoremProducer::generalIneqn: "
		"b2 must be boolean type: "
		"\n b2 = " + b2.toString());
  }

  Expr output;
  // Check for the shortcuts
  if (b1.isFalse() && b2.isTrue()) // b1 < b2
    output = trueExpression;
  else if (b1.isTrue() && b2.isFalse()) // b1 > b2
    output = falseExpression;
  else if (e0len==1) {
    // If this is the last bit, and one of them is a constant
    if (kind==BVLE && (b1.isFalse() || b2.isTrue())) // F <= x or x <= T
      output = trueExpression;
    else if (kind==BVLT && (b2.isFalse() || b1.isTrue())) // x < F or T < x
      output = falseExpression;
  }

  // No shortcuts found
  if (output.isNull()) {

    // Process the top bits
    if (kind == BVLT || e0len > 1) {
      output = (!b1) && b2;
    }
    else {
      output = (!b1) || b2;
    }

    if(e0len > 1) {
      //construct e0[n-2:0]
      Expr e0_extract =
	d_theoryBitvector->newBVExtractExpr(e[0],e0len-2,0);
      //construct e1[n-2:0]
      Expr e1_extract =
	d_theoryBitvector->newBVExtractExpr(e[1],e1len-2,0);

      Expr a;
      if(kind==BVLT)
	//construct e0[n-2:0] < e1[n-2:0]
	a = d_theoryBitvector->newBVLTExpr(e0_extract,e1_extract);
      else
	//construct e0[n-2:0] <= e1[n-2:0]
	a = d_theoryBitvector->newBVLEExpr(e0_extract,e1_extract);

      //construct (b1=0 and/or b2=1) or (b1=b2 and a)
      output = output || (b1.iffExpr(b2) && a);
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("general_ineqn", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

///////////////////////////////////////////////////////////////////////
// BitExtracting rules for terms
///////////////////////////////////////////////////////////////////////

// Input: |- BOOLEXTRACT(a,0) <=> bc_0, ... BOOLEXTRACT(a,n-1) <=> bc_(n-1)
// where each bc_0 is TRUE or FALSE
// Output: |- a = c
// where c is an n-bit constant made from the values bc_0..bc_(n-1)
Theorem BitvectorTheoremProducer::bitExtractAllToConstEq(vector<Theorem>& thms)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(thms.size() > 0, "Expected size > 0");
    unsigned i;
    for(i = 0; i < thms.size(); ++i) {
      Expr e = thms[i].getExpr();
      CHECK_SOUND(e.getKind() == IFF && e.arity() == 2 && e[1].isBoolConst(),
                  "Unexpected structure");
      CHECK_SOUND(e[0].getOpKind() == BOOLEXTRACT &&
                  e[0].arity() == 1 &&
                  e[0][0] == thms[0].getExpr()[0][0] &&
                  unsigned(d_theoryBitvector->getBoolExtractIndex(e[0])) == i,
                  "Unexpected structure");
    }
  }
  Expr lhs = thms[0].getExpr()[0][0];
  vector<bool> bits;
  for (unsigned i = 0; i < thms.size(); ++i) {
    bits.push_back(thms[i].getExpr()[1].isTrue() ? true : false);
  }
  Expr rhs = d_theoryBitvector->newBVConstExpr(bits);

  Assumptions a(thms);
  Proof pf;
  if (withProof())
    pf = newPf("bit_extract_all_to_const_eq");
  return newRWTheorem(lhs, rhs, a, pf);
}


//! t[i] ==> t[i:i] = 0bin1   or    NOT t[i] ==> t[i:i] = 0bin0
Theorem BitvectorTheoremProducer::bitExtractToExtract(const Theorem& thm) {
  const Expr& e = thm.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND((e.isNot() && e[0].getOpKind() == BOOLEXTRACT)
		|| (e.getOpKind() == BOOLEXTRACT),
		"BitvectorTheoremProducer::bitExtractToExtract:\n e = "
		+e.toString());
  }
  bool negative = e.isNot();
  const Expr& boolExtract = negative? e[0] : e;
  int i = d_theoryBitvector->getBoolExtractIndex(boolExtract);
  Expr lhs = d_theoryBitvector->newBVExtractExpr(boolExtract[0], i, i);

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_to_extract", e, thm.getProof());
  return newRWTheorem(lhs, negative? bvZero() : bvOne(), thm.getAssumptionsRef(), pf);
}


//! t[i] <=> t[i:i][0]   (to use rewriter for simplifying t[i:i])
Theorem BitvectorTheoremProducer::bitExtractRewrite(const Expr& x) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(x.getOpKind() == BOOLEXTRACT,
		"BitvectorTheoremProducer::bitExtractRewrite: x = "
		+x.toString());
  }

  int i = d_theoryBitvector->getBoolExtractIndex(x);
  const Expr& t = x[0];
  int bvLength = d_theoryBitvector->BVSize(t);

  if(CHECK_PROOFS) {
    CHECK_SOUND(0<=i && i<bvLength,
		"BitvectorTheoremProducer::bitExtractRewrite:"
		"\n bvLength = "
		+ int2string(bvLength)
		+"\n i = "+ int2string(i)
		+"\n x = "+ x.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_rewrite", x);
  Expr res = d_theoryBitvector->newBVExtractExpr(t, i, i);
  res = d_theoryBitvector->newBoolExtractExpr(res, 0);
  return newRWTheorem(x, res, Assumptions::emptyAssump(), pf);
}


// |- BOOLEXTRACT(x,i) <=> *Boolean value of x[i]*
Theorem BitvectorTheoremProducer::bitExtractConstant(const Expr & x, int i)
{
  TRACE("bitvector", "bitExtractConstant(", x, ", "+ int2string(i) +" ) {");
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector constant.
    CHECK_SOUND(BVCONST == x.getKind(),
		"BitvectorTheoremProducer::bitExtractConstant:"
		"the bitvector must be a constant.");
    //check if 0<= i < bvLength of bitvector constant
    CHECK_SOUND(0 <= i && (unsigned)i < d_theoryBitvector->getBVConstSize(x),
		"BitvectorTheoremProducer::bitExtractConstant:"
		"illegal extraction attempted on the bitvector x = "
		+ x.toString()
		+ "\nat the position i = "
		+ int2string(i));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);

  //extract the actual expr_value string, bitextract it at i and check
  //if the value is 'false'. if so then return c[i] <==> false else
  //return c[i] <==> true.
  Expr output;
  if(!d_theoryBitvector->getBVConstValue(x, i))
    output = d_theoryBitvector->falseExpr();
  else
    output = d_theoryBitvector->trueExpr();

  Proof pf;
  if(withProof()) pf = newPf("bit_extract_constant", x, rat(i));
  Theorem result(newRWTheorem(bitExtract,output,Assumptions::emptyAssump(),pf));
  TRACE("bitvector", "bitExtractConstant => ", result, " }");
  return result;
}


// Input: x: a_0 \@ ... \@ a_n,
//        i: bitposition
// Output |- BOOLEXTRACT(a_0 \@ ... \@ a_n, i) <=> BOOLEXTRACT(a_j, k)
//        where j and k are determined by structure of CONCAT
Theorem BitvectorTheoremProducer::bitExtractConcatenation(const Expr & x,
							  int i)
{
  TRACE("bitvector", "bitExtractConcatenation(",
	x.toString(), ", "+ int2string(i) + " ) {");
  Type type = d_theoryBitvector->getBaseType(x);
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a concat.
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractConcatenation: "
		"term must be bitvector:\n x = "+x.toString());
    CHECK_SOUND(CONCAT == x.getOpKind() && x.arity() >= 2,
		"BitvectorTheoremProducer::bitExtractConcatenation: "
		"the bitvector must be a concat:\n x = " + x.toString());
  }

  //check if 0<= i < bvLength of bitvector constant
  int bvLength = d_theoryBitvector->BVSize(x);
  if(CHECK_PROOFS) {
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = "
		+ int2string(i)
		+ "\non bitvector x = " + x.toString()
		+ "\nwhose bvLength is = " +
		int2string(bvLength));
  }

  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);

  int numOfKids = x.arity();
  int lenOfKidsSeen = 0;
  Expr bitExtractKid;
  for(int count = numOfKids-1; count >= 0; --count) {
    int bvLengthOfKid = d_theoryBitvector->BVSize(x[count]);
    if(lenOfKidsSeen <= i && i < bvLengthOfKid + lenOfKidsSeen) {
      bitExtractKid =
	d_theoryBitvector->newBoolExtractExpr(x[count], i - lenOfKidsSeen);
      break;
    }
    lenOfKidsSeen += bvLengthOfKid;
  }
  DebugAssert(!bitExtractKid.isNull(),
	      "BitvectorTheoremProducer::bitExtractConcatenation: "
	      "something's broken...");

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_concatenation", x, rat(i));
  Theorem result(newRWTheorem(bitExtract, bitExtractKid, Assumptions::emptyAssump(), pf));
  TRACE("bitvector", "bitExtractConcatenation => ", result, " }");
  return result;
}


// |- BOOLEXTRACT(BVMULT(c,t),i) <=> BOOLEXTRACT(t',i) where t' is not a BVMULT
Theorem BitvectorTheoremProducer::bitExtractConstBVMult(const Expr& t, int i)
{
  TRACE("bitvector", "input to bitExtractConstBVMult(", t.toString(), ")");
  TRACE("bitvector", "input to bitExtractConstBVMult(", int2string(i), ")");

  Type type = t.getType();
  int bvLength = d_theoryBitvector->BVSize(t);
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractConstBVMult:"
		"the term must be a bitvector: " + t.toString());
    CHECK_SOUND(BVMULT == t.getOpKind() && 2 == t.arity(),
		"BitvectorTheoremProducer::bitExtractConstBVMult:"
		"the term must be a MULT of arity 2: " + t.toString());
    CHECK_SOUND(d_theoryBitvector->BVSize(t[0]) == bvLength &&
                d_theoryBitvector->BVSize(t[1]) == bvLength,
                "BitvectorTheoremProducer::bitExtractConstBVMult:"
                "Expected inputs of same length");
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = "
		+ int2string(i)
		+ "\non bitvector x = " + t.toString()
		+ "\nwhose bvLength is = " +
		int2string(bvLength));
    CHECK_SOUND(BVCONST == t[0].getKind(),
		"BitvectorTheoremProducer::bitExtractConstBVMult:"
		"illegal BVMULT expression" + t.toString());
  }

	  std::vector<Expr> k;
	  for(int j=0; j < bvLength; ++j)
		if (d_theoryBitvector->getBVConstValue(t[0], j)) {
		  Expr leftshiftTerm =
		d_theoryBitvector->newFixedConstWidthLeftShiftExpr(t[1], j);
		  k.push_back(leftshiftTerm);
		}

	  Expr mult;
	  //size of k will always be >= 0
	  switch(k.size()) {
	  case 0:
		//the vector k will remain empty if all bits in coeff are 0's
		mult = d_theoryBitvector->newBVZeroString(bvLength);
		break;
	  case 1:
		mult = k[0];
		break;
	  default:
		mult = d_theoryBitvector->newBVPlusExpr(bvLength, k);
		break;
	  }
  Expr output = d_theoryBitvector->newBoolExtractExpr(mult, i);

  // bool-extract of the bitvector term
  const Expr bitExtract =
    d_theoryBitvector->newBoolExtractExpr(t, i);

  Proof pf;
  if(withProof()) pf = newPf("bit_extract_const_bvmult", t, rat(i));
  const Theorem result = newRWTheorem(bitExtract,output,Assumptions::emptyAssump(),pf);
  TRACE("bitvector",
	"output of bitExtract_const_bvmult(", result, ")");
  return result;
}

// |- BOOLEXTRACT(t,i) <=> BOOLEXTRACT(t',i) where t' is not BVMULT
Theorem BitvectorTheoremProducer::bitExtractBVMult(const Expr& t, int i)
{
  TRACE("bitvector", "input to bitExtractBVMult(", t.toString(), ")");
  TRACE("bitvector", "input to bitExtractBVMult(", int2string(i), ")");

  Type type = t.getType();
  int bvLength= d_theoryBitvector->BVSize(t);
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractBVMult:"
		"the term must be a bitvector" + t.toString());
    CHECK_SOUND(BVMULT == t.getOpKind() && 2 == t.arity(),
		"BitvectorTheoremProducer::bitExtractBVMult:"
		"the term must be a bitvector" + t.toString());
    CHECK_SOUND(d_theoryBitvector->BVSize(t[0]) == bvLength &&
                d_theoryBitvector->BVSize(t[1]) == bvLength,
                "BitvectorTheoremProducer::bitExtractConstBVMult:"
                "Expected inputs of same length");
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = "
		+ int2string(i)
		+ "\non bitvector t = " + t.toString()
		+ "\nwhose Length is = " +
		int2string(bvLength));
    CHECK_SOUND(BVCONST != t[0].getOpKind(),
		"BitvectorTheoremProducer::bitExtractBVMult:"
		"illegal BVMULT expression" + t.toString());
  }
  Expr trueExpression = d_theoryBitvector->trueExpr();
  std::vector<Expr> k;
  for(int j=bvLength-1; j >= 0; j--) {
    Expr ext = d_theoryBitvector->newBVExtractExpr(t[0],j,j);
    Expr cond = ext.eqExpr(d_theoryBitvector->newBVOneString(1));
    Expr leftshiftTerm = d_theoryBitvector->newFixedConstWidthLeftShiftExpr(t[1], j);
    Expr zeroString = d_theoryBitvector->newBVZeroString(bvLength);
    Expr iteTerm = cond.iteExpr(leftshiftTerm, zeroString);
    k.push_back(iteTerm);
  }

  if(CHECK_PROOFS)
    CHECK_SOUND(k.size() > 0,
		"BitvectorTheoremProducer::bitExtractBVMult:"
		"size of output vector must be > 0");
  Expr mult;
  if (k.size() > 1)
    mult = d_theoryBitvector->newBVPlusExpr(bvLength, k);
  else
    mult = k[0];
  Expr output = d_theoryBitvector->newBoolExtractExpr(mult, i);

  // bool-extract of the bitvector term
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(t, i);

  Proof pf;
  if(withProof()) pf = newPf("bit_extract_bvmult", t, rat(i));
  const Theorem result = newRWTheorem(bitExtract,output,Assumptions::emptyAssump(),pf);
  TRACE("bitvector","output of bitExtract_bvmult(", result, ")");
  return result;
}


// Input x: a[hi:low]
//       i: bitposition
// Output: |- BOOLEXTRACT(a[hi:low], i) <=> BOOLEXTRACT(a, i+low)
Theorem BitvectorTheoremProducer::bitExtractExtraction(const Expr & x, int i)
{
  TRACE("bitvector", "input to bitExtractExtraction(", x.toString(), ")");
  TRACE("bitvector", "input to bitExtractExtraction(", int2string(i), ")");

  Type type = x.getType();
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a concat.
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtract-Extraction:"
		"term must be bitvector.");
    CHECK_SOUND(EXTRACT == x.getOpKind() && 1 == x.arity(),
		"BitvectorTheoremProducer::bitExtract-Extraction:"
		"the bitvector must be an extract." + x.toString());
    //check if 0<= i < bvLength of bitvector constant
    int bvLength= d_theoryBitvector->BVSize(type.getExpr());
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = "
		+ int2string(i)
		+ "\non bitvector t = " + x.toString()
		+ "\nwhose Length is = " +
		int2string(bvLength));
    int extractLeft = d_theoryBitvector->getExtractHi(x);
    int extractRight = d_theoryBitvector->getExtractLow(x);
    CHECK_SOUND(extractLeft >= extractRight && extractLeft >= 0,
		"BitvectorTheoremProducer::bitExtract-Extraction:"
		"illegal boolean extraction was attempted." + int2string(i) +
		int2string(extractLeft) + int2string(extractRight));
    CHECK_SOUND(0 <= i && i < extractLeft-extractRight+1,
    		"BitvectorTheoremProducer::bitExtract-Extraction:"
		"illegal boolean extraction was attempted." + int2string(i) +
		int2string(extractLeft) + int2string(extractRight));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);
  const Expr bitExtractExtraction =
    d_theoryBitvector->newBoolExtractExpr(x[0], i +
					  d_theoryBitvector->getExtractLow(x));

  Proof pf;
  if(withProof()) pf = newPf("bit_extract_extraction", x, rat(i));
  Theorem result(newRWTheorem(bitExtract, bitExtractExtraction, Assumptions::emptyAssump(), pf));
  TRACE("bitvector",
	"output of bitExtractExtraction(", result, ")");
  return result;
}

Theorem
BitvectorTheoremProducer::
  bitExtractBVPlus(const std::vector<Theorem>& t1BitExtractThms,
                   const std::vector<Theorem>& t2BitExtractThms,
                   const Expr& bvPlusTerm, int bitPos)
{
  TRACE("bitvector","input to bitExtractBVPlus(", bvPlusTerm.toString(), ")");
  TRACE("bitvector","input to bitExtractBVPlus(", int2string(bitPos), ")");

  if(CHECK_PROOFS) {
    CHECK_SOUND(BVPLUS == bvPlusTerm.getOpKind() && 2 == bvPlusTerm.arity(), "BitvectorTheoremProducer::bitExtractBVPlus: illegal bitvector fed to the function." + bvPlusTerm.toString());
    CHECK_SOUND(d_theoryBitvector->getBVPlusParam(bvPlusTerm) >= 0,	"BitvectorTheoremProducer::bitExtractBVPlus: illegal bitvector fed to the function." + bvPlusTerm.toString());
    CHECK_SOUND(bitPos+1 == (int)t1BitExtractThms.size() &&	bitPos+1 == (int)t2BitExtractThms.size(), "BitvectorTheoremProducer::bitExtractBVPlus: illegal bitvector fed to the function." + int2string(bitPos));
    const Expr& t1 = bvPlusTerm[0];
    const Expr& t2 = bvPlusTerm[1];
    std::vector<Theorem>::const_iterator i = t1BitExtractThms.begin();
    std::vector<Theorem>::const_iterator iend = t1BitExtractThms.end();
    std::vector<Theorem>::const_iterator j = t2BitExtractThms.begin();
    for(; i !=iend; ++i, ++j) {
      const Expr& t1Expr = i->getLHS();
      const Expr& t2Expr = j->getLHS();
      CHECK_SOUND(t1Expr[0] == t1 && t2Expr[0] == t2, "BitvectorTheoremProducer::bitExtractBVPlus: illegal bitvector fed to the function." + t1Expr.toString() + " ==\n" + t1.toString() + "\n" + t2.toString() + " == \n" + t2Expr.toString());
    }
  }
  const Expr lhs = d_theoryBitvector->newBoolExtractExpr(bvPlusTerm, bitPos);
  Expr rhs;
  const Expr& t1_iBit = (t1BitExtractThms[bitPos]).getRHS();
  const Expr& t2_iBit = (t2BitExtractThms[bitPos]).getRHS();
  if(0 != bitPos) {
    const Expr carry_iBit = computeCarry(t1BitExtractThms, t2BitExtractThms, bitPos);
    //constructing an XOR of 3 exprs using equivalences.  Note that (x
    //\xor y \xor z) is the same as (x \iff y \iff z). but remember, x
    //\xor y is not the same as x \iff y, but is equal instead to x
    //\neg\iff y
    rhs = t1_iBit.iffExpr(t2_iBit).iffExpr(carry_iBit);
    //cout << "the addition output is : " << rhs.toString() << "\n";
    //TRACE("bitvector",
    //  "output of bitExtractBVPlus(", carry_iBit.toString(), ")");
  } else
    //bitblasting the 0th bit. construct NOT(t1_iBit <=> t2_iBit)
    rhs = !(t1_iBit.iffExpr(t2_iBit));

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_BVPlus_rule",bvPlusTerm,rat(bitPos));
  Theorem result = newRWTheorem(lhs, rhs, Assumptions::emptyAssump(), pf);
  TRACE("bitvector","output of bitExtractBVPlus(", result, ")");
  return result;
}

Expr
BitvectorTheoremProducer::computeCarry(const std::vector<Theorem>& t1BitExtractThms,
	                                   const std::vector<Theorem>& t2BitExtractThms,
	                                   int i){
  vector<Expr> carry;
  int bitPos = i;
  DebugAssert(bitPos >= 0,
	      "computeCarry: negative bitExtract_Pos is illegal");
  if(0 == bitPos) {
    const Expr& t1Thm = t1BitExtractThms[bitPos].getRHS();
    const Expr& t2Thm = t2BitExtractThms[bitPos].getRHS();
    carry.push_back(t1Thm.andExpr(t2Thm));
  }
  else {
    const Expr& t1Thm = t1BitExtractThms[bitPos-1].getRHS();
    const Expr& t2Thm = t2BitExtractThms[bitPos-1].getRHS();
    const Expr iMinusOneTerm = t1Thm.andExpr(t2Thm);
    carry.push_back(iMinusOneTerm);

    const Expr iMinusOneCarry =
      computeCarry(t1BitExtractThms,t2BitExtractThms,bitPos-1);
    const Expr secondTerm = t1Thm.andExpr(iMinusOneCarry);
    carry.push_back(secondTerm);

    const Expr thirdTerm  = t2Thm.andExpr(iMinusOneCarry);

    carry.push_back(thirdTerm);
  }
  return orExpr(carry);
}

Theorem
BitvectorTheoremProducer::
bitExtractBVPlusPreComputed(const Theorem& t1_i,
			    const Theorem& t2_i,
			    const Expr& bvPlusTerm,
			    int bitPos,
			    int precomputedFlag)
{
  DebugAssert(0 != precomputedFlag,
	      "precomputedFlag cannot be 0");
  TRACE("bitvector","input to bitExtractBVPlus(", bvPlusTerm.toString(), ")");
  TRACE("bitvector","input to bitExtractBVPlus(", int2string(bitPos), ")");

  if(CHECK_PROOFS) {
    CHECK_SOUND(BVPLUS == bvPlusTerm.getOpKind() && 2 == bvPlusTerm.arity(),
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal bitvector fed to the function." +
		bvPlusTerm.toString());
    CHECK_SOUND(d_theoryBitvector->getBVPlusParam(bvPlusTerm) >= 0,
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal bitvector fed to the function." +
		bvPlusTerm.toString());
    const Expr& t1 = bvPlusTerm[0];
    const Expr& t2 = bvPlusTerm[1];
    CHECK_SOUND(t1_i.getLHS()[0] == t1 &&
		t2_i.getLHS()[0] == t2,
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal theorems fed to the function. Theorem1 = " +
		t1_i.toString() + "\nTheorem2 = " + t2_i.toString());
    CHECK_SOUND(t1_i.getLHS().getOpKind() == BOOLEXTRACT &&
		t2_i.getLHS().getOpKind() == BOOLEXTRACT,
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal theorems fed to the function. Theorem1 = " +
		t1_i.toString() + "\nTheorem2 = " + t2_i.toString());
    CHECK_SOUND(d_theoryBitvector->getBoolExtractIndex(t1_i.getLHS()) == bitPos &&
		d_theoryBitvector->getBoolExtractIndex(t2_i.getLHS()) == bitPos,
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal theorems fed to the function. Theorem1 = " +
		t1_i.toString() + "\nTheorem2 = " + t2_i.toString());
  }
  const Expr lhs =
    d_theoryBitvector->newBoolExtractExpr(bvPlusTerm, bitPos);
  Expr rhs;
  const Expr& t1_iBit = t1_i.getRHS();
  const Expr& t2_iBit = t2_i.getRHS();

  const Expr carry_iBit = computeCarryPreComputed(t1_i, t2_i, bitPos, precomputedFlag);

  if(0 != bitPos) {
    //constructing an XOR of 3 exprs using equivalences.  Note that (x
    //\xor y \xor z) is the same as (x \iff y \iff z). but remember, x
    //\xor y is not the same as x \iff y, but is equal instead to x
    //\neg\iff y
    rhs = t1_iBit.iffExpr(t2_iBit).iffExpr(carry_iBit);
    //cout << "the addition output is : " << rhs.toString() << "\n";
  } else
    //bitblasting the 0th bit. construct NOT(t1_iBit <=> t2_iBit)
    rhs = !(t1_iBit.iffExpr(t2_iBit));

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_BVPlus_precomputed_rule",bvPlusTerm,rat(bitPos));
  Theorem result = newRWTheorem(lhs, rhs, Assumptions::emptyAssump(), pf);
  TRACE("bitvector","output of bitExtractBVPlus(", result, ")");
  return result;
}

//! compute carryout of the current bits and cache them, and return
//carryin of the current bits
Expr
BitvectorTheoremProducer::
computeCarryPreComputed(const Theorem& t1_i,
			const Theorem& t2_i,
			int bitPos, int preComputed){
  DebugAssert(1 == preComputed ||
	      2 == preComputed,
	      "cannot happen");
  Expr carryout;
  Expr carryin;
  DebugAssert(bitPos >= 0,
	      "computeCarry: negative bitExtract_Pos is illegal");

  const Expr& t1Thm = t1_i.getRHS();
  const Expr& t2Thm = t2_i.getRHS();
  Expr x = t1Thm.andExpr(t2Thm);
  const Expr& t1 = t1_i.getLHS()[0];
  const Expr& t2 = t2_i.getLHS()[0];
  Expr t1Andt2 = t1.andExpr(t2);
  Expr index = t1Andt2.andExpr(rat(bitPos));

  if(0 == bitPos) {
    if(1 == preComputed)
      d_theoryBitvector->d_bvPlusCarryCacheLeftBV.insert(index,x);
    else
      d_theoryBitvector->d_bvPlusCarryCacheRightBV.insert(index,x);
    carryout = x;
    //carry.push_back(x);
  }
  else {
    if(1 == preComputed) {
      Expr indexMinusOne = t1Andt2.andExpr(rat(bitPos-1));
      if(d_theoryBitvector->d_bvPlusCarryCacheLeftBV.find(indexMinusOne) ==
	 d_theoryBitvector->d_bvPlusCarryCacheLeftBV.end())
	DebugAssert(false,
		    "this should not happen");
      carryin =
	(d_theoryBitvector->d_bvPlusCarryCacheLeftBV).find(indexMinusOne)->second;
      Expr secondTerm = t1Thm.andExpr(carryin);
      Expr thirdTerm = t2Thm.andExpr(carryin);

      carryout = (x.orExpr(secondTerm)).orExpr(thirdTerm);
      d_theoryBitvector->d_bvPlusCarryCacheLeftBV.insert(index,carryout);
    }
    else {
      Expr indexMinusOne = t1Andt2.andExpr(rat(bitPos-1));
      if(d_theoryBitvector->d_bvPlusCarryCacheRightBV.find(indexMinusOne) ==
	 d_theoryBitvector->d_bvPlusCarryCacheRightBV.end())
	DebugAssert(false,
		    "this should not happen");
      carryin =
	(d_theoryBitvector->d_bvPlusCarryCacheRightBV).find(indexMinusOne)->second;
      //(*d_bvPlusCarryCacheRightBV.find(indexMinusOne)).second;
      Expr secondTerm = t1Thm.andExpr(carryin);
      Expr thirdTerm = t2Thm.andExpr(carryin);

      carryout = (x.orExpr(secondTerm)).orExpr(thirdTerm);
      d_theoryBitvector->d_bvPlusCarryCacheRightBV.insert(index,carryout);
    }
  }
  //cout << "the carry for" << index << " is : " << carryout << "\n";
  return carryin;
}

Theorem
BitvectorTheoremProducer::
zeroPaddingRule(const Expr& e, int i) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR == e.getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::zeroPaddingRule:"
		"Wrong Input: Input must be a bitvector. But the input is: " +
		e.toString());
  }

  int bvLength =
    d_theoryBitvector->BVSize(d_theoryBitvector->getBaseType(e).getExpr());

  if(CHECK_PROOFS) {
    CHECK_SOUND(0 <= i &&  i >= bvLength,
		"BitvectorTheoremProducer::zeroPaddingRule:"
		"bitPosition of extraction must be greater than bvLength" +
		int2string(i) + "bvLength:" + int2string(bvLength));
  }
  const Expr boolExtractExpr = d_theoryBitvector->newBoolExtractExpr(e, i);

  Proof pf;
  if(withProof())
    pf = newPf("zeropadding_rule", e, rat(i));
  return newRWTheorem(boolExtractExpr, d_theoryBitvector->falseExpr(), Assumptions::emptyAssump(), pf);
}

Theorem
BitvectorTheoremProducer::
bvPlusAssociativityRule(const Expr& bvPlusTerm)
{
  TRACE("bitvector",
	"input to bvPlusAssociativityRule(", bvPlusTerm.toString(), ")");

  Type type = bvPlusTerm.getType();
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bvPlusAssociativityRule:"
		"term must be BITVECTOR type.");
    CHECK_SOUND(BVPLUS == bvPlusTerm.getOpKind(),
		"BitvectorTheoremProducer::bvPlusAssociativityRule:"
		"term must have the kind BVPLUS.");
    CHECK_SOUND(2 < bvPlusTerm.arity(),
		"BitvectorTheoremProducer::bvPlusAssociativityRule:"
		"term must have arity() greater than 2 for associativity.");
  }
  std::vector<Expr> BVPlusTerms0;
  std::vector<Expr>::const_iterator j = (bvPlusTerm.getKids()).begin();
  std::vector<Expr>::const_iterator jend = (bvPlusTerm.getKids()).end();
  //skip the first kid
  j++;
  BVPlusTerms0.insert(BVPlusTerms0.end(), j, jend);
  int bvLength = d_theoryBitvector->BVSize(bvPlusTerm);
  const Expr bvplus0 = d_theoryBitvector->newBVPlusExpr(bvLength,
							BVPlusTerms0);

  std::vector<Expr> BVPlusTerms1;
  BVPlusTerms1.push_back(*((bvPlusTerm.getKids()).begin()));
  BVPlusTerms1.push_back(bvplus0);
  const Expr bvplusOutput = d_theoryBitvector->newBVPlusExpr(bvLength,
							     BVPlusTerms1);

  Proof pf;
  if(withProof()) pf = newPf("bv_plus_associativityrule", bvPlusTerm);
  const Theorem result(newRWTheorem(bvPlusTerm, bvplusOutput, Assumptions::emptyAssump(), pf));
  TRACE("bitvector",
	"output of bvPlusAssociativityRule(", result, ")");
  return result;
}


Theorem BitvectorTheoremProducer::bitExtractNot(const Expr & x,
						int i) {
  TRACE("bitvector", "input to bitExtractNot(", x.toString(), ")");
  TRACE("bitvector", "input to bitExtractNot(", int2string(i), ")");

  Type type = x.getType();
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a concat.
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractNot:"
		"term must be bitvector.");
    CHECK_SOUND(BVNEG == x.getOpKind() && 1 == x.arity(),
		"BitvectorTheoremProducer::bitExtractNot:"
		"the bitvector must be an bitwise negation." + x.toString());
    //check if 0<= i < Length of bitvector constant
    int bvLength= d_theoryBitvector->BVSize(type.getExpr());
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = "
		+ int2string(i)
		+ "\non bitvector x = " + x.toString()
		+ "\nwhose Length is = " +
		int2string(bvLength));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);
  const Expr bitNegTerm = d_theoryBitvector->newBoolExtractExpr(x[0], i);

  Proof pf;
  if(withProof()) pf = newPf("bit_extract_bitwiseneg", x, rat(i));
  const Theorem result(newRWTheorem(bitExtract,!bitNegTerm,Assumptions::emptyAssump(),pf));
  TRACE("bitvector","output of bitExtractNot(", result, ")");
  return result;
}


Theorem BitvectorTheoremProducer::bitExtractBitwise(const Expr & x,
                                                    int i, int kind)
{
  TRACE("bitvector", "bitExtractBitwise(", x, ", "+ int2string(i)+") {");
  Type type = x.getType();
  if(CHECK_PROOFS) {
    CHECK_SOUND(kind == BVAND || kind == BVOR || kind == BVXOR,
		"BitvectorTheoremProducer::bitExtractBitwise: kind = "
		+d_theoryBitvector->getEM()->getKindName(kind));
    //check if the expr is indeed a bitvector term and a concat.
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractBitwise: "
		"term must be bitvector.\n x = "+x.toString()
		+" : "+type.toString());
    CHECK_SOUND(x.getOpKind() == kind && 2 <= x.arity(),
		"BitvectorTheoremProducer::bitExtractBitwise: "
		"kind does not match.\n x = "
		+ x.toString());
    //check if 0<= i < Length of bitvector constant
    int size = d_theoryBitvector->BVSize(x);
    CHECK_SOUND(0 <= i && i < size,
		"BitvectorTheoremProducer::bitExtractBitwise: "
		"illegal boolean extraction was attempted.\n i = "
		+ int2string(i) + "\n size = "+ int2string(size));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);
  vector<Expr> kids;
  for(Expr::iterator j=x.begin(), jend=x.end(); j!=jend; ++j) {
    kids.push_back(d_theoryBitvector->newBoolExtractExpr(*j, i));
  }

  int resKind = kind == BVAND ? AND :
    kind == BVOR ? OR : XOR;
  Expr rhs = Expr(resKind, kids);

  Proof pf;
  if(withProof()) pf = newPf("bit_extract_bitwise", x, rat(i));
  const Theorem result(newRWTheorem(bitExtract, rhs, Assumptions::emptyAssump(), pf));
  TRACE("bitvector", "bitExtractBitwise => ", result.toString(), " }");
  return result;
}


Theorem BitvectorTheoremProducer::bitExtractFixedLeftShift(const Expr & x,
							   int i) {
  TRACE("bitvector", "input to bitExtractFixedleftshift(", x.toString(), ")");
  TRACE("bitvector", "input to bitExtractFixedleftshift(", int2string(i), ")");

  Type type = x.getType();
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a left shift.
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractFixedleftshift:"
		"term must be bitvector.");
    CHECK_SOUND((x.getOpKind() == LEFTSHIFT ||
                x.getOpKind() == CONST_WIDTH_LEFTSHIFT) && 1 == x.arity(),
		"BitvectorTheoremProducer::bitExtractFixedleftshift:"
		"the bitvector must be a bitwise LEFTSHIFT." +
		x.toString());
    CHECK_SOUND(d_theoryBitvector->getFixedLeftShiftParam(x) >= 0,
		"BitvectorTheoremProducer::bitExtractFixedleftshift:"
		"the bitvector must be a bitwise LEFTSHIFT." +
		x.toString());
    //check if 0<= i < bvLength of bitvector constant
    int bvLength= d_theoryBitvector->BVSize(type.getExpr());
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = "
		+ int2string(i)
		+ "\non bitvector x = " + x.toString()
		+ "\nwhose bvLength is = " +
		int2string(bvLength));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);
  int shiftLength = d_theoryBitvector->getFixedLeftShiftParam(x);
  Expr output;
  if(0 <= i && i < shiftLength)
    output = d_theoryBitvector->falseExpr();
  else
    output =
      d_theoryBitvector->newBoolExtractExpr(x[0], i-shiftLength);

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_bitwisefixedleftshift", x,rat(i));
  const Theorem result = newRWTheorem(bitExtract, output, Assumptions::emptyAssump(), pf);
  TRACE("bitvector",
	"output of bitExtractFixedleftshift(", result, ")");
  return result;
}

Theorem BitvectorTheoremProducer::bitExtractFixedRightShift(const Expr & x,
							    int i) {
  TRACE("bitvector", "input to bitExtractFixedRightShift(", x.toString(), ")");
  TRACE("bitvector", "input to bitExtractFixedRightShift(", int2string(i), ")");

  Type type = x.getType();
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a concat.
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractFixedRightShift:"
		"term must be bitvector.");
    CHECK_SOUND(RIGHTSHIFT == x.getOpKind() && 1 == x.arity(),
		"BitvectorTheoremProducer::bitExtractFixedRightShift:"
		"the bitvector must be an bitwise RIGHTSHIFT." +
		x.toString());
    CHECK_SOUND(d_theoryBitvector->getFixedRightShiftParam(x) >= 0,
		"BitvectorTheoremProducer::bitExtractFixedRightShift:"
		"the bitvector must be an bitwise RIGHTSHIFT." +
		x.toString());
  }
  //check if 0<= i < bvLength of bitvector constant
  int bvLength = d_theoryBitvector->BVSize(x);
  if(CHECK_PROOFS)
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = "
		+ int2string(i)
		+ "\non bitvector t = " + x.toString()
		+ "\nwhose Length is = " +
		int2string(bvLength));

  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);
  int shiftLength = d_theoryBitvector->getFixedRightShiftParam(x);
  Expr output;
  if(bvLength > i && i > bvLength-shiftLength-1)
    output = d_theoryBitvector->falseExpr();
  else
    output =
      d_theoryBitvector->newBoolExtractExpr(x[0], i);

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_bitwiseFixedRightShift", x,rat(i));
  const Theorem result = newRWTheorem(bitExtract, output, Assumptions::emptyAssump(), pf);
  TRACE("bitvector",
	"output of bitExtractFixedRightShift(", result, ")");
  return result;
}

// BOOLEXTRACT(bvshl(t,s),i) <=> ((s = 0) AND BOOLEXTRACT(t,i)) OR
//                               ((s = 1) AND BOOLEXTRACT(t,i-1)) OR ...
//                               ((s = i) AND BOOLEXTRACT(t,0))
Theorem BitvectorTheoremProducer::bitExtractBVSHL(const Expr & x, int i)
{
  Type type = x.getType();
  int bvLength= d_theoryBitvector->BVSize(x);
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a left shift.
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractBVSHL:"
		"term must be bitvector.");
    CHECK_SOUND(x.getOpKind() == BVSHL && 2 == x.arity(),
		"BitvectorTheoremProducer::bitExtractBVSHL:"
		"the bitvector must be a BVSHL." +
		x.toString());
    //check if 0<= i < bvLength of bitvector constant
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractBVSHL:"
		"illegal boolean extraction was attempted at position i = "
		+ int2string(i)
		+ "\non bitvector x = " + x.toString()
		+ "\nwhose bvLength is = " +
		int2string(bvLength));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);

  const Expr& term = x[0];
  const Expr& shift = x[1];

  vector<Expr> kids;

  for (int j = 0; j <= i; ++j) {
    Expr eq = shift.eqExpr(d_theoryBitvector->newBVConstExpr(j, bvLength));
    Expr ext = d_theoryBitvector->newBoolExtractExpr(term, i-j);
    kids.push_back(eq && ext);
  }

  Expr output;
  if (kids.size() == 1) {
    output = kids[0];
  }
  else {
    output = Expr(OR, kids);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_bvshl", x, rat(i));
  return newRWTheorem(bitExtract, output, Assumptions::emptyAssump(), pf);
}


// BOOLEXTRACT(bvlshr(t,s),i) <=> ((s = 0) AND BOOLEXTRACT(t,i)) OR
//                                ((s = 1) AND BOOLEXTRACT(t,i+1)) OR ...
//                                ((s = n-1-i) AND BOOLEXTRACT(t,n-1))
Theorem BitvectorTheoremProducer::bitExtractBVLSHR(const Expr & x, int i)
{
  Type type = x.getType();
  int bvLength= d_theoryBitvector->BVSize(x);
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a left shift.
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractBVSHL:"
		"term must be bitvector.");
    CHECK_SOUND(x.getOpKind() == BVLSHR && 2 == x.arity(),
		"BitvectorTheoremProducer::bitExtractBVSHL:"
		"the bitvector must be a BVSHL." +
		x.toString());
    //check if 0<= i < bvLength of bitvector constant
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractBVSHL:"
		"illegal boolean extraction was attempted at position i = "
		+ int2string(i)
		+ "\non bitvector x = " + x.toString()
		+ "\nwhose bvLength is = " +
		int2string(bvLength));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);

  const Expr& term = x[0];
  const Expr& shift = x[1];

  vector<Expr> kids;

  for (int j = 0; j <= bvLength-1-i; ++j) {
    Expr eq = shift.eqExpr(d_theoryBitvector->newBVConstExpr(j, bvLength));
    Expr ext = d_theoryBitvector->newBoolExtractExpr(term, i+j);
    kids.push_back(eq && ext);
  }

  Expr output;
  if (kids.size() == 1) {
    output = kids[0];
  }
  else {
    output = Expr(OR, kids);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_bvlshr", x, rat(i));
  return newRWTheorem(bitExtract, output, Assumptions::emptyAssump(), pf);
}


// BOOLEXTRACT(bvashr(t,s),i) <=> ((s = 0) AND BOOLEXTRACT(t,i)) OR
//                                ((s = 1) AND BOOLEXTRACT(t,i+1)) OR ...
//                                ((s >= n-1-i) AND BOOLEXTRACT(t,n-1))
Theorem BitvectorTheoremProducer::bitExtractBVASHR(const Expr & x, int i)
{
  Type type = x.getType();
  int bvLength= d_theoryBitvector->BVSize(x);
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a left shift.
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractBVSHL:"
		"term must be bitvector.");
    CHECK_SOUND(x.getOpKind() == BVASHR && 2 == x.arity(),
		"BitvectorTheoremProducer::bitExtractBVSHL:"
		"the bitvector must be a BVSHL." +
		x.toString());
    //check if 0<= i < bvLength of bitvector constant
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractBVSHL:"
		"illegal boolean extraction was attempted at position i = "
		+ int2string(i)
		+ "\non bitvector x = " + x.toString()
		+ "\nwhose bvLength is = " +
		int2string(bvLength));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);

  const Expr& term = x[0];
  const Expr& shift = x[1];

  vector<Expr> kids;
  int j = 0;
  for (; j < bvLength-1-i; ++j) {
    Expr eq = shift.eqExpr(d_theoryBitvector->newBVConstExpr(j, bvLength));
    Expr ext = d_theoryBitvector->newBoolExtractExpr(term, i+j);
    kids.push_back(eq && ext);
  }
  Expr tmp = d_theoryBitvector->newBVConstExpr(j, bvLength);
  tmp = d_theoryBitvector->newBVLEExpr(tmp, shift);
  Expr ext = d_theoryBitvector->newBoolExtractExpr(term, bvLength-1);
  kids.push_back(tmp && ext);

  Expr output;
  if (kids.size() == 1) {
    output = kids[0];
  }
  else {
    output = Expr(OR, kids);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_bvashr", x, rat(i));
  return newRWTheorem(bitExtract, output, Assumptions::emptyAssump(), pf);
}


//! Check that all the kids of e are BVCONST
static bool constantKids(const Expr& e) {
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
    if(i->getOpKind() != BVCONST) return false;
  return true;
}


//! c1=c2 <=> TRUE/FALSE (equality of constant bitvectors)
Theorem BitvectorTheoremProducer::eqConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.isEq(),
		"BitvectorTheoremProducer::eqConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::eqConst: e = "+e.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("bitvector_eq_const", e);
  Expr res((e[0]==e[1])? d_theoryBitvector->trueExpr() :
                         d_theoryBitvector->falseExpr());
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


//! |- c1=c2 ==> |- AND(c1[i:i] = c2[i:i]) - expanding equalities into bits
Theorem BitvectorTheoremProducer::eqToBits(const Theorem& eq) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(eq.isRewrite(),
		"BitvectorTheoremProducer::eqToBits: eq = "+eq.toString());
  }

  const Expr& lhs = eq.getLHS();
  const Expr& rhs = eq.getRHS();

  if(CHECK_PROOFS) {
    CHECK_SOUND(d_theoryBitvector->getBaseType(lhs).getExpr().getOpKind() == BITVECTOR,
		"BitvectorTheoremProducer::eqToBits: eq = "+eq.toString());
    CHECK_SOUND(d_theoryBitvector->BVSize(lhs)
		== d_theoryBitvector->BVSize(rhs),
		"BitvectorTheoremProducer::eqToBits: eq = "+eq.toString());
  }

  int i=0, size=d_theoryBitvector->BVSize(lhs);
  vector<Expr> bitEqs;
  for(; i<size; i++) {
    Expr l = d_theoryBitvector->newBVExtractExpr(lhs, i, i);
    Expr r = d_theoryBitvector->newBVExtractExpr(rhs, i, i);
    bitEqs.push_back(l.eqExpr(r));
  }
  Expr res = andExpr(bitEqs);
  Proof pf;
  if(withProof())
    pf = newPf("eq_to_bits", eq.getExpr(), eq.getProof());
  return newTheorem(res, eq.getAssumptionsRef(), pf);
}


//! t<<n = c \@ 0bin00...00, takes e == (t<<n)
Theorem BitvectorTheoremProducer::leftShiftToConcat(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == LEFTSHIFT && e.arity() == 1,
		"BitvectorTheoremProducer::leftShiftConst: e = "+e.toString());
    CHECK_SOUND(d_theoryBitvector->getFixedLeftShiftParam(e) >= 0,
		"BitvectorTheoremProducer::leftShiftConst: e = "+e.toString());
  }
  const Expr& e0 = e[0];
  Expr res(e0);
  int shiftSize=d_theoryBitvector->getFixedLeftShiftParam(e);

  if (shiftSize != 0) {
    Expr padding = d_theoryBitvector->newBVConstExpr(Rational(0), shiftSize);
    res = d_theoryBitvector->newConcatExpr(e0, padding);
  }

  Proof pf;
  if(withProof())
    pf = newPf("leftshift_to_concat", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}

//! t<<n = c \@ 0bin00...00, takes e == (t<<n)
Theorem BitvectorTheoremProducer::constWidthLeftShiftToConcat(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == CONST_WIDTH_LEFTSHIFT && e.arity() == 1,
		"BitvectorTheoremProducer::leftShiftConst: e = "+e.toString());
    CHECK_SOUND(d_theoryBitvector->getFixedLeftShiftParam(e) >= 0,
		"BitvectorTheoremProducer::leftShiftConst: e = "+e.toString());
  }
  const Expr& e0 = e[0];
  Expr res;

  int shiftSize=d_theoryBitvector->getFixedLeftShiftParam(e);
  if (shiftSize == 0)
    res = e0;
  else {
    int bvLength = d_theoryBitvector->BVSize(e);
    if (shiftSize >= bvLength)
      res = d_theoryBitvector->newBVConstExpr(Rational(0), bvLength);
    else {
      Expr padding = d_theoryBitvector->newBVConstExpr(Rational(0), shiftSize);
      res = d_theoryBitvector->newBVExtractExpr(e0, bvLength-shiftSize-1, 0);
      res = d_theoryBitvector->newConcatExpr(res, padding);
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("constWidthLeftShift_to_concat", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


//! t>>m = 0bin00...00 \@ t[bvLength-1:m], takes e == (t>>n)
Theorem BitvectorTheoremProducer::rightShiftToConcat(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == RIGHTSHIFT && e.arity() == 1,
		"BitvectorTheoremProducer::rightShiftConst: e = "+e.toString());
    CHECK_SOUND(d_theoryBitvector->getFixedRightShiftParam(e) >= 0,
		"BitvectorTheoremProducer::rightShiftConst: e = "+e.toString());
  }
  int bvLength = d_theoryBitvector->BVSize(e[0]);

  int shiftSize=d_theoryBitvector->getFixedRightShiftParam(e);

  Expr output;
  if (shiftSize == 0) output = e[0];
  if (shiftSize >= bvLength)
    output = d_theoryBitvector->newBVZeroString(bvLength);
  else {
	  Expr padding = d_theoryBitvector->newBVZeroString(shiftSize);
	  Expr out0 = d_theoryBitvector->newBVExtractExpr(e[0],bvLength-1,shiftSize);
	  output = d_theoryBitvector->newConcatExpr(padding,out0);
  }

  DebugAssert(bvLength == d_theoryBitvector->BVSize(output),
	      "BitvectorTheoremProducer::rightShiftConst: e = "+e.toString());

  Proof pf;
  if(withProof())
    pf = newPf("rightshift_to_concat", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! BVSHL(t,c) = t[n-c,0] \@ 0bin00...00
Theorem BitvectorTheoremProducer::bvshlToConcat(const Expr& e) {
  if(CHECK_PROOFS) {
    // The second kid must be a constant expression
    CHECK_SOUND(e.getOpKind() == BVSHL && e.arity() == 2,
		"BitvectorTheoremProducer::bvshlToConcat: e = "+e.toString());
    CHECK_SOUND(e[1].getOpKind() == BVCONST,
		"BitvectorTheoremProducer::bvshlToConcat: e = "+e.toString());
  }
  const Expr& e0 = e[0];
  Expr res;

  Rational shiftSize=d_theoryBitvector->computeBVConst(e[1]);
  if (shiftSize == 0) res = e0;
  else {
    int bvLength = d_theoryBitvector->BVSize(e);
    if (shiftSize >= bvLength)
      res = d_theoryBitvector->newBVConstExpr(Rational(0), bvLength);
    else {
      Expr padding = d_theoryBitvector->newBVConstExpr(Rational(0), shiftSize.getInt());
      res = d_theoryBitvector->newBVExtractExpr(e0, bvLength-shiftSize.getInt()-1, 0);
      res = d_theoryBitvector->newConcatExpr(res, padding);
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("bvshl_to_concat");
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


// bvshl(t,s) = IF (s = 0) THEN t ELSE
//              IF (s = 1) then t[n-2:0] @ 0 Else
//              ...
//              ELSE 0
Theorem BitvectorTheoremProducer::bvshlSplit(const Expr &e)
{
  Type type = e.getType();
  int bvLength= d_theoryBitvector->BVSize(e);
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a left shift.
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractBVSHL:"
		"term must be bitvector.");
    CHECK_SOUND(e.getOpKind() == BVSHL && 2 == e.arity(),
		"BitvectorTheoremProducer::bitExtractBVSHL:"
		"the bitvector must be a BVSHL." +
		e.toString());
  }

  const Expr& term = e[0];
  const Expr& shift = e[1];

  Expr newExpr = d_theoryBitvector->newBVZeroString(bvLength);
  Expr eq, tmp;

  for (int i = bvLength-1; i > 0; --i) {
    eq = shift.eqExpr(d_theoryBitvector->newBVConstExpr(i, bvLength));
    tmp = d_theoryBitvector->newBVExtractExpr(term, bvLength-i-1, 0);
    tmp = d_theoryBitvector->newConcatExpr(tmp, d_theoryBitvector->newBVZeroString(i));
    newExpr = eq.iteExpr(tmp, newExpr);
  }

  eq = shift.eqExpr(d_theoryBitvector->newBVZeroString(bvLength));
  newExpr = eq.iteExpr(term, newExpr);

  Proof pf;
  if(withProof())
    pf = newPf("bvshl_split", e);
  return newRWTheorem(e, newExpr, Assumptions::emptyAssump(), pf);
}


//! BVLSHR(t,c) = 0bin00...00 \@ t[n-1,c]
Theorem BitvectorTheoremProducer::bvlshrToConcat(const Expr& e)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVLSHR && e.arity() == 2,
		"BitvectorTheoremProducer::bvlshrToConcat: e = "+e.toString());
    CHECK_SOUND(e[1].getOpKind() == BVCONST,
		"BitvectorTheoremProducer::bvlshrToConcat: e = "+e.toString());
  }
  int bvLength = d_theoryBitvector->BVSize(e);

  Rational shiftSize=d_theoryBitvector->computeBVConst(e[1]);

  Expr output;
  if (shiftSize == 0) output = e[0];
  else if(shiftSize >= bvLength)
    output = d_theoryBitvector->newBVZeroString(bvLength);
  else {
    Expr padding = d_theoryBitvector->newBVZeroString(shiftSize.getInt());
    Expr out0 = d_theoryBitvector->newBVExtractExpr(e[0],bvLength-1,shiftSize.getInt());
    output = d_theoryBitvector->newConcatExpr(padding,out0);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bvlshr_to_concat", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

Theorem BitvectorTheoremProducer::bvShiftZero(const Expr& e)
{
  if(CHECK_PROOFS) {
	int kind = e.getOpKind();
	CHECK_SOUND((kind == BVLSHR || kind == BVSHL || kind == BVASHR || kind == LEFTSHIFT || kind == CONST_WIDTH_LEFTSHIFT || kind == RIGHTSHIFT)
				 && e.arity() == 2, "BitvectorTheoremProducer::bvShiftZero: e = "+e.toString());
	CHECK_SOUND(e[0].getOpKind() == BVCONST && d_theoryBitvector->computeBVConst(e[0]) == 0, "BitvectorTheoremProducer::bvShiftZero: e = "+e.toString());
  }

  int bvLength = d_theoryBitvector->BVSize(e);
  Expr output = d_theoryBitvector->newBVZeroString(bvLength);

  Proof pf;
  if(withProof())
    pf = newPf("shift_zero", e);

  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! BVASHR(t,c) = SX(t[n-1,c], n-1)
Theorem BitvectorTheoremProducer::bvashrToConcat(const Expr& e)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVASHR && e.arity() == 2,
		"BitvectorTheoremProducer::bvlshrToConcat: e = "+e.toString());
    CHECK_SOUND(e[1].getOpKind() == BVCONST,
		"BitvectorTheoremProducer::bvlshrToConcat: e = "+e.toString());
  }
  int bvLength = d_theoryBitvector->BVSize(e);

  Rational shiftSize=d_theoryBitvector->computeBVConst(e[1]);

  Expr output;
  if (shiftSize > 0) {
	  if (shiftSize >= bvLength) shiftSize = bvLength - 1;
	  Expr out0 = d_theoryBitvector->newBVExtractExpr(e[0],bvLength-1,shiftSize.getInt());
	  output = d_theoryBitvector->newSXExpr(out0, bvLength);
  } else output = e[0];

  Proof pf;
  if(withProof())
    pf = newPf("bvashr_to_concat", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::rewriteXNOR(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == BVXNOR && e.arity() == 2,
                "Bad call to rewriteXNOR");
  }
  Expr res = d_theoryBitvector->newBVNegExpr(e[0]);
  res = d_theoryBitvector->newBVXorExpr(res, e[1]);
  Proof pf;
  if (withProof())
    pf = newPf("rewriteXNOR", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::rewriteNAND(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == BVNAND && e.arity() == 2,
                "Bad call to rewriteNAND");
  }
  Expr andExpr = d_theoryBitvector->newBVAndExpr(e[0], e[1]);
  Proof pf;
  if (withProof())
    pf = newPf("rewriteNAND", e);
  return newRWTheorem(e, d_theoryBitvector->newBVNegExpr(andExpr),
                      Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::rewriteNOR(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == BVNOR && e.arity() == 2,
                "Bad call to rewriteNOR");
  }
  Expr orExpr = d_theoryBitvector->newBVOrExpr(e[0], e[1]);
  Proof pf;
  if (withProof())
    pf = newPf("rewriteNOR", e);
  return newRWTheorem(e, d_theoryBitvector->newBVNegExpr(orExpr),
                      Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::rewriteBVCOMP(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == BVCOMP && e.arity() == 2,
                "Bad call to rewriteBVCOMP");
  }
  Expr res = e[0].eqExpr(e[1]).iteExpr(d_theoryBitvector->newBVOneString(1),
                                       d_theoryBitvector->newBVZeroString(1));
  Proof pf;
  if (withProof())
    pf = newPf("rewriteBVCOMP");
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::rewriteBVSub(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == BVSUB && e.arity() == 2 &&
                d_theoryBitvector->BVSize(e[0]) ==
                d_theoryBitvector->BVSize(e[1]),
                "Bad call to rewriteBVSub");
  }
  int bvsize = d_theoryBitvector->BVSize(e[0]);
  vector<Expr> k;
  k.push_back(e[0]);
  k.push_back(d_theoryBitvector->newBVUminusExpr(e[1]));
  Expr new_expr = d_theoryBitvector->newBVPlusExpr(bvsize, k);

  ExprMap<Rational> sumHashMap;
  Rational known_term;
  getPlusTerms(new_expr, known_term, sumHashMap);
  new_expr = buildPlusTerm(bvsize, known_term, sumHashMap);


  Proof pf;
  if (withProof())
    pf = newPf("rewriteBVSub", e);
  return newRWTheorem(e, new_expr, Assumptions::emptyAssump(), pf);
}


//! k*t = BVPLUS(n, <sum of shifts of t>) -- translation of k*t to BVPLUS
/*! If k = 2^m, return k*t = t\@0...0 */
Theorem BitvectorTheoremProducer::constMultToPlus(const Expr& e) {
  DebugAssert(false,
	      "BitvectorTheoremProducer::constMultToPlus: this rule does not work\n");
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVMULT && e.arity() == 2
		&& e[0].isRational() && e[0].getRational().isInteger(),
		"BitvectorTheoremProducer::constMultToPlus:\n e = "
		+e.toString());
  }

  Rational k = e[0].getRational();
  const Expr& t = e[1];
  int resLength = d_theoryBitvector->BVSize(e);
  string coeffBinary = abs(k).toString(2);
  int len = coeffBinary.length();
  Expr res; // The resulting expression
  if(k == 0) {
    // Construct n-bit vector of 0's
    vector<bool> bits;
    int len = resLength;
    for(int i=0; i<len; ++i) bits.push_back(false);
    res = d_theoryBitvector->newBVConstExpr(bits);
  } else {
    // Construct the vector of shifts, the kids of the resulting BVPLUS
    vector<Expr> kids;
    for(int i=0; i<len; ++i) {
      if(coeffBinary[i] == '1')
	kids.push_back(d_theoryBitvector->newFixedLeftShiftExpr(t, (len-1)-i));
    }
    res = (kids.size() == 1)? kids[0]
      : d_theoryBitvector->newBVPlusExpr(resLength, kids);
    // For negative k, compute (~res+1), the 2's complement
    if(k < 0) {
      vector<Expr> kk;
      kk.push_back(d_theoryBitvector->newBVNegExpr(res));
      kk.push_back(rat(1));
      res = d_theoryBitvector->newBVPlusExpr(resLength, kk);
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("const_mult_to_plus", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


Theorem
BitvectorTheoremProducer::bvplusZeroConcatRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind()==CONCAT && e.arity()==2,
		"BitvectorTheoremProducer::bvplusZeroConcatRule: e = "
		+e.toString());
    CHECK_SOUND(e[0].getKind()==BVCONST && e[1].getOpKind()==BVPLUS
		&& d_theoryBitvector->computeBVConst(e[0])==0,
		"BitvectorTheoremProducer::bvplusZeroConcatRule: e = "
		+e.toString());
  }

  int constSize = d_theoryBitvector->BVSize(e[0]);
  const Expr& bvplus = e[1];
  int bvplusSize = d_theoryBitvector->getBVPlusParam(bvplus);

  // Check if we can apply the rewrite rule
  int maxKidSize(0);
  for(Expr::iterator i=bvplus.begin(), iend=bvplus.end(); i!=iend; ++i) {
    int size(d_theoryBitvector->BVSize(*i));
    // if kid is 0bin0 @ ..., then we can shorten its effective size
    if(i->getOpKind()==CONCAT && i->arity()>=2
       && (*i)[0].getKind()==BVCONST && d_theoryBitvector->computeBVConst((*i)[0])==0)
      size -= d_theoryBitvector->BVSize((*i)[0]);
    if(size > maxKidSize) maxKidSize = size;
  }
  int numKids = bvplus.arity();
  // Compute ceiling of log2(numKids)
  int log2 = 0;
  for(int i=1; i < numKids; i *=2, log2++);
  if(log2+maxKidSize > bvplusSize) {
    // Skip the rewrite, it's potentially unsound
    TRACE("bv 0@+", "bvplusZeroConcatRule(", e, "): skipped");
    return d_theoryBitvector->reflexivityRule(e);
  }

  Expr res(d_theoryBitvector->newBVPlusExpr(bvplusSize+constSize,
					    bvplus.getKids()));

  Proof pf;
  if(withProof())
    pf = newPf("bvplus_zero_concat", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}



//! c1[i:j] = c  (extraction from a constant bitvector)
Theorem BitvectorTheoremProducer::extractConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity() == 1,
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
  }

  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);
  const Expr& e0 = e[0];

  if(CHECK_PROOFS) {
    CHECK_SOUND(0 <= low && low <= hi,
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
    CHECK_SOUND((unsigned)hi < d_theoryBitvector->getBVConstSize(e0),
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
  }
  vector<bool> res;

  for(int bit=low; bit <= hi; bit++)
    res.push_back(d_theoryBitvector->getBVConstValue(e0, bit));

  Proof pf;
  if(withProof())
    pf = newPf("extract_const", e);
  return newRWTheorem(e, d_theoryBitvector->newBVConstExpr(res), Assumptions::emptyAssump(), pf);
}

// t[n-1:0] = t  for n-bit t
Theorem
BitvectorTheoremProducer::extractWhole(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity() == 1,
		"BitvectorTheoremProducer::extractWhole: e = "+e.toString());
  }

  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);
  const Expr& e0 = e[0];

  if(CHECK_PROOFS) {
    CHECK_SOUND(low ==0 && hi == d_theoryBitvector->BVSize(e0) - 1,
		"BitvectorTheoremProducer::extractWhole: e = "+e.toString()
		+"\n BVSize(e) = "+ int2string(d_theoryBitvector->BVSize(e0)));
  }
  Proof pf;
  if(withProof())
    pf = newPf("extract_whole", e);
  return newRWTheorem(e, e0, Assumptions::emptyAssump(), pf);
}


//! t[i:j][k:l] = t[k+j:l+j]  (eliminate double extraction)
Theorem
BitvectorTheoremProducer::extractExtract(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity() == 1,
		"BitvectorTheoremProducer::extractExtract: e = "+e.toString());
  }

  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);
  const Expr& e0 = e[0];

  if(CHECK_PROOFS) {
    // Check the bounds
    CHECK_SOUND(0 <= low && low <= hi,
		"BitvectorTheoremProducer::extractExtract: e = "+e.toString());
    // The base expression must also be EXTRACT
    CHECK_SOUND(e0.getOpKind() == EXTRACT && e0.arity() == 1,
		"BitvectorTheoremProducer::extractExtract: e0 = "
		+e0.toString());
  }

  int hi0 = d_theoryBitvector->getExtractHi(e0);
  int low0 = d_theoryBitvector->getExtractLow(e0);
  const Expr& e00 = e0[0];

  if(CHECK_PROOFS) {
    // The extractions must be within the correct bounds
    CHECK_SOUND((0 <= low) && (low <= hi) && (hi <= hi0-low0),
		"BitvectorTheoremProducer::extractExtract:\n"
		" [hi:low][hi0:low0] = ["+ int2string(hi0)+":"+ int2string(low0)
		+"]["+ int2string(hi) + ":" + int2string(low)
		+"]\n e = "+e.toString());
  }

  Expr res = d_theoryBitvector->newBVExtractExpr(e00, hi+low0, low+low0);

  Proof pf;
  if(withProof())
    pf = newPf("extract_extract", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


//! (t1 \@ t2)[i:j] = t1[...] \@ t2[...]  (push extraction through concat)
Theorem
BitvectorTheoremProducer::extractConcat(const Expr& e) {
  TRACE("bitvector rules", "extractConcat(", e, ") {");
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity() == 1,
		"BitvectorTheoremProducer::extractConcat: e = "+e.toString());
  }

  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);
  const Expr& e0 = e[0];

  if(CHECK_PROOFS) {
    // Check the bounds
    CHECK_SOUND(0 <= low && low <= hi,
		"BitvectorTheoremProducer::extractConcat: e = "+e.toString());
    CHECK_SOUND(hi < d_theoryBitvector->BVSize(e0),
		"BitvectorTheoremProducer::extractConcat: e = "+e.toString()
		+"\n BVSize(e0) = "+ int2string(d_theoryBitvector->BVSize(e0)));
    // The base expression  must be CONCAT
    CHECK_SOUND(e0.getOpKind() == CONCAT,
		"BitvectorTheoremProducer::extractConcat: e0 = "
		+e0.toString());
  }
  // Collect the relevant kids from concatenation
  vector<Expr> kids;
  int width(d_theoryBitvector->BVSize(e0));
  TRACE("bitvector rules", "extractConcat: width=", width, "");
  for(Expr::iterator i=e0.begin(), iend=e0.end(); i!=iend && width>low; ++i) {
    TRACE("bitvector rules", "extractConcat: *i=", *i, "");
    int w(d_theoryBitvector->BVSize(*i));
    int newWidth = width-w;
    int l(0), h(0);
    TRACE("bitvector rules", "extractConcat: w=", w, "");
    TRACE("bitvector rules", "extractConcat: newWidth=", newWidth, "");
    if(width > hi) { // Previous kids were outside of extract window
      if(hi >= newWidth) { // The first relevant kid
	h = hi-newWidth;
	l = (newWidth <= low)? low-newWidth : 0;
	TRACE("bitvector rules", "extractConcat[newWidth<=hi<width]: h=",
	      h, ", l="+ int2string(l));
	kids.push_back(d_theoryBitvector->newBVExtractExpr(*i, h, l));
      }
    } else if(width > low) {
      // High end of the current kid is in the extract window
      h = w-1;
      l = (newWidth <= low)? low-newWidth : 0;
      TRACE("bitvector rules", "extractConcat[low<width<=hi]: h=",
	    h, ", l="+ int2string(l));
      kids.push_back(d_theoryBitvector->newBVExtractExpr(*i, h, l));
    } // The remaining kids are outside of extract window, skip them
    width=newWidth;
    TRACE("bitvector rules", "extractConcat: width=", width, "");
  }
  Expr res = (kids.size()==1)? kids[0]
    : d_theoryBitvector->newConcatExpr(kids);
  Proof pf;
  if(withProof())
    pf = newPf("extract_concat", e);
  Theorem thm(newRWTheorem(e, res, Assumptions::emptyAssump(), pf));
  TRACE("bitvector rules", "extractConcat => ", thm.getExpr(), " }");
  return thm;
}


// (t1 op t2)[i:j] = t1[i:j] op t2[i:j] -- push extraction through
// bit-wise operator
Theorem
BitvectorTheoremProducer::extractBitwise(const Expr& e, int kind,
					 const string& pfName) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity() == 1,
		"BitvectorTheoremProducer::"+pfName+": e = "+e.toString());
    CHECK_SOUND(kind == BVAND || kind == BVOR ||
		kind == BVNEG || kind == BVXOR ||
		kind == BVXNOR,
		"BitvectorTheoremProducer::"+pfName+": kind = "
		+d_theoryBitvector->getEM()->getKindName(kind));
  }

  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);
  const Expr& e0 = e[0];

  if(CHECK_PROOFS) {
    // Check the bounds
    CHECK_SOUND(0 <= low && low <= hi,
		"BitvectorTheoremProducer::"+pfName+": e = "+e.toString());
    // The base expression must also be EXTRACT
    CHECK_SOUND(e0.getOpKind() == kind,
		"BitvectorTheoremProducer::"+pfName+": e0 = "
		+e0.toString());
  }

  vector<Expr> kids;
  for(Expr::iterator i=e0.begin(), iend=e0.end(); i!=iend; ++i) {
    kids.push_back(d_theoryBitvector->newBVExtractExpr(*i, hi, low));
  }
  Expr res = Expr(e0.getOp(), kids);
  Proof pf;
  if(withProof())
    pf = newPf(pfName, e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}

//! (t1 & t2)[i:j] = t1[i:j] & t2[i:j]  (push extraction through OR)
Theorem
BitvectorTheoremProducer::extractAnd(const Expr& e) {
  return extractBitwise(e, BVAND, "extract_and");
}


//! (t1 | t2)[i:j] = t1[i:j] | t2[i:j]  (push extraction through AND)
Theorem
BitvectorTheoremProducer::extractOr(const Expr& e) {
  return extractBitwise(e, BVOR, "extract_or");
}


//! (~t)[i:j] = ~(t[i:j]) (push extraction through NEG)
Theorem
BitvectorTheoremProducer::extractNeg(const Expr& e) {
  return extractBitwise(e, BVNEG, "extract_neg");
}

//! ite(c,t1,t2)[i:j] <=> ite(c,t1[i:j],t2[i:j])
Theorem
BitvectorTheoremProducer::iteExtractRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity()==1,
		"BitvectorTheoremProducer::iteExtractRule: "
		"input must be an bitvector EXTRACT expr:\n"+
		e.toString());
  }
  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);

  if(CHECK_PROOFS) {
    CHECK_SOUND(e[0].getKind() == ITE &&
		e[0].arity()==3 &&
		BITVECTOR == e[0].getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::iteExtractRule: "
		"input must be an bitvector EXTRACT expr over an ITE:\n" +
		e.toString());
    CHECK_SOUND(hi >= low && d_theoryBitvector->BVSize(e[0]) >= hi-low,
		"BitvectorTheoremProducer::iteExtractRule: "
		"i should be greater than j in e[i:j] = "
		+e.toString());
  }
  const Expr ite = e[0];
  Expr cond = ite[0];
  Expr e1 = d_theoryBitvector->newBVExtractExpr(ite[1],hi,low);
  Expr e2 = d_theoryBitvector->newBVExtractExpr(ite[2],hi,low);
  Expr output = Expr(CVC3::ITE,cond,e1,e2);

  Proof pf;
  if(withProof())
    pf = newPf("ite_extract_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! ~ite(c,t1,t2) <=> ite(c,~t1,~t2)
Theorem
BitvectorTheoremProducer::iteBVnegRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity()==1,
		"BitvectorTheoremProducer::itebvnegrule: "
		"input must be an bitvector EXTRACT expr:\n"+
		e.toString());
  }
  if(CHECK_PROOFS) {
    CHECK_SOUND(e[0].getKind() == ITE &&
		e[0].arity()==3 &&
		BITVECTOR == e[0].getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::itebvnegrule: "
		"input must be an bitvector EXTRACT expr over an ITE:\n" +
		e.toString());
  }
  const Expr ite = e[0];
  Expr cond = ite[0];
  Expr e1 = d_theoryBitvector->newBVNegExpr(ite[1]);
  Expr e2 = d_theoryBitvector->newBVNegExpr(ite[2]);
  Expr output = Expr(CVC3::ITE,cond,e1,e2);

  Proof pf;
  if(withProof())
    pf = newPf("ite_bvneg_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! ~c1 = c  (bit-wise negation of a constant bitvector)
Theorem BitvectorTheoremProducer::negConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1,
		"BitvectorTheoremProducer::negConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::negConst: e = "+e.toString());
  }
  const Expr& e0 = e[0];
  vector<bool> res;

  for(int bit=0, size=d_theoryBitvector->getBVConstSize(e0); bit<size; bit++)
    res.push_back(!d_theoryBitvector->getBVConstValue(e0, bit));

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_const", e);
  return newRWTheorem(e, d_theoryBitvector->newBVConstExpr(res), Assumptions::emptyAssump(), pf);
}


//! ~(t1\@...\@tn) = (~t1)\@...\@(~tn) -- push negation through concat
Theorem
BitvectorTheoremProducer::negConcat(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1,
		"BitvectorTheoremProducer::negConcat: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == CONCAT,
		"BitvectorTheoremProducer::negConcat: e = "+e.toString());
  }

  const Expr& e0 = e[0];

  vector<Expr> kids;
  for(Expr::iterator i=e0.begin(), iend=e0.end(); i!=iend; ++i)
    kids.push_back(d_theoryBitvector->newBVNegExpr(*i));

  Expr res = d_theoryBitvector->newConcatExpr(kids);

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_concat", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}

//! ~(~t) = t  -- eliminate double negation
Theorem
BitvectorTheoremProducer::negNeg(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1,
		"BitvectorTheoremProducer::negNeg: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVNEG && e[0].arity() == 1,
		"BitvectorTheoremProducer::negNeg: e = "+e.toString());
  }

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_neg", e);
  return newRWTheorem(e, e[0][0], Assumptions::emptyAssump(), pf);
}


//! ~t = -1*t + 1 -- eliminate negation
Theorem BitvectorTheoremProducer::negElim(const Expr& e)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1,
		"BitvectorTheoremProducer::negNeg: e = "+e.toString());
  }

  int bv_size =  d_theoryBitvector->BVSize(e[0]);
  Rational modulus = pow(Rational(bv_size), Rational(2));
  Expr minus_one = d_theoryBitvector->newBVConstExpr(modulus-1, bv_size);

  vector<Expr> bvplusTerms;
  bvplusTerms.push_back(minus_one);
  bvplusTerms.push_back(d_theoryBitvector->newBVMultExpr(bv_size, minus_one, e[0]));
  Expr res = d_theoryBitvector->newBVPlusExpr(bv_size, bvplusTerms);

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_elim", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


//! ~(t1 & t2) = ~t1 | ~t2  -- DeMorgan's Laws
Theorem
BitvectorTheoremProducer::negBVand(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1,
		"BitvectorTheoremProducer::negBVand: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVAND,
		"BitvectorTheoremProducer::negBVand: e = "+e.toString());
  }
  Expr output;
  std::vector<Expr> negated;
  for(Expr::iterator i = e[0].begin(),iend=e[0].end();i!=iend;++i)
    negated.push_back(d_theoryBitvector->newBVNegExpr(*i));
  output = d_theoryBitvector->newBVOrExpr(negated);

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_and", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! ~(t1 | t2) = ~t1 & ~t2  -- DeMorgan's Laws
Theorem
BitvectorTheoremProducer::negBVor(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1,
		"BitvectorTheoremProducer::negBVor: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVOR,
		"BitvectorTheoremProducer::negBVor: e = "+e.toString());
  }

  Expr output;
  std::vector<Expr> negated;
  for(Expr::iterator i = e[0].begin(),iend=e[0].end();i!=iend;++i)
    negated.push_back(d_theoryBitvector->newBVNegExpr(*i));
  output = d_theoryBitvector->newBVAndExpr(negated);

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_or", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! ~(t1 xor t2) = ~t1 xor t2
Theorem
BitvectorTheoremProducer::negBVxor(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1 && e[0].arity() > 0,
		"BitvectorTheoremProducer::negBVxor: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVXOR,
		"BitvectorTheoremProducer::negBVxor: e = "+e.toString());
  }

  Expr output;
  std::vector<Expr> children;
  Expr::iterator i = e[0].begin(), iend = e[0].end();
  children.push_back(d_theoryBitvector->newBVNegExpr(*i));
  ++i;
  for(; i!=iend; ++i)
    children.push_back(*i);
  output = d_theoryBitvector->newBVXorExpr(children);

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_xor", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! ~(t1 xnor t2) = t1 xor t2
Theorem
BitvectorTheoremProducer::negBVxnor(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1 && e[0].arity() > 0,
		"BitvectorTheoremProducer::negBVxor: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVXNOR,
		"BitvectorTheoremProducer::negBVxor: e = "+e.toString());
  }

  Expr t2 = e[0][1];
  if (e[0].arity() > 2) {
    std::vector<Expr> children;
    Expr::iterator i = e[0].begin(), iend = e[0].end();
    ++i;
    for(; i!=iend; ++i)
      children.push_back(*i);
    t2 = d_theoryBitvector->newBVXnorExpr(children);
  }
  Expr output = d_theoryBitvector->newBVXorExpr(e[0][0], t2);

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_xnor", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! c1 op c2 = c  -- bit-wise AND, OR, XOR of constant bitvectors
Theorem BitvectorTheoremProducer::bitwiseConst(const Expr& e,
					       const vector<int>& idxs,
					       int kind)
{
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == kind,
		"BitvectorTheoremProducer::bitwiseConst: e = "+e.toString());
    CHECK_SOUND(e.getOpKind() == BVAND ||
                e.getOpKind() == BVOR ||
                e.getOpKind() == BVXOR, "Expected AND, OR, or XOR");
    CHECK_SOUND(idxs.size() >= 2, "BitvectorTheoremProducer::bitwiseConst():\n e = "
                +e.toString());
    for(size_t i=0; i<idxs.size(); ++i) {
      CHECK_SOUND(idxs[i] < e.arity(),
		  "BitvectorTheoremProducer::bitwiseConst: idxs["
		  +int2string(i)+"]="+int2string(idxs[i])
		  +", e.arity() = "+int2string(e.arity())
		  +"\n e = "+e.toString());
      CHECK_SOUND(e[idxs[i]].getKind() == BVCONST,
		  "BitvectorTheoremProducer::bitwiseConst: e = "+e.toString());
    }
  }
  // Initialize 'bits' with all 1's or 0's, depending on kind
  vector<bool> bits;
  int size = d_theoryBitvector->BVSize(e);
  for(int bit=0; bit<size; bit++) {
    bits.push_back(kind == BVAND);
  }

  vector<Expr> kids(1); // Reserve the first element for the constant bitvector
  size_t ii(0); // The next index of idxs to match
  int idx(idxs[0]); // The index of the next constant (for efficiency)
  for(int i=0, iend=e.arity(); i<iend; ++i) {
    const Expr& ei = e[i];
    if(i == idx) {
      if(CHECK_PROOFS) {
	CHECK_SOUND(ei.getKind() == BVCONST,
		    "BitvectorTheoremProducer::bitwiseConst: e["
		    +int2string(i)+"] = "+ei.toString());
	CHECK_SOUND(d_theoryBitvector->getBVConstSize(ei) == (unsigned)size,
		    "BitvectorTheoremProducer::bitwiseConst: e["
		    +int2string(i)+"] = "+ei.toString());
      }
      // Incorporate the constant bitvector
      for(int bit=0; bit<size; bit++)
	bits[bit] =
          kind == BVAND ? (bits[bit] && d_theoryBitvector->getBVConstValue(ei, bit)) :
	  kind == BVOR ? (bits[bit] || d_theoryBitvector->getBVConstValue(ei, bit)) :
          bits[bit] != d_theoryBitvector->getBVConstValue(ei, bit);
      // Advance the index of idxs
      if (ii < idxs.size() - 1)
	idx = idxs[++ii];
      else
	idx = e.arity();
    }
    else // Not a constant, add to the list of kids
      kids.push_back(ei);
  }
  // Create the new constant bitvector and make it the first kid
  kids[0] = d_theoryBitvector->newBVConstExpr(bits);
  // Contruct the final expression.
  Expr res = (kids.size() == 1) ? kids[0] :
    kind == BVAND ? d_theoryBitvector->newBVAndExpr(kids) :
    kind == BVOR ? d_theoryBitvector->newBVOrExpr(kids) :
    d_theoryBitvector->newBVXorExpr(kids);

  Proof pf;
  if(withProof()) {
    // Construct a list of indices as a RAW_LIST Expr
    vector<Expr> indices;
    for(size_t i=0, iend=idxs.size(); i<iend; ++i)
      indices.push_back(rat(idxs[i]));
    pf = newPf("bitwise_const", e, Expr(RAW_LIST, indices));
  }
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


//! Lifts concatenation above bitwise operators.
Theorem BitvectorTheoremProducer::bitwiseConcat(const Expr& e, int kind)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == kind,
		"BitvectorTheoremProducer::bitwiseConcat: e = "+e.toString());
  }

  int arity = e.arity();
  int idx;
  for (idx = 0; idx < arity; ++idx) {
    if (e[idx].getOpKind() == CONCAT) break;
  }
  if (idx == arity)
    return d_theoryBitvector->reflexivityRule(e);

  const Expr& ei = e[idx];

  // Build the top-level concatenation
  vector<Expr> concatKids;
  // Current extraction window
  int hi=d_theoryBitvector->BVSize(e)-1;
  int low=hi-d_theoryBitvector->BVSize(ei[0])+1;

  for(int i=0, iend=ei.arity(); i<iend; ++i) {
    // Kids of the current BVAND / BVOR
    vector<Expr> kids;
    for(int j=0; j<arity; ++j) {
      if(j==idx)
	kids.push_back(ei[i]);
      else
	kids.push_back(d_theoryBitvector->newBVExtractExpr(e[j], hi, low));
    }
    concatKids.push_back(Expr(kind, kids));
    if(i+1<iend) {
      int newHi = low-1;
      low = low - d_theoryBitvector->BVSize(ei[i+1]);
      hi = newHi;
    }
  }
  Expr res = d_theoryBitvector->newConcatExpr(concatKids);
  Proof pf;
  if(withProof())
    pf = newPf("bitwise_concat", e, rat(idx));
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


//! Flatten bitwise operation
Theorem BitvectorTheoremProducer::bitwiseFlatten(const Expr& e, int kind)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == kind && e.arity()>=2,
		"BitvectorTheoremProducer::bitwiseFlatten: e = "+e.toString());
    CHECK_SOUND(e.getOpKind() == BVAND ||
                e.getOpKind() == BVOR ||
                e.getOpKind() == BVXOR, "Expected AND, OR, or XOR");
  }
  int bvLength = d_theoryBitvector->BVSize(e);

  // flatten the nested ops
  vector<Expr> flattenkids;
  for(Expr::iterator i = e.begin(),iend=e.end();i!=iend; ++i) {
    if(i->getOpKind() == kind)
      flattenkids.insert(flattenkids.end(),
			 i->getKids().begin(),i->getKids().end());
    else
      flattenkids.push_back(*i);
  }

  // drop duplicate subterms and detect conflicts like t, ~t
  Expr output;
  int flag;
  ExprMap<int> likeTerms;
  vector<Expr>::iterator j = flattenkids.begin();
  vector<Expr>::iterator jend = flattenkids.end();
  bool negate = false;

  for(; output.isNull() && j != flattenkids.end(); ++j) {
    Expr t = *j;
    if (kind == BVXOR && t.getOpKind() == BVNEG) {
      negate = !negate;
      t = t[0];
    }
    //check if *j is duplicated or its negation already occured
    flag = sameKidCheck(t, likeTerms);
    switch(flag) {
      case 0:
        //no duplicates
        break;
      case 1:
        //duplicate detected. ignore the duplicate for BVAND, BVOR
        if (kind == BVXOR) {
          // remove both for BVXOR
          likeTerms.erase(t);
        }
        break;
      case -1:
        //conflict detected
        if (kind == BVAND)
          output = d_theoryBitvector->newBVZeroString(bvLength);
        else if (kind == BVOR)
          output = d_theoryBitvector->newBVOneString(bvLength);
        else {
          DebugAssert(false, "Shouldn't be possible");
        }
        break;
      default:
        DebugAssert(false,
                    "control should not reach here");
        break;
    }
  }

  if (output.isNull()) {
    vector<Expr> outputkids;
    ExprMap<int>::iterator it = likeTerms.begin();
    for(; it != likeTerms.end(); ++it) {
      outputkids.push_back((*it).first);
    }
    if(CHECK_PROOFS) {
      CHECK_SOUND(kind == BVXOR || outputkids.size() > 0,
		  "TheoryBitvector:bitwiseFlatten: fatal error");
    }
    if (outputkids.size() == 0) {
      outputkids.push_back(d_theoryBitvector->newBVZeroString(bvLength));
    }
    if (negate) {
      outputkids[0] = d_theoryBitvector->newBVNegExpr(outputkids[0]);
    }
    if (outputkids.size() == 1) {
      output = outputkids[0];
    }
    else {
      output = Expr(kind, outputkids);
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("bitwise_flatten", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


// Rewrite bitwise operation with constant using concatenation,
// negation, and extraction
Theorem BitvectorTheoremProducer::bitwiseConstElim(const Expr& e,
                                                   int idx, int kind)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == kind,
		"BitvectorTheoremProducer::bitwiseConstElim: e = "+e.toString());
    CHECK_SOUND(e.getOpKind() == BVAND ||
                e.getOpKind() == BVOR ||
                e.getOpKind() == BVXOR, "Expected AND, OR, or XOR");
    CHECK_SOUND(idx < e.arity() && e.arity() > 1,
		"BitvectorTheoremProducer::bitwiseConstElim: e = "+e.toString()
		+"\n idx = "+int2string(idx)
		+"\n e.arity() = "+int2string(e.arity()));
    CHECK_SOUND(e[idx].getOpKind() == BVCONST,
		"BitvectorTheoremProducer::bitwiseConstElim: e["+int2string(idx)
		+"] = "+e[idx].toString());
  }

  int bvLength = d_theoryBitvector->BVSize(e);
  Expr output;
  vector<Expr> kids;
  for (int i = 0; i < e.arity(); ++i) {
    if (i == idx) continue;
    kids.push_back(e[i]);
  }
  if (kids.size() == 1) output = kids[0];
  else output = Expr(kind, kids);

  const Expr& c = e[idx];
  int i=d_theoryBitvector->getBVConstSize(c)-1;
  bool curVal = d_theoryBitvector->getBVConstValue(c, i);
  int hi = bvLength-1;
  Expr term;
  vector<Expr> concatTerms;

  for(--i; i >= 0; --i) {
    if (d_theoryBitvector->getBVConstValue(c,i) != curVal) {
      if (kind == BVAND && curVal == false) {
        term = d_theoryBitvector->newBVZeroString(hi-i);
      }
      else if (kind == BVOR && curVal == true) {
        term = d_theoryBitvector->newBVOneString(hi-i);
      }
      else {
        term = d_theoryBitvector->newBVExtractExpr(output, hi, i+1);
        if (kind == BVXOR && curVal == true) {
          term = d_theoryBitvector->newBVNegExpr(term);
        }
      }
      concatTerms.push_back(term);
      curVal = !curVal;
      hi = i;
    }
  }

  if (kind == BVAND && curVal == false) {
    term = d_theoryBitvector->newBVZeroString(hi+1);
  }
  else if (kind == BVOR && curVal == true) {
    term = d_theoryBitvector->newBVOneString(hi+1);
  }
  else {
    if (hi < bvLength-1) {
      term = d_theoryBitvector->newBVExtractExpr(output, hi, 0);
    }
    else term = output;
    if (kind == BVXOR && curVal == true) {
      term = d_theoryBitvector->newBVNegExpr(term);
    }
  }
  concatTerms.push_back(term);
  if (concatTerms.size() == 1) {
    output = concatTerms[0];
  }
  else {
    output = d_theoryBitvector->newConcatExpr(concatTerms);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bitwise_zero", e, rat(idx));
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


/*! checks if e is already present in likeTerms without conflicts.
 *  if yes return 1, else{ if conflict return -1 else return 0 }
 *  we have conflict if
 *          1. the kind of e is BVNEG,
 *                 and e[0] is already present in likeTerms
 *          2. ~e is present in likeTerms already
 */
int BitvectorTheoremProducer::sameKidCheck(const Expr&  e,
					   ExprMap<int>& likeTerms) {
  //initially flag = 0, i.e. we assume e is not in likeTerms
  int flag = 0;

  //look for e
  ExprMap<int>::iterator it = likeTerms.find(e);

  //no entry found for e
  if(it==likeTerms.end()) {
    switch(e.getOpKind()) {
     case BVNEG: {
       ExprMap<int>::iterator it0 = likeTerms.find(e[0]);
       if(it0!=likeTerms.end())
	 flag = -1;
       break;
     }
     default: {
       Expr bvNeg = d_theoryBitvector->newBVNegExpr(e);
       ExprMap<int>::iterator negIt = likeTerms.find(bvNeg);
       if(negIt!=likeTerms.end())
	 flag=-1;
       break;
     }
    }
    if (flag == 0) likeTerms[e] = 1;
    return flag;
  }

  //found an entry for e
  return 1;
}


//! c1\@c2\@...\@cn = c  (concatenation of constant bitvectors)
Theorem BitvectorTheoremProducer::concatConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == CONCAT,
		"BitvectorTheoremProducer::concatConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::concatConst: e = "+e.toString());
  }
  vector<bool> res;
  for(int i=e.arity()-1; i >= 0; --i) {
    for(int bit=0, size=d_theoryBitvector->getBVConstSize(e[i]); bit < size; bit++)
      res.push_back(d_theoryBitvector->getBVConstValue(e[i], bit));
  }
  Proof pf;
  if(withProof())
    pf = newPf("concat_const", e);
  return newRWTheorem(e, d_theoryBitvector->newBVConstExpr(res), Assumptions::emptyAssump(), pf);
}


//! Flatten one level of nested concatenation, e.g.: x\@(y\@z)\@w = x\@y\@z\@w
Theorem
BitvectorTheoremProducer::concatFlatten(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == CONCAT && e.arity() >= 2,
		"BitvectorTheoremProducer::concatFlatten: e = "+e.toString());
  }
  // Rebuild the expression: copy the kids and flatten the nested CONCATs
  vector<Expr> kids;
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
    if(i->getOpKind() == CONCAT)
      kids.insert(kids.end(), i->getKids().begin(), i->getKids().end());
    else
      kids.push_back(*i);
  }
  Proof pf;
  if(withProof())
    pf = newPf("concat_flatten", e);
  return newRWTheorem(e, Expr(e.getOp(), kids), Assumptions::emptyAssump(), pf);
}


//! Merge n-ary concat. of adjacent extractions: x[15:8]\@x[7:0] = x[15:0]
Theorem
BitvectorTheoremProducer::concatMergeExtract(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == CONCAT && e.arity() >= 2,
		"BitvectorTheoremProducer::concatMergeExtract: e = "
		+e.toString());
    CHECK_SOUND(e[0].getOpKind() == EXTRACT,
		"BitvectorTheoremProducer::concatMergeExtract: e = "
		+e.toString());
    CHECK_SOUND(d_theoryBitvector->getExtractHi(e[0]) >= d_theoryBitvector->getExtractLow(e[0]),
		"BitvectorTheoremProducer::concatMergeExtract: e = "
		+e.toString());
  }

  const Expr& base = e[0][0]; // The common base of all extractions

  if(CHECK_PROOFS) {
    // Check that all extractions have the same base and are contiguous
    int low = d_theoryBitvector->getExtractLow(e[0]);
    for(int i=1, iend=e.arity(); i<iend; ++i) {
      const Expr& ei = e[i];
      CHECK_SOUND(ei.getOpKind() == EXTRACT && ei[0] == base,
		  "BitvectorTheoremProducer::concatMergeExtract: e["
		  +int2string(i)+"] = "+ei.toString()
		  +"\n base = "+base.toString());
      CHECK_SOUND(d_theoryBitvector->getExtractHi(ei) >= d_theoryBitvector->getExtractLow(ei),
		  "BitvectorTheoremProducer::concatMergeExtract: e["
		  +int2string(i)+"] = "+e.toString());

      int newHi = d_theoryBitvector->getExtractHi(ei);

      CHECK_SOUND(0 <= newHi && newHi == low-1,
		  "BitvectorTheoremProducer::concatMergeExtract:\n e["
		  +int2string(i-1)+"] = "+e[i-1].toString()
		  +"\n e["+int2string(i)+"] = "+ei.toString());
      low = d_theoryBitvector->getExtractLow(ei);
    }
  }

  int hi = d_theoryBitvector->getExtractHi(e[0]);
  int low = d_theoryBitvector->getExtractLow(e[e.arity()-1]);
  Expr res = d_theoryBitvector->newBVExtractExpr(base, hi, low);

  Proof pf;
  if(withProof())
    pf = newPf("concat_merge_extract", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}



//! BVPLUS(n, c1,c2,...,cn) = c  (bit-vector plus of constant bitvectors)
Theorem BitvectorTheoremProducer::bvplusConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == BVPLUS,
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
    CHECK_SOUND(d_theoryBitvector->getBVPlusParam(e) > 0,
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
  }
  // Transfer the values for each bitvector to a Rational, then add it
  // to the accumulator.
  Rational acc(0);
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
    Rational x = d_theoryBitvector->computeBVConst(*i);
    TRACE("bitvector rewrite", "bvplusConst: x(", *i, ") = "+x.toString());
    acc += x;
    TRACE("bitvector rewrite", "bvplusConst: acc = ", acc, "");
  }
  // Extract the bits of 'acc' into the vector
  int resSize = d_theoryBitvector->getBVPlusParam(e);
  vector<bool> res(resSize);
  for(int i=0; i<resSize; i++) {
    res[i] = (mod(acc, 2) == 1);
    TRACE("bitvector rewrite", "bvplusConst: acc = ", acc, "");
    TRACE("bitvector rewrite", "bvplusConst: res["+int2string(i)+"] = ",
	  res[i], "");
    acc = floor(acc/2);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bvplus_const", e);
  return newRWTheorem(e, d_theoryBitvector->newBVConstExpr(res), Assumptions::emptyAssump(), pf);
}


/*! @brief c0*c1 = c, multiplication of two BVCONST
 */
Theorem BitvectorTheoremProducer::bvmultConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == BVMULT,
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
  }
  Rational c = d_theoryBitvector->computeBVConst(e[0]);
  // Do the multiplication
  Rational x = d_theoryBitvector->computeBVConst(e[1]) * c;

  // Extract the bits of 'x' into the vector
  int resSize = d_theoryBitvector->BVSize(e.getType().getExpr());
  vector<bool> res(resSize);
  for(int i=0; i<resSize; i++) {
    res[i] = (mod(x, 2) == 1);
    x = floor(x/2);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bvmult_const", e);
  return newRWTheorem(e, d_theoryBitvector->newBVConstExpr(res), Assumptions::emptyAssump(), pf);
}

Theorem
BitvectorTheoremProducer::zeroCoeffBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVMULT && e.arity() == 2,
		"BitvectorTheoremProducer::zeroCoeffBVMult: e = "+e.toString());
    CHECK_SOUND(BVCONST == e[0].getKind(),
		"BitvectorTheoremProducer::zeroCoeffBVMult: e = "+e.toString());
    Rational c = d_theoryBitvector->computeBVConst(e[0]);
    CHECK_SOUND(0 == c,
		"BitvectorTheoremProducer::zeroCoeffBVMult:"
		"coeff must be zero:\n e = " +e.toString());
  }
  int size = d_theoryBitvector->BVSize(e);
  Expr output = d_theoryBitvector->newBVZeroString(size);

  Proof pf;
  if(withProof())
    pf = newPf("zerocoeff_bvmult", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

Theorem
BitvectorTheoremProducer::oneCoeffBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVMULT && e.arity() == 2,
		"BitvectorTheoremProducer::oneCoeffBVMult: e = "
		+e.toString());
    CHECK_SOUND(BVCONST == e[0].getKind(),
		"BitvectorTheoremProducer::oneCoeffBVMult: e = "
		+e.toString());
    Rational c = d_theoryBitvector->computeBVConst(e[0]);
    CHECK_SOUND(1 == c,
		"BitvectorTheoremProducer::oneCoeffBVMult:"
		"coeff must be one:\n e = " +e.toString());
  }
  int size = d_theoryBitvector->BVSize(e);
  Expr output = pad(size,e);

  Proof pf;
  if(withProof())
    pf = newPf("onecoeff_bvmult", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! t1*a <==> a*t1
Theorem
BitvectorTheoremProducer::flipBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.arity()==2 && BVMULT == e.getOpKind(),
		"BVMULT must have exactly 2 kids: " + e.toString());
  }
  int len = d_theoryBitvector->BVSize(e);
  Expr output = d_theoryBitvector->newBVMultExpr(len,e[1],e[0]);

  Proof pf;
  if(withProof())
    pf = newPf("flip_bvmult", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! Converts e into a BVVECTOR of bvLength 'len'
/*!
 * \param len is the desired bvLength of the resulting bitvector
 * \param e is the original bitvector of arbitrary bvLength
 */
Expr
BitvectorTheoremProducer::pad(int len, const Expr& e) {
  DebugAssert(len > 0,
	      "TheoryBitvector::pad:"
	      "padding bvLength must be a non-negative integer: "+
	      int2string(len));
  DebugAssert(BITVECTOR == e.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVPlusExpr:"
	      "input must be a BITVECTOR: " + e.toString());

  int size = d_theoryBitvector->BVSize(e);
  Expr res;
  if(size == len)
    res = e;
  else if (len < size)
    res = d_theoryBitvector->newBVExtractExpr(e,len-1,0);
  else {
    // size < len
    Expr zero = d_theoryBitvector->newBVZeroString(len-size);
    res = d_theoryBitvector->newConcatExpr(zero,e);
  }
  return res;
}

//! Pad the kids of BVMULT to make their bvLength = # of output-bits
Theorem
BitvectorTheoremProducer::padBVPlus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVPLUS == e.getOpKind() && e.arity()>1,
		"BitvectorTheoremProducer::padBVPlus: "
		"input must be a BVPLUS: " + e.toString());
  }
  int len = d_theoryBitvector->BVSize(e);
  vector<Expr> kids;
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
    if(i->getOpKind() == BVMULT) {
      Expr e0 = pad(len, (*i)[0]);
      Expr e1 = pad(len, (*i)[1]);
      Expr out = d_theoryBitvector->newBVMultExpr(len,e0,e1);
      kids.push_back(out);
    }
    else
      kids.push_back(pad(len, *i));
  }

  Expr output = d_theoryBitvector->newBVPlusExpr(len, kids);

  Proof pf;
  if(withProof())
    pf = newPf("pad_bvplus", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! Pad the kids of BVMULT to make their bvLength = # of output-bits
Theorem
BitvectorTheoremProducer::padBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVMULT == e.getOpKind() && e.arity()==2,
		"BitvectorTheoremProducer::padBVMult: "
		"input must be a BVMULT: " + e.toString());
    CHECK_SOUND(BITVECTOR==e[0].getType().getExpr().getOpKind() &&
		BITVECTOR==e[1].getType().getExpr().getOpKind(),
		"for BVMULT terms e[0],e[1] must be a BV: " + e.toString());
  }
  int len = d_theoryBitvector->BVSize(e);
  Expr e0 = pad(len, e[0]);
  Expr e1 = pad(len, e[1]);

  Expr output = d_theoryBitvector->newBVMultExpr(len,e0,e1);

  Proof pf;
  if(withProof())
    pf = newPf("pad_bvmult", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! a*(b*t) <==> (a*b)*t, where a,b,t have same bvLength
Theorem
BitvectorTheoremProducer::bvConstMultAssocRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVMULT == e.getOpKind() && e.arity() == 2,
		"BitvectorTheoremProducer::bvConstMultAssocRule: "
		"input must be a BVMULT: " + e.toString());
    CHECK_SOUND(BVMULT == e[1].getOpKind(),
		"BitvectorTheoremProducer::bvConstMultAssocRule: "
		"e[1] must be a BVMULT:\n e= " + e.toString());
    CHECK_SOUND(BVCONST == e[0].getKind() &&
		BVCONST == e[1][0].getKind(),
		"BitvectorTheoremProducer::bvConstMultAssocRule: "
		"e[0] & e[1][0] must be a BVCONST:\n e = " + e.toString());
  }
  int len = d_theoryBitvector->BVSize(e);
  int len0 = d_theoryBitvector->BVSize(e[0]);
  int len10 = d_theoryBitvector->BVSize(e[1][0]);
  int len11 = d_theoryBitvector->BVSize(e[1][1]);
  if(CHECK_PROOFS) {
    CHECK_SOUND(len == len0 && len0 == len10 && len0 == len11,
		"BitvectorTheoremProducer::bvConstMultAssocRule: "
		"kids of BVMULT must be equibvLength: ");
  }
  Rational e0 = d_theoryBitvector->computeBVConst(e[0]);
  Rational e10 = d_theoryBitvector->computeBVConst(e[1][0]);
  Expr c = d_theoryBitvector->newBVConstExpr(e0*e10, len);
  Expr output = d_theoryBitvector->newBVMultExpr(len, c, e[1][1]);

  Proof pf;
  if(withProof())
    pf = newPf("bvconstmult_assoc_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}


//FIXME: make BVMULT n-ary
//! (t1*t2)*t3 <==> t1*(t2*t3), where t1<t2<t3
Theorem
BitvectorTheoremProducer::bvMultAssocRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVMULT == e.getOpKind() && e.arity() == 2,
		"BitvectorTheoremProducer::bvMultAssocRule: "
		"input must be a BVMULT: " + e.toString());
    CHECK_SOUND(BVMULT == e[0].getOpKind() ||
		BVMULT == e[1].getOpKind(),
		"BitvectorTheoremProducer::bvMultAssocRule: "
		"e[0] or e[1] must be a BVMULT:\n e= " + e.toString());
    CHECK_SOUND(!(BVCONST == e[0].getOpKind() &&
		  BVCONST == e[1][0].getOpKind()),
		"BitvectorTheoremProducer::bvMultAssocRule: "
		"e[0] & e[1][0] cannot be a BVCONST:\n e = " +
		e.toString());
  }
  int len = d_theoryBitvector->BVSize(e);
  int len0 = d_theoryBitvector->BVSize(e[0]);
  int len1 = d_theoryBitvector->BVSize(e[1]);
  if(CHECK_PROOFS)
    CHECK_SOUND(len == len0 && len0 == len1,
		"BitvectorTheoremProducer::bvMultAssocRule: "
		"kids of BVMULT must be equibvLength: ");
  Expr e0, e1;
  e0 = e[0];
  e1 = e[1];

  std::vector<Expr> outputkids;
  if(BVMULT == e[0].getOpKind() && BVMULT != e[1].getOpKind()) {
    outputkids.push_back(e0[0]);
    outputkids.push_back(e0[1]);
    outputkids.push_back(e1);

  } else if(BVMULT != e[0].getOpKind() && BVMULT == e[1].getOpKind()) {
    outputkids.push_back(e1[0]);
    outputkids.push_back(e1[1]);
    outputkids.push_back(e0);
  } else {
    //both must be BVMULTs
    outputkids.push_back(e0[0]);
    outputkids.push_back(e0[1]);
    outputkids.push_back(e1[0]);
    outputkids.push_back(e1[1]);
  }
  sort(outputkids.begin(),outputkids.end());

  Expr output;
  switch(outputkids.size()) {
  case 3: {
    Expr out1 =
      d_theoryBitvector->newBVMultExpr(len, outputkids[1],outputkids[2]);
    output =
      d_theoryBitvector->newBVMultExpr(len, outputkids[0], out1);
    break;
  }
  case 4: {
    Expr out0 =
      d_theoryBitvector->newBVMultExpr(len, outputkids[0], outputkids[1]);
    Expr out1 =
      d_theoryBitvector->newBVMultExpr(len, outputkids[2], outputkids[3]);
    output =
      d_theoryBitvector->newBVMultExpr(len, out0, out1);
    break;
  }
  }

  Proof pf;
  if(withProof())
    pf = newPf("bvmult_assoc_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! a*(t1+...+tn) <==> (a*t1+...+a*tn), where all kids are equibvLength
Theorem
BitvectorTheoremProducer::bvMultDistRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVMULT == e.getOpKind() && e.arity() == 2,
		"BitvectorTheoremProducer::bvMultDistRule: "
		"input must be a BVMULT: " + e.toString());
    CHECK_SOUND(BVPLUS == e[1].getOpKind(),
		"BitvectorTheoremProducer::bvMultDistRule: "
		"input must be of the form a*(t1+...+tn): " + e.toString());
  }
  int bvLength= d_theoryBitvector->BVSize(e);
  int e0len = d_theoryBitvector->BVSize(e[0]);
  int e1len = d_theoryBitvector->BVSize(e[1]);
  if(CHECK_PROOFS) {
    CHECK_SOUND(bvLength== e0len && e0len == e1len,
		"BitvectorTheoremProducer::bvMultDistRule: "
		"all subterms must of equal bvLength: " + e.toString());
  }
  const Expr& e0 = e[0];
  const Expr& e1 = e[1];

  std::vector<Expr> v;
  Expr::iterator i = e1.begin();
  Expr::iterator iend = e1.end();
  for(;i != iend; ++i) {
    Expr s = d_theoryBitvector->newBVMultExpr(bvLength, e0, *i);
    v.push_back(s);
  }
  Expr output = d_theoryBitvector->newBVPlusExpr(bvLength,v);

  Proof pf;
  if(withProof())
    pf = newPf("bvmult_distributivity_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! input BVPLUS expression e.output e <==> e', where e' has no BVPLUS
//  kids. remember, the invariant is that kids are already in
//  bvplus normal-form
Theorem
BitvectorTheoremProducer::flattenBVPlus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVPLUS && e.arity() >= 2,
		"BitvectorTheoremProducer::flattenBVPlus: e = "+e.toString());
  }
  int bvLength= d_theoryBitvector->BVSize(e);
  const int numOfKids = e.arity();

  if(CHECK_PROOFS) {
    for(int i=0; i<numOfKids; ++i)
      CHECK_SOUND(d_theoryBitvector->BVSize(e[i]) == bvLength,
		  "BitvectorTheoremProducer::flattenBVPlus: "
		  "summands must be of the same bvLength as BVPLUS:\n e = "
		  +e.toString());
  }

  //collect the kids of e in the vector v. if any kid is a BVPLUS,
  //then collect its kids into v. then construct a BVPLUS expr
  std::vector<Expr> v;
  for(int i = 0; i < numOfKids; ++i) {
    if(e[i].getOpKind() == BVPLUS) {
      const Expr& bvplusKid = e[i];
      const int bvplusArity = bvplusKid.arity();
      for(int j=0; j < bvplusArity; ++j)
	v.push_back(bvplusKid[j]);
    } else
      v.push_back(e[i]);
  }
  Expr eprime = d_theoryBitvector->newBVPlusExpr(bvLength, v);

  Proof pf;
  if(withProof())
    pf = newPf("flatten_bvplus", e);
  return newRWTheorem(e, eprime, Assumptions::emptyAssump(), pf);
}

void
BitvectorTheoremProducer::collectOneTermOfPlus(const Rational & coefficient,
					       const Expr& term,
					       ExprMap<Rational> & likeTerms,
					       Rational & plusConstant)
{
  ExprMap<Rational>::iterator it = likeTerms.find(term);

  if(it!=likeTerms.end())
    likeTerms[term] += coefficient;
  else {
    // Check if there is a negated form of this term already in likeTerms map.
    bool foundNegated= false;
    if (!likeTerms.empty()) {
      Expr negTerm = d_theoryBitvector->newBVNegExpr(term);
      negTerm = d_theoryBitvector->pushNegationRec(term).getRHS();
      it = likeTerms.find(negTerm);
      if (it!= likeTerms.end()) {
	foundNegated = true;

	// Use the rule that ~(c*x) = -c*x-1 (based on the fact: -x= ~x+1).
	likeTerms[negTerm] += -coefficient;
	plusConstant+= -1;
      }
    }
    if (!foundNegated)
      // Negated form was not found, need to register the new positive form.
      likeTerms[term] = coefficient;
  }
}

void
BitvectorTheoremProducer::collectLikeTermsOfPlus(const Expr& e,
						 ExprMap<Rational> & likeTerms,
						 Rational & plusConstant) {
  likeTerms.clear();
  Expr::iterator i = e.begin();
  Expr::iterator iend = e.end();
  plusConstant= 0;
  //go thru' bvplus term, one monom at a time
  for(; i!=iend; ++i) {
    const Expr s = *i;
    switch(s.getOpKind()) {
    case BVMULT: {
      //if monom is BVMULT, collect like terms using ExprMap
      if (s[0].getKind() == BVCONST) {
        Rational coefficient= d_theoryBitvector->computeBVConst(s[0]);
        const Expr& var = s[1];
        collectOneTermOfPlus(coefficient, var, likeTerms, plusConstant);
      }
      else { // non-linear mult
        if(CHECK_PROOFS) {
          CHECK_SOUND(BVCONST != s[1].getKind(),
		    "TheoryBitvector::combineLikeTerms: "
		    "Unexpected MULT syntax:\n\n s = " + s.toString()
		    +"\n\n in e = "+e.toString());
        }
        collectOneTermOfPlus(1, s, likeTerms, plusConstant);
      }
      break;
    }
    case BVUMINUS:
      collectOneTermOfPlus(-1, s[0], likeTerms, plusConstant);
      break;
    case BVCONST:
      plusConstant += d_theoryBitvector->computeBVConst(s);
      break;
    default:
      //we have just a variable; check if variable in ExprMap
      collectOneTermOfPlus(1, s, likeTerms, plusConstant);
      break;
    }
  }
}

static Rational boundedModulo(const Rational & value, const Rational & modulo,
			      const Rational & lowerBound) {
    Rational ret = mod(value, modulo);
    if(ret == 0)
      return ret;

    if (ret< lowerBound)
      ret+= modulo;
    else {
      // end is one position beyond upper limit.
      Rational end= modulo+lowerBound;
      if (ret >= end)
	ret-= modulo;
    }
    return ret;
}

void
BitvectorTheoremProducer::
createNewPlusCollection(const Expr & e,
			const ExprMap<Rational> & likeTerms,
			Rational & plusConstant,
			std::vector<Expr> & result) {
  int bvplusLength= d_theoryBitvector->BVSize(e);
  // Compute 2^n, to use as a modulus base
  Rational power2(1);
  for(int i=0; i<bvplusLength; i += 1) power2 *= 2;

  ExprMap<Rational>::const_iterator j = likeTerms.begin();
  ExprMap<Rational>::const_iterator jend = likeTerms.end();
  for(; j!=jend; ++j) {
    // The coefficient will be equivalent to j->second modulus of power2
    // and in the range [-power2/2+1, power2/2]
    // FIXME: Need to reconsider the "best" coefficient normalization scheme.
    Rational coefficient = boundedModulo(j->second, power2, -power2/2+1);
    if(coefficient == 0)
      continue;
    Expr multiplicand = j->first;
    Expr monomial;
    if (coefficient<0) {
      // Make the coefficient positive: c<0 ;
      // (c*x)= (-c)*(-x)= (-c)*(~x+1)=(-c)*(~x) -c
      multiplicand = d_theoryBitvector->newBVNegExpr(multiplicand);
      multiplicand = d_theoryBitvector->pushNegationRec(multiplicand).getRHS();
      coefficient= coefficient*-1;
      plusConstant +=coefficient;
    }
    if(coefficient == 1)
      monomial = multiplicand;
    else {
      Expr coeffExpr =
	d_theoryBitvector->newBVConstExpr(coefficient, bvplusLength);
      monomial =
	d_theoryBitvector->newBVMultExpr(bvplusLength, coeffExpr,multiplicand);
    }
    if(CHECK_PROOFS) {
      CHECK_SOUND(BITVECTOR==monomial.getType().getExpr().getOpKind(),
		  "TheoryBitvector::combineLikeTerms:"
		  "each monomial must be a bitvector:\n"
		  "monomial = " + monomial.toString());
      CHECK_SOUND(bvplusLength == d_theoryBitvector->BVSize(monomial),
		  "TheoryBitvector::combineLikeTerms:"
		  "bvLength of each monomial must be the same as e:\n"
		  "monomial = " + monomial.toString() + "\n e = " + e.toString());
    }
    result.push_back(monomial);
  }
  // Positive modulo of the constant
  plusConstant = boundedModulo(plusConstant, power2, 0);

  //make the constant a subterm of the BVPLUS expression
  if(plusConstant != 0) {
    const Expr c =
      d_theoryBitvector->newBVConstExpr(plusConstant, bvplusLength);
    result.push_back(c);
  }
}

Expr
BitvectorTheoremProducer::sumNormalizedElements(int bvplusLength,
						const std::vector<Expr>&items){
  //construct a new BVPLUS term using the ExprMap.  if size of
  //likeTerms is less than 2, then do NOT construct BVPLUS
  switch(items.size()) {
  case 0:
    //items are empty. only constant 0 remains
    return d_theoryBitvector->newBVZeroString(bvplusLength);

  case 1:
    //items may contain a Expr of the form a*x or x or a
    return items[0];

  default:
    //items have 2 or more kids
    return d_theoryBitvector->newBVPlusExpr(bvplusLength, items);
  }
}

Theorem
BitvectorTheoremProducer::combineLikeTermsRule(const Expr& e) {
  TRACE("bitvector rewrite", "combineLikeTermsRule(",e.toString(), ") {");
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVPLUS == e.getOpKind() && e.arity()>=2,
		"TheoryBitvector::combineLikeTerms: "
		"input must be a BVPLUS term:\n e = " + e.toString());
    int bvplusLength = d_theoryBitvector->BVSize(e);
    Expr::iterator i = e.begin();
    Expr::iterator iend = e.end();
    for(;i!=iend;++i) {
      const Expr& s = *i;
      if(s.getOpKind() == BVPLUS) {
	CHECK_SOUND(s.getOpKind() != BVPLUS,
		    "TheoryBitvector::combineLikeTerms: "
		    "BVPLUS must be flattened:\n e = " + e.toString());
      }

      int bvLength= d_theoryBitvector->BVSize(s);
      //bvLength checks for BVCONST and variables
      CHECK_SOUND(bvLength==bvplusLength,
		  "TheoryBitvector::combineLikeTerms: "
		  "BVPLUS must be padded:\n e = " + e.toString());
      //Length checks for BVMULTs
      if(s.getOpKind()==BVMULT) {
	int s0len = d_theoryBitvector->BVSize(s[0]);
	int s1len = d_theoryBitvector->BVSize(s[1]);
	CHECK_SOUND(bvplusLength == s0len && s0len== s1len,
		    "all monoms must have the samebvLength "
		    "as the bvplus term: " + e.toString());
      }
    }
  }
  int bvplusLength = d_theoryBitvector->BVSize(e);
  ExprMap<Rational> likeTerms;
  Rational theConstant(0);
  collectLikeTermsOfPlus(e, likeTerms, theConstant);

  std::vector<Expr> collection;
  createNewPlusCollection(e, likeTerms, theConstant, collection);

  Expr output= sumNormalizedElements(bvplusLength, collection);

  TRACE("bitvector rewrite",
	"combineLikeTermsRule =>",output.toString(), "}");
  Proof pf;
  if(withProof())
    pf=newPf("bvplus_combine_like_terms", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

Theorem
BitvectorTheoremProducer::lhsMinusRhsRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(EQ == e.getKind() && e.arity() == 2,
		"BitvectorTheoremProducer::lhsMinusRhsRule: "
		"input must be an EQ: e = " +e.toString());
    CHECK_SOUND(BVPLUS == e[0].getOpKind() ||
		BVPLUS == e[1].getOpKind(),
		"BitvectorTheoremProducer::lhsMinusRhsRule: "
		"atleast one of the input subterms must be BVPLUS:"
		"e = " +e.toString());
    int bvLength0 = d_theoryBitvector->BVSize(e[0]);
    int bvLength1 = d_theoryBitvector->BVSize(e[1]);
    CHECK_SOUND(bvLength0 == bvLength1,
		"BitvectorTheoremProducer::lhsMinusRhsRule: "
		"both sides of EQ must be same Length. e = " +e.toString());
    for(Expr::iterator i=e[0].begin(),iend=e[0].end();i!=iend;++i) {
      int bvLength= d_theoryBitvector->BVSize(*i);
      CHECK_SOUND(bvLength0 == bvLength,
		  "BitvectorTheoremProducer::lhsMinusRhsRule: "
		  "all subterms of e[0] must be of same Length."
		  "e = " +e.toString());
    }
    for(Expr::iterator i=e[1].begin(),iend=e[1].end();i!=iend;++i) {
      int bvLength= d_theoryBitvector->BVSize(*i);
      CHECK_SOUND(bvLength1 == bvLength,
		  "BitvectorTheoremProducer::lhsMinusRhsRule: "
		  "all subterms of e[1] must be of same Length."
		  "e = " +e.toString());
    }
  }
  Expr output;
  int bvLength = d_theoryBitvector->BVSize(e[0]);
  std::vector<Expr> k;

  //construct 0 of bvLength
  Expr zeroStr = d_theoryBitvector->newBVZeroString(bvLength);

  if(e[0] == e[1])
    output = Expr(EQ, zeroStr, zeroStr);
  else {
    //drop common subterms
    std::vector<Expr> e0K = e[0].getKids();
    std::vector<Expr> e1K = e[1].getKids();
    for(vector<Expr>::iterator i=e0K.begin(),iend=e0K.end();i!=iend;++i){
      for(vector<Expr>::iterator j=e1K.begin(),jend=e1K.end();j!=jend;++j){
	if(*i == *j) {
	  e0K.erase(i);
	  e1K.erase(j);
	  break;
	}
      }
    }
    Expr newLhs = d_theoryBitvector->newBVPlusExpr(bvLength, e0K);
    k.push_back(newLhs);
    Expr newRhs = d_theoryBitvector->newBVPlusExpr(bvLength, e1K);
    //construct -rhs
    Expr uminus = d_theoryBitvector->newBVUminusExpr(newRhs);
    //push back -rhs
    k.push_back(uminus);
    //construct lhs-rhs
    Expr lhsMinusRhs = d_theoryBitvector->newBVPlusExpr(bvLength,k);
    //construct lhs-rhs=0
    output = Expr(EQ, lhsMinusRhs, zeroStr);
  }

  Proof pf;
  if(withProof())
    pf = newPf("lhs_minus_rhs_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! generic rule used for bitblasting step. -e <==> ~e+1
Theorem
BitvectorTheoremProducer::bvuminusToBVPlus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind(),
		"BitvectorTheoremProducer::bvuminusBitBlastRule: "
		"input must be bvuminus: e = " + e.toString());
  }
  int bvLength = d_theoryBitvector->BVSize(e);
  std::vector<Expr> k;
  Expr negE0 = d_theoryBitvector->newBVNegExpr(e[0]);
  k.push_back(negE0);
  Expr plusOne = d_theoryBitvector->newBVConstExpr(1, bvLength);
  k.push_back(plusOne);

  Expr output = d_theoryBitvector->newBVPlusExpr(bvLength, k);
  Proof pf;
  if(withProof())
    pf = newPf("bvuminus_bitblast_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! -0 <==> 0, -c <==> ~c+1
Theorem
BitvectorTheoremProducer::bvuminusBVConst(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind() &&
		BVCONST == e[0].getKind(),
		"BitvectorTheoremProducer::bvuminusBVConst: "
		"e should be bvuminus, e[0] should be bvconst: e = " +
		e.toString());
  }
  Expr output;
  int e0Length = d_theoryBitvector->BVSize(e[0]);
  // output == 0
  if(d_theoryBitvector->computeBVConst(e[0]) == 0)
    output = e[0];
  else {
    // Compute -c, which is ~c+1
    Rational x = d_theoryBitvector->computeNegBVConst(e[0]);
    output = d_theoryBitvector->newBVConstExpr(x, e0Length);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bvuminus_bvconst_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! -(c*t)<=>(-c)*t; if -c==0 return e<=>0. if(-c==1) return e<=>t
Theorem
BitvectorTheoremProducer::bvuminusBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind(),
		"BitvectorTheoremProducer::bvuminusBVMult: "
		"e should be bvuminus: e =" + e.toString());
    CHECK_SOUND(BVMULT == e[0].getOpKind(),
		"Bitvectortheoremproducer::bvuminusBVMult: "
		"in input expression e = " + e.toString() +
		"\ne[0] should be bvmult: e[0] = " + e[0].toString());
    CHECK_SOUND(BVCONST == e[0][0].getKind(),
		"Bitvectortheoremproducer::bvuminusBVMult: "
		"in input expression e = " + e.toString() +
		"\ne[0][0] should be bvconst: e[0][0] = " + e[0][0].toString());
    int bvLength =  d_theoryBitvector->BVSize(e);
    int e0Length =  d_theoryBitvector->BVSize(e[0]);
    int e00Length =  d_theoryBitvector->BVSize(e[0][0]);
    CHECK_SOUND(bvLength == e0Length && e0Length == e00Length,
		"Bitvectortheoremproducer::bvuminusBVMult: "
		"in input expression e = " + e.toString() +
		"\nLengths of all subexprs must be equal: e = " + e.toString());
  }
  //e is of the form -(c*t)
  Expr output;
  int e0Length = d_theoryBitvector->BVSize(e[0]);
  //compute ~c+1
  Rational coeff = d_theoryBitvector->computeNegBVConst(e[0][0]);
  if(0 == coeff)
    //if ~c+1 == 0
    output = d_theoryBitvector->newBVZeroString(e0Length);
  else if (1 == coeff)
    //if ~c+1 == 1
    output = e[0][1];
  else {
    //construct (~c+1)*t
    Expr newcoeff = d_theoryBitvector->newBVConstExpr(coeff, e0Length);
    output = d_theoryBitvector->newBVMultExpr(e0Length, newcoeff, e[0][1]);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bvuminus_bvmult_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! -(-e) <==> e
Theorem
BitvectorTheoremProducer::bvuminusBVUminus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind(),
		"BitvectorTheoremProducer::bvuminusBVUminus: "
		"e should be bvuminus: e =" + e.toString());
    CHECK_SOUND(BVUMINUS == e[0].getOpKind(),
		"Bitvectortheoremproducer::bvuminusBVUminus: "
		"in input expression e = " + e.toString() +
		"\ne[0] should be bvmult: e[0] = " + e[0].toString());
  }
  Expr output;
  // -(-e) <==> e
  output = e[0][0];
  Proof pf;
  if(withProof())
    pf = newPf("bvuminus_bvuminus_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! -v <==> -1*v
Theorem
BitvectorTheoremProducer::bvuminusVar(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind(),
		"BitvectorTheoremProducer::bvuminusVar: "
		"e should be bvuminus: e =" + e.toString());
  }
  Expr output;
  std::vector<bool> res;
  int e0Length = d_theoryBitvector->BVSize(e[0]);
  for(int i=0; i<e0Length; ++i) {
    res.push_back(true);
  }
  Expr coeff = d_theoryBitvector->newBVConstExpr(res);
  output = d_theoryBitvector->newBVMultExpr(e0Length, coeff, e[0]);

  Proof pf;
  if(withProof())
    pf = newPf("bvuminus_var_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! c*(-t) <==> (-c)*t
Theorem
BitvectorTheoremProducer::bvmultBVUminus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind(),
		"BitvectorTheoremProducer::bvmultBVUminus: "
		"e should be bvuminus: e =" + e.toString());
    CHECK_SOUND(BVMULT == e[0].getOpKind() &&
		BVCONST == e[0][0].getKind() &&
		BVUMINUS == e[0][1].getOpKind(),
		"Bitvectortheoremproducer::bvmultBVUminus: "
		"in input expression e = " + e.toString() +
		"\ne[0] has to be bvmult"
		"e[0][1] must be bvuminus: e[0] = " + e[0].toString());
    int bvLength = d_theoryBitvector->BVSize(e);
    int e00Length = d_theoryBitvector->BVSize(e[0][0]);
    int e01Length = d_theoryBitvector->BVSize(e[0][1]);
    CHECK_SOUND(bvLength == e00Length && e00Length == e01Length,
		"Bitvectortheoremproducer::bvmultBVUminus: "
		"in input expression e = " + e.toString() +
		"\nLengths of all subexprs must be equal.");
  }
  Expr output;
  int bvLength = d_theoryBitvector->BVSize(e);
  const Expr& coeff = e[0][0];
  Rational negatedcoeff = d_theoryBitvector->computeNegBVConst(coeff);
  const Expr& e010 = e[0][1][0];

  if(0 == negatedcoeff)
    //if ~c+1 == 0
    output = d_theoryBitvector->newBVZeroString(bvLength);
  else if (1 == negatedcoeff)
    //if ~c+1 == 1
    output = e010;
  else {
    //construct (~c+1)*t
    Expr newcoeff = d_theoryBitvector->newBVConstExpr(negatedcoeff, bvLength);
    output = d_theoryBitvector->newBVMultExpr(bvLength, newcoeff, e010);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bvmult_bvuminus_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! -(c1*t1+...+cn*tn) <==> (-(c1*t1)+...+-(cn*tn))
Theorem
BitvectorTheoremProducer::bvuminusBVPlus(const Expr& e) {
//   if(CHECK_PROOFS) {
//     CHECK_SOUND(BVUMINUS == e.getOpKind(),
// 		"BitvectorTheoremProducer::bvuminusBVPlus: "
// 		"e should be bvuminus: e =" + e.toString());
//     CHECK_SOUND(BVPLUS == e[0].getOpKind(),
// 		"BitvectorTheoremProducer::bvuminusBVPlus: "
// 		"e[0] should be bvplus: e[0] =" + e[0].toString());
//   }
//   int bvLength = d_theoryBitvector->BVSize(e);
//   const Expr& e0 = e[0];
//   Expr::iterator i = e0.begin();
//   Expr::iterator iend = e0.end();
//   std::vector<Expr> output;
//   for(; i!=iend; ++i) {
//     const Expr& s = *i;
//     Expr t = d_theoryBitvector->newBVUminusExpr(s);
//     output.push_back(t);
//   }
//   Expr outputPlus =
//     d_theoryBitvector->newBVPlusExpr(bvLength, output);

//   Assumptions a;
//   Proof pf;
//   if(withProof())
//     pf = newPf("bvminus_bvplus_rule", e);
//   return newRWTheorem(e, outputPlus, a, pf);

  Proof pf;
  if(withProof())
    pf = newPf("bvminus_bvplus_rule", e);
  return newRWTheorem(e, e, Assumptions::emptyAssump(), pf);
}

Theorem
BitvectorTheoremProducer::extractBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT &&
		e[0].getOpKind() == BVMULT &&
		e[0].arity() == 2,
		"BitvectorTheoremProducer::extractBVMult: "
		"input must be an EXTRACT over BVMULT:\n e = "+e.toString());
  }
  const Expr& bvmult = e[0];
  int bvmultLen = d_theoryBitvector->BVSize(bvmult);
  int extractHi = d_theoryBitvector->getExtractHi(e);
  int extractLow = d_theoryBitvector->getExtractLow(e);

  if(CHECK_PROOFS) {
    CHECK_SOUND(bvmultLen > extractHi,
		"BitvectorTheoremProducer::extractBVMult: "
		"bvmult Length must be greater than extract Length:\n e = "
		+e.toString());
  }

  Expr output = d_theoryBitvector->newBVMultPadExpr(extractHi+1, bvmult[0],
                                                    bvmult[1]);
  if(extractLow > 0)
    output=d_theoryBitvector->newBVExtractExpr(output, extractHi, extractLow);

  Proof pf;
  if(withProof())
    pf = newPf("extract_bvmult_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

Theorem
BitvectorTheoremProducer::extractBVPlus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e[0].getOpKind() == BVPLUS,
		"BitvectorTheoremProducer::extractBVPlus: "
		"input must be an EXTRACT over BVPLUS:\n e = "+e.toString());
  }
  const Expr& bvplus = e[0];
  int bvplusLen = d_theoryBitvector->BVSize(bvplus);
  int extractHi = d_theoryBitvector->getExtractHi(e);
  int extractLow = d_theoryBitvector->getExtractLow(e);

  if(CHECK_PROOFS) {
    CHECK_SOUND(bvplusLen > extractHi,
		"BitvectorTheoremProducer::extractBVPlus: "
		"bvplus Length must be greater than extract bvLength:\n e = "
		+e.toString());
  }

  // Shortcut
  if(bvplusLen == extractHi+1)
    return d_theoryBitvector->reflexivityRule(e);

  // Shorten the result width of the bvplus term
  Expr output(d_theoryBitvector->newBVPlusPadExpr(extractHi+1, bvplus.getKids()));
  if(extractLow > 0)
    output=d_theoryBitvector->newBVExtractExpr(output, extractHi, extractLow);

  Proof pf;
  if(withProof())
    pf = newPf("extract_bvplus_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


// |- t=0 OR t=1  for any 1-bit bitvector t
Theorem
BitvectorTheoremProducer::typePredBit(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(d_theoryBitvector->getBaseType(e).getExpr().getOpKind() == BITVECTOR,
		"BitvectorTheoremProducer::typePredBit: e = "+e.toString());
    CHECK_SOUND(d_theoryBitvector->BVSize(e) == 1,
		"BitvectorTheoremProducer::typePredBit: e = "+e.toString());
  }

  Proof pf;
  if(withProof())
    pf=newPf("type_pred_bit", e);
  return newTheorem(e.eqExpr(bvZero()) || e.eqExpr(bvOne()), Assumptions::emptyAssump(), pf);
}


//! Expand the type predicate wrapper (compute the actual type predicate)
Theorem
BitvectorTheoremProducer::expandTypePred(const Theorem& tp) {
  Expr tpExpr = tp.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(tpExpr.getOpKind() == BVTYPEPRED ||
		(tpExpr.getKind() == NOT && tpExpr[0].getOpKind() == BVTYPEPRED),
		"BitvectorTheoremProducer::expandTypePred: "
		"Expected BV_TYPE_PRED wrapper:\n tp = "
		+tpExpr.toString());
  }
  Expr res;
  if(tpExpr.getKind() == NOT)
    res = d_theoryBitvector->falseExpr();
  else {
    Type t(d_theoryBitvector->getTypePredType(tpExpr));
    const Expr& e(d_theoryBitvector->getTypePredExpr(tpExpr));
    int size(d_theoryBitvector->getBitvectorTypeParam(t));
    //   DebugAssert(BVSize(e)==size, "TheoryBitvector::computeTypePred: e="
    // 	      +e.toString()+", t="+t.toString());
    if(size >= 2) {
      vector<Expr> kids;
      for(int i=0; i<size; i++) {
	Expr bit(d_theoryBitvector->newBVExtractExpr(e, i, i));
	kids.push_back(bit.eqExpr(bvZero()) || bit.eqExpr(bvOne()));
      }
      res = andExpr(kids);
    } else {
      res = (e.eqExpr(bvZero()) || e.eqExpr(bvOne()));
    }
  }
  Proof pf;
  if(withProof())
    pf = newPf("expand_type_pred", tp.getExpr(), tp.getProof());

  return newTheorem(res, tp.getAssumptionsRef(), pf);
}

/*Beginning of Lorenzo PLatania's methods*/

// Theorem BitvectorTheoremProducer::multiply_coeff( Rational mult_inv, const Expr& e)
// {

//   Expr rhs= d_theoryBitvector->multiply_coeff( mult_inv, e);
//   Proof pf= newPf("multiply both sides for a constant");
//   return newRWTheorem( e, rhs, Assumptions::emptyAssump(), pf);
// }


// rewrites the equation in the form 0 = Expr
// this is needed for TheoryBitvector::solve
Theorem BitvectorTheoremProducer::MarkNonSolvableEq( const Expr& e)
{

  int bv_size =  d_theoryBitvector->BVSize(e[0]);
  Expr bv_zero( d_theoryBitvector->newBVZeroString(bv_size));

  if (CHECK_PROOFS)
    CHECK_SOUND( e.isEq() &&
		( e[0] == bv_zero || e[1] == bv_zero ),
		"MarkNonSolvableEq: input must be a canonized equation" + e.toString());
  if( e[1] == bv_zero )
    {
      Expr expr_res= Expr(EQ, e[1], e[0]);
      Proof pf= newPf("mark non solvable eq");
      Theorem th_res= newRWTheorem( e, expr_res, Assumptions::emptyAssump(), pf);
      return th_res;
    }
  else
    {
      return d_theoryBitvector->reflexivityRule(e);
    }


}

// Given an expression t = 0, isolate a single leaf on the lhs if possible,
// returning t = 0 <=> leaf = rest.
// Otherwise, return e <=> e
Theorem BitvectorTheoremProducer::isolate_var(const Expr& e)
{
  int bv_size = d_theoryBitvector->BVSize(e[0]);
  Expr bv_zero(d_theoryBitvector->newBVZeroString(bv_size));

  if (CHECK_PROOFS) {
    CHECK_SOUND(e.isEq() && e[1] == bv_zero && e[0].getOpKind() != BVCONST,
		"isolate_var: input must be an equation with lhs non-cosnt and rhs must be zero" + e.toString());
  }

  //  cout<<"BitvectorTheoremProducer::isolate_var: "<<e.toString()<<endl;

  Rational modulus = pow(Rational(bv_size), Rational(2));
  Expr res_expr;
  Expr lhs = e[0];

  switch (lhs.getOpKind()) {
    case BVMULT:
      // linear BVMULT term
      if( lhs[0].getOpKind() == BVCONST )
      {
        DebugAssert(lhs[1].getOpKind() != BVCONST &&
                    lhs[1].getOpKind() != BVPLUS, "Should have been canonized");
        DebugAssert(d_theoryBitvector->computeBVConst(lhs[0]) % 2 == 0,
                    "Expected even coeff");
      }
      res_expr = e;
      break;
    case BVPLUS:
    {
      int e_kid_arity = lhs.arity();
      bool foundUnitCoeff = false;
      Expr new_lhs, new_rhs, new_coeff;
      vector<Expr> newKids;
      Rational tmp, const_term = 0;
      for( int i = 0; i < e_kid_arity; ++i)
      {
        // it can be a BVMULT, a var, or a const
        Expr e_sub_kid = lhs[i];
        switch (e_sub_kid.getOpKind()) {
          case BVCONST:
            DebugAssert(const_term == 0, "Expected only one constant");
            const_term = ((modulus-1) * d_theoryBitvector->computeBVConst(e_sub_kid)) % modulus;
            newKids.push_back(d_theoryBitvector->newBVConstExpr(const_term, bv_size));
            break;
          case BVMULT:
            if( e_sub_kid[0].getOpKind() == BVCONST )
            {
              DebugAssert(e_sub_kid.arity() == 2, "Expected arity 2 BVMULT");
              tmp = d_theoryBitvector->computeBVConst(e_sub_kid[0]);
              DebugAssert(tmp != 1, "Expected coeff other than 1");
              tmp = (tmp * (modulus-1)) % modulus;
              new_coeff = d_theoryBitvector->newBVConstExpr(tmp, bv_size);
              newKids.push_back(d_theoryBitvector->newBVMultExpr(bv_size, new_coeff, e_sub_kid[1]));
            }
            else {
              new_coeff = d_theoryBitvector->newBVConstExpr(modulus-1, bv_size);
              newKids.push_back(d_theoryBitvector->newBVMultExpr(bv_size, new_coeff, e_sub_kid));
            }
            break;
          default:
            if (!foundUnitCoeff) {
              foundUnitCoeff = true;
              new_lhs = e_sub_kid;
            }
            else {
              new_coeff = d_theoryBitvector->newBVConstExpr(modulus-1, bv_size);
              newKids.push_back(d_theoryBitvector->newBVMultExpr(bv_size, new_coeff, e_sub_kid));
            }
            break;
        }
      }
      if (foundUnitCoeff) {
        DebugAssert(newKids.size() > 0, "Expected non-empty kids");
        Expr new_rhs;
        if (newKids.size() == 1) {
          new_rhs = newKids[0];
        }
        else {
          new_rhs = d_theoryBitvector->newBVPlusExpr(bv_size, newKids);
        }
        res_expr = Expr(EQ, new_lhs, new_rhs);
      }
      else {
        res_expr = e;
      }
      break;
    }
    default:
      res_expr = e;
      break;
  }
  Proof pf= newPf("isolate var");
  //  cout<<"TheoryBitvector::isolate_var: result is: " <<res_expr.toString()<<endl;

  DebugAssert(e == res_expr || (res_expr.isEq() && d_theoryBitvector->isLeaf(res_expr[0]) &&
              !d_theoryBitvector->isLeafIn(res_expr[0], res_expr[1])),
              "Expected no change or solved form");

  return newRWTheorem(e, res_expr, Assumptions::emptyAssump(), pf);
}


// Theorem BitvectorTheoremProducer::isolate_var( const Theorem& t, const Expr& e)
// {
//   int bv_size =  d_theoryBitvector->BVSize(e[0]);
//   Expr bv_zero( d_theoryBitvector->newBVZeroString(bv_size));
//   Expr BV_one = d_theoryBitvector->newBVConstExpr(1,bv_size);

//   if (CHECK_PROOFS)
//     // the RHS assumptio has to be removed
//     CHECK_SOUND( e.isEq() &&
// 		( e[0] == bv_zero || e[1] == bv_zero ),
// 		"isolate_var: input must be an equation and one of the kids must be a zero" + e.toString());

//   cout<<"BitvectorTheoremProducer::isolate_var: "<<e.toString()<<endl;

//   Expr new_rhs;
//   Expr lhs;
//   Expr new_lhs;
//   //  Expr rhs;
//   lhs = e[0];

//   int lhs_arity = lhs.arity();

//   int found = 0;
//   int index, solve_pos;

//   // add the case for a*x = 0

//   //  equation of just one variable, like x= c, nothing to be done
//   if( lhs.isVar())
//     {
//       Proof pf= newPf("isolate var");
//       return newRWTheorem( t.getExpr(), e, Assumptions::emptyAssump(), pf);
//     }
//   else
//     {
//       //      look for a variable we can solve for
//       for( index=0; index < lhs_arity; ++index)
// 	{
// // 	  if( lhs[index].getOpKind() == BVMULT )
// // 	    {
// // 	      if( lhs[index][0] == BV_one)
// 	  cout<<"BitvectorTheoremProducer::isolate_var, lhs[index]: "<<lhs[index]<<endl;
// 	  if( d_theoryBitvector->canSolveFor( lhs[index], e))
// 	    //	  if( d_theoryBitvector->isLeaf( lhs[index]) || (lhs[index].getOpKind() == BVMULT && lhs[index][0].isVar() && lhs[index][0].isVar()) )
// 	    {
// 	      found = 1;
// 	      solve_pos = index;
// 	      break;
// 	    }
// 	}
// // 	  else
// // 	    if( lhs[index].getOpKind() == BVCONST )
// // 	      rhs = lhs[index];

//     }
//   DebugAssert(found,
// 	      "BitvectorTheoremProducer::isolate_var: No variable with unary coefficient found");

//   // L:: Index says which variable we are solving the equation for.
//   // for all other variables we have to invert the sign of the
//   // coefficient and put them in the rhs with the known term

//   cout<<"we solve for the var in position "<<solve_pos<<endl;
//   //L:: x= sum(list)
//   std::vector<Expr> new_rhs_list;
//   Rational known_term = 0;
//   int scan;
//   for( scan = 0; scan < lhs_arity; ++scan)
//     {
//       if( scan != solve_pos )
// 	{
// 	  // I think the first case is useless
// 	  // the operand of the sum is just a var, but different from
// 	  // the one we choose to solve the equation
// // 	  if( lhs[scan].isVar())
// // 	    {
// // 	      new_rhs_list.push_back( d_theoryBitvector->newBVUminusExpr( lhs[scan]) );
// // 	    }
// // 	  else
// 	    // we add the constant to the known term
// 	    if( lhs[scan].getOpKind() == BVCONST )
// 	      {
// 		Rational tmp = d_theoryBitvector->computeNegBVConst( lhs[scan]);
// 		Expr bv_tmp = d_theoryBitvector->signed_newBVConstExpr( tmp, bv_size );
// 		new_rhs_list.push_back ( bv_tmp);
// 		cout<<"input constant: "<<lhs[scan].toString()<<" rational constant: "<<tmp<<" bv constant: "<<bv_tmp<<endl;
// 	      }
// 	    else

// 	    // the operand is a variable multiplied by a constant
// 	    if( lhs[scan].getOpKind() == BVMULT )
// 	    {
// 	      if( lhs[scan][0].getOpKind() == BVCONST )
// 		{
// 		  Rational new_coeff = d_theoryBitvector->computeNegBVConst( lhs[scan][0] );
// 		  Expr bv_new_coeff = d_theoryBitvector->signed_newBVConstExpr( new_coeff, bv_size );
// 		  if( bv_new_coeff == BV_one)
// 		    new_rhs_list.push_back( lhs[scan][1]);
// 		  else
// 		    {
// 		      Expr bv_new_expr = d_theoryBitvector->newBVMultExpr( bv_size, bv_new_coeff, lhs[scan][1]);
// 		      new_rhs_list.push_back( bv_new_expr );
// 		    }
// 		}
// 	      else
// 		{
// 		  new_rhs_list.push_back( d_theoryBitvector->newBVUminusExpr( lhs[scan] ) );
// 		}
// 	    }
// 	    else
// 	      if( d_theoryBitvector->isLeaf( lhs[scan] ) )
// 		new_rhs_list.push_back( lhs[scan] );
// 	      else
// 		DebugAssert(0,
// 			    "BitvectorTheoremProducer::isolate_var: subterm of non implemented kind");

// 	}
//     }
//   for(unsigned int i=0; i < new_rhs_list.size(); i++)
//     cout<<"new_rhs_list["<<i<<"]: "<<new_rhs_list[i]<<endl;
//   if( new_rhs_list.size() > 1)
//     new_rhs =  d_theoryBitvector->newBVPlusExpr( bv_size, new_rhs_list);
//   else
//     new_rhs = new_rhs_list[0];

//   Expr expr_res;

// //   if( lhs[index] >= new_rhs)
// //     expr_res= Expr(EQ, lhs[index], new_rhs);
// //   else
// //     expr_res= Expr(EQ, new_rhs, lhs[index]);

// // L:: fix according to the new form for variables
//   new_lhs = lhs[solve_pos];
//   expr_res= Expr(EQ, new_lhs, new_rhs);
//   Proof pf= newPf("isolate var");
//   Theorem th_res= newRWTheorem( e, expr_res, Assumptions::emptyAssump(), pf);
//   cout<<"TheoryBitvector::isolate_var: result is: "<<expr_res.toString()<<endl;


//   return newRWTheorem( t.getExpr(), expr_res, Assumptions::emptyAssump(), pf);
//   //return d_theoryBitvector->iffMP( e, expr_res);
// }


Theorem BitvectorTheoremProducer::BVMult_order_subterms( const Expr& e )
{
  if (CHECK_PROOFS)
    CHECK_SOUND(e.getOpKind() == BVMULT,
		"BitvectorTheoremProducer::BVMult_order_vars: input must be a BVMULT expression" + e.toString());

  //  cout<<"BitvectorTheoremProducer::BVMult_order_subterms, e: "<<e.toString()<<endl;
  int bv_size= d_theoryBitvector->BVSize(e);
  Expr new_expr;
  vector<Expr> vars;

  // as the term has already been processed by BVcanon, a constant can
  // be just at the beginning of the term
  bool hasConst = false;
  if (e[0].getOpKind() == BVCONST) {
    d_theoryBitvector->extract_vars(e[1], vars);
    hasConst = true;
  }
  else {
    d_theoryBitvector->extract_vars(e, vars);
  }

  int vars_size = vars.size();
  ExprMap<int> vars_map;

  for( int i=0; i < vars_size; ++i)
    {
      //      cout<<"vars["<<i<<"]: "<<vars[i].toString()<<endl;
      // L:: we count how many times we found a variable
      if( vars_map.count( vars[i] ) == 0)
	vars_map[ vars[i] ] = 1;
      else
	vars_map[ vars[i] ] = vars_map[ vars[i] ] + 1;
    }
  // retrieving the variables from the map; the order of the variables
  // is like BVMULT(size, a, BVMULT(size, b, ...))  todo:: be careful
  // about the order in which variables are retrieved
  ExprMap<int>::iterator j = vars_map.begin();
  new_expr = (*j).first;
  if ((*j).second != 1) {
    for(int k=1; k < (*j).second; ++k) {
      new_expr = d_theoryBitvector->newBVMultExpr( bv_size, (*j).first, new_expr);
    }
  }

  for( ++j; j != vars_map.end(); ++j) {
    new_expr = d_theoryBitvector->newBVMultExpr( bv_size, (*j).first, new_expr);
    if ((*j).second != 1) {
      for(int k=1; k < (*j).second; ++k) {
        new_expr = d_theoryBitvector->newBVMultExpr( bv_size, (*j).first, new_expr);
      }
    }
  }

  Proof pf;
  if (withProof()) pf = newPf("BVMult_order_subterms");

  if (hasConst) {
    new_expr = d_theoryBitvector->newBVMultExpr( bv_size, e[0], new_expr);
  }

  Theorem result = newRWTheorem( e, new_expr, Assumptions::emptyAssump(), pf);
  return result;
}


// BVMULT(N, a\@b, y) = BVPLUS(N, BVMULT(N,b,y), BVMULT(N-n,a,y) \@ n-bit-0-string)
// where n = BVSize(b), a != 0, one of a or b is a constant
Theorem BitvectorTheoremProducer::liftConcatBVMult(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVMULT,
		"BitvectorTheoremProducer::liftConcatBVMult: input must be a BVMULT expression" + e.toString());
  }
  int bv_size = d_theoryBitvector->BVSize( e );
  vector<Expr> kids;
  int idx = -1;
  bool first = false;
  int i = 0;
  for (; i< e.arity(); ++i) {
    const Expr& kid = e[i];
    if (idx == -1 &&
        kid.getOpKind() == CONCAT) {
      if (kid[kid.arity()-1].getKind() == BVCONST) {
        idx = i;
      }
      else if (kid[0].getKind() == BVCONST &&
               d_theoryBitvector->computeBVConst(kid[0]) != 0) {
        idx = i;
        first = true;
      }
      else kids.push_back(kid);
    }
    else kids.push_back(kid);
  }
  if (idx == -1) return d_theoryBitvector->reflexivityRule(e);

  Expr concatHi, concatLo;

  if (first) {
    // Split concat at the first kid
    if (e[idx].arity() == 2) {
      concatLo = e[idx][1];
    }
    else {
      vector<Expr> concatKids;
      for (i = 1; i < e[idx].arity(); ++i) {
        concatKids.push_back(e[idx][i]);
      }
      concatLo = d_theoryBitvector->newConcatExpr(concatKids);
    }
    concatHi = e[idx][0];
  }
  else {
    // Split concat at the last kid
    vector<Expr> concatKids = e[idx].getKids();
    concatLo = concatKids.back();
    concatKids.pop_back();
    if (concatKids.size() == 1) {
      concatHi = concatKids[0];
    }
    else {
      concatHi = d_theoryBitvector->newConcatExpr(concatKids);
    }
  }

  int n = d_theoryBitvector->BVSize(concatLo);
  kids.push_back(concatLo);
  Expr bvMult1 = d_theoryBitvector->newBVMultPadExpr(bv_size, kids);
  kids.pop_back();
  kids.push_back(concatHi);
  Expr bvMult2 = d_theoryBitvector->newBVMultPadExpr(bv_size-n,kids);
  Expr newLowConcat = d_theoryBitvector->newBVZeroString(n);
  Expr newConcat = d_theoryBitvector->newConcatExpr(bvMult2, newLowConcat);
  Expr res_expr = d_theoryBitvector->newBVPlusExpr(bv_size, bvMult1, newConcat);

  Proof pf;
  if (withProof()) pf = newPf("liftConcatBVMult");
  return newRWTheorem(e, res_expr, Assumptions::emptyAssump(), pf);
}


// Let c * \prod_1^n a_i be the flattened BVMult term where c is a constant and each a_i cannot be:
//   a) const, b) bvuminus, c) bvplus, d) bvmult
// The canonical form is:
// 1. if c = 0, then 0
// 2. if c = 1 and n = 1 then a_1
// 3. else if c = 1 then \prod_1^n a_i
// 4. else c * \prod_1^n a_i
// Note that \prod should be ordered and made up of binary mult's

Theorem BitvectorTheoremProducer::canonBVMult( const Expr& e )
{
  TRACE("canonBVMult", "canonBVMult: {\n    ", e.toString(), " --");
  if (CHECK_PROOFS)
    CHECK_SOUND(e.getOpKind() == BVMULT,
		"BitvectorTheoremProducer::canonBVMult: input must be a BVMULT expression" + e.toString());

  //  cout<<"BitvectorTheoremProducer::canonBVMult, e:"<<e.toString()<<endl;
  int expr_arity = e.arity();
  int bv_size= d_theoryBitvector->BVSize(e);
  Theorem result;
  std::vector<Expr> mult_vars;
  Rational temp_coeff = 1;
  Expr new_expr;
  Expr no_minus_kid;
  Expr new_prod;
  Rational modulus = pow(Rational(bv_size), Rational(2));
  // separating all the constants and variables in the
  // multiplications

  for( int i = 0; i < expr_arity; ++i) {
    if (e[i].getOpKind() == BVUMINUS)	{
      temp_coeff = (temp_coeff * (modulus-1)) % modulus;
      no_minus_kid = e[i][0];
    } else no_minus_kid = e[i];

    switch (no_minus_kid.getOpKind()) {

      case BVCONST: {
        // Collect constants
        temp_coeff *= d_theoryBitvector->computeBVConst( no_minus_kid );
        temp_coeff = temp_coeff % modulus;
        break;
      }

      case BVMULT: {
        if (no_minus_kid[0].getOpKind() == BVCONST) {
          // collect coefficient and the variable
          temp_coeff *= d_theoryBitvector->computeBVConst(no_minus_kid[0]);
          temp_coeff = temp_coeff % modulus;
          DebugAssert(no_minus_kid[1].getOpKind() != BVCONST &&
                      no_minus_kid[1].getOpKind() != BVPLUS &&
                      no_minus_kid[1].getOpKind() != BVUMINUS,
                      "Expected canonized subterm");

          if (!new_prod.isNull()) {
            // multiply the kid by the product so far
            new_prod = d_theoryBitvector->newBVMultExpr( bv_size, new_prod, no_minus_kid[1]);
          }
          else
          {
            new_prod = no_minus_kid[1];
          }
        }
        else {
          if (!new_prod.isNull()) {
            // multiply the kid by the product so far
            new_prod = d_theoryBitvector->newBVMultExpr( bv_size, new_prod, no_minus_kid);
          }
          else
          {
            new_prod = no_minus_kid;
          }
        }
        break;
      }

      case BVPLUS: {
        result = distributive_rule( e );
        TRACE("canonBVMult", "--> ", result.getRHS().toString(), "\n}");
        return result;
      }

      default:
        if (!new_prod.isNull()) {
          // multiply the kid by the product so far
          new_prod = d_theoryBitvector->newBVMultExpr( bv_size, new_prod, no_minus_kid);
        }
        else
        {
          new_prod = no_minus_kid;
        }
    }
  }

  // producing the result
  if (temp_coeff == 0 || new_prod.isNull()) {
    // the variables found don't matter
    new_expr = d_theoryBitvector->newBVConstExpr(temp_coeff, bv_size);
  }
  else {
    if (new_prod.getOpKind() == BVMULT) {
      new_prod = BVMult_order_subterms(new_prod).getRHS();
    }
    ExprMap<Rational> sumHashMap;
    Rational known_term;
    Expr coeff_expr = d_theoryBitvector->newBVConstExpr(temp_coeff, bv_size);
    new_expr = d_theoryBitvector->newBVMultExpr(bv_size, coeff_expr, new_prod);
    getPlusTerms(new_expr, known_term, sumHashMap);
    new_expr = buildPlusTerm(bv_size, known_term, sumHashMap);
  }

  Proof pf;
  if (withProof()) pf = newPf("canonBVMult");
  result = newRWTheorem(e, new_expr, Assumptions::emptyAssump(), pf);
  TRACE("canonBVMult", "--> ", new_expr.toString(), "\n}");
  //  cout<<"BitvectorTheoremProducer::canonBVMult, e: "<<e.toString()<<" result: "<<result.toString()<<endl;
  return result;
}


// BVMULT(a,b) = X where X is the result of applying distributivity of BVMULT over BVPLUS
Theorem BitvectorTheoremProducer::distributive_rule( const Expr& e )
{
  if (CHECK_PROOFS)
    CHECK_SOUND(e.getOpKind() == BVMULT,
		"BitvectorTheoremProducer::distributive_rule: input must be a BVMULT expression" + e.toString());

  int bv_size= d_theoryBitvector->BVSize(e);

  // BVMULT terms have just two kids; at least one of the two must be
  // a BVPLUS

  vector<Expr> e0_kids, e1_kids, result_kids;

  if (e[0].getOpKind() == BVPLUS) {
    e0_kids = e[0].getKids();
  }
  else e0_kids.push_back(e[0]);

  if (e[1].getOpKind() == BVPLUS) {
    e1_kids = e[1].getKids();
  }
  else e1_kids.push_back(e[1]);

  unsigned e0_kids_size = e0_kids.size();
  unsigned e1_kids_size = e1_kids.size();
  for( unsigned i = 0; i < e0_kids_size; ++i) {
    for( unsigned j = 0; j < e1_kids_size; ++j) {
      Expr sum_term = d_theoryBitvector->newBVMultExpr ( bv_size, e0_kids[i], e1_kids[j] );
      result_kids.push_back( sum_term );
    }
  }
  Expr result_sum = d_theoryBitvector->newBVPlusExpr ( bv_size, result_kids);
  Proof pf;
  if (withProof()) pf = newPf("distributive rule");
  Theorem result = newRWTheorem( e, result_sum, Assumptions::emptyAssump(), pf);
  return result;
}


// BVPLUS(N, a0, ..., an) = BVPLUS(N-n,a0[N-1:n],...an[N-1:n])\@t
// where n = BVSize(t), and the sum of the lowest n bits of a0..an is exactly
// equal to t (i.e. no carry)
Theorem BitvectorTheoremProducer::liftConcatBVPlus(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVPLUS,
		"BitvectorTheoremProducer::liftConcatBVPlus: input must be a BVPLUS expression" + e.toString());
  }
  int bv_size = d_theoryBitvector->BVSize( e );
  vector<Expr> kids;
  int i = 0;
  Rational c = 0;

  if (e[0].getOpKind() == BVCONST) {
    ++i;
    c = d_theoryBitvector->computeBVConst(e[0]);
  }

  int chopSize = bv_size;

  bool nonzero = false;
  bool nonconst = false;
  Expr term;

  for (; i< e.arity(); ++i) {
    const Expr& kid = e[i];
    if (kid.getOpKind() != CONCAT) {
      return d_theoryBitvector->reflexivityRule(e);
    }
    Expr last = kid[kid.arity()-1];
    int size = d_theoryBitvector->BVSize(last);

    // If the last concat kid is not a constant, then our only hope is to chop
    // it off exactly and hope that all other last concat kids are equal to
    // 0 and wider (in bits) than last
    if (last.getOpKind() != BVCONST) {
      if (nonzero || size > chopSize) {
        return d_theoryBitvector->reflexivityRule(e);
      }
      nonzero = true;
      nonconst = true;
      chopSize = size;
      term = last;
      continue;
    }

    // If last is a zero-string, then we are OK, as long as it's at least as
    // wide as any nonconst we have encountered.  If it's less wide than the
    // constants we have encountered so far, reduce chopSize accordingly
    if (d_theoryBitvector->computeBVConst(last) == 0) {
      if (size >= chopSize) continue;
      if (nonconst) return d_theoryBitvector->reflexivityRule(e);
      chopSize = size;
      continue;
    }

    // If last is a nonzero const, it's OK as long as it is the only nonzero
    // thing we encounter
    if (nonzero) return d_theoryBitvector->reflexivityRule(e);
    nonzero = true;
    if (size < chopSize) chopSize = size;
    term = last;
  }

  // if nonzero exists, check the constant
  if (nonzero) {
    if (c != 0) {
      Rational modulus = pow(Rational(chopSize), Rational(2));
      if ((c % modulus) != 0) {
        return d_theoryBitvector->reflexivityRule(e);
      }
    }
  }
  else if (c == 0) {
    term = d_theoryBitvector->newBVZeroString(chopSize);
  }
  else {
    term = d_theoryBitvector->newBVExtractExpr(e[0], chopSize-1, 0);
  }

  vector<Expr> newKids;
  for (i = 0; i < e.arity(); ++i) {
    newKids.push_back(d_theoryBitvector->newBVExtractExpr(e[i], bv_size-1, chopSize));
  }

  Expr bvPlus = d_theoryBitvector->newBVPlusExpr(bv_size-chopSize, newKids);
  if (d_theoryBitvector->BVSize(term) > chopSize) {
    term = d_theoryBitvector->newBVExtractExpr(term, chopSize-1, 0);
  }

  Expr res_expr = d_theoryBitvector->newConcatExpr(bvPlus, term);

  Proof pf;
  if (withProof()) pf = newPf("liftConcatBVPlus");
  return newRWTheorem(e, res_expr, Assumptions::emptyAssump(), pf);
}


void BitvectorTheoremProducer::getPlusTerms(const Expr& e, Rational& known_term,
                                            ExprMap<Rational>& sumHashMap)
{
  int bv_size = d_theoryBitvector->BVSize( e );
  Rational modulus = pow(Rational(bv_size), Rational(2));
  unsigned i;
  vector<Expr> plusTerms;
  vector<Rational> coeffs;

  plusTerms.push_back(e);
  coeffs.push_back(1);
  known_term = 0;

  for(i = 0; i < plusTerms.size(); ++i) {
    Expr kid = plusTerms[i];
    int kidSize = d_theoryBitvector->BVSize(kid);
    DebugAssert(kidSize <= bv_size, "Expected kid no wider than bv_size");
    Rational coeff = coeffs[i];
    if (coeff == 0) continue;

    switch (kid.getOpKind()) {

      case BVCONST:
        known_term += coeff * d_theoryBitvector->computeBVConst( kid );
        known_term = known_term % modulus;
        break;

      case BVUMINUS:
        DebugAssert(kidSize == bv_size, "Unexpected size for uminus");
        plusTerms.push_back(plusTerms[i][0]);
        coeffs.push_back((coeff * (modulus - 1)) % modulus);
        break;

      case BVNEG:
        if (kidSize < bv_size) {
          Rational m2 = pow(Rational(kidSize), Rational(2));
          known_term += coeff * (m2-1);
        }
        else {
          known_term += coeff * (modulus-1);
        }
        known_term = known_term % modulus;
        plusTerms.push_back(plusTerms[i][0]);
        coeffs.push_back((coeff * (modulus-1)) % modulus);
        break;

      case BVMULT:
        if (kidSize < bv_size) {
          int shift = 0;
          Rational tcoeff = coeff;
          for (; tcoeff % 2 == 0; ++shift, tcoeff = tcoeff / 2);
          if (shift + kidSize < bv_size) {
            // can't combine different sizes--
            // just insert it as is
            sumHashMap[ kid ] = sumHashMap[ kid ] + coeff;
            break;
          }
        }
        // OK to combine sizes
        if( kid[0].getOpKind() == BVCONST )
        {
          DebugAssert(kid.arity() == 2, "Expected arity 2 BVMULT");
          plusTerms.push_back(kid[1]);
          coeffs.push_back((coeff * d_theoryBitvector->computeBVConst(kid[0])) % modulus);
        }
        else
        {
          sumHashMap[ kid ] = sumHashMap[ kid ] + coeff;
        }
        break;

      case BVPLUS: {
        if (kidSize < bv_size) {
          int shift = 0;
          Rational tcoeff = coeff;
          for (; tcoeff % 2 == 0; ++shift, tcoeff = tcoeff / 2);
          if (shift + kidSize < bv_size) {
            // can't combine BVPLUSes of different size--
            // just insert it as is
            sumHashMap[ kid ] = sumHashMap[ kid ] + coeff;
            break;
          }
        }
        // OK to combine BVPLUS terms
        int kid_arity = kid.arity();
        for(int j = 0; j < kid_arity; ++j) {
          plusTerms.push_back(kid[j]);
          coeffs.push_back(coeff);
        }
        break;
      }

      case CONCAT: {
        // Convert CONCAT to BVPLUS
        int n = d_theoryBitvector->BVSize(kid);
        Rational concatConst;
        for (int j = 0; j < kid.arity(); ++j) {
          const Expr& concatKid = kid[j];
          n -= d_theoryBitvector->BVSize(concatKid);
          concatConst = pow(Rational(n), Rational(2)) * coeff;
          plusTerms.push_back(concatKid);
          coeffs.push_back(concatConst % modulus);
        }
        break;
      }

      case EXTRACT: {
        // TODO: maybe re-enable this in some cases, but it leads to simplification loops
        if (false && kidSize < bv_size) {
          // If the top part of a term is cut off with an extract, try to put it back
          const Expr& ext_kid = kid[0];
          int size = d_theoryBitvector->BVSize(ext_kid);
          int extractLeft = d_theoryBitvector->getExtractHi(kid);
          if (extractLeft < size-1) {
            int shift = 0;
            Rational tcoeff = coeff;
            for (; tcoeff % 2 == 0; ++shift, tcoeff = tcoeff / 2);
            if (shift + kidSize >= bv_size) {
              int bitsToAdd = bv_size - kidSize;
              extractLeft += bitsToAdd;
              if (extractLeft > size - 1) extractLeft = size - 1;
              int extractRight = d_theoryBitvector->getExtractLow(kid);
              if (extractLeft == size-1 && extractRight == 0) {
                plusTerms.push_back(ext_kid);
                coeffs.push_back(coeff);
              }
              else {
                plusTerms.push_back(d_theoryBitvector->newBVExtractExpr(ext_kid, extractLeft, extractRight));
                coeffs.push_back(coeff);
              }
              break;
            }
          }
          else {
            DebugAssert(d_theoryBitvector->getExtractLow(kid) != 0,
                        "Unexpected extract bounds");
          }
        }
        // fall through
      }

      default:
        sumHashMap[ kid] = sumHashMap[ kid] + coeff;
        break;
    }
  }
}


Expr BitvectorTheoremProducer::chopConcat(int bv_size, Rational c,
                                          vector<Expr>& concatKids)
{
  int chopSize = bv_size;

  bool nonzero = false;
  bool nonconst = false;
  Expr term, kid, last;
  int size;
  unsigned i;

  for (i = 0; i< concatKids.size(); ++i) {
    kid = concatKids[i];
    if (kid.getOpKind() != CONCAT) return Expr();

    last = kid[kid.arity()-1];
    size = d_theoryBitvector->BVSize(last);

    // If the last concat kid is not a constant, then our only hope is to chop
    // it off exactly and hope that all other last concat kids are equal to
    // 0 and wider (in bits) than last
    if (last.getOpKind() != BVCONST) {
      if (nonzero || size > chopSize) return Expr();
      nonzero = true;
      nonconst = true;
      chopSize = size;
      term = last;
      continue;
    }

    // If last is a zero-string, then we are OK, as long as it's at least as
    // wide as any nonconst we have encountered.  If it's less wide than the
    // constants we have encountered so far, reduce chopSize accordingly
    if (d_theoryBitvector->computeBVConst(last) == 0) {
      if (size >= chopSize) continue;
      if (nonconst) return Expr();
      chopSize = size;
      continue;
    }

    // If last is a nonzero const, it's OK as long as it is the only nonzero
    // thing we encounter
    if (nonzero) return Expr();
    nonzero = true;
    if (size < chopSize) chopSize = size;
    term = last;
  }

  Rational modulus = pow(Rational(chopSize), Rational(2));

  // if nonzero exists, check the constant
  if (nonzero) {
    if (c != 0) {
      if ((c % modulus) != 0) return Expr();
      c = c / modulus;
    }
  }
  else if (c == 0) {
    term = d_theoryBitvector->newBVZeroString(chopSize);
  }
  else {
    Rational value = c % modulus;
    term = d_theoryBitvector->newBVConstExpr(value, chopSize);
    c = c - value;
    c = c / modulus;
  }

  // Now chop them
  for (i = 0; i < concatKids.size(); ++i) {
    kid = concatKids[i];
    vector<Expr> kids = kid.getKids();
    last = kids.back();
    kids.pop_back();
    size = d_theoryBitvector->BVSize(last);

    if (size != chopSize) {
      DebugAssert(size > chopSize, "Expected last to be wider than chopSize");
      DebugAssert(last.getOpKind() == BVCONST, "Expected last kind = BVCONST");
      Rational value = d_theoryBitvector->computeBVConst(last);
      if (value != 0) {
        value = value - (value % modulus);
        value = value / modulus;
      }
      kids.push_back(d_theoryBitvector->newBVConstExpr(value, size - chopSize));
    }
    DebugAssert(kids.size() > 0, "Expected size > 0");
    if (kids.size() == 1) {
      concatKids[i] = kids[0];
    }
    else {
      concatKids[i] = d_theoryBitvector->newConcatExpr(kids);
    }
  }

  if (d_theoryBitvector->BVSize(term) > chopSize) {
    DebugAssert(term.getOpKind() == BVCONST, "Expected BVCONST");
    Rational value = d_theoryBitvector->computeBVConst(term);
    DebugAssert(value != 0, "Expected 0");
    value = value % modulus;
    term = d_theoryBitvector->newBVConstExpr(value, chopSize);
  }

  Expr bvPlus = chopConcat(bv_size-chopSize, c, concatKids);
  if (!bvPlus.isNull()) {
    DebugAssert(bvPlus.getOpKind() == CONCAT, "Expected CONCAT");
    vector<Expr> kids = bvPlus.getKids();
    kids.push_back(term);
    return d_theoryBitvector->newConcatExpr(kids);
  }

  vector<Expr> newKids;
  if (c != 0) {
    newKids.push_back(d_theoryBitvector->newBVConstExpr(c, bv_size - chopSize));
  }
  for (i = 0; i < concatKids.size(); ++i) {
    newKids.push_back(concatKids[i]);
  }
  DebugAssert(newKids.size() > 1, "Expected more than one kid");
  bvPlus = d_theoryBitvector->newBVPlusExpr(bv_size-chopSize, newKids);

  // Make sure bvPlus is canonized
  ExprMap<Rational> sumHashMap;
  Rational known_term;
  getPlusTerms(bvPlus, known_term, sumHashMap);
  bvPlus = buildPlusTerm(bv_size-chopSize, known_term, sumHashMap);
  return d_theoryBitvector->newConcatExpr(bvPlus, term);
}


Expr BitvectorTheoremProducer::buildPlusTerm(int bv_size,
                                             Rational& known_term,
                                             ExprMap<Rational>& sumHashMap)
{
  // Try to convert into CONCATs
  Rational modulus = pow(Rational(bv_size), Rational(2));
  Rational coeff, pos;
  Rational tmask, tcoeff, marked = 0;
  int nbits, lg;
  ExprMap<Rational>::iterator j = sumHashMap.begin();
  vector<Expr> multKids, concatKids;
  unsigned i;
  for(; j != sumHashMap.end(); ++j) {
    coeff = mod((*j).second, modulus);
    Expr term = (*j).first;
    nbits = d_theoryBitvector->BVSize(term);

    // Fast case: coeff is 1 and term takes up all the bits
    if (coeff == 1 && nbits == bv_size) {
      if (nbits == 1 && known_term == 1) {
        // rewrite 1-bit x + 1 as ~x
        multKids.push_back(d_theoryBitvector->newBVNegExpr(term));
        known_term = 0;
      }
      else {
        multKids.push_back(term);
      }
      continue;
    }

    while (coeff != 0) {

      for (pos = coeff, lg = 0; pos % 2 == 0; pos = pos / 2, ++lg);
      pos = pow(Rational(lg), Rational(2));          // Position of lsb containing a 1

      Expr concatTerm;

      // pos of first bit beyond term
      Rational tmodulus = modulus;
      if (nbits+lg < bv_size) tmodulus = pow(Rational(nbits+lg), Rational(2));
      Rational tcoeff = coeff % tmodulus;

      if (tcoeff == pos) {
        coeff -= tcoeff;
        concatTerm = term;
      }
      else if (((tcoeff + pos) % tmodulus) == 0) {
        coeff = (coeff + pos) % modulus;
        // rewrite as bvneg
        concatTerm = d_theoryBitvector->newBVNegExpr(term);
        known_term += pos;
        if (nbits + lg < bv_size) {
          known_term += (modulus - tmodulus);
        }
        if (pos == 1 && nbits == bv_size) {
          multKids.push_back(concatTerm);
          continue;
        }
      }
      else {
        // create a BVMULT
        if (nbits + lg > bv_size) {
          // term is too big: chop it off
          int diff = nbits + lg - bv_size;
          int high, low;
          if (term.getOpKind() == EXTRACT) {
            // Collapse extract of extract
            high = d_theoryBitvector->getExtractHi(term) - diff;
            low = d_theoryBitvector->getExtractLow(term);
            term = term[0];
          }
          else {
            high = nbits - 1 - diff;
            low = 0;
          }
          term = d_theoryBitvector->newBVExtractExpr(term, high, low);
        }
        nbits = bv_size - lg;
        coeff = coeff / pos;
        Expr new_coeff = d_theoryBitvector->newBVConstExpr(coeff, nbits);
        term = d_theoryBitvector->newBVMultPadExpr(nbits, new_coeff, term);
        coeff = 0;
        if (lg == 0) {
          multKids.push_back(term);
          continue;
        }
        concatTerm = term;
      }

      // Insert concatTerm at position lg into a CONCAT
      bool found = false;
      Expr t;
      vector<Expr> tmp;
      int bits, size, k, t_arity;
      for (i = 0; i < concatKids.size(); ++i) {
        t = concatKids[i];
        DebugAssert(t.getOpKind() == CONCAT, "Expected CONCAT");
        bits = bv_size;
        t_arity = t.arity();
        for (k = 0; k < t_arity; ++k) {
          if (k > 0 && bits < lg + nbits) break;
          size = d_theoryBitvector->BVSize(t[k]);
          if (bits - size <= lg) {
            if (t[k].getOpKind() == BVCONST) {
              found = true;
            }
            break;
          }
          else {
            tmp.push_back(t[k]);
            bits -= size;
          }
        }
        if (found) break;
        tmp.clear();
      }
      if (!found) {
        bits = bv_size;
        size = bv_size;
        k = t_arity = 0;
      }
      if (lg + nbits < bits) {
        tmp.push_back(d_theoryBitvector->newBVZeroString(bits-(lg+nbits)));
      }
      if (lg + nbits > bits) {
        bool negate = false;
        if (concatTerm.getOpKind() == BVNEG) {
          // Push extract inside negation
          negate = true;
          concatTerm = concatTerm[0];
        }
        DebugAssert(!found || k == 0,
                    "Too big only OK for first child");
        // If term is too big, chop it off
        int diff = lg + nbits - bits;
        int high, low;
        if (concatTerm.getOpKind() == EXTRACT) {
          // Collapse extract of extract
          high = d_theoryBitvector->getExtractHi(concatTerm) - diff;
          low = d_theoryBitvector->getExtractLow(concatTerm);
          concatTerm = concatTerm[0];
        }
        else {
          high = nbits - 1 - diff;
          low = 0;
        }
        concatTerm = d_theoryBitvector->newBVExtractExpr(concatTerm, high, low);
        if (negate) {
          concatTerm = d_theoryBitvector->newBVNegExpr(concatTerm);
        }
      }
      tmp.push_back(concatTerm);
      bits -= size;
      if (lg > bits) {
        tmp.push_back(d_theoryBitvector->newBVZeroString(lg-bits));
      }
      for (++k; k < t_arity; ++k) {
        tmp.push_back(t[k]);
      }

      if (tmp.size() == 1) {
        DebugAssert(!found, "Invariant violated");
        multKids.push_back(tmp[0]);
      }
      else if (found) {
        // replace existing concat term
        concatKids[i] = d_theoryBitvector->newConcatExpr(tmp);
      }
      else {
        // push back new concat term
        concatKids.push_back(d_theoryBitvector->newConcatExpr(tmp));
      }
    }
  }

  known_term = known_term % modulus;

  // See if we can merge constant in with CONCATs
  if (known_term != 0 && !concatKids.empty()) {
    vector<Expr> tmp;
    for (i = 0; i < concatKids.size(); ++i) {
      Expr t = concatKids[i];
      DebugAssert(t.getOpKind() == CONCAT, "Expected CONCAT");
      int bits = bv_size;
      int size;
      bool anyChanged = false;
      for (int k = 0; k < t.arity(); ++k) {
        size = d_theoryBitvector->BVSize(t[k]);
        bool changed = false;
        if (known_term != 0 && t[k].getOpKind() == BVCONST) {
          Rational high = pow(Rational(bits), Rational(2));
          Rational partConst = known_term % high;
          if (partConst != 0) {
            Rational low = pow(Rational(bits - size), Rational(2));
            partConst = partConst - (partConst % low);
            if (partConst != 0) {
              anyChanged = changed = true;
              tmp.push_back(d_theoryBitvector->newBVConstExpr(partConst / low, size));
              known_term -= partConst;
            }
          }
        }
        if (!changed) {
          tmp.push_back(t[k]);
        }
        bits -= size;
      }
      if (anyChanged) {
        concatKids[i] = d_theoryBitvector->newConcatExpr(tmp);
        if (known_term == 0) break;
      }
      tmp.clear();
    }
  }

  // reassembling terms into a unique BVPLUS expression
  Expr expr_result;

  // Check to see if we can chop off the bottom of the BVPLUS
  if (multKids.size() == 0 &&
      (concatKids.size() > 1 ||
       (concatKids.size() == 1 && known_term != 0))) {
    expr_result = chopConcat(bv_size, known_term, concatKids);
    if (!expr_result.isNull()) return expr_result;
  }

  if (known_term == 0) {
    for (i = 0; i < concatKids.size(); ++i) {
      multKids.push_back(concatKids[i]);
    }
    if (multKids.size() == 0) {
      expr_result = d_theoryBitvector->newBVConstExpr( Rational(0), bv_size);
    }
    else if (multKids.size() == 1) {
      expr_result = multKids[0];
    }
    else {
      expr_result = d_theoryBitvector->newBVPlusExpr( bv_size, multKids);
    }
  }
  else {
    vector<Expr> sumKids;
    sumKids.push_back( d_theoryBitvector->newBVConstExpr( known_term, bv_size));
    for (i = 0; i < multKids.size(); ++i) {
      sumKids.push_back(multKids[i]);
    }
    for (i = 0; i < concatKids.size(); ++i) {
      sumKids.push_back(concatKids[i]);
    }
    if (sumKids.size() == 1) {
      expr_result = sumKids[0];
    }
    else {
      expr_result = d_theoryBitvector->newBVPlusExpr( bv_size, sumKids);
    }
  }
  return expr_result;
}


// It assumes that all the kids have already been canonized
Theorem BitvectorTheoremProducer::canonBVPlus( const Expr& e )
{
  TRACE("canonBVPlus", "canonBVPlus: {\n    ", e.toString(), " --");

  if (CHECK_PROOFS)
    CHECK_SOUND(e.getOpKind() == BVPLUS,
		"BitvectorTheoremProducer::canonBVPlus: input must be a BVPLUS expression" + e.toString());

  //  cout<<"BitvectorTheoremProducer::canonBVPlus, e is: "<<e.toString()<<endl;
  //! L:: to store the sum of the coefficients for each var
  ExprMap<Rational> sumHashMap;
  int bv_size = d_theoryBitvector->BVSize( e );
  Rational known_term;

  // Get plus terms in a hash map
  getPlusTerms(e, known_term, sumHashMap);

  // Build the plus term from known_term, sumHashMap
  Expr expr_result = buildPlusTerm(bv_size, known_term, sumHashMap);

  Proof pf;
  if (withProof()) pf = newPf("canonBVPlus");
  Theorem result = newRWTheorem( e, expr_result, Assumptions::emptyAssump(), pf);
  TRACE("canonBVPlus", "--> ", expr_result.toString(), "\n}");
  return result;
}


Theorem BitvectorTheoremProducer::canonBVUMinus( const Expr& e )
{
  if (CHECK_PROOFS)
    CHECK_SOUND(e.getOpKind() == BVUMINUS,
		"BitvectorTheoremProducer::canonBVUMinus: input must be a BVUMINUS expression" + e.toString());

  int bv_size = d_theoryBitvector->BVSize(e);
  Rational modulus = pow(Rational(bv_size), Rational(2));
  Expr coeff = d_theoryBitvector->newBVConstExpr(modulus-1, bv_size);
  Expr res_expr = d_theoryBitvector->newBVMultExpr(bv_size, coeff, e[0]);
  Proof pf;
  if (withProof()) pf = newPf("canonBVUMinus");
  return newRWTheorem(e, res_expr, Assumptions::emptyAssump(), pf);
}
/*End of Lorenzo PLatania's methods*/


// Input: t[hi:lo] = rhs
// if t appears as leaf in rhs, then:
//    t[hi:lo] = rhs |- Exists x,y,z. (t = x \@ y \@ z AND y = rhs), solvedForm = false
// else
//    t[hi:lo] = rhs |- Exists x,z. (t = x \@ rhs \@ z), solvedForm = true
Theorem BitvectorTheoremProducer::processExtract(const Theorem& e, bool& solvedForm)
{
  Expr expr = e.getExpr();

  if (CHECK_PROOFS) {
    CHECK_SOUND(expr.getOpKind() == EQ && expr[0].getOpKind() == EXTRACT,
                "BitvectorTheoremProducer::processExtract: invalid input");
    CHECK_SOUND(d_theoryBitvector->BVSize(expr[0]) == d_theoryBitvector->BVSize(expr[1]),
                "Expected same size");
  }

  Expr ext = expr[0];
  Expr lhs;
  Expr rhs = expr[1];
  Expr child = ext[0];
  int size = d_theoryBitvector->BVSize(child);
  int high = d_theoryBitvector->getExtractHi(ext);
  int low  = d_theoryBitvector->getExtractLow(ext);

  DebugAssert(d_theoryBitvector->isLeaf(child), "Expected leaf");
  solvedForm = !d_theoryBitvector->isLeafIn(child, rhs);

  vector<Expr> terms;
  vector<Expr> boundVars;
  if (high < size-1) {
    terms.push_back(d_theoryBitvector->getEM()->newBoundVarExpr(d_theoryBitvector->newBitvectorType(size-1-high)));
    boundVars.push_back(terms.back());
  }
  if (solvedForm) terms.push_back(rhs);
  else {
    lhs = d_theoryBitvector->getEM()->newBoundVarExpr(d_theoryBitvector->newBitvectorType(high-low+1));
    terms.push_back(lhs);
    boundVars.push_back(lhs);
  }
  if (low > 0) {
    terms.push_back(d_theoryBitvector->getEM()->newBoundVarExpr(d_theoryBitvector->newBitvectorType(low)));
    boundVars.push_back(terms.back());
  }
  DebugAssert(terms.size() > 1, "Expected at least two terms");
  Expr result = child.eqExpr(d_theoryBitvector->newConcatExpr(terms));
  if (!solvedForm) result = result && lhs.eqExpr(rhs);
  result = d_theoryBitvector->getEM()->newClosureExpr(EXISTS, boundVars, result);
  Assumptions a(e);
  Proof pf;
  if (withProof()) pf = newPf("processExtract");
  return newTheorem(result, a, pf);
}

bool BitvectorTheoremProducer::okToSplit(const Expr& e)
{
  if (d_theoryBitvector->isLeaf(e)) return true;
  switch (e.getOpKind()) {
    case BVCONST:
    case EXTRACT:
    case BVAND:
    case BVOR:
    case BVXOR:
    case BVNEG:
      return true;
    case BVSHL:
    case BVLSHR:
    case BVASHR:
    case BVPLUS:
    case BVMULT:
    case BVUDIV:
    case BVSDIV:
    case BVUREM:
    case BVSREM:
    case BVSMOD:
      return false;
    default:
      FatalAssert(false, "unexpected kind in okToSplit");
      break;
  }
  return false;
}


// puts the equation in solved form if possible, otherwise in the form
// \sum a_i*x_i +c = 0.
// default maxEffort is 3: solves only when lhs can be isolated without splitting
// maxEffort 5: solves when lhs can be isolated with splitting
// maxEffort 6: solves even when result is not in solved form (good for bitblasting)
Theorem BitvectorTheoremProducer::canonBVEQ( const Expr& e, int maxEffort )
{
  TRACE("canonBVEQ", "canonBVEQ: {\n    ", e.toString(), " --");
  DebugAssert(maxEffort == 3 || maxEffort == 5 || maxEffort == 6,
              "Unexpected value for maxEffort");
  if(CHECK_PROOFS) {
    CHECK_SOUND( e.getOpKind() == EQ,
                 "BitvectorTheoremProducer::canonBVEQ: expression must be an equation");
    CHECK_SOUND(BITVECTOR==e[0].getType().getExpr().getOpKind(),
		"input must be a bitvector eqn. \n e = " + e.toString());
  }

  Expr lhs = e[0];
  Expr rhs = e[1];
  int bv_size = d_theoryBitvector->BVSize( lhs );

  // Look for easy split of concats
  if (lhs.getOpKind() == CONCAT || rhs.getOpKind() == CONCAT) {
    Expr::iterator lit, rit;
    int lsize, rsize;
    if (lhs.getOpKind() == CONCAT) {
      lit = e[0].begin();
    }
    else {
      lit = e.begin();
    }
    if (rhs.getOpKind() == CONCAT) {
      rit = e[1].begin();
    }
    else {
      rit = e.begin();
      ++rit;
    }
    int splitSize;
    lsize = d_theoryBitvector->BVSize(*lit);
    rsize = d_theoryBitvector->BVSize(*rit);
    while (true) {
      DebugAssert(lsize <= bv_size && rsize <= bv_size, "invariant violated");
      if (lsize < rsize) {
        if (okToSplit(*rit)) {
          splitSize = lsize;
          break;
        }
        else {
          ++lit;
          lsize += d_theoryBitvector->BVSize(*lit);
        }
      }
      else if (lsize > rsize) {
        if (okToSplit(*lit)) {
          splitSize = rsize;
          break;
        }
        else {
          ++rit;
          rsize += d_theoryBitvector->BVSize(*rit);
        }
      }
      else {
        splitSize = lsize;
        break;
      }
    }
    if (splitSize != bv_size) {
      Proof pf;
      if (withProof()) pf = newPf("canonBVEQ");
      Expr tmp = d_theoryBitvector->newBVExtractExpr(lhs, bv_size-1, bv_size-splitSize);
      tmp = tmp.eqExpr(d_theoryBitvector->newBVExtractExpr(rhs, bv_size-1, bv_size-splitSize));
      Expr expr_result = d_theoryBitvector->newBVExtractExpr(lhs, bv_size-splitSize-1, 0);
      expr_result = expr_result.eqExpr(d_theoryBitvector->newBVExtractExpr(rhs, bv_size-splitSize-1, 0));
      expr_result = tmp && expr_result;
      TRACE("canonBVEQ", "--> ", expr_result.toString(), "\n}");
      return newRWTheorem( e, expr_result, Assumptions::emptyAssump(), pf);
    }
  }

  rhs = d_theoryBitvector->newBVUminusExpr(rhs);
  ExprMap<Rational> sumHashMap;
  Rational modulus = pow(Rational(bv_size), Rational(2));
  Rational known_term;

  getPlusTerms(d_theoryBitvector->newBVPlusExpr(bv_size, lhs, rhs), known_term, sumHashMap);

  // Loop through all terms and perform two tasks:
  // A. Truncate coefficients
  // B. Look for a something to solve for:
  //    1. first choice: full-sized leaf not occurring elsewhere
  //    2. second choice: full-sized leaf inside BVXOR not occurring elsewhere
  //    3. third choice: full-sized extract of a leaf or over-sized leaf or extract of leaf
  //    4. fourth choice: under-sized leaf not occurring elsewhere or extract of leaf
  //    5. fifth choice: even-coeff leaf not occurring elsewhere or extract of leaf
  //    6. sixth choice: first term with an odd coeff (even if not a leaf or occurring elsewhere)
  //    7. seventh choice: nothing to solve for and all coeffs are even

  // If choice > maxEffort (and not 7), put in form sum = 0 instead.

  Rational coeff, foundCoeff = 1;
  ExprMap<Rational>::iterator j = sumHashMap.begin();
  ExprMap<Rational>::iterator fixCoeff = j;
  Expr xor_leaf, leaf, foundterm;
  unsigned xor_idx=0, xor_size=0;
  int priority, size, foundpriority = 7;
  bool isExtract;
  for(; j != sumHashMap.end(); ++j) {
    Expr t = (*j).first;
    coeff = (*j).second;
    size = d_theoryBitvector->BVSize(t);
    if (j == fixCoeff) {
      coeff = (*j).second = mod(coeff, modulus);
      ++fixCoeff;
    }
    if (coeff == 0) continue;

    priority = 7;
    isExtract = false;
    if (coeff % 2 == 1) {
      if (d_theoryBitvector->isLeaf(t)) {
        if (size == bv_size) {
          leaf = t; priority = 1;
        } else if (size > bv_size) {
          isExtract = true;
          leaf = t; priority = 3;
        } else {
          leaf = t; priority = 4;
        }
      } else if (t.getOpKind() == EXTRACT &&
                 d_theoryBitvector->isLeaf(t[0])) {
        isExtract = true;
        if (size >= bv_size) {
          leaf = t[0]; priority = 3;
        } else {
          leaf = t[0]; priority = 4;
        }
      } else if (t.getOpKind() == BVXOR && size == bv_size) {
        if (foundpriority == 2) continue;
        xor_idx = 0;
        xor_size = t.arity();
        for (xor_idx = 0; xor_idx < xor_size; ++xor_idx) {
          if (!d_theoryBitvector->isLeaf(t[xor_idx])) {
            continue;
          }
          unsigned l = 0;
          for (; l < xor_size; ++l) {
            if (l == xor_idx) continue;
            if (d_theoryBitvector->isLeafIn(t[xor_idx], t[l])) break;
          }
          if (l < xor_size) continue;
          break;
        }
        if (xor_idx < xor_size) {
          leaf = t[xor_idx];
          xor_leaf = leaf;
          priority = 2;
        }
        else {
          leaf = t; priority = 6;
        }
      }
      else {
        leaf = t; priority = 6;
      }
    } else if (maxEffort >= 5) {
      if (d_theoryBitvector->isLeaf(t)) {
        leaf = t; priority = 5;
      } else if (t.getOpKind() == EXTRACT &&
                 d_theoryBitvector->isLeaf(t[0])) {
        isExtract = true;
        leaf = t[0]; priority = 5;
      }
    }

    if (priority < foundpriority) {
      if (priority < 6) {
        ExprMap<Rational>::iterator k = sumHashMap.begin();
        while (k != sumHashMap.end()) {
          if (j == k) {
            ++k; continue;
          }
          if (k == fixCoeff) {
            (*k).second = mod((*k).second, modulus);
            ++fixCoeff;
          }
          if ((*k).second == 0) {
            ++k; continue;
          }
          if (!isExtract && d_theoryBitvector->isLeafIn(leaf, (*k).first)) {
            if (priority == 2) {
              // Try to find another leaf in the BVXOR
              for (++xor_idx; xor_idx < xor_size; ++xor_idx) {
                if (!d_theoryBitvector->isLeaf(t[xor_idx])) {
                  continue;
                }
                unsigned l = 0;
                for (; l < xor_size; ++l) {
                  if (l == xor_idx) continue;
                  if (d_theoryBitvector->isLeafIn(t[xor_idx], t[l])) break;
                }
                if (l < xor_size) continue;
                break;
              }
              if (xor_idx < xor_size) {
                // found a leaf, continue checking it
                leaf = t[xor_idx];
                xor_leaf = leaf;
                k = sumHashMap.begin();
                continue;
              }
            }
            // this leaf cannot be solved for
            break;
          }
          ++k;
        }
        if (k == sumHashMap.end()) {
          foundpriority = priority;
          foundterm = t;
          if (coeff == 1 || priority == 5) foundCoeff = 1;
          else foundCoeff = d_theoryBitvector->multiplicative_inverse(coeff, bv_size);
          if (priority == 1) break;
        }
      }
      if (foundpriority > 6 && priority != 5) {
        foundpriority = 6;
        foundterm = t;
        if (coeff == 1) foundCoeff = 1;
        else foundCoeff = d_theoryBitvector->multiplicative_inverse(coeff, bv_size);
      }
    }
  }

  bool solving = (foundpriority <= maxEffort);

  if (foundpriority == 7) {
    // All coeffs are even
    if (known_term % 2 == 1) {
      Proof pf;
      if (withProof()) pf = newPf("canonBVEQ");
      TRACE("canonBVEQ", "--> ", d_theoryBitvector->falseExpr().toString(), "\n}");
      return newRWTheorem(e, d_theoryBitvector->falseExpr(), Assumptions::emptyAssump(), pf);
    }
    else foundCoeff = foundCoeff / Rational(2);
    if (bv_size > 1) {
      bv_size = bv_size - 1;
      modulus = pow(Rational(bv_size), Rational(2));
    }
  }
  else if (!solving && (e[1] == d_theoryBitvector->newBVZeroString(bv_size))) {
    // if we aren't solving, and rhs was already 0, then stop here: lhs already normalized by plus canonizer
    // further rewriting risks a simplification loop
    TRACE("canonBVEQ", "--> ", e, "\n}");
    return newReflTheorem(e);
  }

  Rational solveCoeff = 0;
  // Multiply through by foundCoeff if it is not 1
  // Also, multiply by -1 (i.e. subtract from modulus) if solving
  if (solving || foundCoeff != 1) {
    known_term = (known_term * foundCoeff) % modulus;
    if (solving && known_term != 0)
      known_term = modulus - known_term;
    for(j = sumHashMap.begin(); j != sumHashMap.end(); ++j) {
      coeff = (*j).second;
      if (coeff == 0) continue;
      (*j).second = (coeff * foundCoeff) % modulus;
      if (solving) {
        if ((*j).first == foundterm) {
          // remove the leaf being solved for
          solveCoeff = (*j).second;
          (*j).second = 0;
        }
        else {
          (*j).second = modulus - (*j).second;
        }
      }
    }
  }

  // Collect the terms for the new bitplus term
  Expr plusTerm = buildPlusTerm(bv_size, known_term, sumHashMap);

  Expr new_lhs, new_rhs, expr_result;
  // Solve the equation
  if (solving) {
    DebugAssert(solveCoeff != 0, "Expected solveCoeff != 0");
    if (foundpriority == 6 && d_theoryBitvector->BVSize(foundterm) < bv_size) {
      // zero-extend to get the right size
      foundterm = d_theoryBitvector->pad(bv_size, foundterm);
    }
    switch (foundpriority) {
      case 1:
        // 1. first choice: full-sized leaf
        // foundterm is full-sized leaf
      case 6:
        //  6. sixth choice: Not in solved form, but isolate first term
        //  with odd coeff on lhs anyway.
        DebugAssert(solveCoeff == 1, "Expected coeff = 1");
        new_lhs = foundterm;
        new_rhs = plusTerm;
        break;
      case 2: {
        // 2. second choice: leaf inside BVXOR
        DebugAssert(solveCoeff == 1, "Expected coeff = 1");
        vector<Expr> rhsTerms;
        rhsTerms.push_back(plusTerm);
        for (unsigned l = 0; l < xor_size; ++l) {
          if (l == xor_idx) continue;
          rhsTerms.push_back(foundterm[l]);
        }
        new_lhs = xor_leaf;
        new_rhs = d_theoryBitvector->newBVXorExpr(rhsTerms);
        break;
      }
      case 3:
        // 3. third choice: full-sized extract of a leaf or over-sized leaf or extract of leaf
        // foundterm is full-sized extract of leaf
        DebugAssert(solveCoeff == 1, "Expected coeff = 1");
        if (d_theoryBitvector->BVSize(foundterm) > bv_size) {
          if (foundterm.getOpKind() == EXTRACT) {
            int diff = d_theoryBitvector->BVSize(foundterm) - bv_size;
            int high = d_theoryBitvector->getExtractHi(foundterm);
            int low  = d_theoryBitvector->getExtractLow(foundterm);
            foundterm = d_theoryBitvector->newBVExtractExpr(foundterm[0], high - diff, low);
          }
          else {
            foundterm = d_theoryBitvector->newBVExtractExpr(foundterm, bv_size-1, 0);
          }
        }
        new_lhs = foundterm;
        new_rhs = plusTerm;
        break;
      case 4: {
        // 4. fourth choice: under-sized leaf or extract of leaf
        // foundterm is less than full-sized extract or leaf
        DebugAssert(solveCoeff == 1, "Expected coeff = 1");
        int foundtermsize = d_theoryBitvector->BVSize(foundterm);
        DebugAssert(foundtermsize < bv_size, "Expected undersized term");
        new_rhs = d_theoryBitvector->newBVExtractExpr(plusTerm, foundtermsize-1, 0);
        expr_result = foundterm.eqExpr(new_rhs);
        new_rhs = d_theoryBitvector->newBVExtractExpr(plusTerm, bv_size-1, foundtermsize);
        new_lhs = d_theoryBitvector->newBVZeroString(bv_size - foundtermsize);
        expr_result = expr_result && new_lhs.eqExpr(new_rhs);
        break;
      }
      case 5: {
        // 5. fifth choice: even-coeff leaf or extract of leaf
        // foundterm has even coeff
        int lg = 0;
        for (; solveCoeff % 2 == 0; solveCoeff = solveCoeff / 2, ++lg);
        new_lhs = d_theoryBitvector->newBVConstExpr(solveCoeff, bv_size-lg);
        new_lhs = d_theoryBitvector->newBVMultPadExpr(bv_size-lg, new_lhs, foundterm);
        new_rhs = d_theoryBitvector->newBVExtractExpr(plusTerm, bv_size-1, lg);
        expr_result = new_lhs.eqExpr(new_rhs);
        new_lhs = d_theoryBitvector->newBVZeroString(lg);
        new_rhs = d_theoryBitvector->newBVExtractExpr(plusTerm, lg - 1, 0);
        expr_result = expr_result && new_lhs.eqExpr(new_rhs);
        break;
      }
      default:
        FatalAssert(false, "Expected priority < 7");
        break;
    }
  }
  else {
    new_lhs = plusTerm;
    new_rhs = d_theoryBitvector->newBVZeroString(bv_size);
  }

  if (expr_result.isNull()) {
    if ( new_lhs == new_rhs) {
      expr_result = d_theoryBitvector->trueExpr();
    }
    else if ( new_lhs >= new_rhs) {
      expr_result =  Expr(EQ, new_lhs, new_rhs);
    }
    else {
      expr_result =  Expr(EQ, new_rhs, new_lhs);
    }
  }

  Proof pf;
  if (withProof()) pf = newPf("canonBVEQ");
  TRACE("canonBVEQ", "--> ", expr_result.toString(), "\n}");
  Theorem result = newRWTheorem( e, expr_result, Assumptions::emptyAssump(), pf);
  return result;
}


//! BVZEROEXTEND(e, i) = zeroString \@ e
// where zeroString is a string of i zeroes
Theorem BitvectorTheoremProducer::zeroExtendRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR==e.getType().getExpr().getOpKind(),
		"input must be a bitvector. \n e = " + e.toString());
    CHECK_SOUND(BVZEROEXTEND == e.getOpKind(),
		"input must be BVZEROEXTEND(e).\n e = " + e.toString());
  }

  int extendLen = d_theoryBitvector->getBVIndex(e);
  Expr res;
  if (extendLen == 0) {
    res = e[0];
  }
  else {
    Expr extend = d_theoryBitvector->newBVZeroString(extendLen);
    res = d_theoryBitvector->newConcatExpr(extend, e[0]);
  }

  Proof pf;
  if(withProof())
    pf = newPf("zero_extend_rule");
  Theorem result(newRWTheorem(e, res, Assumptions::emptyAssump(), pf));
  return result;
}


//! BVREPEAT(e, i) = e \@ e \@ ... \@ e
// where e appears i times on the right
Theorem BitvectorTheoremProducer::repeatRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR==e.getType().getExpr().getOpKind(),
		"input must be a bitvector. \n e = " + e.toString());
    CHECK_SOUND(BVREPEAT == e.getOpKind(),
		"input must be BVREPEAT(e).\n e = " + e.toString());
    CHECK_SOUND(d_theoryBitvector->getBVIndex(e) > 0,
                "Expected positive repeat value");
  }

  int repeatVal = d_theoryBitvector->getBVIndex(e);
  Expr res;
  if (repeatVal == 1) {
    res = e[0];
  }
  else {
    vector<Expr> kids;
    for (int i = 0; i < repeatVal; ++i) {
      kids.push_back(e[0]);
    }
    res = d_theoryBitvector->newConcatExpr(kids);
  }

  Proof pf;
  if(withProof())
    pf = newPf("repeat_rule");
  Theorem result(newRWTheorem(e, res, Assumptions::emptyAssump(), pf));
  return result;
}


//! BVROTL(e, i) = a[n-i-1:0] \@ a[n-1:n-i]
// where n is the size of e and i is less than n (otherwise i mod n is used)
Theorem BitvectorTheoremProducer::rotlRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR==e.getType().getExpr().getOpKind(),
		"input must be a bitvector. \n e = " + e.toString());
    CHECK_SOUND(BVROTL == e.getOpKind(),
		"input must be BVROTL(e).\n e = " + e.toString());
  }

  int bvsize = d_theoryBitvector->BVSize(e);
  int rotation = d_theoryBitvector->getBVIndex(e);
  rotation = rotation % bvsize;
  Expr res;
  if (rotation == 0) {
    res = e[0];
  }
  else {
    Expr hi = d_theoryBitvector->newBVExtractExpr(e[0],bvsize-1-rotation,0);
    Expr low = d_theoryBitvector->newBVExtractExpr(e[0],bvsize-1, bvsize-rotation);
    res = d_theoryBitvector->newConcatExpr(hi, low);
  }

  Proof pf;
  if(withProof())
    pf = newPf("rotl_rule");
  Theorem result(newRWTheorem(e, res, Assumptions::emptyAssump(), pf));
  return result;
}


//! BVROTR(e, i) = a[i-1:0] \@ a[n-1:i]
// where n is the size of e and i is less than n (otherwise i mod n is used)
Theorem BitvectorTheoremProducer::rotrRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR==e.getType().getExpr().getOpKind(),
		"input must be a bitvector. \n e = " + e.toString());
    CHECK_SOUND(BVROTR == e.getOpKind(),
		"input must be BVROTR(e).\n e = " + e.toString());
  }

  int bvsize = d_theoryBitvector->BVSize(e);
  int rotation = d_theoryBitvector->getBVIndex(e);
  rotation = rotation % bvsize;
  Expr res;
  if (rotation == 0) {
    res = e[0];
  }
  else {
    Expr hi = d_theoryBitvector->newBVExtractExpr(e[0],rotation-1,0);
    Expr low = d_theoryBitvector->newBVExtractExpr(e[0],bvsize-1, rotation);
    res = d_theoryBitvector->newConcatExpr(hi, low);
  }

  Proof pf;
  if(withProof())
    pf = newPf("rotr_rule");
  Theorem result(newRWTheorem(e, res, Assumptions::emptyAssump(), pf));
  return result;
}

Theorem BitvectorTheoremProducer::bvURemConst(const Expr& remExpr) {
	const Expr& a = remExpr[0];
	const Expr& b = remExpr[1];
	int size = d_theoryBitvector->BVSize(remExpr);

	Rational a_value = d_theoryBitvector->computeBVConst(a);
	Rational b_value = d_theoryBitvector->computeBVConst(b);

	Expr rem;

	if (b_value != 0) {
		Rational rem_value = a_value - floor(a_value / b_value)*b_value;
		rem = d_theoryBitvector->newBVConstExpr(rem_value, size);
	} else {
		static int div_by_zero_count = 0;
		div_by_zero_count ++;
		char var_name[10000];
		sprintf(var_name, "mod_by_zero_const_%d", div_by_zero_count);
		rem = d_theoryBitvector->newVar(var_name, remExpr.getType());
	}

	Proof pf;
	if (withProof())
		pf = newPf("bvUDivConst");

	return newRWTheorem(remExpr, rem, Assumptions::emptyAssump(), pf);
}

Theorem BitvectorTheoremProducer::bvURemRewrite(const Expr& remExpr) {
	Expr a = remExpr[0];
	Expr b = remExpr[1];
	int size = d_theoryBitvector->BVSize(remExpr);
	Expr div = d_theoryBitvector->newBVUDivExpr(a, b);

	Expr rem = d_theoryBitvector->newBVSubExpr(a, d_theoryBitvector->newBVMultExpr(size, div, b));
	Proof pf;
	if (withProof())
		pf = newPf("bvURemRewrite", remExpr);
	return newRWTheorem(remExpr, rem, Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::bvUDivConst(const Expr& divExpr)
{
	const Expr& a = divExpr[0];
	const Expr& b = divExpr[1];
	int size = d_theoryBitvector->BVSize(divExpr);

    Rational a_value = d_theoryBitvector->computeBVConst(a);
    Rational b_value = d_theoryBitvector->computeBVConst(b);

    Expr div;

    if (b_value != 0) {
    	Rational div_value = floor(a_value / b_value);
    	div = d_theoryBitvector->newBVConstExpr(div_value, size);
    } else {
    	static int div_by_zero_count = 0;
    	div_by_zero_count ++;
    	char var_name[10000];
    	sprintf(var_name, "div_by_zero_const_%d", div_by_zero_count);
    	div = d_theoryBitvector->newVar(var_name, divExpr.getType());
    }

	Proof pf;
	if (withProof())
		pf = newPf("bvUDivConst");

	return newRWTheorem(divExpr, div, Assumptions::emptyAssump(), pf);
}

Theorem BitvectorTheoremProducer::bvUDivTheorem(const Expr& divExpr)
{
	int size = d_theoryBitvector->BVSize(divExpr);

	if(CHECK_PROOFS) {
		CHECK_SOUND(BITVECTOR == divExpr.getType().getExpr().getOpKind(), "input must be a bitvector. \n e = " + divExpr.toString());
		CHECK_SOUND(BVUDIV == divExpr.getOpKind(),"input must be BVUDIV(e).\n e = " + divExpr.toString());
	}

	const Expr a = divExpr[0];
	const Expr b = divExpr[1];


	Type type = divExpr.getType();
	Expr div = d_theoryBitvector->getEM()->newBoundVarExpr(type);
	Expr mod = d_theoryBitvector->getEM()->newBoundVarExpr(type);
	vector<Expr> boundVars;
	boundVars.push_back(div);
	boundVars.push_back(mod);

	vector<Expr> assertions;
	Expr pad          = d_theoryBitvector->newBVConstExpr(Rational(0), size);
	Expr a_expanded   = d_theoryBitvector->newConcatExpr(pad, a);
	Expr b_expanded   = d_theoryBitvector->newConcatExpr(pad, b);
	Expr div_expanded = d_theoryBitvector->newConcatExpr(pad, div);
	Expr mod_expanded = d_theoryBitvector->newConcatExpr(pad, mod);
	assertions.push_back(a_expanded.eqExpr(
			d_theoryBitvector->newBVPlusExpr(2*size,
					d_theoryBitvector->newBVMultExpr(2*size, b_expanded, div_expanded),
					mod_expanded
				)
			)
		);
	assertions.push_back(d_theoryBitvector->newBVLTExpr(mod, b));

	Expr non_zero_div = andExpr(assertions);
	// b != 0 -> a = b*div + mod ...
	Expr complete_div = (b.eqExpr(d_theoryBitvector->newBVConstExpr(Rational(0), size))).negate().impExpr(non_zero_div);
	// x/y = div \wedge complete_div
	complete_div = divExpr.eqExpr(div).andExpr(complete_div);
	// Close the result
	Expr result = d_theoryBitvector->getEM()->newClosureExpr(EXISTS, boundVars, complete_div);

	// Make the proof
	Proof pf;
	if (withProof())
		pf = newPf("bvUDiv");

	// Return the theorem
	return newTheorem(result, Assumptions::emptyAssump(), pf);
}

Theorem BitvectorTheoremProducer::bitblastBVMult(const std::vector<Theorem>& a_bits, const std::vector<Theorem>& b_bits,
    		                            const Expr& a_times_b, std::vector<Theorem>& output_bits)
{
	if(CHECK_PROOFS) {
		CHECK_SOUND(a_times_b.arity() == 2, "must be a binary multiplication");
		CHECK_SOUND(BITVECTOR == a_times_b.getType().getExpr().getOpKind(), "input must be a bitvector. \n e = " + a_times_b.toString());
		CHECK_SOUND(BVMULT == a_times_b.getOpKind(),"input must be BVMULT(e).\n e = " + a_times_b.toString());
		CHECK_SOUND(a_bits.size() == b_bits.size(), "given bit expansions of different size");
		CHECK_SOUND((int) a_bits.size() <= d_theoryBitvector->BVSize(a_times_b), "the expansion is bigger than the multiplier");
	}

	int size = a_bits.size();
	Expr falseExpr = d_theoryBitvector->falseExpr();

//  DISABLED FOR NOW, WE ARENT ENSURING THAT ALL TERMS THAT ENTER BITBLASTING
//  ARE NON-ZERO
//	if (CHECK_PROOFS) {
//          bool all_zero = true;
//          Expr a = a_times_b[0];
//          for (int bit = 0; bit < size; bit++) {
//            Theorem bit_i = a_bits[bit];
//            Expr bit_extract = d_theoryBitvector->newBoolExtractExpr(a, bit);
//            CHECK_SOUND(bit_extract == bit_i.getLHS(), "not the right bit theorems");
//            if (bit_i.getRHS() != falseExpr) all_zero = false;
//          }
//          CHECK_SOUND(!all_zero, "expected non-zero inputs");
//          all_zero = true;
//          Expr b = a_times_b[1];
//          for (int bit = 0; bit < size; bit++) {
//            Theorem bit_i = b_bits[bit];
//            Expr bit_extract = d_theoryBitvector->newBoolExtractExpr(b, bit);
//            CHECK_SOUND(bit_extract == bit_i.getLHS(), "not the right bit theorems");
//            if (bit_i.getRHS() != falseExpr) all_zero = false;
//          }
//          CHECK_SOUND(!all_zero, "expected non-zero inputs");
//	}

	vector<Expr> sum_bits;
	vector<Expr> carry_bits;

	// Find the first non-zero bits in a and b
	int a_bit, b_bit;
	for (a_bit = size - 1; a_bit >= 0 && a_bits[a_bit].getRHS() == falseExpr; a_bit --);
	for (b_bit = size - 1; b_bit >= 0 && b_bits[b_bit].getRHS() == falseExpr; b_bit --);
//  DISABLED, SAME AS ABOVE
//	DebugAssert(a_bit >= 0 && b_bit >= 0, "Expected non-zero inputs");

	int new_size = size;
    if (a_bit + b_bit + 2 < new_size) new_size = a_bit + b_bit + 2;

	// Build the first row of the multiplier
	for (int i = 0; i < new_size; i ++) {
		sum_bits.push_back(a_bits[i].getRHS().andExpr(b_bits[0].getRHS()));
		carry_bits.push_back(d_theoryBitvector->falseExpr());
	}

	// Now go down the rows
	Expr carry = d_theoryBitvector->falseExpr();
	for (int row = 1; row < new_size; row ++) {
		for (int bit = new_size-1; bit >= row; bit --) {
			Expr m = a_bits[bit-row].getRHS().andExpr(b_bits[row].getRHS());
			Expr sum = sum_bits[bit].iffExpr(m).iffExpr(carry_bits[bit - 1]);
			Expr carry = sum_bits[bit].andExpr(m).orExpr(carry_bits[bit - 1].andExpr(sum_bits[bit].orExpr(m)));
			sum_bits[bit] = sum;
			carry_bits[bit] = carry;
		}
		// The carry on the side of the multiplier
		carry = carry.orExpr(carry_bits[new_size - 1]);
	}

	// Create all the theorems now
	for (int bit = 0; bit < size; bit ++) {
		Proof pf;
		if (withProof()) {
			pf = newPf("bitblastBVMult", a_times_b, rat(bit));
		}
		output_bits.push_back(newRWTheorem(d_theoryBitvector->newBoolExtractExpr(a_times_b, bit), bit < new_size ? sum_bits[bit] : falseExpr, Assumptions::emptyAssump(), pf));
	}

	Theorem carry_thm;
	return carry_thm;
}

Theorem BitvectorTheoremProducer::bitblastBVPlus(const std::vector<Theorem>& a_bits, const std::vector<Theorem>& b_bits,
                                                 const Expr& a_plus_b, std::vector<Theorem>& output_bits)
{
	if(CHECK_PROOFS) {
		CHECK_SOUND(a_plus_b.arity() == 2, "must be a binary addition");
		CHECK_SOUND(BITVECTOR == a_plus_b.getType().getExpr().getOpKind(), "input must be a bitvector. \n e = " + a_plus_b.toString());
		CHECK_SOUND(BVPLUS == a_plus_b.getOpKind(),"input must be BVPLUS(e).\n e = " + a_plus_b.toString());
		CHECK_SOUND(a_bits.size() == b_bits.size(), "given bit expansions of different size");
		CHECK_SOUND((int) a_bits.size() <= d_theoryBitvector->BVSize(a_plus_b), "the expansion is bigger than the multiplier");
	}

	int size = a_bits.size();

	if (CHECK_PROOFS) {
		Expr a = a_plus_b[0];
		for (int bit = 0; bit < size; bit++) {
			Theorem bit_i = a_bits[bit];
			Expr bit_extract = d_theoryBitvector->newBoolExtractExpr(a, bit);
			CHECK_SOUND(bit_extract == bit_i.getLHS(), "not the right bit theorems");
		}
		Expr b = a_plus_b[1];
		for (int bit = 0; bit < size; bit++) {
			Theorem bit_i = b_bits[bit];
			Expr bit_extract = d_theoryBitvector->newBoolExtractExpr(b, bit);
			CHECK_SOUND(bit_extract == bit_i.getLHS(), "not the right bit theorems");
		}
	}

	vector<Expr> sum_bits;

	Expr carry = d_theoryBitvector->falseExpr();
	for (int i = 0; i < size; i ++)
	{
		Expr a_i = a_bits[i].getRHS();
		Expr b_i = b_bits[i].getRHS();
		sum_bits.push_back(a_i.iffExpr(b_i).iffExpr(carry));
		carry = a_i.andExpr(b_i).orExpr(carry.andExpr(a_i.orExpr(b_i)));
	}

	// Create all the theorems now
	for (int bit = 0; bit < size; bit ++) {
		Proof pf;
		if (withProof()) {
			pf = newPf("bitblastBVPlus", a_plus_b, rat(bit));
		}
		output_bits.push_back(newRWTheorem(d_theoryBitvector->newBoolExtractExpr(a_plus_b, bit), sum_bits[bit], Assumptions::emptyAssump(), pf));
	}

	Theorem carry_thm;
	return carry_thm;
}

/**
 * Rewrite the signed divide in terms of the unsigned one.
 */
Theorem BitvectorTheoremProducer::bvSDivRewrite(const Expr& sDivExpr)
{
	if(CHECK_PROOFS) {
		CHECK_SOUND(BITVECTOR == sDivExpr.getType().getExpr().getOpKind(), "input must be a bitvector. \n e = " + sDivExpr.toString());
		CHECK_SOUND(BVSDIV == sDivExpr.getOpKind(),"input must be BVSDIV(e).\n e = " + sDivExpr.toString());
	}

	int m      = d_theoryBitvector->BVSize(sDivExpr);

	Proof pf;
	if (withProof()) pf = newPf("bvSDivRewrite", sDivExpr);

	//	(bvsdiv s t) abbreviates
	//	      (let (?msb_s (extract[|m-1|:|m-1|] s))
	//	      (let (?msb_t (extract[|m-1|:|m-1|] t))
	//	      (ite (and (= ?msb_s bit0) (= ?msb_t bit0)) ---------> cond1
	//	           (bvudiv s t)
	//	      (ite (and (= ?msb_s bit1) (= ?msb_t bit0)) ---------> cond2
	//	           (bvneg (bvudiv (bvneg s) t))
	//	      (ite (and (= ?msb_s bit0) (= ?msb_t bit1)) ---------> cond3
	//	           (bvneg (bvudiv s (bvneg t)))
	//	           (bvudiv (bvneg s) (bvneg t)))))))

	Expr s     = sDivExpr[0];
	Expr t     = sDivExpr[1];

	Expr s_neg = d_theoryBitvector->newBVUminusExpr(s);
	Expr t_neg = d_theoryBitvector->newBVUminusExpr(t);

	Expr msb_s = d_theoryBitvector->newBVExtractExpr(s, m-1, m-1);
	Expr msb_t = d_theoryBitvector->newBVExtractExpr(t, m-1, m-1);

	Expr bit0  = d_theoryBitvector->newBVConstExpr(Rational(0), 1);
	Expr bit1  = d_theoryBitvector->newBVConstExpr(Rational(1), 1);

	Expr cond1 = msb_s.eqExpr(bit0).andExpr(msb_t.eqExpr(bit0));
	Expr cond2 = msb_s.eqExpr(bit1).andExpr(msb_t.eqExpr(bit0));
	Expr cond3 = msb_s.eqExpr(bit0).andExpr(msb_t.eqExpr(bit1));

	Expr result = cond1.iteExpr(
				d_theoryBitvector->newBVUDivExpr(s, t),
				cond2.iteExpr(
						d_theoryBitvector->newBVUminusExpr(d_theoryBitvector->newBVUDivExpr(s_neg, t)),
						cond3.iteExpr(
								d_theoryBitvector->newBVUminusExpr(d_theoryBitvector->newBVUDivExpr(s, t_neg)),
								d_theoryBitvector->newBVUDivExpr(s_neg, t_neg)
								)
						)
			);

	return newRWTheorem(sDivExpr, result, Assumptions::emptyAssump(), pf);
}

/**
 * Rewrite the signed remainder in terms of the unsigned one.
 */
Theorem BitvectorTheoremProducer::bvSRemRewrite(const Expr& sRemExpr)
{
	if(CHECK_PROOFS) {
		CHECK_SOUND(BITVECTOR == sRemExpr.getType().getExpr().getOpKind(), "input must be a bitvector. \n e = " + sRemExpr.toString());
		CHECK_SOUND(BVSREM == sRemExpr.getOpKind(),"input must be BVSDIV(e).\n e = " + sRemExpr.toString());
	}

	int m      = d_theoryBitvector->BVSize(sRemExpr);

	Proof pf;
	if (withProof()) pf = newPf("bvSRemRewrite", sRemExpr);

	//    (bvsrem s t) abbreviates
	//	      (let (?msb_s (extract[|m-1|:|m-1|] s))
	//	      (let (?msb_t (extract[|m-1|:|m-1|] t))
	//	      (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
	//	           (bvurem s t)
	//	      (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
	//	           (bvneg (bvurem (bvneg s) t))
	//	      (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
	//	           (bvurem s (bvneg t))
	//	           (bvneg (bvurem (bvneg s) (bvneg t))))))))

	Expr s     = sRemExpr[0];
	Expr t     = sRemExpr[1];

	Expr s_neg = d_theoryBitvector->newBVUminusExpr(s);
	Expr t_neg = d_theoryBitvector->newBVUminusExpr(t);

	Expr msb_s = d_theoryBitvector->newBVExtractExpr(s, m-1, m-1);
	Expr msb_t = d_theoryBitvector->newBVExtractExpr(t, m-1, m-1);

	Expr bit0  = d_theoryBitvector->newBVConstExpr(Rational(0), 1);
	Expr bit1  = d_theoryBitvector->newBVConstExpr(Rational(1), 1);

	Expr cond1 = msb_s.eqExpr(bit0).andExpr(msb_t.eqExpr(bit0));
	Expr cond2 = msb_s.eqExpr(bit1).andExpr(msb_t.eqExpr(bit0));
	Expr cond3 = msb_s.eqExpr(bit0).andExpr(msb_t.eqExpr(bit1));

	Expr result = cond1.iteExpr(
				d_theoryBitvector->newBVURemExpr(s, t),
				cond2.iteExpr(
						d_theoryBitvector->newBVUminusExpr(d_theoryBitvector->newBVURemExpr(s_neg, t)),
						cond3.iteExpr(
								d_theoryBitvector->newBVURemExpr(s, t_neg),
								d_theoryBitvector->newBVUminusExpr(d_theoryBitvector->newBVURemExpr(s_neg, t_neg))
								)
						)
			);

	return newRWTheorem(sRemExpr, result, Assumptions::emptyAssump(), pf);
}

/**
 * Rewrite the signed mod in terms of the unsigned one.
 */
Theorem BitvectorTheoremProducer::bvSModRewrite(const Expr& sModExpr)
{
	if(CHECK_PROOFS) {
		CHECK_SOUND(BITVECTOR == sModExpr.getType().getExpr().getOpKind(), "input must be a bitvector. \n e = " + sModExpr.toString());
		CHECK_SOUND(BVSMOD == sModExpr.getOpKind(),"input must be BVSDIV(e).\n e = " + sModExpr.toString());
	}

	int m      = d_theoryBitvector->BVSize(sModExpr);

	Proof pf;
	if (withProof()) pf = newPf("bvSModRewrite", sModExpr);

	//      (bvsmod s t) abbreviates
	//	      (let (?msb_s (extract[|m-1|:|m-1|] s))
	//	      (let (?msb_t (extract[|m-1|:|m-1|] t))
	//	      (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
	//	           (bvurem s t)
	//	      (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
	//	           (bvadd (bvneg (bvurem (bvneg s) t)) t)
	//	      (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
	//	           (bvadd (bvurem s (bvneg t)) t)
	//             (bvneg (bvurem (bvneg s) (bvneg t))))))))

	Expr s     = sModExpr[0];
	Expr t     = sModExpr[1];

	Expr s_neg = d_theoryBitvector->newBVUminusExpr(s);
	Expr t_neg = d_theoryBitvector->newBVUminusExpr(t);

	Expr msb_s = d_theoryBitvector->newBVExtractExpr(s, m-1, m-1);
	Expr msb_t = d_theoryBitvector->newBVExtractExpr(t, m-1, m-1);

	Expr bit0  = d_theoryBitvector->newBVConstExpr(Rational(0), 1);
	Expr bit1  = d_theoryBitvector->newBVConstExpr(Rational(1), 1);

	Expr cond1 = msb_s.eqExpr(bit0).andExpr(msb_t.eqExpr(bit0));
	Expr cond2 = msb_s.eqExpr(bit1).andExpr(msb_t.eqExpr(bit0));
	Expr cond3 = msb_s.eqExpr(bit0).andExpr(msb_t.eqExpr(bit1));

	Expr result = cond1.iteExpr(
				d_theoryBitvector->newBVURemExpr(s, t),
				cond2.iteExpr(
						d_theoryBitvector->newBVPlusExpr(m, d_theoryBitvector->newBVUminusExpr(d_theoryBitvector->newBVURemExpr(s_neg, t)), t),
						cond3.iteExpr(
								d_theoryBitvector->newBVPlusExpr(m, d_theoryBitvector->newBVURemExpr(s, t_neg), t),
								d_theoryBitvector->newBVUminusExpr(d_theoryBitvector->newBVURemExpr(s_neg, t_neg))
								)
						)
			);

	return newRWTheorem(sModExpr, result, Assumptions::emptyAssump(), pf);
}

Theorem BitvectorTheoremProducer::zeroBVOR(const Expr& orEqZero)
{
	if(CHECK_PROOFS) {
		CHECK_SOUND(orEqZero.isEq(), "input must be an equality. \n e = " + orEqZero.toString());
		CHECK_SOUND(orEqZero[0].getKind() == BVOR, "left-hand side must be a bitwise or. \n e = " + orEqZero.toString());
		CHECK_SOUND(orEqZero[1].getKind() == BVCONST, "right-hand side must be a constant or. \n e = " + orEqZero.toString());
		CHECK_SOUND(d_theoryBitvector->computeBVConst(orEqZero[1]) == 0, "right-hand side must be 0. \n e = " + orEqZero.toString());
	}

	vector<Expr> conjuncts;

	for (int disjunct = 0; disjunct < orEqZero[0].arity(); disjunct ++)
		conjuncts.push_back(orEqZero[0][disjunct].eqExpr(orEqZero[1]));

	Expr result = andExpr(conjuncts);

	Proof pf;
	if (withProof()) pf = newPf("zeroBVOR", orEqZero);

	return newRWTheorem(orEqZero, result, Assumptions::emptyAssump(), pf);
}

Theorem BitvectorTheoremProducer::oneBVAND(const Expr& andEqOne)
{
	if(CHECK_PROOFS) {
		CHECK_SOUND(andEqOne.isEq(), "input must be an equality. \n e = " + andEqOne.toString());
		CHECK_SOUND(andEqOne[0].getKind() == BVAND, "left-hand side must be a bitwise and. \n e = " + andEqOne.toString());
		CHECK_SOUND(andEqOne[1].getKind() == BVCONST, "right-hand side must be a constant or. \n e = " + andEqOne.toString());
		CHECK_SOUND(d_theoryBitvector->computeBVConst(andEqOne[1]) == pow(d_theoryBitvector->BVSize(andEqOne[1]), (Unsigned)2) - 1, "right-hand side must be 1^n. \n e = " + andEqOne.toString());
	}

	vector<Expr> conjuncts;

	for (int conjunct = 0; conjunct < andEqOne[0].arity(); conjunct ++)
		conjuncts.push_back(andEqOne[0][conjunct].eqExpr(andEqOne[1]));

	Expr result = andExpr(conjuncts);

	Proof pf;
	if (withProof()) pf = newPf("oneBVAND", andEqOne);

	return newRWTheorem(andEqOne, result, Assumptions::emptyAssump(), pf);
}

Theorem BitvectorTheoremProducer::constEq(const Expr& eq)
{
	if(CHECK_PROOFS) {
		CHECK_SOUND(eq.isEq(), "input must be an equality. \n e = " + eq.toString());
		CHECK_SOUND(eq[0].getKind() == BVCONST, "left-hand side must be a constant. \n e = " + eq.toString());
		CHECK_SOUND(eq[1].getKind() == BVCONST, "right-hand side must be a constant. \n e = " + eq.toString());
	}

	Expr result = eq[0] == eq[1] ? d_theoryBitvector->trueExpr() : d_theoryBitvector->falseExpr();

	Proof pf;
	if (withProof()) pf = newPf("constEq", eq);

	return newRWTheorem(eq, result, Assumptions::emptyAssump(), pf);
}

bool BitvectorTheoremProducer::solveExtractOverlapApplies(const Expr& eq)
{
  // Both sides should be an extract
  if (eq[0].getOpKind() != EXTRACT) return false;
  if (eq[1].getOpKind() != EXTRACT) return false;
  // Terms under extract should be identical
  if (eq[0][0] != eq[1][0]) return false;
  // We have x[i:j] == x[k:l]
  int i = d_theoryBitvector->getExtractHi(eq[0]);
  int j = d_theoryBitvector->getExtractLow(eq[0]);
  int k = d_theoryBitvector->getExtractHi(eq[1]);
  int l = d_theoryBitvector->getExtractLow(eq[1]);
  // They can't be equal, so we either have
  // i > k >= j > l or
  // k > i >= l > j
  if (i == k) return false;
  else if (i > k)
    return (k >= j && j > l);
  else
    return (i >= l && l > j);
}

Theorem BitvectorTheoremProducer::solveExtractOverlap(const Expr& eq)
{
  Expr res;

  if (CHECK_PROOFS)
    CHECK_SOUND(solveExtractOverlapApplies(eq), "solveExtractOvelap does not apply to " + eq.toString());

  // Left and right side of the equation
  Expr lhs = eq[0];
  Expr rhs = eq[1];

  // We have x[i:j] == x[k:l]
  int i = d_theoryBitvector->getExtractHi(lhs);
  int j = d_theoryBitvector->getExtractLow(lhs);
  int k = d_theoryBitvector->getExtractHi(rhs);
  int l = d_theoryBitvector->getExtractLow(rhs);

  // We only do case where i > k
  if (i > k)
  {
    vector<Expr> terms;
    vector<Expr> boundVars;

    // Get the term
    Expr x = lhs[0];
    int x_size = d_theoryBitvector->BVSize(x);

    // If there is a initial part of x, put it in
    if (i < x_size - 1) {
      Expr x_begin = d_theoryBitvector->getEM()->newBoundVarExpr(d_theoryBitvector->newBitvectorType(x_size - i - 1));
      terms.push_back(x_begin);
      boundVars.push_back(x_begin);
    }

    if (2*k + 1 <= i + j)
    {
      // Case when the overlap is smaller then the rest
      //     i                k   j                l
      // xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
      // xxxxAAAAABBBBBBBBBBBBAAAAABBBBBBBBBBBBAAAAAxxxxx
      //       a       b        c        d       e
      int o_size = k - j + 1; // Overlap size
      bool no_rest = (2*k + 1 == i + j);

      // Make The a = c = e expression
      Expr a = d_theoryBitvector->getEM()->newBoundVarExpr(d_theoryBitvector->newBitvectorType(o_size));
      boundVars.push_back(a);
      terms.push_back(a);

      if (no_rest) {
        // c and e
        terms.push_back(a);
        terms.push_back(a);
      } else {
        // Make the b = d expression
        Expr b = d_theoryBitvector->getEM()->newBoundVarExpr(d_theoryBitvector->newBitvectorType(i - k - o_size));
        boundVars.push_back(b);
        terms.push_back(b);
        terms.push_back(a);
        terms.push_back(b);
        terms.push_back(a);
      }
    }
    else
    {
      // Case when the overlap is bigger then the rest
      //     i  k                               j  l
      // xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
      // xxxxABCABCABCABCABCABCABCABCABCABCABCABCABCxxxxx
      int o_size = k - j + 1; // Overlap size
      int r_size = i - k;     // Rest szie
      // Smallest slice
      int d = gcd(Rational(o_size), Rational(r_size)).getInt();
      // Number of different pieces
      int different_pieces = r_size / d; // How many different slices will we get
      // Add all the initial different pieces
      for (int p = 0; p < different_pieces; p ++) {
        Expr piece = d_theoryBitvector->getEM()->newBoundVarExpr(d_theoryBitvector->newBitvectorType(d));
        boundVars.push_back(piece);
        terms.push_back(piece);
      }
      // Add the rest of them cyclicly
      int other_pieces = (o_size + r_size) / d;
      for (int p = 0; p < other_pieces; p ++)
        terms.push_back(terms[terms.size() - different_pieces]);
    }

    // If there is a ending part of x, put it in
    if (l > 0) {
      Expr x_end = d_theoryBitvector->getEM()->newBoundVarExpr(d_theoryBitvector->newBitvectorType(l));
      terms.push_back(x_end);
      boundVars.push_back(x_end);
    }

    res = x.eqExpr(d_theoryBitvector->newConcatExpr(terms));
    res = d_theoryBitvector->getEM()->newClosureExpr(EXISTS, boundVars, res);

  } else
    // Other case by symmetry
    res = solveExtractOverlap(rhs.eqExpr(lhs)).getRHS();

  Proof pf;
  if (withProof()) pf = newPf("solveExtractOverlap", eq);

  return newTheorem(eq.iffExpr(res), Assumptions::emptyAssump(), pf);
}

