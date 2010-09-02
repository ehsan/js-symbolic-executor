/*****************************************************************************/
/*!
 * \file theory_bitvector.cpp
 *
 * Author: Vijay Ganesh.
 *
 * Created: Wed May  5 16:16:59 PST 2004
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


#include "theory_bitvector.h"
#include "bitvector_proof_rules.h"
#include "bitvector_exception.h"
#include "typecheck_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
#include "bitvector_expr_value.h"
#include "command_line_flags.h"


#define HASH_VALUE_ZERO 380
#define HASH_VALUE_ONE  450


using namespace std;
using namespace CVC3;


///////////////////////////////////////////////////////////////////////////////
// TheoryBitvector Private Methods                                           //
///////////////////////////////////////////////////////////////////////////////


int TheoryBitvector::BVSize(const Expr& e)
{
  Type tp(getBaseType(e));
  DebugAssert(tp.getExpr().getOpKind() == BITVECTOR,
	      "BVSize: e = "+e.toString());
  return getBitvectorTypeParam(tp);
}


//! Converts e into a BITVECTOR of length 'len'
/*!
 * \param len is the desired length of the resulting bitvector
 * \param e is the original bitvector of arbitrary length
 */
Expr TheoryBitvector::pad(int len, const Expr& e)
{
  DebugAssert(len >=0,
	      "TheoryBitvector::newBVPlusExpr:"
	      "padding length must be a non-negative integer: "+
	      int2string(len));
  DebugAssert(BITVECTOR == e.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVPlusExpr:"
	      "input must be a BITVECTOR: " + e.toString());

  int size = BVSize(e);
  Expr res;
  if(size == len)
    res = e;
  else if (len < size)
    res = newBVExtractExpr(e,len-1,0);
  else {
    // size < len
    Expr zero = newBVZeroString(len-size);
    res = newConcatExpr(zero,e);
  }
  return res;
}


// Bit-blasting methods


//! accepts a bitvector equation t1 = t2.
/*! \return a rewrite theorem which is a conjunction of equivalences
 * over the bits of t1,t2 respectively.
 */
Theorem TheoryBitvector::bitBlastEqn(const Expr& e)
{
  TRACE("bitvector", "bitBlastEqn(", e.toString(), ") {");
  d_bvBitBlastEq++;

  DebugAssert(e.isEq(),
	      "TheoryBitvector::bitBlastEqn:"
	      "expecting an equation" + e.toString());
  const Expr& leftBV = e[0];
  const Expr& rightBV = e[1];
  IF_DEBUG(const Type& leftType = getBaseType(leftBV);)
  IF_DEBUG(const Type& rightType = getBaseType(rightBV);)
  DebugAssert(BITVECTOR == leftType.getExpr().getOpKind() &&
	      BITVECTOR == rightType.getExpr().getOpKind(),
	      "TheoryBitvector::bitBlastEqn:"
	      "lhs & rhs must be bitvectors");
  DebugAssert(BVSize(leftBV) == BVSize(rightBV),
	      "TheoryBitvector::bitBlastEqn:\n e = "
	      +e.toString());

  Theorem result = reflexivityRule(e);
  Theorem bitBlastLeftThm;
  Theorem bitBlastRightThm;
  std::vector<Theorem> substThms;
  std::vector<Theorem> leftBVrightBVThms;
  int bvLength = BVSize(leftBV);
  int bitPosition = 0;
  Theorem thm0;

  for(; bitPosition < bvLength; ++bitPosition) {
    //bitBlastLeftThm is the theorem 'leftBV[bitPosition] <==> phi'
    bitBlastLeftThm = bitBlastTerm(leftBV, bitPosition);
    //bitBlastRightThm is the theorem 'rightBV[bitPosition] <==> theta'
    bitBlastRightThm = bitBlastTerm(rightBV, bitPosition);
    //collect the two theorems created above in the vector
    //leftBVrightBVthms.
    leftBVrightBVThms.push_back(bitBlastLeftThm);
    leftBVrightBVThms.push_back(bitBlastRightThm);
    //construct (leftBV[bitPosition] <==> rightBV[bitPosition])
    //<====> phi <==> theta
    //and store in the vector substThms.
    Theorem thm = substitutivityRule(IFF, leftBVrightBVThms);
    thm = transitivityRule(thm, rewriteBoolean(thm.getRHS()));
    leftBVrightBVThms.clear();
    substThms.push_back(thm);
    //if phi <==> theta is false, then stop bitblasting. immediately
    //exit and return false.
    if(thm.getRHS().isFalse())
      return transitivityRule(result,
			      d_rules->bitvectorFalseRule(thm));
  }
  // AND_0^bvLength(leftBV[bitPosition] <==> rightBV[bitPosition]) <====>
  // AND_0^bvLength(phi <==> theta)
  Theorem thm = substitutivityRule(AND, substThms);
  // AND_0^bvLength(leftBV[bitPosition] <==> rightBV[bitPosition]) <====>
  // rewriteBoolean(AND_0^bvLength(phi <==> theta))
  thm = transitivityRule(thm, rewriteBoolean(thm.getRHS()));
  //call trusted rule for bitblasting equations.
  result = d_rules->bitBlastEqnRule(e, thm.getLHS());
  result = transitivityRule(result, thm);
  TRACE("bitvector", "bitBlastEqn => ", result.toString(), " }");
  return result;
}


//! accepts a bitvector equation t1 != t2.
/*! \return a rewrite theorem which is a conjunction of
 * (dis)-equivalences over the bits of t1,t2 respectively.
 *
 * A separate rule for disequations for efficiency sake. Obvious
 * implementation using rule for equations and rule for NOT, is not
 * efficient.
 */
Theorem TheoryBitvector::bitBlastDisEqn(const Theorem& notE)
{
  TRACE("bitvector", "bitBlastDisEqn(", notE, ") {");
  IF_DEBUG(debugger.counter("bit-blasted diseq")++);
  //stat counter
  d_bvBitBlastDiseq++;

  DebugAssert(notE.getExpr().isNot() && (notE.getExpr())[0].isEq(),
	      "TheoryBitvector::bitBlastDisEqn:"
	      "expecting an equation" + notE.getExpr().toString());
  //e is the equation
  const Expr& e = (notE.getExpr())[0];
  const Expr& leftBV = e[0];
  const Expr& rightBV = e[1];
  IF_DEBUG(Type leftType = leftBV.getType());
  IF_DEBUG(debugger.counter("bit-blasted diseq bits")+=
	   BVSize(leftBV));
  IF_DEBUG(Type rightType = rightBV.getType());
  DebugAssert(BITVECTOR == leftType.getExpr().getOpKind() &&
	      BITVECTOR == rightType.getExpr().getOpKind(),
	      "TheoryBitvector::bitBlastDisEqn:"
	      "lhs & rhs must be bitvectors");
  DebugAssert(BVSize(leftBV) == BVSize(rightBV),
	      "TheoryBitvector::bitBlastDisEqn: e = "
	      +e.toString());
  Theorem bitBlastLeftThm;
  Theorem bitBlastRightThm;
  std::vector<Theorem> substThms;
  std::vector<Theorem> leftBVrightBVThms;
  int bvLength = BVSize(leftBV);
  int bitPosition = 0;
  for(; bitPosition < bvLength; bitPosition = bitPosition+1) {
    //bitBlastLeftThm is the theorem '~leftBV[bitPosition] <==> ~phi'
    bitBlastLeftThm =
      getCommonRules()->iffContrapositive(bitBlastTerm(leftBV, bitPosition));
    //bitBlastRightThm is the theorem 'rightBV[bitPosition] <==> theta'
    bitBlastRightThm = bitBlastTerm(rightBV, bitPosition);
    //collect the two theorems created above in the vector leftBVrightBVthms.
    leftBVrightBVThms.push_back(bitBlastLeftThm);
    leftBVrightBVThms.push_back(bitBlastRightThm);
    //construct (~leftBV[bitPosition] <==> rightBV[bitPosition])
    //<====> ~phi <==> theta
    //and store in the vector substThms.
    //recall that (p <=/=> q) is same as (~p <==> q)
    Theorem thm = substitutivityRule(IFF, leftBVrightBVThms);
    thm = transitivityRule(thm, rewriteBoolean(thm.getRHS()));
    leftBVrightBVThms.clear();
    substThms.push_back(thm);

    //if phi <==> theta is the True theorem, then stop bitblasting. immediately
    //exit and return t1!=t2 <=> true.
    if(thm.getRHS().isTrue())
      return d_rules->bitvectorTrueRule(thm);
  }

  // OR_0^bvLength(~leftBV[bitPosition] <==> rightBV[bitPosition]) <====>
  // OR_0^bvLength(~phi <==> theta)
  Theorem thm1 = substitutivityRule(OR, substThms);
  // Call trusted rule for bitblasting disequations.
  Theorem result = d_rules->bitBlastDisEqnRule(notE, thm1.getLHS());
  Theorem thm2 = transitivityRule(thm1, rewriteBoolean(thm1.getRHS()));
  result = iffMP(result, thm2);
  TRACE("bitvector", "bitBlastDisEqn => ", result.toString(), " }");
  return result;
}


/*! \param e has the form e1 pred e2, where pred is < or <=.
 *
 *  if e1,e2 are constants, determine bv2int(e1) pred bv2int(e2).
 *
 *  most significant bit of ei is denoted by msb(ei)
 *
 *  \return \f$(msb(e1)\ pred\ msb(e2)) \vee
 *          (msb(e1)=msb(e2) \wedge e1[n-2:0]\ pred\ e2[n-2:0])\f$
 */
Theorem TheoryBitvector::bitBlastIneqn(const Expr& e)
{
  TRACE("bitvector", "bitBlastIneqn(", e.toString(), ") {");

  DebugAssert(BVLT == e.getOpKind() ||
	      BVLE == e.getOpKind(),
	      "TheoryBitvector::bitBlastIneqn: "
	      "input e must be BVLT/BVLE: e = " + e.toString());
  DebugAssert(e.arity() == 2,
	      "TheoryBitvector::bitBlastIneqn: "
	      "arity of e must be 2: e = " + e.toString());
  Expr lhs = e[0];
  Expr rhs = e[1];
  int e0len = BVSize(lhs);
  DebugAssert(e0len == BVSize(rhs), "Expected sizes to match");

  int kind = e.getOpKind();
  Theorem res;
  if(lhs == rhs) {
    res = d_rules->lhsEqRhsIneqn(e, kind);
  }
  else if (lhs.getKind() == BVCONST && rhs.getKind() == BVCONST) {
    res = d_rules->bvConstIneqn(e, kind);
  } else {
    Theorem lhs_i = bitBlastTerm(lhs, e0len-1);
    Theorem rhs_i = bitBlastTerm(rhs, e0len-1);
    res = d_rules->generalIneqn(e, lhs_i, rhs_i, kind);

    //check if output is TRUE or FALSE theorem, and then simply return
    Theorem output = rewriteBoolean(res.getRHS());
    if (output.getRHS().isBoolConst()) {
      res = transitivityRule(res, output);
    }
    else if (e0len > 1) {
      // Copy by value, since 'res' will be changing
      Expr resRHS = res.getRHS();
      // resRHS is of the form (\alpha or (\beta and \gamma))
      // where \gamma is an inequality
      DebugAssert(resRHS.getKind() == OR && resRHS.arity() == 2 &&
                  resRHS[1].getKind() == AND && resRHS[1].arity() == 2,
                  "Unexpected structure");

      vector<unsigned> changed;
      vector<Theorem> thms;

      // \gamma <=> \gamma'
      Theorem thm = bitBlastIneqn(resRHS[1][1]);

      // (\beta and \gamma) <=> (\beta and \gamma')
      changed.push_back(1);
      thms.push_back(thm);
      thm = substitutivityRule(resRHS[1], changed, thms);

      // (\alpha or (\beta and \gamma)) <=> (\alpha or (\beta and \gamma'))
      // 'changed' is the same, only update thms[0]
      thms[0] = thm;
      thm = substitutivityRule(resRHS, changed, thms);
      res = transitivityRule(res, thm);
      /*

      //resRHS can be of the form (\beta and \gamma) or
      //resRHS can be of the form (\alpha or \gamma) or
      //resRHS can be of the form (\gamma)
      // Our mission is to bitblast \gamma and insert it back to the formula
      switch(resRHS.getOpKind()) {
        case OR:
          if(resRHS[1].isAnd()) { // (\alpha or (\beta and \gamma))
            break;
          }
          // (\alpha or \gamma) - fall through (same as the AND case)
        case AND: { // (\beta and \gamma)
          changed.push_back(1);
          gamma = resRHS[1];
          // \gamma <=> \gamma'
          gammaThm = rewriteBV(gamma,2);
          //\gamma' <=> \gamma"
          Theorem thm3 = bitBlastIneqn(gammaThm.getRHS());
          //Theorem thm3 = bitBlastIneqn(gamma);
          //\gamma <=> \gamma' <=> \gamma"
          thm3 = transitivityRule(gammaThm, thm3);
          thms.push_back(thm3);
          // (\beta and \gamma) <=> (\beta and \gamma")
          thm3 = substitutivityRule(resRHS,changed,thms);
          res = transitivityRule(res, thm3);
          break;
        }
        default: // (\gamma)
          IF_DEBUG(gamma = resRHS;)
          // \gamma <=> \gamma'
          gammaThm = rewriteBV(resRHS,2);
          //\gamma' <=> \gamma"
          Theorem thm3 = bitBlastIneqn(gammaThm.getRHS());
          //Theorem thm3 = bitBlastIneqn(gamma);
          //\gamma <=> \gamma' <=> \gamma"
          thm3 = transitivityRule(gammaThm, thm3);
          res = transitivityRule(res, thm3);
          break;
      }

      DebugAssert(kind == gamma.getOpKind(),
                  "TheoryBitvector::bitBlastIneqn: "
                  "gamma must be a BVLT/BVLE. gamma = " +
                  gamma.toString());
      */
    }
  }
  TRACE("bitvector", "bitBlastIneqn => ", res.toString(), " }");
  return res;
}


/*! The invariant maintained by this function is: accepts a bitvector
 * term, t,and a bitPosition, i. returns a formula over the set of
 * propositional variables defined using BOOLEXTRACT of bitvector
 * variables in t at the position i.
 *
 * \return Theorem(BOOLEXTRACT(t, bitPosition) <=> phi), where phi is
 * a Boolean formula over the individual bits of bit-vector variables.
 */
Theorem TheoryBitvector::bitBlastTerm(const Expr& t, int bitPosition)
{
  TRACE("bitvector", "bitBlastTerm(", t, ", " + int2string(bitPosition) + ") {");

  IF_DEBUG(Type type = t.getType();)
  DebugAssert(BITVECTOR == type.getExpr().getOpKind(), "TheoryBitvector::bitBlastTerm: The type of input to bitBlastTerm must be BITVECTOR.\n t = " +t.toString());
  DebugAssert(bitPosition >= 0, "TheoryBitvector::bitBlastTerm: illegal bitExtraction attempted.\n bitPosition = " + int2string(bitPosition));

  Theorem result;

  // Check the cache
  Expr t_i = newBoolExtractExpr(t, bitPosition);
  CDMap<Expr,Theorem>::iterator it = d_bitvecCache.find(t_i);
  if (it != d_bitvecCache.end()) {
	  result = (*it).second;
	  TRACE("bitvector", "bitBlastTerm[cached] => ", result, " }");
	  DebugAssert(t_i == result.getLHS(),	"TheoryBitvector::bitBlastTerm: created wrong theorem" + result.toString() + t_i.toString());
	  return result;
  }

  // Construct the theorem t[bitPosition] <=> \theta_i and put it into
  // d_bitvecCache
  switch(t.getOpKind()) {
    case BVCONST:
    	result = d_rules->bitExtractConstant(t, bitPosition);
    	break;
    case CONCAT:
    {
    	Theorem thm = d_rules->bitExtractConcatenation(t, bitPosition);
    	const Expr& boolExtractTerm = thm.getRHS();
    	DebugAssert(BOOLEXTRACT == boolExtractTerm.getOpKind(), "TheoryBitvector::bitBlastTerm: recursion: term must be bool_extract");
    	const Expr& term = boolExtractTerm[0];
    	int bitPos = getBoolExtractIndex(boolExtractTerm);
    	TRACE("bitvector", "term for bitblastTerm recursion:(", term.toString(), ")");
    	result = transitivityRule(thm, bitBlastTerm(term, bitPos));
    	break;
    }
    case EXTRACT:
    {
    	Theorem thm = d_rules->bitExtractExtraction(t, bitPosition);
    	const Expr& boolExtractTerm = thm.getRHS();
    	DebugAssert(BOOLEXTRACT == boolExtractTerm.getOpKind(), "TheoryBitvector::bitBlastTerm: recursion: term must be bool_extract");
    	const Expr& term = boolExtractTerm[0];
    	int bitPos = getBoolExtractIndex(boolExtractTerm);
    	TRACE("bitvector", "term for bitblastTerm recursion:(", term, ")");
    	result = transitivityRule(thm, bitBlastTerm(term, bitPos));
    	break;
    }
    case CONST_WIDTH_LEFTSHIFT:
    {
    	result = d_rules->bitExtractFixedLeftShift(t, bitPosition);
    	const Expr& extractTerm = result.getRHS();
    	if(BOOLEXTRACT == extractTerm.getOpKind())
    		result = transitivityRule(result, bitBlastTerm(extractTerm[0], getBoolExtractIndex(extractTerm)));
    	break;
    }
    case BVSHL:
    {
    	// BOOLEXTRACT(bvshl(t,x),i) <=> ((x = 0) AND BOOLEXTRACT(t,i)) OR
    	//                               ((x = 1) AND BOOLEXTRACT(t,i-1)) OR ...
    	//                               ((x = i) AND BOOLEXTRACT(t,0))
    	Theorem thm = d_rules->bitExtractBVSHL(t, bitPosition);
    	// bitblast the equations and extractions
      	vector<Theorem> thms, thms0;
    	int bvsize = BVSize(t);
      	for (int i = 0; i <= bitPosition; ++i) {
    		thms0.push_back(bitBlastEqn(t[1].eqExpr(newBVConstExpr(i, bvsize))));
    		thms0.push_back(bitBlastTerm(t[0], bitPosition-i));
        	thms.push_back(substitutivityRule(AND, thms0));
    		thms0.clear();
    	}
    	// Put it all together
    	if (thms.size() == 1) {
    		result = transitivityRule(thm, thms[0]);
    	}
    	else {
    		Theorem thm2 = substitutivityRule(OR, thms);
    		result = transitivityRule(thm, thm2);
    	}
    	break;
    }
    case BVLSHR:
    {
    	// BOOLEXTRACT(bvlshr(t,x),i) <=> ((x = 0) AND BOOLEXTRACT(t,i)) OR
    	//                                ((x = 1) AND BOOLEXTRACT(t,i+1)) OR ...
    	//                                ((x = n-1-i) AND BOOLEXTRACT(t,n-1))
    	Theorem thm = d_rules->bitExtractBVLSHR(t, bitPosition);
    	// bitblast the equations and extractions
    	vector<Theorem> thms, thms0;
    	int bvsize = BVSize(t);
    	for (int i = 0; i <= bvsize-1-bitPosition; ++i) {
    		thms0.push_back(bitBlastEqn(t[1].eqExpr(newBVConstExpr(i, bvsize))));
    		thms0.push_back(bitBlastTerm(t[0], bitPosition+i));
    		thms.push_back(substitutivityRule(AND, thms0));
    		thms0.clear();
    	}
    	// Put it all together
    	if (thms.size() == 1) {
    		result = transitivityRule(thm, thms[0]);
    	}
    	else {
    		Theorem thm2 = substitutivityRule(OR, thms);
    		result = transitivityRule(thm, thm2);
    	}
    	break;
    }
    case BVASHR:
    {
    	// BOOLEXTRACT(bvlshr(t,x),i) <=> ((x = 0) AND BOOLEXTRACT(t,i)) OR
    	//                                ((x = 1) AND BOOLEXTRACT(t,i+1)) OR ...
    	//                                ((x >= n-1-i) AND BOOLEXTRACT(t,n-1))
    	Theorem thm = d_rules->bitExtractBVASHR(t, bitPosition);
    	// bitblast the equations and extractions
    	vector<Theorem> thms, thms0;
    	int bvsize = BVSize(t);
    	int i = 0;
    	for (; i < bvsize-1-bitPosition; ++i) {
    		thms0.push_back(bitBlastEqn(t[1].eqExpr(newBVConstExpr(i, bvsize))));
    		thms0.push_back(bitBlastTerm(t[0], bitPosition+i));
    		thms.push_back(substitutivityRule(AND, thms0));
    		thms0.clear();
    	}
    	Expr leExpr = newBVLEExpr(newBVConstExpr(i, bvsize), t[1]);
    	thms0.push_back(bitBlastIneqn(leExpr));
    	thms0.push_back(bitBlastTerm(t[0], bvsize-1));
    	thms.push_back(substitutivityRule(AND, thms0));
    	// Put it all together
    	if (thms.size() == 1) {
    		result = transitivityRule(thm, thms[0]);
    	}
    	else {
    		Theorem thm2 = substitutivityRule(OR, thms);
    		result = transitivityRule(thm, thm2);
    	}
    	break;
    }
    case BVOR:
    case BVAND:
    case BVXOR:
    {
    	int kind = t.getOpKind();
    	int resKind = (kind == BVOR) ? OR :
        kind == BVAND ? AND : XOR;
    	Theorem thm = d_rules->bitExtractBitwise(t, bitPosition, kind);
    	const Expr& phi = thm.getRHS();
    	DebugAssert(phi.getOpKind() == resKind && phi.arity() == t.arity(), "TheoryBitvector::bitBlastTerm: recursion:\n phi = " + phi.toString() + "\n t = " + t.toString());
    	vector<Theorem> substThms;
    	for(Expr::iterator i=phi.begin(), iend=phi.end(); i!=iend; ++i) {
    		DebugAssert(i->getOpKind() == BOOLEXTRACT, "Expected BOOLEXTRACT");
    		substThms.push_back(bitBlastTerm((*i)[0], getBoolExtractIndex(*i)));
    	}
    	result = transitivityRule(thm, substitutivityRule(resKind, substThms));
    	break;
    }
    case BVNEG:
    {
    	Theorem thm = d_rules->bitExtractNot(t, bitPosition);
    	const Expr& extractTerm = thm.getRHS();
    	DebugAssert(NOT == extractTerm.getKind(), "TheoryBitvector::bitBlastTerm: recursion: term must be NOT");
    	const Expr& term0 = extractTerm[0];
    	DebugAssert(BOOLEXTRACT == term0.getOpKind(), "TheoryBitvector::bitBlastTerm: recursion:(terms must be BOOL-EXTRACT");
    	int bitPos0 = getBoolExtractIndex(term0);
    	std::vector<Theorem> res;
    	res.push_back(bitBlastTerm(term0[0], bitPos0));
    	result = transitivityRule(thm, substitutivityRule(NOT, res));
    	break;
    }
    case BVPLUS:
    {
		Theorem thm_binary;
		if(t.arity() > 2) thm_binary = d_rules->bvPlusAssociativityRule(t);
		else thm_binary = reflexivityRule(t);

		Expr bvPlusTerm = thm_binary.getRHS();

    	// Get the bits of the right multiplicand
    	Expr b = bvPlusTerm[1];
    	vector<Theorem> b_bits(bitPosition + 1);
    	for (int bit = bitPosition; bit >= 0; -- bit)
    	    b_bits[bit] = bitBlastTerm(b, bit);

    	// The output of the bit-blasting
    	vector<Theorem> output_bits;

  		// Get the bits of the left multiplicand
   		Expr a = bvPlusTerm[0];
   		vector<Theorem> a_bits(bitPosition + 1);
   		for (int bit = bitPosition; bit >= 0; -- bit)
   			a_bits[bit] = bitBlastTerm(a, bit);

   		// Bit-blast them and get all the output bits (of this size)
   		d_rules->bitblastBVPlus(a_bits, b_bits, bvPlusTerm, output_bits);

    	// Simplify all the resulting bit expressions and add them to the bit-blasting cache
    	Theorem thm;
    	for (int bit = 0; bit <= bitPosition; bit ++)
    	{
    		thm = output_bits[bit];

    		Expr original_boolextract = newBoolExtractExpr(t, bit);
    		Expr boolextract = thm.getLHS();
    		Expr bitblasted  = thm.getRHS();

    		CDMap<Expr,Theorem>::iterator it = d_bitvecCache.find(boolextract);
    		if (it != d_bitvecCache.end())
    			continue;

    		thm = d_bitvecCache[boolextract] = transitivityRule(thm, rewriteBoolean(thm.getRHS()));
    		if (boolextract != original_boolextract)
    			thm = d_bitvecCache[original_boolextract] = transitivityRule(substitutivityRule(original_boolextract, thm_binary), thm);
       	}

    	// We are returning the last theorem
    	return thm;

    	break;
    }
    case BVMULT: {

    	Theorem thm;

    	bool a_is_const = (BVCONST == t[0].getKind());

    			// If a constant, rewrite using addition
    	if (a_is_const) {
    		thm = d_rules->bitExtractConstBVMult(t, bitPosition);
    		const Expr& boolExtractTerm = thm.getRHS();
		    const Expr& term = boolExtractTerm[0];
    		result = transitivityRule(thm, bitBlastTerm(term, bitPosition));
    		break;
    	}

    	// Get the bits ot the right multiplicant
    	Expr b = t[1];
    	vector<Theorem> b_bits(bitPosition + 1);
    	for (int bit = bitPosition; bit >= 0; -- bit)
    	    b_bits[bit] = bitBlastTerm(b, bit);

    	// The output of the bitblasting
    	vector<Theorem> output_bits;

		// Get the bits of the left multiplicant
    	Expr a = t[0];
    	vector<Theorem> a_bits(bitPosition + 1);
    	for (int bit = bitPosition; bit >= 0; -- bit)
    		a_bits[bit] = bitBlastTerm(a, bit);

    	// Bitblast them and get all the output bits (of this size)
    	d_rules->bitblastBVMult(a_bits, b_bits, t, output_bits);

    	// Simplify all the resulting bit expressions and add them to the bitblasting cache
    	for (int bit = 0; bit <= bitPosition; bit ++)
    	{
    		thm = output_bits[bit];

    		Expr boolextract = thm.getLHS();
    		Expr bitblasted  = thm.getRHS();

    		CDMap<Expr,Theorem>::iterator it = d_bitvecCache.find(boolextract);
    		if (it != d_bitvecCache.end())
    			continue;

    		thm = d_bitvecCache[boolextract] = transitivityRule(thm, rewriteBoolean(thm.getRHS()));
                // not allowed to use simplify in bitblasting
                //theoryCore()->simplify(thm.getRHS()));
    	}

    	// We are returning the last theorem
    	return thm;

    	break;
    }
//    case BVMULT: {
//
//    	Theorem thm;
//      if(BVCONST == t[0].getKind())
//    		thm = d_rules->bitExtractConstBVMult(t, bitPosition);
//      else
//	thm = d_rules->bitExtractBVMult(t, bitPosition);
//    		const Expr& boolExtractTerm = thm.getRHS();
//      const Expr& term = boolExtractTerm[0];
//      result = transitivityRule(thm, bitBlastTerm(term, bitPosition));
//    	break;
//    }
    default:
    {
    	FatalAssert(theoryOf(t.getOpKind()) != this, "Unexpected operator in bitBlastTerm:" + t.toString());
    	//we have bitvector variable. check if the expr is indeed a BITVECTOR.
    	IF_DEBUG(Type type = t.getType();)
    	DebugAssert(BITVECTOR == (type.getExpr()).getOpKind(), "BitvectorTheoremProducer::bitBlastTerm: the type must be BITVECTOR");
    	//check if 0<= i < length of BITVECTOR
    	IF_DEBUG(int bvLength=BVSize(t);)
    	DebugAssert(0 <= bitPosition && bitPosition < bvLength, "BitvectorTheoremProducer::bitBlastTerm: the bitextract position must be legal");
    	TRACE("bitvector", "bitBlastTerm: blasting variables(", t, ")");
    	const Expr bitExtract = newBoolExtractExpr(t, bitPosition);
    	result = reflexivityRule(bitExtract);
    	TRACE("bitvector", "bitBlastTerm: blasting variables(", t, ")");
    	break;
    }
  }
  DebugAssert(!result.isNull(), "TheoryBitvector::bitBlastTerm()");
  Theorem simpThm = rewriteBoolean(result.getRHS());
  // not allowed to use simplify in bitblasting
  // theoryCore()->simplify(result.getRHS());
  result = transitivityRule(result, simpThm);
  d_bitvecCache[t_i] = result;
  DebugAssert(t_i == result.getLHS(),
              "TheoryBitvector::bitBlastTerm: "
              "created wrong theorem.\n result = "
              +result.toString()
              +"\n t_i = "+t_i.toString());
  TRACE("bitvector", "bitBlastTerm => ", result, " }");
  return result;
}


// Rewriting methods


//! Check that all the kids of e are BVCONST
static bool constantKids(const Expr& e) {
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
    if(!i->isRational() && i->getKind() != BVCONST) return false;
  return true;
}


//! Search for all the BVCONST kids of e, and return their indices in idxs
static void constantKids(const Expr& e, vector<int>& idxs) {
  for(int i=0, iend=e.arity(); i<iend; ++i)
    if(e[i].getKind() == BVCONST) idxs.push_back(i);
}


// Recursively descend into the expression e, keeping track of whether
// we are under even or odd number of negations ('neg' == true means
// odd, the context is "negative").
// Produce a proof of e <==> e' or !e <==> e', depending on whether
// neg is false or true, respectively.
// This function must be called only from the pushNegation function
Theorem TheoryBitvector::pushNegationRec(const Expr& e)
{
  TRACE("pushNegation", "pushNegationRec(", e,") {");
  DebugAssert(e.getKind() == BVNEG, "Expected BVNEG in pushNegationRec");
  ExprMap<Theorem>::iterator i = d_pushNegCache.find(e);
  if(i != d_pushNegCache.end()) { // Found cached result
    TRACE("TheoryBitvector::pushNegation",
	  "pushNegationRec [cached] => ", (*i).second, "}");
    return (*i).second;
  }
  Theorem res(reflexivityRule(e));

  switch(e[0].getOpKind()) {
    case BVCONST:
      res = d_rules->negConst(e);
      break;
    case BVNEG:{
      res = d_rules->negNeg(e);
      break;
    }
    case BVAND: {
      //demorgan's laws.
      Theorem thm0 = d_rules->negBVand(e);
      Expr ee = thm0.getRHS();
      if (ee.arity() == 0) res = thm0;
      else {
        //process each negated kid
        Op op = ee.getOp();
        vector<Theorem> thms;
        for(Expr::iterator i=ee.begin(), iend=ee.end(); i!=iend; ++i)
          thms.push_back(pushNegationRec(*i));
        res = substitutivityRule(op, thms);
        res = transitivityRule(thm0, res);
      }
      break;
    }
    case BVOR: {
      //demorgan's laws.
      Theorem thm0 = d_rules->negBVor(e);
      Expr ee = thm0.getRHS();
      if (ee.arity() == 0) res = thm0;
      else {
        //process each negated kid
        Op op = ee.getOp();
        vector<Theorem> thms;
        for(Expr::iterator i=ee.begin(), iend=ee.end(); i!=iend; ++i)
          thms.push_back(pushNegationRec(*i));
        res = substitutivityRule(op, thms);
        res = transitivityRule(thm0, res);
      }
      break;
    }
    case BVXOR: {
      res = d_rules->negBVxor(e);
      Expr ee = res.getRHS();

      // only the first child is negated
      Theorem thm0 = pushNegationRec(ee[0]);
      if (!thm0.isRefl()) {
        thm0 = substitutivityRule(ee, 0, thm0);
        res = transitivityRule(res, thm0);
      }
      break;
    }
    case BVXNOR: {
      res = d_rules->negBVxnor(e);
      break;
    }
    case CONCAT: {
      //demorgan's laws.
      Theorem thm0 = d_rules->negConcat(e);
      Expr ee = thm0.getRHS();
      if (ee.arity() == 0) res = thm0;
      else {
        //process each negated kid
        Op op = ee.getOp();
        vector<Theorem> thms;
        for(Expr::iterator i=ee.begin(), iend=ee.end(); i!=iend; ++i)
          thms.push_back(pushNegationRec(*i));
        res = substitutivityRule(op, thms);
        res = transitivityRule(thm0, res);
      }
      break;
    }
    case BVPLUS:
      // FIXME: Need to implement the following transformation:
      // ~(x+y) <=> ~x+~y+1
      // (because  ~(x+y)+1= -(x+y) = -x-y = ~x+1+~y+1)
    case BVMULT:
      // FIXME: Need to implement the following transformation:
      // ~(x*y) <=> (~x+1)*y-1
      // [ where we prefer x to be constant/AND/OR/NEG and then
      //   BVPLUS, and only then everything else].
      // (because  ~(x*y)+1= -(x+y) = (-x)*y = (~x+1)*y)
    default:
      res = reflexivityRule(e);
      break;
  }
  TRACE("TheoryBitvector::pushNegation", "pushNegationRec => ", res, "}");
  d_pushNegCache[e] = res;
  return res;
}


// We assume that the cache is initially empty
Theorem TheoryBitvector::pushNegation(const Expr& e) {
  d_pushNegCache.clear();
  DebugAssert(BVNEG == e.getOpKind(), "Expected BVNEG");
  return pushNegationRec(e);
}


//! Top down simplifier
Theorem TheoryBitvector::simplifyOp(const Expr& e) {
  if (e.arity() > 0) {
    Expr ee(e);
    Theorem thm0;
    switch(e.getOpKind()) {
    case BVNEG:
      thm0 = pushNegation(e);
      break;
    case EXTRACT:
      switch(e[0].getOpKind()) {
      case BVPLUS:
	thm0 = d_rules->extractBVPlus(e);
	break;
      case BVMULT:
	thm0 = d_rules->extractBVMult(e);
	break;
      default:
	thm0 = reflexivityRule(e);
	break;
      }
      break;
    case BVPLUS:
      break;
    case BVMULT:
      //      thm0 = d_rules->padBVMult(e);
      break;
    case CONCAT: // 0bin0_[k] @ BVPLUS(n, args) => BVPLUS(n+k, args)
//       if(e.arity()==2 && e[0].getKind()==BVCONST && e[1].getOpKind()==BVPLUS
// 	 && computeBVConst(e[0]) == 0) {
// 	thm0 = d_rules->bvplusZeroConcatRule(e);
//       }
      break;
    case RIGHTSHIFT:
      thm0 = d_rules->rightShiftToConcat(e);
      break;
    case LEFTSHIFT:
      thm0 = d_rules->leftShiftToConcat(e);
      break;
    case CONST_WIDTH_LEFTSHIFT:
      thm0 = d_rules->constWidthLeftShiftToConcat(e);
      break;
    default:
      thm0 = reflexivityRule(e);
      break;
    }
    vector<Theorem> newChildrenThm;
    vector<unsigned> changed;
    if(thm0.isNull()) thm0 = reflexivityRule(e);
    ee = thm0.getRHS();
    int ar = ee.arity();
    for(int k = 0; k < ar; ++k) {
      // Recursively simplify the kids
      Theorem thm = simplify(ee[k]);
      if (thm.getLHS() != thm.getRHS()) {
	newChildrenThm.push_back(thm);
	changed.push_back(k);
      }
    }
    if(changed.size() > 0) {
      Theorem thm1 = substitutivityRule(ee, changed, newChildrenThm);
      return transitivityRule(thm0,thm1);
    } else
      return thm0;
  }
  return reflexivityRule(e);
}


// Theorem TheoryBitvector::rewriteConst(const Expr& e)
// {
//   Theorem result = reflexivityRule(e);
//   return result;
// }


Theorem TheoryBitvector::rewriteBV(const Expr& e, ExprMap<Theorem>& cache, int n)
{
  TRACE("bitvector rewrite", "TheoryBitvector::rewriteBV(", e, ") {");

  if (n <= 0) return reflexivityRule(e);

  Theorem res;

  if(n >= 2) {
    // rewrite children recursively
    Theorem thm;
    vector<Theorem> thms;
    vector<unsigned> changed;
    for(int i=0, iend=e.arity(); i<iend; ++i) {
      thm = rewriteBV(e[i], cache, n-1);
      if(thm.getLHS() != thm.getRHS()) {
        thms.push_back(thm);
        changed.push_back(i);
      }
    }
    if(changed.size() > 0) {
      thm = substitutivityRule(e, changed, thms);
      return transitivityRule(thm, rewriteBV(thm.getRHS(), cache));
    }
    // else fall through
  }

  // Check the cache
  ExprMap<Theorem>::iterator it = cache.find(e);
  if (it != cache.end()) {
    res = (*it).second;
    TRACE("bitvector rewrite", "TheoryBitvector::rewrite["+int2string(n)
          +"][cached] => ", res.getExpr(), " }");
    IF_DEBUG(debugger.counter("bv rewriteBV[n] cache hits")++;)
    return res;
  }

  // Main rewrites
  switch(e.getOpKind()) {
    case NOT:
      switch (e[0].getKind()) {
        case BVLT:
        case BVLE:
          res = d_rules->notBVLTRule(e);
          if (!res.isRefl()) {
            res = transitivityRule(res, simplify(res.getRHS()));
          }
          break;
        case EQ:
          if (BVSize(e[0][0]) == 1) {
            res = d_rules->notBVEQ1Rule(e);
            res = transitivityRule(res, simplify(res.getRHS()));
            break;
          }
          break;
      }
      break;
    case EQ:
    {
      // Canonise constant equations to true or false
      if (e[0].getKind() == BVCONST && e[1].getKind() == BVCONST) {
    	  res = d_rules->constEq(e);
      } else
      // If x_1 or x_2 = 0 then both have to be 0
      if (e[0].getKind() == BVOR && e[1].getKind() == BVCONST && computeBVConst(e[1]) == 0) {
    	  res = d_rules->zeroBVOR(e);
    	  res = transitivityRule(res, simplify(res.getRHS()));
      }
      // if x_1 and x_2 = 1 then both have to be 1
      else if (e[0].getKind() == BVAND && e[1].getKind() == BVCONST && computeBVConst(e[1]) == pow(BVSize(e[1]), (Unsigned)2) - 1) {
    	  res = d_rules->oneBVAND(e);
    	  res = transitivityRule(res, simplify(res.getRHS()));
      }
      // Solve
      else {
    	  res = d_rules->canonBVEQ(e);
    	  if (!res.isRefl()) {
    		  res = transitivityRule(res, simplify(res.getRHS()));
    	  }
    	  else e.setRewriteNormal();
      }
      break;
    }
    case BVCONST:
    {
      res = reflexivityRule(e);
      break;
    }
    case CONCAT: {
      // First, flatten concatenation
      res = d_rules->concatFlatten(e);
      TRACE("bitvector rewrite", "rewriteBV (CONCAT): flattened = ",
	    res.getRHS(), "");
      // Search for adjacent constants and accumulate the vector of
      // nested concatenations (@ t1 ... (@ c1 ... ck) ... tn), and the
      // indices of constant concatenations in this new expression.
      // We'll connect this term to 'e' by inverse of flattenning, and
      // rewrite concatenations of constants into bitvector constants.
      vector<unsigned> idxs;
      vector<Expr> kids; // Kids of the new concatenation
      vector<Theorem> thms; // Rewrites of constant concatenations
      vector<Expr> nestedKids; // Kids of the current concatenation of constants
      // res will be overwritten, using const Expr& may be dangerous
      Expr e1 = res.getRHS();
      for(int i=0, iend=e1.arity(); i<iend; ++i) {
	TRACE("bitvector rewrite", "rewriteBV: e["+int2string(i)+"]=",
	      e1[i], "");
	if(e1[i].getKind() == BVCONST) {
	  // INVARIANT: if it is the first constant in a batch,
	  // then nestedKids must be empty.
	  nestedKids.push_back(e1[i]);
	  TRACE("bitvector rewrite", "rewriteBV: queued up BVCONST: ",
		e1[i], "");
	} else { // e1[i] is not a BVCONST
	  if(nestedKids.size() > 0) { // This is the end of a batch
	    if(nestedKids.size() >= 2) { // Create a nested const concat
	      Expr cc = newConcatExpr(nestedKids);
	      idxs.push_back(kids.size());
	      kids.push_back(cc);
	      thms.push_back(d_rules->concatConst(cc));
	      TRACE("bitvector rewrite", "rewriteBV: wrapping ", cc, "");
	    } else { // A single constant, add it as it is
	      TRACE("bitvector rewrite", "rewriteBV: single const ",
		    nestedKids[0], "");
	      kids.push_back(nestedKids[0]);
	    }
	    nestedKids.clear();
	  }
	  // Add the current non-constant BV
	  kids.push_back(e1[i]);
	}
      }
      // Handle the last BVCONST
      if(nestedKids.size() > 0) {
	if(nestedKids.size() >= 2) { // Create a nested const concat
	  Expr cc = newConcatExpr(nestedKids);
	  idxs.push_back(kids.size());
	  kids.push_back(cc);
	  thms.push_back(d_rules->concatConst(cc));
	  TRACE("bitvector rewrite", "rewriteBV: wrapping ", cc, "");
	} else { // A single constant, add it as it is
	  kids.push_back(nestedKids[0]);
	  TRACE("bitvector rewrite", "rewriteBV: single const ",
		nestedKids[0], "");
	}
	nestedKids.clear();
      }
      // If there are any constants to merge, do the merging
      if(idxs.size() > 0) {
	// CONCAT with constants groupped
	if(kids.size() == 1) { // Special case: all elements are constants
	  DebugAssert(thms.size() == 1, "TheoryBitvector::rewriteBV:\n"
		      "case CONCAT: all constants.  thms.size() == "
		      +int2string(thms.size()));
	  res = transitivityRule(res, thms[0]);
	} else {
	  Expr ee = newConcatExpr(kids);

	  Theorem constMerge = substitutivityRule(ee, idxs, thms);
	  // The inverse flattening of ee
	  Theorem unFlatten = symmetryRule(d_rules->concatFlatten(ee));
	  // Putting it together: Theorem(e==e'), where e' has constants merged
	  res = transitivityRule(res, unFlatten);
	  res = transitivityRule(res, constMerge);
	}
      }

      // Now do a similar search for mergeable extractions
      idxs.clear();
      thms.clear();
      kids.clear();
      // nestedKids must already be empty
      DebugAssert(nestedKids.size() == 0,
		  "rewriteBV() case CONCAT, end of const merge");
      Expr prevExpr; // Previous base of extraction (initially Null)
      // The first and the last bit in the batch of mergeable extractions
      int hi(-1), low(-1);
      // Refresh e1
      e1 = res.getRHS();
      for(int i=0, iend=e1.arity(); i<iend; ++i) {
	const Expr& ei = e1[i];
	if(ei.getOpKind() == EXTRACT) {
	  if(nestedKids.size() > 0 && ei[0] == prevExpr
	     && (low-1) == getExtractHi(ei)) {
	    // Continue to accumulate the current batch
	    nestedKids.push_back(ei);
	    low = getExtractLow(ei);
	  } else { // Start a new batch
	    // First, check if there was a batch before that
	    if(nestedKids.size() >= 2) { // Create a nested const concat
	      Expr cc = newConcatExpr(nestedKids);
	      idxs.push_back(kids.size());
	      kids.push_back(cc);
	      thms.push_back(d_rules->concatMergeExtract(cc));
	      nestedKids.clear();
	    } else if(nestedKids.size() == 1) {
	      // A single extraction, add it as it is
	      kids.push_back(nestedKids[0]);
	      nestedKids.clear();
	    }
	    // Now, actually start a new batch
	    nestedKids.push_back(ei);
	    hi = getExtractHi(ei);
	    low = getExtractLow(ei);
	    prevExpr = ei[0];
	  }
	} else { // e1[i] is not an EXTRACT
	  if(nestedKids.size() >= 2) { // Create a nested const concat
	    Expr cc = newConcatExpr(nestedKids);
	    idxs.push_back(kids.size());
	    kids.push_back(cc);
	    thms.push_back(d_rules->concatMergeExtract(cc));
	  } else if(nestedKids.size() == 1) {
	    // A single extraction, add it as it is
	    kids.push_back(nestedKids[0]);
	  }
	  nestedKids.clear();
	  // Add the current non-EXTRACT BV
	  kids.push_back(ei);
	}
      }
      // Handle the last batch of extractions
      if(nestedKids.size() >= 2) { // Create a nested const concat
	Expr cc = newConcatExpr(nestedKids);
	idxs.push_back(kids.size());
	kids.push_back(cc);
	// The extraction may include all the bits, we need to rewrite again
	thms.push_back(rewriteBV(d_rules->concatMergeExtract(cc), cache, 1));
      } else if(nestedKids.size() == 1) {
	// A single extraction, add it as it is
	kids.push_back(nestedKids[0]);
      }
      // If there are any extractions to merge, do the merging
      if(idxs.size() > 0) {
	// CONCAT with extractions groupped
	if(kids.size() == 1) { // Special case: all elements merge together
	  DebugAssert(thms.size() == 1, "TheoryBitvector::rewriteBV:\n"
		      "case CONCAT: all extracts merge.  thms.size() == "
		      +int2string(thms.size()));
	  res = thms[0];
	} else {
	  Expr ee = newConcatExpr(kids);
	  Theorem extractMerge = substitutivityRule(ee, idxs, thms);
	  // The inverse flattening of ee
	  Theorem unFlatten = symmetryRule(d_rules->concatFlatten(ee));
	  // Putting it together: Theorem(e==e'), where e' has extractions merged
	  res = transitivityRule(res, unFlatten);
	  res = transitivityRule(res, extractMerge);
	}
      }
      // Check for 0bin00 @ BVPLUS(n, ...).  Most of the time, this
      // case will be handled during the top-down phase
      // (simplifyOp()), but not always.
//       Expr ee = res.getRHS();
//       if(ee.getOpKind()==CONCAT && ee.arity() == 2 && ee[0].getKind()==BVCONST
// 	 && ee[1].getOpKind()==BVPLUS && computeBVConst(ee[0]) == 0) {
// 	// Push the concat down through BVPLUS
// 	Theorem thm = d_rules->bvplusZeroConcatRule(ee);
// 	if(thm.getLHS()!=thm.getRHS()) {
// 	  thm = transitivityRule(thm, d_rules->padBVPlus(thm.getRHS()));
// 	  // Kids may need to be rewritten again
// 	  res = rewriteBV(transitivityRule(res, thm), cache, 2);
// 	}
//       }
      // Since we may have pulled subexpressions from more than one
      // level deep, we cannot guarantee that all the new kids are
      // fully simplified, and have to call simplify explicitly again.
      // Since this is potentially an expensive operation, we try to
      // minimize the need for it:

      // * check if the result has a find pointer (then kids don't
      //   need to be simplified),
      // * check if any of the kids simplify (if not, don't bother).
      // If kids are already simplified, we'll hit the simplifier
      // cache.  It's only expensive when kids do indeed simplify.
      if(!res.isRefl() && (theoryCore()->inUpdate() || !res.getRHS().hasFind())) {
        res = transitivityRule(res, simplify(res.getRHS()));
      }
      break;
    }
    case EXTRACT: {
      DebugAssert(e.arity() == 1, "TheoryBitvector::rewriteBV: e = "
		  +e.toString());
      if(getExtractLow(e) == 0 && getExtractHi(e) == BVSize(e[0])-1)
	res = d_rules->extractWhole(e);
      else {
	switch(e[0].getOpKind()) {
	case BVCONST:
	  res = d_rules->extractConst(e);
	  break;
	case EXTRACT:
	  res = d_rules->extractExtract(e);
	  break;
	case CONCAT:
	  // Push extraction through concat, and rewrite the kids
	  res = rewriteBV(d_rules->extractConcat(e), cache, 2);
	  break;
	case BVNEG:
          res = rewriteBV(d_rules->extractNeg(e), cache, 2);
	  break;
	case BVAND:
	  res = rewriteBV(d_rules->extractAnd(e), cache, 2);
	  break;
	case BVOR:
	  res = rewriteBV(d_rules->extractOr(e), cache, 2);
	  break;
	case BVXOR:
	  res =
	    rewriteBV(d_rules->extractBitwise(e, BVXOR, "extract_bvxor"), cache, 2);
	  break;
	case BVMULT: {
	  const Expr& bvmult = e[0];
	  int hiBit = getExtractHi(e);
	  int bvmultLen = BVSize(bvmult);
	  // Applicable if it changes anything
	  if(hiBit+1 < bvmultLen) {
	    res = d_rules->extractBVMult(e);
            res = rewriteBV(res, cache, 3);
	  } else
	    res = reflexivityRule(e);
	  break;
	}
	case BVPLUS: {
	  const Expr& bvplus = e[0];
	  int hiBit = getExtractHi(e);
	  int bvplusLen = BVSize(bvplus);
	  if(hiBit+1 < bvplusLen) {
	    res = d_rules->extractBVPlus(e);
	  } else res = reflexivityRule(e);
	  break;
	}
	default:
	  res = reflexivityRule(e);
	  break;
	}
      }
      if (!res.isRefl()) {
        res = transitivityRule(res, simplify(res.getRHS()));
      }
      break;
    }
    case BOOLEXTRACT: {
      Expr t(e);
      // Normal form: t[0] for 1-bit t, collapse t[i:i][0] into t[i]
      if(BVSize(e[0]) > 1) { // transform t[i] to t[i:i][0] and rewrite
        res = rewriteBV(d_rules->bitExtractRewrite(e), cache, 2);
        t = res.getRHS();
      }
      if(t.getOpKind() == BOOLEXTRACT && t[0].getOpKind() == EXTRACT) {
        // Collapse t[i:i][0] to t[i]
        int low = getExtractLow(t[0]);
        if(getExtractHi(t[0]) == low) {
          Theorem thm(d_rules->bitExtractRewrite
                      (newBoolExtractExpr(t[0][0], low)));
          thm = symmetryRule(thm);
          res = (res.isNull())? thm : transitivityRule(res, thm);
          t = res.getRHS()[0];
          // Make sure t in the resulting t[i] is its own find pointer
          // (global invariant)
          if(t.hasFind()) {
            Theorem findThm = find(t);
            if(t != findThm.getRHS()) {
              vector<Theorem> thms;
              thms.push_back(findThm);
              thm = substitutivityRule(res.getRHS().getOp(), thms);
              res = transitivityRule(res, thm);
            }
          }
        }
      }
      if(!res.isNull()) t = res.getRHS();
      // Rewrite a constant extraction to TRUE or FALSE
      if(t.getOpKind() == BOOLEXTRACT && constantKids(t)) {
        Theorem thm = d_rules->bitExtractConstant(t[0], getBoolExtractIndex(t));
        res = (res.isNull())? thm : transitivityRule(res, thm);
      }
      break;
    }
    case LEFTSHIFT:
        if (e[0].getKind() == BVCONST && computeBVConst(e[0]) == 0) {
          res = d_rules->bvShiftZero(e);
        } else {
        	res = d_rules->leftShiftToConcat(e);
        	if (!res.isRefl()) {
        		res = transitivityRule(res, simplify(res.getRHS()));
        	}
        }
        break;
    case CONST_WIDTH_LEFTSHIFT:
        if (e[0].getKind() == BVCONST && computeBVConst(e[0]) == 0) {
          res = d_rules->bvShiftZero(e);
        } else {
        	res = d_rules->constWidthLeftShiftToConcat(e);
        	if (!res.isRefl()) {
        		res = transitivityRule(res, simplify(res.getRHS()));
        	}
        }
        break;
    case RIGHTSHIFT:
        if (e[0].getKind() == BVCONST && computeBVConst(e[0]) == 0) {
          res = d_rules->bvShiftZero(e);
        } else {
        	res = d_rules->rightShiftToConcat(e);
        	if (!res.isRefl()) {
        		res = transitivityRule(res, simplify(res.getRHS()));
        	}
        }
        break;
    case BVSHL:
      if (e[0].getKind() == BVCONST && computeBVConst(e[0]) == 0) {
        res = d_rules->bvShiftZero(e);
      } else
      if (e[1].getKind() == BVCONST) {
        res = d_rules->bvshlToConcat(e);
        res = transitivityRule(res, simplify(res.getRHS()));
      }
//       else {
//         res = d_rules->bvshlSplit(e);
//         res = transitivityRule(res, simplify(res.getRHS()));
//       }
      break;
    case BVLSHR:
      if (e[0].getKind() == BVCONST && computeBVConst(e[0]) == 0) {
        res = d_rules->bvShiftZero(e);
      } else
      if (e[1].getKind() == BVCONST) {
        res = d_rules->bvlshrToConcat(e);
        res = transitivityRule(res, simplify(res.getRHS()));
      }
      break;
    case BVASHR:
      if (e[0].getKind() == BVCONST && computeBVConst(e[0]) == 0) {
    	res = d_rules->bvShiftZero(e);
      } else
    	  if (e[1].getKind() == BVCONST) {
            res = d_rules->bvashrToConcat(e);
            res = transitivityRule(res, simplify(res.getRHS()));
          }
      break;
    case SX: {
      res = d_rules->signExtendRule(e);
      res = transitivityRule(res, simplify(res.getRHS()));
      break;
    }

    case BVZEROEXTEND:
      res = d_rules->zeroExtendRule(e);
      res = transitivityRule(res, simplify(res.getRHS()));
      break;

    case BVREPEAT:
      res = d_rules->repeatRule(e);
      res = transitivityRule(res, simplify(res.getRHS()));
      break;

    case BVROTL:
      res = d_rules->rotlRule(e);
      res = transitivityRule(res, simplify(res.getRHS()));
      break;

    case BVROTR:
      res = d_rules->rotrRule(e);
      res = transitivityRule(res, simplify(res.getRHS()));
      break;

    case BVAND:
    case BVOR:
    case BVXOR:
    {
      int kind = e.getOpKind();
      // Flatten the bit-wise AND, eliminate duplicates, reorder terms
      res = d_rules->bitwiseFlatten(e, kind);
      Expr ee = res.getRHS();
      if (ee.getOpKind() != kind) break;

      // Search for constant bitvectors
      vector<int> idxs;
      constantKids(ee, idxs);
      int idx = -1;

      if(idxs.size() >= 2) {
        res = transitivityRule(res, d_rules->bitwiseConst(ee, idxs, kind));
        ee = res.getRHS();
        if (ee.getOpKind() != kind) break;
        idx = 0;
      }
      else if (idxs.size() == 1) {
        idx = idxs[0];
      }

      if (idx >= 0) {
        res = transitivityRule(res, d_rules->bitwiseConstElim(ee, idx, kind));
        ee = res.getRHS();
      }
      if (ee.getOpKind() == kind) {
        res = transitivityRule(res, d_rules->bitwiseConcat(ee, kind));
      }
      if (!res.isRefl()) {
        res = transitivityRule(res, simplify(res.getRHS()));
      }
      else {
        e.setRewriteNormal();
      }
      break;
    }
    case BVXNOR: {
      res = d_rules->rewriteXNOR(e);
      res = transitivityRule(res, simplify(res.getRHS()));
      break;
    }
    case BVNEG: {
      res = pushNegation(e);
      if (!res.isRefl()) {
        res = transitivityRule(res, simplify(res.getRHS()));
      }
      break;
    }
    case BVNAND: {
      res = d_rules->rewriteNAND(e);
      res = transitivityRule(res, simplify(res.getRHS()));
      break;
    }
    case BVNOR: {
      res = d_rules->rewriteNOR(e);
      res = transitivityRule(res, simplify(res.getRHS()));
      break;
    }
    case BVCOMP: {
      res = d_rules->rewriteBVCOMP(e);
      res = transitivityRule(res, simplify(res.getRHS()));
      break;
    }
    case BVUMINUS:
    {
      res = d_rules->canonBVUMinus( e );
      res = transitivityRule(res, simplify(res.getRHS()));
      break;
    }
    case BVPLUS:
    {
      res = d_rules->canonBVPlus(e );
      if (!res.isRefl()) {
        res = transitivityRule(res, simplify(res.getRHS()));
      }
      else e.setRewriteNormal();
      break;
    }
    case BVSUB: {
      res = d_rules->rewriteBVSub(e);
      res = transitivityRule(res, simplify(res.getRHS()));
      break;
    }
    case BVMULT:
    {
      res = d_rules->liftConcatBVMult(e);
      if (!res.isRefl()) {
        res = transitivityRule(res, simplify(res.getRHS()));
      }
      else {
        res =  d_rules->canonBVMult( e );
        if (!res.isRefl())
          res = transitivityRule(res, simplify(res.getRHS()));
        else e.setRewriteNormal();
      }
      break;
    }

    case BVUDIV:
    {
      Expr a = e[0];
      Expr b = e[1];

      // Constant division
      if (a.getOpKind() == BVCONST && b.getOpKind() == BVCONST) {
        res = d_rules->bvUDivConst(e);
        break;
      }

      if (theoryCore()->okToEnqueue())
      {
        // get the full theorem
        // e = x/y
        // \exists div, mod: e = div & (y != 0 -> ...)
        // result is the equality
        // assert the additional conjunct
        Theorem fullTheorem =  d_rules->bvUDivTheorem(e);
        // Skolemise the variables
        Theorem skolem_div = getCommonRules()->skolemize(fullTheorem);
        // Get the rewrite part
        res = getCommonRules()->andElim(skolem_div, 0);
        // Get the division part
        Theorem additionalConstraint = getCommonRules()->andElim(skolem_div, 1);
        // Enqueue the division part
        enqueueFact(additionalConstraint);
        res = transitivityRule(res, simplify(res.getRHS()));
      } else {
        res = reflexivityRule(e);
      }
      break;
    }
    case BVSDIV:
    	res = d_rules->bvSDivRewrite(e);
    	res = transitivityRule(res, simplify(res.getRHS()));
    	break;
    case BVUREM:
    {
    	Expr a = e[0];
    	Expr b = e[1];

    	// Constant division
    	if (a.getOpKind() == BVCONST && b.getOpKind() == BVCONST) {
          res = d_rules->bvURemConst(e);
          break;
    	}

       	res = d_rules->bvURemRewrite(e);
       	res = transitivityRule(res, theoryCore()->simplify(res.getRHS()));

    	break;
    }
    case BVSREM:
    	res = d_rules->bvSRemRewrite(e);
    	res = transitivityRule(res, simplify(res.getRHS()));
    	break;
    case BVSMOD:
    	res = d_rules->bvSModRewrite(e);
    	res = transitivityRule(res, simplify(res.getRHS()));
    	break;
    case BVLT:
    case BVLE: {
      Expr lhs = e[0];
      Expr rhs = e[1];
      if (BVSize(lhs) != BVSize(rhs)) {
        res = d_rules->padBVLTRule(e, BVSize(lhs) > BVSize(rhs) ? BVSize(lhs) : BVSize(rhs));
        res = transitivityRule(res, simplify(res.getRHS()));
      }
      else {
        if(lhs == rhs)
          res = d_rules->lhsEqRhsIneqn(e, e.getOpKind());
        else if (BVCONST == lhs.getKind() && BVCONST == rhs.getKind())
          res = d_rules->bvConstIneqn(e, e.getOpKind());
        else if (e.getOpKind() == BVLE && BVCONST == lhs.getKind() && computeBVConst(lhs) == 0)
          res = d_rules->zeroLeq(e);
      }
      break;
    }

    case BVGT:
    case BVGE:
      FatalAssert(false, "Should be eliminated at parse-time");
      break;

    case BVSLT:
    case BVSLE:{
      /*! input: e0 <=(s) e1. output depends on whether the topbits(MSB) of
       *  e0 and e1 are constants. If they are constants then optimizations
       *  are done. In general, the following rule is implemented.
       * Step1:
       *                    e0 <=(s) e1
       *                       <==>
       *                 pad(e0) <=(s) pad(e1)
       * Step2:
       *                 pad(e0) <=(s) pad(e1)
       *                       <==>
       *             (e0[n-1] AND NOT e1[n-1]) OR
       *             (e0[n-1] = e1[n-1] AND e0[n-2:0] <= e1[n-2:0])
       */
      int e0len = BVSize(e[0]);
      int e1len = BVSize(e[1]);
      int bvlength = e0len>=e1len ? e0len : e1len;
      //e0 <=(s) e1 <=> signpad(e0) <=(s) signpad(e1)

      std::vector<Theorem> thms;
      std::vector<unsigned> changed;

      //e0 <= e1 <==> pad(e0) <= pad(e1)
      Theorem thm = d_rules->padBVSLTRule(e, bvlength);
      Expr paddedE = thm.getRHS();

      //the rest of the code simply normalizes pad(e0) and pad(e1)
      Theorem thm0 = d_rules->signExtendRule(paddedE[0]);
      Expr rhs0 = thm0.getRHS();
      thm0 = transitivityRule(thm0, rewriteBV(rhs0, cache));
      if(thm0.getLHS() != thm0.getRHS()) {
        thms.push_back(thm0);
        changed.push_back(0);
      }

      Theorem thm1 = d_rules->signExtendRule(paddedE[1]);
      Expr rhs1 = thm1.getRHS();
      thm1 = transitivityRule(thm1, rewriteBV(rhs1, cache));
      if(thm1.getLHS() != thm1.getRHS()) {
        thms.push_back(thm1);
        changed.push_back(1);
      }

      if(changed.size() > 0) {
        thm0 = substitutivityRule(paddedE,changed,thms);
        thm0 = transitivityRule(thm, thm0);
      }
      else
        thm0 = reflexivityRule(e);

      //signpad(e0) <= signpad(e1)
      Expr thm0RHS = thm0.getRHS();
      DebugAssert(thm0RHS.getOpKind() == BVSLT ||
                  thm0RHS.getOpKind() == BVSLE,
                  "TheoryBitvector::RewriteBV");
      //signpad(e0)[bvlength-1:bvlength-1]
      const Expr MSB0 = newBVExtractExpr(thm0RHS[0],bvlength-1,bvlength-1);
      //signpad(e1)[bvlength-1:bvlength-1]
      const Expr MSB1 = newBVExtractExpr(thm0RHS[1],bvlength-1,bvlength-1);
      //rewritten MSB0
      const Theorem topBit0 = rewriteBV(MSB0, cache, 2);
      //rewritten MSB1
      const Theorem topBit1 = rewriteBV(MSB1, cache, 2);
      //compute e0 <=(s) e1 <==> signpad(e0) <=(s) signpad(e1) <==>
      //output as given above
      thm1 = d_rules->signBVLTRule(thm0RHS, topBit0, topBit1);
      thm1 = transitivityRule(thm1,simplify(thm1.getRHS()));
      res = transitivityRule(thm0,thm1);
      break;
    }
    case BVSGT:
    case BVSGE:
      FatalAssert(false, "Should be eliminated at parse-time");
      break;
    default:
      res = reflexivityRule(e);
      break;
  }

  if (res.isNull()) res = reflexivityRule(e);

  // Update cache
  cache[e] = res;

  TRACE("bitvector rewrite", "TheoryBitvector::rewriteBV => ",
	res.getExpr(), " }");

  return res;
}


Theorem TheoryBitvector::rewriteBV(const Expr& e, int n)
{
  ExprMap<Theorem> cache;
  return rewriteBV(e, cache, n);
}


Theorem TheoryBitvector::rewriteBoolean(const Expr& e)
{
  Theorem thm;
  switch (e.getKind()) {
  case NOT:
    if (e[0].isTrue())
      thm = getCommonRules()->rewriteNotTrue(e);
    else if (e[0].isFalse())
      thm = getCommonRules()->rewriteNotFalse(e);
    else if (e[0].isNot())
      thm = getCommonRules()->rewriteNotNot(e);
    break;
  case IFF: {
    thm = getCommonRules()->rewriteIff(e);
    const Expr& rhs = thm.getRHS();
    // The only time we need to rewrite the result (rhs) is when
    // e==(FALSE<=>e1) or (e1<=>FALSE), so rhs==!e1.
    if (e != rhs && rhs.isNot())
      thm = transitivityRule(thm, rewriteBoolean(rhs));
    break;
  }
  case AND:{
    std::vector<Theorem> newK;
    std::vector<unsigned> changed;
    unsigned count(0);
    for(Expr::iterator ii=e.begin(),iiend=e.end();ii!=iiend;ii++,count++) {
      Theorem temp = rewriteBoolean(*ii);
      if(temp.getLHS() != temp.getRHS()) {
	newK.push_back(temp);
	changed.push_back(count);
      }
    }
    if(changed.size() > 0) {
      Theorem res = substitutivityRule(e,changed,newK);
      thm = transitivityRule(res, rewriteAnd(res.getRHS()));
    } else
      thm = rewriteAnd(e);
  }
    break;
  case OR:{
    std::vector<Theorem> newK;
    std::vector<unsigned> changed;
    unsigned count(0);
    for(Expr::iterator ii=e.begin(),iiend=e.end();ii!=iiend;ii++,count++) {
      Theorem temp = rewriteBoolean(*ii);
      if(temp.getLHS() != temp.getRHS()) {
	newK.push_back(temp);
	changed.push_back(count);
      }
    }
    if(changed.size() > 0) {
      Theorem res = substitutivityRule(e,changed,newK);
      thm = transitivityRule(res, rewriteOr(res.getRHS()));
    } else
      thm = rewriteOr(e);
  }
    break;

  default:
    break;
  }
  if(thm.isNull()) thm = reflexivityRule(e);

  return thm;
}


///////////////////////////////////////////////////////////////////////////////
// TheoryBitvector Public Methods                                            //
///////////////////////////////////////////////////////////////////////////////
TheoryBitvector::TheoryBitvector(TheoryCore* core)
  : Theory(core, "Bitvector"),
    d_bvDelayEq(core->getStatistics().counter("bv delayed assert eqs")),
    d_bvAssertEq(core->getStatistics().counter("bv eager assert eqs")),
    d_bvDelayDiseq(core->getStatistics().counter("bv delayed assert diseqs")),
    d_bvAssertDiseq(core->getStatistics().counter("bv eager assert diseqs")),
    d_bvTypePreds(core->getStatistics().counter("bv type preds enqueued")),
    d_bvDelayTypePreds(core->getStatistics().counter("bv type preds delayed")),
    d_bvBitBlastEq(core->getStatistics().counter("bv bitblast eqs")),
    d_bvBitBlastDiseq(core->getStatistics().counter("bv bitblast diseqs")),
    d_bv32Flag(&(core->getFlags()["bv32-flag"].getBool())),
    d_bitvecCache(core->getCM()->getCurrentContext()),
    d_eq(core->getCM()->getCurrentContext()),
    d_eqPending(core->getCM()->getCurrentContext()),
    d_eq_index(core->getCM()->getCurrentContext(), 0, 0),
    d_bitblast(core->getCM()->getCurrentContext()),
    d_bb_index(core->getCM()->getCurrentContext(), 0, 0),
    d_sharedSubterms(core->getCM()->getCurrentContext()),
    d_sharedSubtermsList(core->getCM()->getCurrentContext()),
    d_maxLength(0),
    d_index1(core->getCM()->getCurrentContext(), 0, 0),
    d_index2(core->getCM()->getCurrentContext(), 0, 0)
    //    d_solvedEqSet(core->getCM()->getCurrentContext(), 0, 0)
{
  getEM()->newKind(BITVECTOR, "_BITVECTOR", true);
  getEM()->newKind(BVCONST, "_BVCONST");
  getEM()->newKind(CONCAT, "_CONCAT");
  getEM()->newKind(EXTRACT, "_EXTRACT");
  getEM()->newKind(BOOLEXTRACT, "_BOOLEXTRACT");
  getEM()->newKind(LEFTSHIFT, "_LEFTSHIFT");
  getEM()->newKind(CONST_WIDTH_LEFTSHIFT, "_CONST_WIDTH_LEFTSHIFT");
  getEM()->newKind(RIGHTSHIFT, "_RIGHTSHIFT");
  getEM()->newKind(BVSHL, "_BVSHL");
  getEM()->newKind(BVLSHR, "_BVLSHR");
  getEM()->newKind(BVASHR, "_BVASHR");
  getEM()->newKind(SX,"_SX");
  getEM()->newKind(BVREPEAT,"_BVREPEAT");
  getEM()->newKind(BVZEROEXTEND,"_BVZEROEXTEND");
  getEM()->newKind(BVROTL,"_BVROTL");
  getEM()->newKind(BVROTR,"_BVROTR");
  getEM()->newKind(BVAND, "_BVAND");
  getEM()->newKind(BVOR, "_BVOR");
  getEM()->newKind(BVXOR, "_BVXOR");
  getEM()->newKind(BVXNOR, "_BVXNOR");
  getEM()->newKind(BVNEG, "_BVNEG");
  getEM()->newKind(BVNAND, "_BVNAND");
  getEM()->newKind(BVNOR, "_BVNOR");
  getEM()->newKind(BVCOMP, "_BVCOMP");
  getEM()->newKind(BVUMINUS, "_BVUMINUS");
  getEM()->newKind(BVPLUS, "_BVPLUS");
  getEM()->newKind(BVSUB, "_BVSUB");
  getEM()->newKind(BVMULT, "_BVMULT");
  getEM()->newKind(BVUDIV, "_BVUDIV");
  getEM()->newKind(BVSDIV, "_BVSDIV");
  getEM()->newKind(BVUREM, "_BVUREM");
  getEM()->newKind(BVSREM, "_BVSREM");
  getEM()->newKind(BVSMOD, "_BVSMOD");
  getEM()->newKind(BVLT, "_BVLT");
  getEM()->newKind(BVLE, "_BVLE");
  getEM()->newKind(BVGT, "_BVGT");
  getEM()->newKind(BVGE, "_BVGE");
  getEM()->newKind(BVSLT, "_BVSLT");
  getEM()->newKind(BVSLE, "_BVSLE");
  getEM()->newKind(BVSGT, "_BVSGT");
  getEM()->newKind(BVSGE, "_BVSGE");
  getEM()->newKind(INTTOBV, "_INTTOBV");
  getEM()->newKind(BVTOINT, "_BVTOINT");
  getEM()->newKind(BVTYPEPRED, "_BVTYPEPRED");

  std::vector<int> kinds;
  kinds.push_back(BITVECTOR);
  kinds.push_back(BVCONST);
  kinds.push_back(CONCAT);
  kinds.push_back(EXTRACT);
  kinds.push_back(BOOLEXTRACT);
  kinds.push_back(LEFTSHIFT);
  kinds.push_back(CONST_WIDTH_LEFTSHIFT);
  kinds.push_back(RIGHTSHIFT);
  kinds.push_back(BVSHL);
  kinds.push_back(BVLSHR);
  kinds.push_back(BVASHR);
  kinds.push_back(SX);
  kinds.push_back(BVREPEAT);
  kinds.push_back(BVZEROEXTEND);
  kinds.push_back(BVROTL);
  kinds.push_back(BVROTR);
  kinds.push_back(BVAND);
  kinds.push_back(BVOR);
  kinds.push_back(BVXOR);
  kinds.push_back(BVXNOR);
  kinds.push_back(BVNEG);
  kinds.push_back(BVNAND);
  kinds.push_back(BVNOR);
  kinds.push_back(BVCOMP);
  kinds.push_back(BVUMINUS);
  kinds.push_back(BVPLUS);
  kinds.push_back(BVSUB);
  kinds.push_back(BVMULT);
  kinds.push_back(BVUDIV);
  kinds.push_back(BVSDIV);
  kinds.push_back(BVUREM);
  kinds.push_back(BVSREM);
  kinds.push_back(BVSMOD);
  kinds.push_back(BVLT);
  kinds.push_back(BVLE);
  kinds.push_back(BVGT);
  kinds.push_back(BVGE);
  kinds.push_back(BVSLT);
  kinds.push_back(BVSLE);
  kinds.push_back(BVSGT);
  kinds.push_back(BVSGE);
  kinds.push_back(INTTOBV);
  kinds.push_back(BVTOINT);
  kinds.push_back(BVTYPEPRED);

  registerTheory(this, kinds);

  d_bvConstExprIndex = getEM()->registerSubclass(sizeof(BVConstExpr));

  // Cache constants 0bin0 and 0bin1
  vector<bool> bits(1);
  bits[0]=false;
  d_bvZero = newBVConstExpr(bits);
  bits[0]=true;
  d_bvOne = newBVConstExpr(bits);

  // Instantiate the rules after all expression creation is
  // registered, since the constructor creates some bit-vector
  // expressions.
  d_rules = createProofRules();
}


// Destructor: delete the proof rules class if it's present
TheoryBitvector::~TheoryBitvector() {
  if(d_rules != NULL) delete d_rules;
}


// Main theory API


void TheoryBitvector::addSharedTerm(const Expr& e)
{
}


/*Modified by Lorenzo PLatania*/

// solvable fact (e.g. solvable equations) are added to d_eq CDList,
// all the others have to be in a different CDList. If the equation is
// solvable it comes here already solved. Should distinguish between
// solved and not solved eqs
void TheoryBitvector::assertFact(const Theorem& e)
{
  const Expr& expr = e.getExpr();
  TRACE("bvAssertFact", "TheoryBitvector::assertFact(", e.getExpr().toString(), ")");
  //  cout<<"TheoryBitvector::assertFact, expr: "<<expr.toString()<<endl;
  // every time a new fact is added to the list the whole set may be
  // not in a solved form

  switch (expr.getOpKind()) {

    case BVTYPEPRED:
      assertTypePred(expr[0], e);
      break;

    case BOOLEXTRACT:
      // facts form the SAT solver are just ignored
      return;

    case NOT:
      // facts form the SAT solver are just ignored
      if (expr[0].getOpKind() == BOOLEXTRACT) return;

      if (expr[0].getOpKind() == BVTYPEPRED) {
        Expr tpExpr = getTypePredExpr(expr[0]);
        Theorem tpThm = typePred(tpExpr);
        DebugAssert(tpThm.getExpr() == expr[0], "Expected BVTYPEPRED theorem");
        setInconsistent(getCommonRules()->contradictionRule(tpThm, e));
        return;
      }

      DebugAssert(expr[0].isEq(), "Unexpected negation");

      d_bitblast.push_back(e);
      break;

    case EQ:
      // Updates are also ignored:
      // Note: this can only be true if this fact was asserted as a result of
      // assertEqualities.  For BV theory, this should only be possible if
      // the update was made from our own theory, so we can ignore it.
      if (theoryCore()->inUpdate()) return;

      // If we have already started bitblasting, just store the eq in d_bitblast;
      // if we haven't yet bitblasted and expr is a solved linear equation then
      // we store it in d_eq CDList, otherwise we store it in d_eqPending
      if (d_bb_index != 0) {
        d_bitblast.push_back(e);
      }
      else if (isLeaf(expr[0]) && !isLeafIn(expr[0], expr[1])) {
        d_eq.push_back( e );
      }
      else {
        d_eqPending.push_back( e );
      }
      break;

    default:
      // if the fact is not an equation it will be bit-blasted
      d_bitblast.push_back( e );
      break;
  }
}


//TODO: can we get rid of this in exchange for a more general politeness-based sharing mechanism?
void TheoryBitvector::assertTypePred(const Expr& e, const Theorem& pred) {
  // Ignore bitvector constants (they always satisfy type predicates)
  // and bitvector operators.  When rewrites and updates are enabled.
  // their type predicates will be implicitly derived from the type
  // predicates of the arguments.

  if (theoryOf(e) == this) return;
  TRACE("bvAssertTypePred", "TheoryBitvector::assertTypePred(", e.toString(PRESENTATION_LANG), ")");
  addSharedTerm(e);
}


/*Beginning of Lorenzo PLatania's methods*/

// evaluates the gcd of two integers using
// Euclid algorithm
// int TheoryBitvector::gcd(int c1, int c2)
// {
//   if(c2==0)
//     return c1;
//   else
//     return gcd( c2, c1%c2);
// }

void TheoryBitvector::extract_vars(const Expr& e, vector<Expr>& result)
{
  if (e.getOpKind() == BVMULT ) {
    extract_vars(e[0], result);
    extract_vars(e[1], result);
  }
  else {
    DebugAssert(e.getOpKind() != BVCONST &&
                e.getOpKind() != BVUMINUS &&
                e.getOpKind() != BVPLUS, "Unexpected structure");
    result.push_back(e);
  }
}


Expr TheoryBitvector::multiply_coeff( Rational mult_inv, const Expr& e)
{

  // nothing to be done
  if( mult_inv == 1)
    return e;
  if(e.isEq())
    {
      Expr lhs = e[0];
      Expr rhs = e[1];
      Expr new_lhs = multiply_coeff( mult_inv, lhs);
      Expr new_rhs = multiply_coeff( mult_inv, rhs);
      Expr res(EQ, new_lhs, new_rhs);
      return res;
    }
  else
    {
      int kind = e.getOpKind();
      int size = BVSize(e);
      if( kind == BVMULT )
	{

	  //lhs is like 'a_0*x_0'
	  Rational new_coeff = mult_inv * computeBVConst( e[0] );
	  Expr new_expr_coeff = newBVConstExpr( new_coeff, size);
 	  Expr BV_one = newBVConstExpr(1,size);
  	  if( new_expr_coeff == BV_one )
	    {
	      return e[1];
	    }
	  else
	    {
	      return newBVMultExpr( size, new_expr_coeff, e[1]);
	    }
	}
      else
	if( kind == BVPLUS)
	  {

	    int expr_arity= e.arity();
	    std::vector<Expr> tmp_list;
	    for( int i = 0; i < expr_arity; ++i)
	      {
		tmp_list.push_back(multiply_coeff( mult_inv, e[i]));
	      }
// 	    Expr::iterator i = e.begin();
// 	    int index;
// 	    Expr::iterator end = e.end();
// 	    std::vector<Expr> tmp_list;
// 	    for( i = e.begin(), index=0; i!=end; ++i, ++index)
// 	      {
// 		tmp_list.push_back(multiply_coeff( mult_inv, *i));
// 	      }
	    return newBVPlusExpr(size, tmp_list);
	  }
	else
	  if( kind == BVCONST )
	    {

	      Rational new_const = mult_inv * computeBVConst(e);
	      Expr res = newBVConstExpr( new_const, size);
              //	      cout<<res.toString()+"\n";
	      return res;
	    }
	  else
	    if( isLeaf( e ) )
	      {
		//lhs is like 'x_0'
		// need to know the lenght of the var
		// L:: guess it is not correct, mult_inv * e
		Expr BV_mult_inv = newBVConstExpr( mult_inv, size);
		Expr new_var = newBVMultExpr( size, BV_mult_inv, e);

		return new_var;
	      }
	    else
	      {
		return e;
	      }
    }
}

// L::return the index of the minimum element returns -1 if the list
// is empty assuming only non-negative elements to be sostituted with
// some debug assertion. ***I guess n_bits can be just an integer, no
// need to declare it as a Rational

Rational TheoryBitvector::multiplicative_inverse(Rational r, int n_bits)
{

  //  cout<<"TheoryBitvector::multiplicative_inverse: working on "<<r.toString()<<endl;
  Rational i=r;
  Rational max_val= pow( n_bits, (Rational) 2);
  while(r!=1)
    {
      r = ( r*r ) % max_val;
      i = ( i*r ) % max_val;
    }
  //  cout<<"TheoryBitvector::multiplicative_inverse: result is "<<i.toString()<<endl;
  return i;
}

// int TheoryBitvector::min(std::vector<Rational> list)
// {
//   int res = 0;
//   int i;
//   int size = list.size();
//   for(i = 0; i < size; ++i)
//     {
//       cout<<"list["<<i<<"]: "<<list[i]<<endl;
//     }
//   for(i = 1; i < size; ++i)
//     {
//       if(list[res]>list[i])
// 	res=i;
//       cout<<"res: "<<res<<endl;
//       cout<<"min: "<<list[res]<<endl;
//     }

//   cout<<"min: "<<res<<endl;
//   return res;
// }

//***************************
// ecco come fare il delete!
//***************************

// int main ()
// {
//   unsigned int i;
//   deque<unsigned int> mydeque;

//   // set some values (from 1 to 10)
//   for (i=1; i<=10; i++) mydeque.push_back(i);

//   // erase the 6th element
//   mydeque.erase (mydeque.begin()+5);

//   // erase the first 3 elements:
//   mydeque.erase (mydeque.begin(),mydeque.begin()+3);

//   cout << "mydeque contains:";
//   for (i=0; i<mydeque.size(); i++)
//     cout << " " << mydeque[i];
//   cout << endl;

//   return 0;
// }

// use the method in rational.h
// it uses std::vector<Rational> instead of std::deque<int>
// int TheoryBitvector::gcd(std::deque<int> coeff_list)
// {

//   cout<<"TheoryBitvector::gcd: begin\n";
//   for(unsigned int i=0; i<coeff_list.size(); ++i)
//     {
//       cout<<"coeff_list["<<i<<"]: "<<coeff_list[i]<<endl;
//     }
//   int gcd_list;
//   int min_index = min(coeff_list);
//   int min_coeff_1 = coeff_list[min_index];
//   cout<<"erasing element: "<<coeff_list[min_index];
//   coeff_list.erase( coeff_list.begin() + min_index );

//   while(coeff_list.size()>0)
//     {
//       min_index = min(coeff_list);
//       int min_coeff_2 = coeff_list[min_index];
//       cout<<"erasing element: "<<coeff_list[min_index];
//       coeff_list.erase( coeff_list.begin() + min_index );

//       // save one recursion
//       gcd_list = gcd( min_coeff_2, min_coeff_1);
//       cout<<"TheoryBitvector::gcd: erased min1\n";
//       min_coeff_1 = gcd_list;
//     }
//   cout<<"gcd_list: "<<gcd_list<<endl;
//   return gcd_list;
// }

// int TheoryBitvector::bv2int(const Expr& e)
// {
//   int sum=0;
//   if(e.arity()==0 && ! e.isVar())
//     {
//       std::string tmp = e.toString();
//       int s_length = tmp.length();
//       int bit;
//       int exp;
//       // first 4 cells contains the bv prefix 0bin
//       // just discard them
//       for(int i=3; i < s_length; ++i)
// 	{
// 	  if(tmp[i]=='1')
// 	    {
// 	      sum += (int)std::pow((float) 2, s_length - 1 - i);
// 	    }
// 	}
//     }
//   else
//     {
//       cerr<<"error: non-constant to be converted\n";
//     }
//   return sum;
// }

// returning the position of the first odd coefficient found;
// moreover, it multiplies a variable which does not appear in other
// subterms. It assumes that the input expression has already been
// canonized, so the lhs is a flat BVPLUS expression and the rhs is a
// zero BVCONST

Rational TheoryBitvector::Odd_coeff( const Expr& e )
{
  int bv_size =  BVSize(e[0]);
  Expr bv_zero( newBVZeroString(bv_size));

  DebugAssert(e.getOpKind()==EQ && e[1] == bv_zero,
	      "TheoryBitvector::Odd_coeff: the input expression has a non valid form ");

  Expr lhs = e[0];
  if( lhs.getOpKind() == BVMULT )
    {
      if( lhs[0].getOpKind() == BVCONST && computeBVConst( lhs[0]) % 2 != 0)
	return computeBVConst( lhs[0] );
    }
  else
    if( isLeaf( lhs))
      return 1;
    else
      if( lhs.getOpKind() == BVPLUS )
	{
	  int lhs_arity = lhs.arity();
	  // scanning lhs in order to find a good odd coefficient
	  for( int i = 0; i < lhs_arity; ++i)
	    {
	      // checking that the subterm is a leaf
	      if( isLeaf( lhs[i] ) )
		{
		  // checking that the current subterm does not appear in other
		  // subterms
		  for( int j = 0; j < lhs_arity; ++j)
		    if( j != i && !isLeafIn( lhs[i], lhs[j] ))
		      return 1;
		}
	      else
		if( lhs[i].getOpKind() == BVMULT)
		  {
		    // the subterm is a BVMULT with a odd coefficient
		    if( lhs[i][0].getOpKind() == BVCONST && computeBVConst( lhs[i][0]) % 2 != 0)
		      {
			// checking that the current subterm does not appear in other
			// subterms
			int flag = 0;
			for( int j = 0; j < lhs_arity; ++j)
			  {
			    // as we can solve also for non-leaf terms we use
			    // isTermIn instead of isLeafIn
			    if( j != i && isTermIn( lhs[i][1], lhs[j] ))
			      flag = 1;
			  }
			// if the leaf is not a subterm of other terms in the
			// current expression then we can solve for it
			if( flag == 0)
			  return computeBVConst( lhs[i][0] );
		      }
		  }
		else
		  // the subterm is a non-linear one
		  if ( lhs[i].getOpKind() != BVCONST )
		    {
		      // checking that the current subterm does not appear in other
		      // subterms
		      for( int j = 0; j < lhs_arity; ++j)
			if( j != i && !isLeafIn( lhs[i][1], lhs[j] ))
			  return 1;
		    }
		  else
		    ;
	    }
	}
  // no leaf found to solve for
  return 0;
}

int TheoryBitvector::check_linear( const Expr &e )
{
  TRACE("bv_check_linear", "TheoryBitvector::check_linear(", e.toString(PRESENTATION_LANG), ")");
  // recursively check if the expression is linear
  if( e.isVar() || e.getOpKind() == BVCONST )
    return 1;
  else
    if( e.getOpKind() == BVPLUS )
      {
	int e_arity= e.arity();
	int flag = 1;
	for( int i=0; i < e_arity && flag == 1; ++i)
	  {
	    flag = check_linear( e[i]);
	  }
	return flag;
      }
    else
      if( e.getOpKind() == BVMULT)
	{
	  if( e[0].getOpKind() == BVCONST && e[1].isVar() )
	    return 1;
	  else
	    return 0;
	}
      else
	if( e.getOpKind() == BVUMINUS)
	  return check_linear( e[0]);
	else
	  if( e.getOpKind() == EQ )
	    return ( check_linear( e[0] ) && check_linear( e[1] ));
	  else
	    // all other operators are non-linear
	    return 0;
}

// please check it is right. It is the same as Theory::isLeafIn but it
// does not require e1 to be a leaf. In this way we can check for e1
// to be a subterm of other expressions even if it is not a leaf,
// i.e. a non-linear term
bool TheoryBitvector::isTermIn(const Expr& e1, const Expr& e2)
{
  if (e1 == e2) return true;
  if (theoryOf(e2) != this) return false;
  for(Expr::iterator i=e2.begin(), iend=e2.end(); i != iend; ++i)
    if (isTermIn(e1, *i)) return true;
  return false;
}

// checks whether e can be solved in term
bool TheoryBitvector::canSolveFor( const Expr& term, const Expr& e )
{
  DebugAssert( e.getOpKind() == EQ, "TheoryBitvector::canSolveFor, input 'e' must be an equation");

  //  cout<<"TheoryBitvector::canSolveFor, term: "<<term.toString()<<endl;
  // the term has not a unary coefficient, so we did not multiply the
  // equation by its multiplicative inverse
  if( term.getOpKind() == BVMULT && term[0].getOpKind() == BVCONST)
    return 0;
  else
    if( isLeaf( term ) || !isLinearTerm( term))
      {
	int count = countTermIn( term, e);
        //	cout<<"TheoryBitvector::canSolveFor, count for "<<term.toString()<<" is: "<<count<<endl;
	if( count == 1)
	  return true;
	else
	  return false;
      }
    else
      {
	DebugAssert( false, "TheoryBitvector::canSolveFor, input 'term' of not treated kind");
	return false;
      }
}

int TheoryBitvector::countTermIn( const Expr& term, const Expr& e)
{
  //  cout<<"TheoryBitvector::countTermIn, term: "<<term.toString()<<" e: "<<e.toString()<<endl;
  int e_arity = e.arity();
  int result = 0;
  // base cases recursion happen when e is a constant or a leaf
  if( e.getOpKind() == BVCONST )
    return 0;
  if( term ==  e )
    return 1;

  for( int i = 0; i < e_arity; ++i)
    {
      result += countTermIn( term, e[i]);
    }
  return result;
}

bool TheoryBitvector::isLinearTerm( const Expr& e )
{
  if( isLeaf( e ) )
    return true;
  switch( e.getOpKind())
    {
    case BVPLUS:
      return true;
    case BVMULT:
      if( e[0].getOpKind() == BVCONST && isLinearTerm( e[1] ))
	return true;
      else
	return false;
      break;
    default:
      return false;
    }
}


// returns thm if no change
Theorem TheoryBitvector::simplifyPendingEq(const Theorem& thm, int maxEffort)
{
  Expr e = thm.getExpr();
  DebugAssert(e.getKind() == EQ, "Expected EQ");
  Expr lhs = e[0];
  Expr rhs = e[1];

  Theorem thm2 = thm;
  if (!isLeaf(lhs)) {
    // Carefully simplify lhs:
    // We can't take find(lhs) because find(lhs) = find(rhs) and this would result in a trivially true equation.
    // So, take the find of the children instead.
    int ar = lhs.arity();
    vector<Theorem> newChildrenThm;
    vector<unsigned> changed;
    Theorem thm0;
    for (int k = 0; k < ar; ++k) {
      thm0 = find(lhs[k]);
      if (thm0.getLHS() != thm0.getRHS()) {
        newChildrenThm.push_back(thm0);
        changed.push_back(k);
      }
    }
    if(changed.size() > 0) {
      // lhs = updated_lhs
      thm0 = substitutivityRule(lhs, changed, newChildrenThm);
      // lhs = updated_and_rewritten_lhs
      thm0 = transitivityRule(thm0, rewrite(thm0.getRHS()));
      // updated_and_rewritten_lhs = rhs
      thm2 = transitivityRule(symmetryRule(thm0), thm);
    }
  }
  // updated_and_rewritten_lhs = find(rhs)
  thm2 = transitivityRule(thm2, find(rhs));
  // canonized EQ
  thm2 = iffMP(thm2, d_rules->canonBVEQ(thm2.getExpr(), maxEffort));
  if (thm2.isRewrite() && thm2.getRHS() == lhs && thm2.getLHS() == rhs) {
    thm2 = thm;
  }
  return thm2;
}


Theorem TheoryBitvector::generalBitBlast( const Theorem& thm )
{
  // cout<<"TheoryBitvector::generalBitBlast, thm: "<<thm.toString()<<" to expr(): "<<thm.getExpr().toString()<<endl;
  Expr e = thm.getExpr();
  switch (e.getOpKind()) {
    case EQ: {
      Theorem thm2 = simplifyPendingEq(thm, 6);
      const Expr& e2 = thm2.getExpr();
      switch (e2.getKind()) {
        case TRUE_EXPR:
        case FALSE_EXPR:
          return thm2;
        case EQ:
          return iffMP(thm2, bitBlastEqn(thm2.getExpr()));
        case AND: {
          DebugAssert(e2.arity() == 2 && e2[0].getKind() == EQ && e2[1].getKind() == EQ,
                      "Expected two equations");
          Theorem t1 = bitBlastEqn(e2[0]);
          Theorem t2 = bitBlastEqn(e2[1]);
          Theorem thm3 = substitutivityRule(e2, t1, t2);
          return iffMP(thm2, thm3);
        }
        default:
          FatalAssert(false, "Unexpected Expr");
          break;
      }
      break;
    }
    case BVLT:
    case BVLE: {
      // Carefully simplify
      int ar = e.arity();
      DebugAssert(ar == 2, "Expected arity 2");
      vector<Theorem> newChildrenThm;
      vector<unsigned> changed;
      Theorem thm0;
      for (int k = 0; k < ar; ++k) {
        thm0 = find(e[k]);
        if (thm0.getLHS() != thm0.getRHS()) {
          newChildrenThm.push_back(thm0);
          changed.push_back(k);
        }
      }
      if(changed.size() > 0) {
        // updated_e
        thm0 = iffMP(thm, substitutivityRule(e, changed, newChildrenThm));
        // updated_and_rewritten_e
        thm0 = iffMP(thm0, rewrite(thm0.getExpr()));
        if (thm0.getExpr().getOpKind() != e.getOpKind()) return thm0;
        return iffMP(thm0, bitBlastIneqn(thm0.getExpr()));
      }
      return iffMP(thm, bitBlastIneqn(e));
    }
    // a NOT should mean a disequality, as negation of inequalities
    // can be expressed as other inequalities.
    case NOT: {
      // Carefully simplify
      DebugAssert(e.arity() == 1, "Expected arity 1");
      DebugAssert(e[0].isEq(), "Expected disequality");
      DebugAssert(e[0].arity() == 2, "Expected arity 2");
      vector<Theorem> newChildrenThm;
      vector<unsigned> changed;
      Theorem thm0;
      for (int k = 0; k < 2; ++k) {
        thm0 = find(e[0][k]);
        if (thm0.getLHS() != thm0.getRHS()) {
          newChildrenThm.push_back(thm0);
          changed.push_back(k);
        }
      }
      if(changed.size() > 0) {
        // a = b <=> a' = b'
        thm0 = substitutivityRule(e[0], changed, newChildrenThm);
      }
      else thm0 = reflexivityRule(e[0]);
      // a = b <=> canonized EQ
      thm0 = transitivityRule(thm0, d_rules->canonBVEQ(thm0.getRHS(), 6));
      // NOT(canonized EQ)
      thm0 = iffMP(thm, substitutivityRule(e, thm0));
      if (thm0.getExpr()[0].isEq()) {
        return bitBlastDisEqn(thm0);
      }
      else return thm0;
    }
    default:
      FatalAssert(false, "TheoryBitvector::generalBitBlast: unknown expression kind");
      break;
  }
  return reflexivityRule( e );
}
/*End of Lorenzo PLatania's methods*/

static Expr findAtom(const Expr& e)
{
  if (e.isAbsAtomicFormula()) return e;
  for (int i = 0; i < e.arity(); ++i) {
    Expr e_i = findAtom(e[i]);
    if (!e_i.isNull()) return e_i;
  }
  return Expr();
}


bool TheoryBitvector::comparebv(const Expr& e1, const Expr& e2)
{
  int size = BVSize(e1);
  FatalAssert(size == BVSize(e2), "expected same size");
  Theorem c1, c2;
  int idx1 = -1;
  vector<Theorem> thms1;

  if (d_bb_index == 0) {
    Expr splitter = e1.eqExpr(e2);
    Theorem thm = simplify(splitter);
    if (!thm.getRHS().isBoolConst()) {
      addSplitter(e1.eqExpr(e2));
      return true;
    }
    // Store a dummy theorem to indicate bitblasting has begun
    d_bb_index = 1;
    d_bitblast.push_back(getCommonRules()->trueTheorem());
  }

  for (int i = 0; i < size; ++i) {
    c1 = bitBlastTerm(e1, i);
    c1 = transitivityRule(c1, simplify(c1.getRHS()));
    c2 = bitBlastTerm(e2, i);
    c2 = transitivityRule(c2, simplify(c2.getRHS()));
    thms1.push_back(c1);
    if (!c1.getRHS().isBoolConst()) {
      if (idx1 == -1) idx1 = i;
      continue;
    }
    if (!c2.getRHS().isBoolConst()) {
      continue;
    }
    if (c1.getRHS() != c2.getRHS()) return false;
  }
  if (idx1 == -1) {
    // If e1 is known to be a constant, assert that
    DebugAssert(e1.getKind() != BVCONST, "Expected non-const");
    assertEqualities(d_rules->bitExtractAllToConstEq(thms1));
    addSplitter(e1.eqExpr(e2));
    //    enqueueFact(getCommonRules()->trueTheorem());
    return true;
  }

  Theorem thm = bitBlastEqn(e1.eqExpr(e2));
  thm = iffMP(thm, simplify(thm.getExpr()));
  if (!thm.getExpr().isTrue()) {
    enqueueFact(thm);
    return true;
  }

  // Nothing to assert from bitblasted equation.  Best way to resolve this
  // problem is to split until the term can be equated with a bitvector
  // constant.
  Expr e = findAtom(thms1[idx1].getRHS());
  DebugAssert(!e.isNull(), "Expected atom");
  addSplitter(e);
  return true;
}

static bool bvdump = false;

void TheoryBitvector::checkSat(bool fullEffort)
{
	if(fullEffort) {

	for (unsigned i = 0; i < additionalRewriteConstraints.size(); i ++)
		enqueueFact(additionalRewriteConstraints[i]);
	additionalRewriteConstraints.clear();

    if (bvdump) {
      CDList<Theorem>::const_iterator it_list=d_eq.begin();
      unsigned int i;
      for(i=0; i<d_eq.size(); ++i)
      {
        cout<<"d_eq [" << i << "]= "<< it_list[i].getExpr().toString() << endl;
      }

      it_list=d_eqPending.begin();

      for(i=0; i<d_eqPending.size(); ++i)
      {
        cout<<"d_eqPending [" << i << "]= "<< it_list[i].getExpr().toString() << endl;
      }

      it_list=d_bitblast.begin();

      for(i=0; i<d_bitblast.size(); ++i)
      {
        cout<<"d_bitblast [" << i << "]= "<< it_list[i].getExpr().toString() << endl;
      }

      if (d_eq.size() || d_eqPending.size() || d_bitblast.size()) cout << endl;
    }

    unsigned eq_list_size = d_eqPending.size();
    bool bitBlastEq = d_eq_index < eq_list_size;
    if (d_bb_index == 0 && bitBlastEq) {
      bitBlastEq = false;
      unsigned eqIdx = d_eq_index;
      for(; eqIdx < eq_list_size; ++eqIdx) {
        Expr eq = d_eqPending[eqIdx].getExpr();
        DebugAssert(eq[1] == newBVConstExpr(Rational(0), BVSize(eq[0])), "Expected 0 on rhs");
        Theorem thm = simplifyPendingEq(d_eqPending[eqIdx], 5);
        if (thm == d_eqPending[eqIdx]) {
          bitBlastEq = true;
          continue;
        }
        const Expr& e2 = thm.getExpr();
        switch (e2.getKind()) {
          case TRUE_EXPR:
            break;
          case FALSE_EXPR:
            enqueueFact(thm);
            return;
          case EQ:
          case AND:
            if (simplify(thm.getExpr()).getRHS() == trueExpr()) {
              bitBlastEq = true;
              break;
            }
            for (; d_eq_index < eqIdx; d_eq_index = d_eq_index + 1) {
              d_eqPending.push_back(d_eqPending[d_eq_index]);
            }
            d_eq_index = d_eq_index + 1;
            enqueueFact(thm);
            return;
          default:
            FatalAssert(false, "Unexpected expr");
            break;
        }
      }
    }

   // Bitblast any new formulas
    unsigned bb_list_size = d_bitblast.size();
    bool bbflag = d_bb_index < bb_list_size || bitBlastEq;
    if (bbflag) {
      for( ; d_bb_index < bb_list_size; d_bb_index = d_bb_index + 1) {
        Theorem bb_result = generalBitBlast( d_bitblast[ d_bb_index ]);
        enqueueFact( bb_result);
      }
      if (d_bb_index == 0) {
        // push dummy on the stack to indicate bitblasting has started
        d_bb_index = 1;
        d_bitblast.push_back(getCommonRules()->trueTheorem());
      }
      for( ; d_eq_index < eq_list_size; d_eq_index = d_eq_index + 1) {
        Theorem bb_result = generalBitBlast( d_eqPending[ d_eq_index ]);
        enqueueFact( bb_result);
      }
      // If newly bitblasted formulas, skip the shared term check
      return;
    }
  }
}


Theorem TheoryBitvector::rewrite(const Expr& e)
{
  ExprMap<Theorem> cache;
  return rewriteBV(e, cache);
}


Theorem TheoryBitvector::rewriteAtomic(const Expr& e)
{
  return reflexivityRule(e);
}


void TheoryBitvector::setup(const Expr& e)
{
  int k(0), ar(e.arity());
  if( e.isTerm() ) {
    for ( ; k < ar; ++k) {
      e[k].addToNotify(this, e);
    }
  }
}


// Lorenzo's version
void TheoryBitvector::update(const Theorem& e, const Expr& d) {

  if (inconsistent()) return;
  //  cout<<"TheoryBitvector::update, theorem e:"<<e.toString()<<" expression d: "<<d.toString()<<endl;
  // Updating shared terms informations, code inherited from the old
  // version of the bitvector theory

  // Constants should never change their find pointers to non-constant
  // expressions
  DebugAssert(e.getLHS().getOpKind()!=BVCONST,
	      "TheoryBitvector::update(e="+e.getExpr().toString()
	      +", d="+d.toString());
  if (d.isNull()) {
    Expr lhs = e.getLHS();
    Expr rhs = e.getRHS();
    DebugAssert(d_sharedSubterms.find(lhs) != d_sharedSubterms.end(),
                "Expected lhs to be shared");
    CDMap<Expr,Expr>::iterator it = d_sharedSubterms.find(rhs);
    if (it == d_sharedSubterms.end()) {
      addSharedTerm(rhs);
    }
    return;
  }
// 	{
// 	  // found an equality between shared subterms!
//           bool changed = false;
// 	  if ((*it).second != lhs) {
// 	    lhs = (*it).second;
// 	    it = d_sharedSubterms.find(lhs);
// 	    DebugAssert(it != d_sharedSubterms.end() && (*it).second == lhs,
// 			"Invariant violated in TheoryBitvector::update");
//             changed = true;
// 	  }
// 	  if ((*it2).second != rhs) {
//             rhs = (*it2).second;
//             it2 = d_sharedSubterms.find(rhs);
//             DebugAssert(it2 != d_sharedSubterms.end() && (*it2).second == rhs,
//                         "Invariant violated in TheoryBitvector::update");
//             changed = true;
//           }
// 	  DebugAssert(findExpr(lhs) == e.getRHS() &&
// 		      findExpr(rhs) == e.getRHS(), "Unexpected value for finds");
// 	  // It may be needed to check whether the two terms are the
// 	  // same, in that case don't do anything
//           if (changed) {
//             Theorem thm = transitivityRule(find(lhs),symmetryRule(find(rhs)));
//             const Expr& expr = thm.getExpr();

//             if (d_bb_index == 0 &&
//                 isLeaf(expr[0]) && !isLeafIn(expr[0], expr[1])) {
//               d_eq.push_back( thm );
//             }
//             else {
//               d_bitblast.push_back( thm );
//             }
//           }


// 	  // canonize and solve befor asserting it
// 	  //	  cout<<"TheoryBitvector::update, thm.getRHS(): "<<thm.getRHS()<<" thm.getLHS():"<<thm.getLHS()<<" thm.getExpr():"<<thm.getExpr()<<endl;
// 	  Theorem rwt_thm = rewrite( thm.getExpr() );
// 	  Theorem solved_thm = solve( rwt_thm);
// 	  assertFact( solved_thm );
	  //	  assertFact( thm );
	  //    enqueueFact(iffMP(thm, bitBlastEqn(thm.getExpr())));
// 	}
//       else
// 	{
// 	  d_sharedSubterms[rhs] = (*it).second;
// 	}
//     }
  // Propagate the "find" information to all the terms in the notify
  // list of d

  // if d has no find there is nothing to be updated
  if (!d.hasFind()) return;

  if (find(d).getRHS() == d) {
//     Theorem thm = updateSubterms(d);
//     TRACE("bvupdate", "TheoryArithOld::update(): thm = ", thm, "");
//     DebugAssert(leavesAreSimp(thm.getRHS()), "updateHelper error: "
//  		+thm.getExpr().toString());
    Theorem thm = simplify(d);
    if (thm.getRHS().isAtomic()) {
      assertEqualities(thm);
    }
    else {
      // Simplify could introduce case splits in the expression.  Handle this by renaminig
      Theorem renameTheorem = renameExpr(d);
      enqueueFact(transitivityRule(symmetryRule(renameTheorem), thm));
      assertEqualities(renameTheorem);
    }
  }
}


Theorem TheoryBitvector::updateSubterms( const Expr& e )
{
  //  DebugAssert(canonRec(e).getRHS() == e, "canonSimp expects input to be canonized");
  int ar = e.arity();
  if (isLeaf(e)) return find(e);
  if (ar > 0) {
    vector<Theorem> newChildrenThm;
    vector<unsigned> changed;
    Theorem thm;
    for (int k = 0; k < ar; ++k) {
      thm = updateSubterms(e[k]);
      if (thm.getLHS() != thm.getRHS()) {
        newChildrenThm.push_back(thm);
        changed.push_back(k);
      }
    }
    if(changed.size() > 0) {
      thm = substitutivityRule(e, changed, newChildrenThm);
      thm = transitivityRule(thm, rewrite(thm.getRHS()));
      return transitivityRule(thm, find(thm.getRHS()));
    }
    else return find(e);
  }
  return find(e);
}


Theorem TheoryBitvector::solve(const Theorem& t)
{
  DebugAssert(t.isRewrite() && t.getLHS().isTerm(), "");
  Expr e = t.getExpr();

  if (isLeaf(e[0]) && !isLeafIn(e[0], e[1])) {
    // already solved
    return t;
  }
  else if (isLeaf(e[1]) && !isLeafIn(e[1], e[0])) {
    return symmetryRule(t);
  }
  else if (e[0].getOpKind() == EXTRACT && isLeaf(e[0][0])) {
    bool solvedForm;
    Theorem thm;
    if (d_rules->solveExtractOverlapApplies(e))
    {
      thm = iffMP(t, d_rules->solveExtractOverlap(e));
      solvedForm = true;
    }
    else
      thm = d_rules->processExtract(t, solvedForm);

    thm = getCommonRules()->skolemize(thm);

    if (solvedForm) return thm;
    else {
      enqueueFact(getCommonRules()->andElim(thm, 1));
      return getCommonRules()->andElim(thm, 0);
    }
  }
  else if (e[1].getOpKind() == EXTRACT && isLeaf(e[1][0])) {
    bool solvedForm;
    Theorem thm = getCommonRules()->skolemize(d_rules->processExtract(symmetryRule(t), solvedForm));
    if (solvedForm) return thm;
    else {
      enqueueFact(getCommonRules()->andElim(thm, 1));
      return getCommonRules()->andElim(thm, 0);
    }
  }

  IF_DEBUG(
    Theorem t2 = iffMP(t, d_rules->canonBVEQ(e));
    if (e[0] < e[1]) {
      DebugAssert(e[1].getOpKind() == BVCONST,
                  "Should be only case when lhs < rhs");
      t2 = symmetryRule(t2);
    }
    DebugAssert(t2.getExpr() == e, "Expected no change");
  )

  if (e[0].getOpKind() == BVCONST) {
    DebugAssert(e[1].getOpKind() != BVCONST, "should not have const = const");
    return symmetryRule(t);
  }
  return t;
}

//   // solving just linear equations; for everything else I just return
//   // the same expression
//   if( ! e.isEq())
//     {
//       return reflexivityRule( e );
//     }
//   //the search for the odd coefficient should also check that the
//   //multiplied term does not appear in other terms. The coefficient can
//   //also multiply a non-linear term


//   // L:: look for a odd coefficient, if one, then the eq is solvable
//   // and we can find the mult-inverse using Barrett-Dill-Levitt
//   Expr lhs = e[0];
//   Expr::iterator it = lhs.begin(), iend = lhs.end();
//   for (; it != iend; ++it) {
//     switch ((*it).getOpKind()) {
//       case BVCONST: continue;
//       case BVMULT: {
//         DebugAssert((*it).arity() == 2 &&
//                     (*it)[0].getOpKind() == BVCONST &&
//                     computeBVConst((*it)[0]) != 1, "Unexpected format");
//         continue
//   }

//   coefficient = Odd_coeff( e );
//   //  Rational odd_coeff = anyOdd( coeff );
//   if( coefficient != 0)
//     {
//       // the equation is solvable
//       cout<<"Odd coefficient found => the equation is solvable\n";
//       if (coefficient != 1) {
//         Rational mult_inv = multiplicative_inverse( coefficient, BVSize(e[0]));
//         // multiply all the coefficients in the expression by the inverse
//         //      Expr tmp_expr = e;
//         e = multiply_coeff( mult_inv, e);
//         //      Expr isolated_expr = isolate_var( new_expr);
//       }

//       Theorem solved_th = d_rules->isolate_var( t, e);
//       cout<<"solved theorem: "<<solved_th.toString()<<endl;
//       cout<<"solved theorem expr: "<<solved_th.getExpr().toString()<<endl;

//       return iffMP( t, solved_th);
//     }
//   else
//     {
//       cout<<"Odd coefficient not found => the equation is not solvable\n";
//       Theorem thm = d_rules->MarkNonSolvableEq( e );
//       cout<<"TheoryBitvector::solve, input e: "<<e.toString()<<" thm: "<<thm.toString()<<endl;
//       return iffMP( t, thm);
//       //return reflexivityRule(e);
//     }
//}


void TheoryBitvector::checkType(const Expr& e)
{
  switch (e.getOpKind()) {
    case BITVECTOR:
      //TODO: check that this is a well-formed type
      break;
    default:
      FatalAssert(false, "Unexpected kind in TheoryBitvector::checkType"
                  +getEM()->getKindName(e.getOpKind()));
  }
}


Cardinality TheoryBitvector::finiteTypeInfo(Expr& e, Unsigned& n,
                                            bool enumerate, bool computeSize)
{
  FatalAssert(e.getKind() == BITVECTOR,
              "Unexpected kind in TheoryBitvector::finiteTypeInfo");
  if (enumerate || computeSize) {
    int bitwidth = getBitvectorTypeParam(e);
    Rational max_val = pow( bitwidth, (Rational) 2);

    if (enumerate) {
      if (n < max_val.getUnsigned()) {
        e = newBVConstExpr(n, bitwidth);
      }
      else e = Expr();
    }

    if (computeSize) {
      n = max_val.getUnsignedMP();
    }
  }
  return CARD_FINITE;
}


void TheoryBitvector::computeType(const Expr& e)
{
  if (e.isApply()) {
    switch(e.getOpKind()) {
      case BOOLEXTRACT: {
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException("Type Checking error:"\
                                   "attempted extraction from non-bitvector \n"+
                                   e.toString());
        int extractLength = getBoolExtractIndex(e);
        if(!(0 <= extractLength))
          throw TypecheckException("Type Checking error: \n"
                                   "attempted out of range extraction  \n"+
                                   e.toString());
        e.setType(boolType());
        break;
      }
      case BVMULT:{
        if(!(2 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind() &&
             BITVECTOR == getBaseType(e[1]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in BVMULT:\n\n  "
             +e.toString());
        int bvLen = getBVMultParam(e);
        Type bvType = newBitvectorType(bvLen);
        e.setType(bvType);
        break;
      }
      case EXTRACT:{
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in bit-vector extraction:\n\n  "
             + e.toString());
        int bvLength = BVSize(e[0]);
        int leftExtract = getExtractHi(e);
        int rightExtract = getExtractLow(e);
        if(!(0 <= rightExtract &&
             rightExtract <= leftExtract && leftExtract < bvLength))
          throw TypecheckException
            ("Wrong bounds in bit-vector extract:\n\n  "+e.toString());
        int extractLength = leftExtract - rightExtract + 1;
        Type bvType = newBitvectorType(extractLength);
        e.setType(bvType);
        break;
      }
      case BVPLUS: {
        int bvPlusLength = getBVPlusParam(e);
        if(!(0 <= bvPlusLength))
          throw TypecheckException
            ("Bad bit-vector length specified in BVPLUS expression:\n\n  "
             + e.toString());
        for(Expr::iterator i=e.begin(), iend=e.end(); i != iend; ++i) {
          if(BITVECTOR != getBaseType(*i).getExpr().getOpKind())
            throw TypecheckException
              ("Not a bit-vector expression in BVPLUS:\n\n  "+e.toString());
        }
        Type bvType = newBitvectorType(bvPlusLength);
        e.setType(bvType);
        break;
      }
      case LEFTSHIFT: {
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in bit-vector shift:\n\n  "
             +e.toString());
        int bvLength = BVSize(e[0]);
        int shiftLength = getFixedLeftShiftParam(e);
        if(!(shiftLength >= 0))
          throw TypecheckException("Bad shift value in bit-vector shift:\n\n  "
                                   +e.toString());
        int newLength = bvLength + shiftLength;
        Type bvType = newBitvectorType(newLength);
        e.setType(bvType);
        break;
      }
      case CONST_WIDTH_LEFTSHIFT: {
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in bit-vector shift:\n\n  "
             +e.toString());
        int bvLength = BVSize(e[0]);
        int shiftLength = getFixedLeftShiftParam(e);
        if(!(shiftLength >= 0))
          throw TypecheckException("Bad shift value in bit-vector shift:\n\n  "
                                   +e.toString());
        Type bvType = newBitvectorType(bvLength);
        e.setType(bvType);
        break;
      }
      case RIGHTSHIFT: {
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in bit-vector shift:\n\n  "
             +e.toString());
        int bvLength = BVSize(e[0]);
        int shiftLength = getFixedRightShiftParam(e);
        if(!(shiftLength >= 0))
          throw TypecheckException("Bad shift value in bit-vector shift:\n\n  "
                                   +e.toString());
        //int newLength = bvLength + shiftLength;
        Type bvType = newBitvectorType(bvLength);
        e.setType(bvType);
        break;
      }
      case BVTYPEPRED:
        e.setType(boolType());
        break;
      case SX: {
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException("Type Checking error:"\
                                   "non-bitvector \n"+ e.toString());
        int bvLength = getSXIndex(e);
        if(!(1 <= bvLength))
          throw TypecheckException("Type Checking error: \n"
                                   "out of range\n"+ e.toString());
        Type bvType = newBitvectorType(bvLength);
        e.setType(bvType);
        break;
      }
      case BVREPEAT: {
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException("Type Checking error:"\
                                   "non-bitvector \n"+ e.toString());
        int bvLength = getBVIndex(e) * BVSize(e[0]);
        if(!(1 <= bvLength))
          throw TypecheckException("Type Checking error: \n"
                                   "out of range\n"+ e.toString());
        Type bvType = newBitvectorType(bvLength);
        e.setType(bvType);
        break;
      }
      case BVZEROEXTEND: {
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException("Type Checking error:"\
                                   "non-bitvector \n"+ e.toString());
        int bvLength = getBVIndex(e) + BVSize(e[0]);
        if(!(1 <= bvLength))
          throw TypecheckException("Type Checking error: \n"
                                   "out of range\n"+ e.toString());
        Type bvType = newBitvectorType(bvLength);
        e.setType(bvType);
        break;
      }
      case BVROTL:
      case BVROTR: {
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException("Type Checking error:"\
                                   "non-bitvector \n"+ e.toString());
        e.setType(getBaseType(e[0]));
        break;
      }
      default:
        FatalAssert(false,
                    "TheoryBitvector::computeType: unexpected kind in application" +
                    int2string(e.getOpKind()));
        break;
    }
  }
  else {
    switch(e.getKind()) {
      case BOOLEXTRACT:
      case BVMULT:
      case EXTRACT:
      case BVPLUS:
      case LEFTSHIFT:
      case CONST_WIDTH_LEFTSHIFT:
      case RIGHTSHIFT:
      case BVTYPEPRED:
      case SX:
      case BVREPEAT:
      case BVZEROEXTEND:
      case BVROTL:
      case BVROTR:
        // These operators are handled above when applied to arguments, here we
        // are dealing with the operators themselves which are polymorphic, so
        // don't assign them a specific type.
        e.setType(Type::anyType(getEM()));
        break;
      case BVCONST: {
        Type bvType = newBitvectorType(getBVConstSize(e));
        e.setType(bvType);
        break;
      }
      case CONCAT: {
        if(e.arity() < 2)
          throw TypecheckException
            ("Concatenation must have at least 2 bit-vectors:\n\n  "+e.toString());

        // Compute the total length of concatenation
        int bvLength(0);
        for(int i=0, iend=e.arity(); i<iend; ++i) {
          if(BITVECTOR != getBaseType(e[i]).getExpr().getOpKind())
            throw TypecheckException
              ("Not a bit-vector expression (child #"+int2string(i+1)
               +") in concatenation:\n\n  "+e[i].toString()
               +"\n\nIn the expression:\n\n  "+e.toString());
          bvLength += BVSize(e[i]);
        }
        Type bvType = newBitvectorType(bvLength);
        e.setType(bvType);
        break;
      }
      case BVAND:
      case BVOR:
      case BVXOR:
      case BVXNOR:
      {
        string kindStr((e.getOpKind()==BVAND)? "AND" :
                       ((e.getOpKind()==BVOR)? "OR" :
                        ((e.getOpKind()==BVXOR)? "BVXOR" : "BVXNOR")));

        if(e.arity() < 2)
          throw TypecheckException
            ("Bit-wise "+kindStr+" must have at least 2 bit-vectors:\n\n  "
             +e.toString());

        int bvLength(0);
        bool first(true);
        for(int i=0, iend=e.arity(); i<iend; ++i) {
          if(BITVECTOR != getBaseType(e[i]).getExpr().getOpKind())
            throw TypecheckException
              ("Not a bit-vector expression (child #"+int2string(i+1)
               +") in bit-wise "+kindStr+":\n\n  "+e[i].toString()
               +"\n\nIn the expression:\n\n  "+e.toString());
          if(first) {
            bvLength = BVSize(e[i]);
            first=false;
          } else { // Check that the size is the same for all subsequent BVs
            if(BVSize(e[i]) != bvLength)
              throw TypecheckException
                ("Mismatched bit-vector size in bit-wise "+kindStr+" (child #"
                 +int2string(i)+").\nExpected type: "
                 +newBitvectorType(bvLength).toString()
                 +"\nFound: "+e[i].getType().toString()
                 +"\nIn the following expression:\n\n  "+e.toString());
          }
        }
        e.setType(newBitvectorType(bvLength));
        break;
      }
      case BVNEG:{
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in bit-wise negation:\n\n  "
             + e.toString());
        e.setType(e[0].getType());
        break;
      }
      case BVNAND:
      case BVNOR:
      case BVCOMP:
      case BVSUB:
      case BVUDIV:
      case BVSDIV:
      case BVUREM:
      case BVSREM:
      case BVSMOD:
      case BVSHL:
      case BVASHR:
      case BVLSHR:
        if(!(2 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind() &&
             BITVECTOR == getBaseType(e[1]).getExpr().getOpKind()))
          throw TypecheckException
            ("Expressions must have arity=2, and"
             "each subterm must be a bitvector term:\n"
             "e = " +e.toString());
        if (BVSize(e[0]) != BVSize(e[1]))
          throw TypecheckException
            ("Expected args of same size:\n"
             "e = " +e.toString());
        if (e.getKind() == BVCOMP) {
          e.setType(newBitvectorTypeExpr(1));
        }
        else {
          e.setType(getBaseType(e[0]));
        }
        break;
      case BVUMINUS:{
        Type bvType(getBaseType(e[0]));
        if(!(1 == e.arity() &&
             BITVECTOR == bvType.getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in BVUMINUS:\n\n  "
             +e.toString());
        e.setType(bvType);
        break;
      }
      case BVLT:
      case BVLE:
      case BVGT:
      case BVGE:
      case BVSLT:
      case BVSLE:
      case BVSGT:
      case BVSGE:
        if(!(2 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind() &&
             BITVECTOR == getBaseType(e[1]).getExpr().getOpKind()))
          throw TypecheckException
            ("BVLT/BVLE expressions must have arity=2, and"
             "each subterm must be a bitvector term:\n"
             "e = " +e.toString());
        e.setType(boolType());
        break;
      default:
        FatalAssert(false,
                    "TheoryBitvector::computeType: wrong input" +
                    int2string(e.getOpKind()));
        break;
    }
  }
  TRACE("bitvector", "TheoryBitvector::computeType => ", e.getType(), " }");
}


void TheoryBitvector::computeModelTerm(const Expr& e, std::vector<Expr>& v) {
  switch(e.getOpKind()) {
  case BVPLUS:
  case BVSUB:
  case BVUMINUS:
  case BVMULT:
  case LEFTSHIFT:
  case CONST_WIDTH_LEFTSHIFT:
  case RIGHTSHIFT:
  case BVOR:
  case BVAND:
  case BVXOR:
  case BVXNOR:
  case BVNAND:
  case BVNOR:
  case BVNEG:
  case CONCAT:
  case EXTRACT:
  case BVSLT:
  case BVSLE:
  case BVSGT:
  case BVSGE:
  case BVLT:
  case BVLE:
  case BVGT:
  case BVGE:
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
      // getModelTerm(*i, v);
      v.push_back(*i);
    return;
  case BVCONST: // No model variables here
    return;
  default: break; // It's a variable; continue processing
  }

  Type tp(e.getType());
  switch(tp.getExpr().getOpKind()) {
  case BITVECTOR: {
    int n = getBitvectorTypeParam(tp);
    for(int i=0; i<n; i = i+1)
      v.push_back(newBoolExtractExpr(e, i));
    break;
  }
  default:
    v.push_back(e);
  }
}


void TheoryBitvector::computeModel(const Expr& e, std::vector<Expr>& v) {
  switch(e.getOpKind()) {
  case BVPLUS:
  case BVSUB:
  case BVUMINUS:
  case BVMULT:
  case LEFTSHIFT:
  case CONST_WIDTH_LEFTSHIFT:
  case RIGHTSHIFT:
  case BVOR:
  case BVAND:
  case BVXOR:
  case BVXNOR:
  case BVNAND:
  case BVNOR:
  case BVNEG:
  case CONCAT:
  case EXTRACT:
  case SX:
  case BVSLT:
  case BVSLE:
  case BVSGT:
  case BVSGE:
  case BVLT:
  case BVLE:
  case BVGT:
  case BVGE: {
    // More primitive vars are kids, and they should have been
    // assigned concrete values
    assignValue(simplify(e));
    v.push_back(e);
    return;
  }
  case BVCONST: // No model variables here
    return;
  default: break; // It's a variable; continue processing
  }

  Type tp(e.getType());
  switch(tp.getExpr().getOpKind()) {
  case BITVECTOR: {
    const Rational& n = getBitvectorTypeParam(tp);
    vector<bool> bits;
    // FIXME: generate concrete assignment from bits using proof
    // rules. For now, just create a new assignment.
    for(int i=0; i<n; i++) {
      Theorem val(getModelValue(newBoolExtractExpr(e, i)));
      DebugAssert(val.getRHS().isBoolConst(),
		  "TheoryBitvector::computeModel: unassigned bit: "
		  +val.getExpr().toString());
      bits.push_back(val.getRHS().isTrue());
    }
    Expr c(newBVConstExpr(bits));
    assignValue(e, c);
    v.push_back(e);
    break;
  }
  default:
    FatalAssert(false, "TheoryBitvector::computeModel[not BITVECTOR type]("
		+e.toString()+")");
  }
}


// TODO: get rid of this - don't need type predicates for bv's, just need to share the right terms
Expr
TheoryBitvector::computeTypePred(const Type& t, const Expr& e) {
  DebugAssert(t.getExpr().getOpKind() == BITVECTOR,
	      "TheoryBitvector::computeTypePred: t = "+t.toString());
//   switch(e.getKind()) {
//   case BVCONST:
//     return getEM()->trueExpr();
//   default:
  return e.getEM()->trueExpr();

  //    return newBitvectorTypePred(t, e);
    //  }
}

///////////////////////////////////////////////////////////////////////////////
// Pretty-printing                                                           //
///////////////////////////////////////////////////////////////////////////////

ExprStream&
TheoryBitvector::printSmtLibShared(ExprStream& os, const Expr& e) {

  d_theoryUsed = true;
  switch( e.getOpKind() ) {

  case CONCAT:
    if( e.arity() == 0 )
      throw SmtlibException("TheoryBitvector::print: CONCAT arity = 0");
    else if( e.arity() == 1 )
      os << e[0];
    else {
      int i;
      for( i = 0; i < e.arity(); ++i ) {
        if( (i + 1) == e.arity() ) {
          os << e[i];
        } else {
          os << "(concat" << space << push << e[i] << space << push;
        }
      }
      for( --i; i != 0; --i )
        os << push << ")";
    }
    break;
  case BVSHL:
    os << "(bvshl" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVLSHR:
    os << "(bvlshr" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVASHR:
    os << "(bvashr" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVAND:
    if( e.arity() == 0 )
      throw SmtlibException("TheoryBitvector::print: BVAND arity = 0");
    else if( e.arity() == 1 )
      os << e[0];
    else {
      int i;
      for( i = 0; i < e.arity(); ++i ) {
        if( (i + 1) == e.arity() ) {
          os << e[i];
        } else {
          os << "(bvand" << space << push << e[i] << space << push;
        }
      }
      for( --i; i != 0; --i )
        os << push << ")";
    }
    break;
  case BVOR:
    if( e.arity() == 0 )
      throw SmtlibException("TheoryBitvector::print: BVAND arity = 0");
    else if( e.arity() == 1 )
      os << e[0];
    else {
      int i;
      for( i = 0; i < e.arity(); ++i ) {
        if( (i + 1) == e.arity() ) {
          os << e[i];
        } else {
          os << "(bvor" << space << push << e[i] << space << push;
        }
      }
      for( --i; i != 0; --i )
        os << push << ")";
    }
    break;
  case BVXOR:
    if( e.arity() == 0 )
      throw SmtlibException("TheoryBitvector::print: BVXOR arity = 0");
    else if( e.arity() == 1 )
      os << e[0];
    else {
      int i;
      for( i = 0; i < e.arity(); ++i ) {
        if( (i + 1) == e.arity() ) {
          os << e[i];
        } else {
          os << "(bvxor" << space << push << e[i] << space << push;
        }
      }
      for( --i; i != 0; --i )
        os << push << ")";
    }
    break;
  case BVXNOR:
    if( e.arity() == 0 )
      throw SmtlibException("TheoryBitvector::print: BVXNOR arity = 0");
    else if( e.arity() == 1 )
      os << e[0];
    else {
      int i;
      for( i = 0; i < e.arity(); ++i ) {
        if( (i + 1) == e.arity() ) {
          os << e[i];
        } else {
          os << "(bvxnor" << space << push << e[i] << space << push;
        }
      }
      for( --i; i != 0; --i )
        os << push << ")";
    }
    break;
  case BVNEG:
    os << "(bvnot" << space << push << e[0] << push << ")";
    break;
  case BVNAND:
    os << "(bvnand" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVNOR:
    os << "(bvnor" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVCOMP:
    os << "(bvcomp" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;

  case BVUMINUS:
    os << "(bvneg" << space << push << e[0] << push << ")";
    break;
  case BVPLUS: {
    DebugAssert(e.arity() > 0, "expected arity > 0 in BVPLUS");
    int length = getBVPlusParam(e);
    int i;
    for( i = 0; i < e.arity(); ++i ) {
      if( (i + 1) == e.arity() ) {
        os << pad(length, e[i]);
      } else {
        os << "(bvadd" << space << push << pad(length, e[i]) << space << push;
      }
    }
    for( --i; i != 0; --i )
      os << push << ")";
  }
    break;
  case BVSUB:
    os << "(bvsub" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVMULT: {
    int length = getBVMultParam(e);
    os << "(bvmul" << space << push << pad(length, e[0]) << space << push
        << pad(length, e[1]) << push << ")";
    break;
  }
  case BVUDIV:
    os << "(bvudiv" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVSDIV:
    os << "(bvsdiv" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVUREM:
    os << "(bvurem" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVSREM:
    os << "(bvsrem" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVSMOD:
    os << "(bvsmod" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;

  case BVLT:
    os << "(bvult" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVLE:
    os << "(bvule" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVGT:
    os << "(bvugt" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVGE:
    os << "(bvuge" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVSLT:
    os << "(bvslt" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVSLE:
    os << "(bvsle" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVSGT:
    os << "(bvsgt" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;
  case BVSGE:
    os << "(bvsge" << space << push << e[0] << space << push << e[1] << push
        << ")";
    break;

  case INTTOBV:
    throw SmtlibException(
        "TheoryBitvector::print: INTTOBV, SMTLIB not supported");
    break;
  case BVTOINT:
    throw SmtlibException(
        "TheoryBitvector::print: BVTOINT, SMTLIB not supported");
    break;

  case BVTYPEPRED:
    throw SmtlibException(
        "TheoryBitvector::print: BVTYPEPRED, SMTLIB not supported");
    if( e.isApply() ) {
      os << "BVTYPEPRED[" << push << e.getOp().getExpr() << push << "," << pop
          << space << e[0] << push << "]";
    } else
      e.printAST(os);
    break;

  default:
    FatalAssert(false, "Unknown BV kind");
    e.printAST(os);
    break;
  }
  return os;
}

ExprStream&
TheoryBitvector::print(ExprStream& os, const Expr& e) {
  switch(os.lang()) {
  case PRESENTATION_LANG:
    switch(e.getOpKind()) {

    case BITVECTOR: //printing type expression
      os << "BITVECTOR(" << push
	 << getBitvectorTypeParam(e) << push << ")";
      break;

    case BVCONST: {
      std::ostringstream ss;
      ss << "0bin";
      for(int i=(int)getBVConstSize(e)-1; i>=0; --i)
	ss << (getBVConstValue(e, i) ? "1" : "0");
      os << ss.str();
      break;
    }

    case CONCAT:
      if(e.arity() <= 1) e.printAST(os);
      else {
	os << "(" << push;
	bool first(true);
	for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	  if(first) first=false;
	  else os << space << "@" << space;
	  os << (*i);
	}
	os << push << ")";
      }
      break;
    case EXTRACT:
      os << "(" << push << e[0] << push << ")" << pop << pop
	 << "[" << push << getExtractHi(e) << ":";
      os << getExtractLow(e) << push << "]";
      break;
    case BOOLEXTRACT:
      os << "BOOLEXTRACT(" << push  << e[0] << ","
	 << getBoolExtractIndex(e) << push << ")";
      break;

    case LEFTSHIFT:
      os <<  "(" << push << e[0] << space << "<<" << space
	 << getFixedLeftShiftParam(e) << push << ")";
      break;
    case CONST_WIDTH_LEFTSHIFT:
      os <<  "(" << push << e[0] << space << "<<" << space
	 << getFixedLeftShiftParam(e) << push << ")";
      os << "[" << push << BVSize(e)-1 << ":0]";
      break;
    case RIGHTSHIFT:
      os <<  "(" << push << e[0] << space << ">>" << space
	 << getFixedRightShiftParam(e) << push << ")";
      break;
    case BVSHL:
      os << "BVSHL(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVLSHR:
      os << "BVLSHR(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVASHR:
      os << "BVASHR(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVZEROEXTEND:
      os << "BVZEROEXTEND(" << push << e[0] << "," << getBVIndex(e) << push << ")";
      break;
    case BVREPEAT:
      os << "BVREPEAT(" << push << e[0] << "," << getBVIndex(e) << push << ")";
      break;
    case BVROTL:
      os << "BVROTL(" << push << e[0] << "," << getBVIndex(e) << push << ")";
      break;
    case BVROTR:
      os << "BVROTR(" << push << e[0] << "," << getBVIndex(e) << push << ")";
      break;
    case SX:
      os << "SX(" << push  << e[0] << ","
	 << push <<  getSXIndex(e) << ")";
      break;

    case BVAND:
      if(e.arity() <= 1) e.printAST(os);
      else {
	os << "(" << push;
	bool first(true);
	for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	  if(first) first=false;
	  else os << space << "&" << space;
	  os << (*i);
	}
	os << push << ")";
      }
      break;
    case BVOR:
      if(e.arity() <= 1) e.printAST(os);
      else {
	os << "(" << push;
	bool first(true);
	for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	  if(first) first=false;
	  else os << space << "|" << space;
	  os << (*i);
	}
	os << push << ")";
      }
      break;
    case BVXOR:
      DebugAssert(e.arity() > 0, "TheoryBitvector::print: BVXOR arity <= 0");
      if (e.arity() == 1) os << e[0];
      else {
        int i;
	for(i = 0; i < e.arity(); ++i) {
          if ((i+1) == e.arity()) {
            os << e[i];
          }
          else {
            os << "BVXOR(" << push << e[i] << "," << push;
          }
	}
        for (--i; i != 0; --i) os << push << ")";
      }
      break;
    case BVXNOR:
      DebugAssert(e.arity() > 0, "TheoryBitvector::print: BVXNOR arity <= 0");
      if (e.arity() == 1) os << e[0];
      else {
        int i;
	for(i = 0; i < e.arity(); ++i) {
          if ((i+1) == e.arity()) {
            os << e[i];
          }
          else {
            os << "BVXNOR(" << push << e[i] << "," << push;
          }
	}
        for (--i; i != 0; --i) os << push << ")";
      }
      break;
    case BVNEG:
      os << "(~(" << push << e[0] << push << "))";
      break;
    case BVNAND:
      os << "BVNAND(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVNOR:
      os << "BVNAND(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVCOMP:
      os << "BVCOMP(" << push << e[0] << "," << e[1] << push << ")";
      break;

    case BVUMINUS:
      os << "BVUMINUS(" << push << e[0] << push << ")";
      break;
    case BVPLUS:
      os << "BVPLUS(" << push << getBVPlusParam(e);
      for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	os << push << "," << pop << space << (*i);
      }
      os << push << ")";
      break;
    case BVSUB:
      os << "BVSUB(" << push << BVSize(e) << "," << e[0] << "," << e[1] << push << ")";
      break;
    case BVMULT:
      os << "BVMULT(" << push << getBVMultParam(e) << "," << e[0] << "," << e[1]<<push<<")";
      break;
    case BVUDIV:
        os << "BVUDIV(" << push << e[0] << "," << e[1]<<push<<")";
        break;
    case BVSDIV:
        os << "BVSDIV(" << push << e[0] << "," << e[1]<<push<<")";
        break;
    case BVUREM:
        os << "BVUREM(" << push << e[0] << "," << e[1]<<push<<")";
        break;
    case BVSREM:
        os << "BVSREM(" << push << e[0] << "," << e[1]<<push<<")";
        break;
    case BVSMOD:
        os << "BVSMOD(" << push << e[0] << "," << e[1]<<push<<")";
        break;
    case BVLT:
      os << "BVLT(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVLE:
      os << "BVLE(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVGT:
      os << "BVGT(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVGE:
      os << "BVGE(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVSLT:
      os << "BVSLT(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVSLE:
      os << "BVSLE(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVSGT:
      os << "BVSGT(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVSGE:
      os << "BVSGE(" << push << e[0] << "," << e[1] << push << ")";
      break;

    case INTTOBV:
      FatalAssert(false, "INTTOBV not implemented yet");
      break;
    case BVTOINT:
      FatalAssert(false, "BVTOINT not implemented yet");
      break;

    case BVTYPEPRED:
      if(e.isApply()) {
	os << "BVTYPEPRED[" << push << e.getOp().getExpr()
	   << push << "," << pop << space << e[0]
	   << push << "]";
      } else
	e.printAST(os);
      break;

    default:
      FatalAssert(false, "Unknown BV kind");
      e.printAST(os);
      break;
    }
    break;

  case SMTLIB_LANG:
    switch(e.getOpKind()) {
    case BITVECTOR: //printing type expression
      os << push << "BitVec[" << getBitvectorTypeParam(e) << "]";
      break;

    case BVCONST: {
      Rational r = computeBVConst(e);
      DebugAssert(r.isInteger() && r >= 0, "Expected non-negative integer");
      os << push << "bv" << r << "[" << BVSize(e) << "]";
      break;
    }

    case EXTRACT:
      os << push << "(extract[" << getExtractHi(e) << ":" << getExtractLow(e)
         << "]";
      os << space << push << e[0] << push << ")";
      break;
    case BOOLEXTRACT:
      os << "(=" << space << push << "(extract[" << getBoolExtractIndex(e) << ":"
         << getBoolExtractIndex(e) << "]";
      os << space << push << e[0] << push << ")" << space << "bit1" << push
         << ")";
      break;

    case LEFTSHIFT: {
      int bvLength = getFixedLeftShiftParam(e);
      if( bvLength != 0 ) {
        os << "(concat" << space << push << e[0] << space;
        os << push << "bv0[" << bvLength << "]" << push << ")";
        break;
      }
      // else fall-through
    }
    case CONST_WIDTH_LEFTSHIFT:
      os << "(bvshl" << space << push << e[0] << space << push << "bv"
         << getFixedLeftShiftParam(e) << "[" << BVSize(e[0]) << "]" << push
         << ")";
      break;
    case RIGHTSHIFT:
      os << "(bvlshr" << space << push << e[0] << space << push << "bv"
         << getFixedRightShiftParam(e) << "[" << BVSize(e[0]) << "]" << push
         << ")";
      break;
  case SX: {
    int extend = getSXIndex(e) - BVSize(e[0]);
    if( extend == 0 )
      os << e[0];
    else if( extend < 0 )
      throw SmtlibException(
          "TheoryBitvector::print: SX: extension is shorter than argument");
    else
      os << "(sign_extend[" << extend << "]" << space << push << e[0] << push
          << ")";
    break;
  }
  case BVREPEAT:
    os << "(repeat[" << getBVIndex(e) << "]" << space << push << e[0] << push
        << ")";
    break;
  case BVZEROEXTEND: {
    int extend = getBVIndex(e);
    if( extend == 0 )
      os << e[0];
    else if( extend < 0 )
      throw SmtlibException(
          "TheoryBitvector::print: ZEROEXTEND: extension is less than zero");
    else
      os << "(zero_extend[" << extend << "]" << space << push << e[0] << push
          << ")";
    break;
  }
  case BVROTL:
    os << "(rotate_left[" << getBVIndex(e) << "]" << space << push << e[0]
        << push << ")";
    break;
  case BVROTR:
    os << "(rotate_right[" << getBVIndex(e) << "]" << space << push << e[0]
        << push << ")";
    break;

    default:
      printSmtLibShared(os,e);
    }
    break;

  case SMTLIB_V2_LANG:
    switch(e.getOpKind()) {
    case BITVECTOR: //printing type expression
      os << push << "(_" << space << "BitVec" << space << getBitvectorTypeParam(e) << ")" << pop;
      break;

    case BVCONST: {
      Rational r = computeBVConst(e);
      DebugAssert(r.isInteger() && r >= 0, "Expected non-negative integer");
      os << push << "(_ bv" << r << space << BVSize(e) << ")";
      break;
    }

    case EXTRACT:
      os << push << "((_ extract" << space << getExtractHi(e) << space << getExtractLow(e)
         << ")";
      os << space << push << e[0] << push << ")";
      break;

    case BOOLEXTRACT:
      os << "(=" << space << push << "((_ extract" << getBoolExtractIndex(e) << space
         << getBoolExtractIndex(e) << ")";
      os << space << push << e[0] << push << ")" << space << "#b1" << push
         << ")";
      break;

    case LEFTSHIFT: {
      int bvLength = getFixedLeftShiftParam(e);
      if( bvLength != 0 ) {
        os << "(concat" << space << push << e[0] << space;
        os << push << "#b";
        for (int i = 0; i < bvLength; ++i) os << "0";
        os << push << ")";
        break;
      }
      // else fall-through
    }
    case CONST_WIDTH_LEFTSHIFT:
      os << "(bvshl" << space << push << e[0] << space << push;
      os << newBVConstExpr(getFixedLeftShiftParam(e), BVSize(e[0])) << push  << ")";
      break;
    case RIGHTSHIFT:
      os << "(bvlshr" << space << push << e[0] << space << push;
      os << newBVConstExpr(getFixedRightShiftParam(e), BVSize(e[0])) << push << ")";
      break;
    case SX: {
      int extend = getSXIndex(e) - BVSize(e[0]);
      if( extend == 0 )
        os << e[0];
      else if( extend < 0 )
        throw SmtlibException(
          "TheoryBitvector::print: SX: extension is shorter than argument");
      else
        os << "((_ sign_extend" << space << extend << ")" << space << push << e[0] << push
           << ")";
      break;
  }
  case BVREPEAT:
    os << "((_ repeat" << space << getBVIndex(e) << ")" << space << push << e[0] << push
        << ")";
    break;
  case BVZEROEXTEND: {
    int extend = getBVIndex(e);
    if( extend == 0 )
      os << e[0];
    else if( extend < 0 )
      throw SmtlibException(
          "TheoryBitvector::print: ZEROEXTEND: extension is less than zero");
    else
      os << "((_ zero_extend" << space << extend << ")" << space << push << e[0] << push
          << ")";
    break;
  }
  case BVROTL:
    os << "((_ rotate_left" << space << getBVIndex(e) << ")" << space << push << e[0]
        << push << ")";
    break;
  case BVROTR:
    os << "((_ rotate_right" << space << getBVIndex(e) << ")" << space << push << e[0]
        << push << ")";
    break;

    default:
      printSmtLibShared(os,e);
    }
    break;

  default:
    switch(e.getOpKind()) {
    case BVCONST: {
      os << "0bin";
      for(int i=(int)getBVConstSize(e)-1; i>=0; --i)
	os << (getBVConstValue(e, i) ? "1" : "0");
      break;
    }
    default:
      e.printAST(os);
      break;
    }
  }
  return os;
}


///////////////////////////////////////////////////////////////////////////////
//parseExprOp:
//translating special Exprs to regular EXPR??
///////////////////////////////////////////////////////////////////////////////
Expr TheoryBitvector::parseExprOp(const Expr& e)
{
  d_theoryUsed = true;
  TRACE("parser", "TheoryBitvector::parseExprOp(", e, ")");

  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  if(RAW_LIST != e.getKind()) return e;

  if(!(e.arity() > 0))
    throw ParserException("TheoryBitvector::parseExprOp: wrong input:\n\n"
			  +e.toString());

  const Expr& c1 = e[0][0];
  int kind = getEM()->getKind(c1.getString());
  switch(kind) {

  case BITVECTOR:
    if(!(e.arity() == 2))
      throw ParserException("TheoryBitvector::parseExprOp: BITVECTOR"
			    "kind should have exactly 1 arg:\n\n"
			    + e.toString());
    if(!(e[1].isRational() && e[1].getRational().isInteger()))
      throw ParserException("BITVECTOR TYPE must have an integer constant"
			    "as its first argument:\n\n"
			    +e.toString());
    if(!(e[1].getRational().getInt() >=0 ))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());
    return newBitvectorTypeExpr(e[1].getRational().getInt());
    break;

  case BVCONST:
    if(!(e.arity() == 2 || e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVCONST "
			    "kind should have 1 or 2 args:\n\n"
			    + e.toString());
    if(!(e[1].isRational() || e[1].isString()))
      throw ParserException("TheoryBitvector::parseExprOp: BVCONST "
			    "kind should have arg of type Rational "
			    "or String:\n\n" + e.toString());
    if(e[1].isRational()) { // ("BVCONST" value [bitwidth])
      if(e.arity()==3) {
	if(!e[2].isRational() || !e[2].getRational().isInteger())
	  throw ParserException("TheoryBitvector::parseExprOp: BVCONST "
				"2nd argument must be an integer:\n\n"
				+e.toString());
	return newBVConstExpr(e[1].getRational(), e[2].getRational().getInt());
      } else
	return newBVConstExpr(e[1].getRational());
    } else if(e[1].isString()) { // ("BVCONST" string [base])
      if(e.arity() == 3) {
	if(!e[2].isRational() || !e[2].getRational().isInteger())
	  throw ParserException("TheoryBitvector::parseExprOp: BVCONST "
				"2nd argument must be an integer:\n\n"
				+e.toString());
	return newBVConstExpr(e[1].getString(), e[2].getRational().getInt());
      } else
	return newBVConstExpr(e[1].getString());
    }
    break;

  case CONCAT: {
    if(!(e.arity() >= 3))
      throw ParserException("TheoryBitvector::parseExprOp: CONCAT"
			    "kind should have at least 2 args:\n\n"
			    + e.toString());
    vector<Expr> kids;
    Expr::iterator i=e.begin(), iend=e.end();
    DebugAssert(i!=iend, "TheoryBitvector::parseExprOp("+e.toString()+")");
    ++i; // Skip the first element - the operator name
    for(; i!=iend; ++i)
      kids.push_back(parseExpr(*i));
    return newConcatExpr(kids);
    break;
  }
  case EXTRACT: {
    if(!(e.arity() == 4))
      throw ParserException("TheoryBitvector::parseExprOp: EXTRACT"
			    "kind should have exactly 3 arg:\n\n"
			    + e.toString());
    if(!e[1].isRational() || !e[1].getRational().isInteger())
      throw ParserException("EXTRACT must have an integer constant as its "
			    "1st argument:\n\n"
			    +e.toString());
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("EXTRACT must have an integer constant as its "
			    "2nd argument:\n\n"
			    +e.toString());
    int hi = e[1].getRational().getInt();
    int lo = e[2].getRational().getInt();
    if(!(hi >= lo && lo >=0))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());

    // Check for extract of left shift
    Expr arg = e[3];
    if (lo == 0 && arg.getKind() == RAW_LIST && arg[0].getKind() == ID &&
        getEM()->getKind(arg[0][0].getString()) == LEFTSHIFT) {
      if(!(arg.arity() == 3))
        throw ParserException("TheoryBitvector::parseExprOp: LEFTSHIFT"
                              "kind should have exactly 2 arg:\n\n"
                              + arg.toString());
      if(!arg[2].isRational() || !arg[2].getRational().isInteger())
        throw ParserException("LEFTSHIFT must have an integer constant as its "
                              "2nd argument:\n\n"
                              +arg.toString());
      if(!(arg[2].getRational().getInt() >=0 ))
        throw ParserException("parameter must be an integer constant >= 0.\n"
                              +arg.toString());
      Expr ls_arg = parseExpr(arg[1]);
      if (BVSize(ls_arg) == hi + 1) {
        return newFixedConstWidthLeftShiftExpr(ls_arg, arg[2].getRational().getInt());
      }
    }
    return newBVExtractExpr(parseExpr(arg), hi, lo);
    break;
  }
  case BOOLEXTRACT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BOOLEXTRACT"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("BOOLEXTRACT must have an integer constant as its"
			    " 2nd argument:\n\n"
			    +e.toString());
    if(!(e[2].getRational().getInt() >=0 ))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());
    return newBoolExtractExpr(parseExpr(e[1]), e[2].getRational().getInt());
    break;

  case LEFTSHIFT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: LEFTSHIFT"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("LEFTSHIFT must have an integer constant as its "
			    "2nd argument:\n\n"
			    +e.toString());
    if(!(e[2].getRational().getInt() >=0 ))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());
    return newFixedLeftShiftExpr(parseExpr(e[1]), e[2].getRational().getInt());
    break;
  case CONST_WIDTH_LEFTSHIFT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: CONST_WIDTH_LEFTSHIFT"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("CONST_WIDTH_LEFTSHIFT must have an integer constant as its "
			    "2nd argument:\n\n"
			    +e.toString());
    if(!(e[2].getRational().getInt() >=0 ))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());
    return newFixedConstWidthLeftShiftExpr(parseExpr(e[1]), e[2].getRational().getInt());
    break;
  case RIGHTSHIFT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: RIGHTSHIFT"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("RIGHTSHIFT must have an integer constant as its "
			    "2nd argument:\n\n"
			    +e.toString());
    if(!(e[2].getRational().getInt() >=0 ))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());
    return newFixedRightShiftExpr(parseExpr(e[1]), e[2].getRational().getInt());
    break;
  // BVSHL, BVLSHR, BVASHR handled with arith operators below
  case SX:
    // smtlib format interprets the integer argument as the number of bits to
    // extend, while CVC format interprets it as the new total size.
    // The smtlib parser inserts an extra argument "_smtlib" for this operator
    // so that we can distinguish the two cases here.
    if (e.arity() == 4 &&
        e[1].getKind() == ID &&
        e[1][0].getString() == "_smtlib") {
      if(!e[2].isRational() || !e[2].getRational().isInteger())
        throw ParserException("sign_extend must have an integer constant as its"
                              " 1st argument:\n\n"
                              +e.toString());
      if(!(e[2].getRational().getInt() >=0 ))
        throw ParserException("sign_extend must have an integer constant as its"
                              " 1st argument >= 0:\n\n"
                              +e.toString());
      Expr e3 = parseExpr(e[3]);
      return newSXExpr(e3, BVSize(e3) + e[2].getRational().getInt());
    }
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: SX"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("SX must have an integer constant as its"
			    " 2nd argument:\n\n"
			    +e.toString());
    if(!(e[2].getRational().getInt() >=0 ))
      throw ParserException("SX must have an integer constant as its"
			    " 2nd argument >= 0:\n\n"
			    +e.toString());
    return newSXExpr(parseExpr(e[1]), e[2].getRational().getInt());
    break;
  case BVROTL:
  case BVROTR:
  case BVREPEAT:
  case BVZEROEXTEND:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp:"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    if(!e[1].isRational() || !e[1].getRational().isInteger())
      throw ParserException("BVIndexExpr must have an integer constant as its"
			    " 1st argument:\n\n"
			    +e.toString());
    if (kind == BVREPEAT && !(e[1].getRational().getInt() >0 ))
      throw ParserException("BVREPEAT must have an integer constant as its"
			    " 1st argument > 0:\n\n"
			    +e.toString());
    if(!(e[1].getRational().getInt() >=0 ))
      throw ParserException("BVIndexExpr must have an integer constant as its"
			    " 1st argument >= 0:\n\n"
			    +e.toString());
    return newBVIndexExpr(kind, parseExpr(e[2]), e[1].getRational().getInt());
    break;

  case BVAND: {
    if(!(e.arity() >= 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVAND "
			    "kind should have at least 2 arg:\n\n"
			    + e.toString());
    vector<Expr> kids;
    for(int i=1, iend=e.arity(); i<iend; ++i)
      kids.push_back(parseExpr(e[i]));
    return newBVAndExpr(kids);
    break;
  }
  case BVOR: {
    if(!(e.arity() >= 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVOR "
			    "kind should have at least 2 arg:\n\n"
			    + e.toString());
    vector<Expr> kids;
    for(int i=1, iend=e.arity(); i<iend; ++i)
      kids.push_back(parseExpr(e[i]));
    return newBVOrExpr(kids);
    break;
  }
  case BVXOR: {
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVXOR "
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVXorExpr(parseExpr(e[1]), parseExpr(e[2]));
    break;
  }
  case BVXNOR: {
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVXNOR"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVXnorExpr(parseExpr(e[1]), parseExpr(e[2]));
    break;
  }
  case BVNEG:
    if(!(e.arity() == 2))
      throw ParserException("TheoryBitvector::parseExprOp: BVNEG"
			    "kind should have exactly 1 arg:\n\n"
			    + e.toString());
    return newBVNegExpr(parseExpr(e[1]));
    break;
  case BVNAND:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVNAND"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVNandExpr(parseExpr(e[1]), parseExpr(e[2]));
    break;
  case BVNOR:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVNOR"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVNorExpr(parseExpr(e[1]), parseExpr(e[2]));
    break;
  case BVCOMP: {
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVXNOR"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVCompExpr(parseExpr(e[1]), parseExpr(e[2]));
    break;
  }

  case BVUMINUS:
    if(!(e.arity() == 2))
      throw ParserException("TheoryBitvector::parseExprOp: BVUMINUS"
			    "kind should have exactly 1 arg:\n\n"
			    + e.toString());
    return newBVUminusExpr(parseExpr(e[1]));
    break;
  case BVPLUS: {
    vector<Expr> k;
    Expr::iterator i = e.begin(), iend=e.end();
    if (!e[1].isRational()) {
      int maxsize = 0;
      Expr child;
      // Parse the kids of e and push them into the vector 'k'
      for(++i; i!=iend; ++i) {
        child = parseExpr(*i);
        if (getBaseType(child).getExpr().getOpKind() != BITVECTOR) {
          throw ParserException("BVPLUS argument is not bitvector");
        }
        if (BVSize(child) > maxsize) maxsize = BVSize(child);
        k.push_back(child);
      }
      if (e.arity() == 1) return k[0];
      return newBVPlusPadExpr(maxsize, k);
    }
    else {
      if(!(e.arity() >= 4))
        throw ParserException("Expected at least 3 args in BVPLUS:\n\n"
                              +e.toString());
      if(!e[1].isRational() || !e[1].getRational().isInteger())
        throw ParserException
          ("Expected integer constant in BVPLUS:\n\n"
           +e.toString());
      if(!(e[1].getRational().getInt() > 0))
        throw ParserException("parameter must be an integer constant > 0.\n"
                              +e.toString());
      // Skip first two elements of the vector of kids in 'e'.
      // The first element is the kind, and the second is the
      // numOfBits of the bvplus operator.
      ++i;++i;
      // Parse the kids of e and push them into the vector 'k'
      for(; i!=iend; ++i) k.push_back(parseExpr(*i));
      return newBVPlusPadExpr(e[1].getRational().getInt(), k);
    }
    break;
  }
  case BVSUB: {
    if (e.arity() == 3) {
      Expr summand1 = parseExpr(e[1]);
      Expr summand2 = parseExpr(e[2]);
      if (BVSize(summand1) != BVSize(summand2)) {
        throw ParserException("BVSUB: expected same sized arguments"
                              +e.toString());
      }
      return newBVSubExpr(summand1, summand2);
    }
    else if (e.arity() != 4)
      throw ParserException("BVSUB: wrong number of arguments:\n\n"
			    +e.toString());
    if (!e[1].isRational() || !e[1].getRational().isInteger())
      throw ParserException("BVSUB: expected an integer constant as "
			    "first argument:\n\n"
			    +e.toString());
    if (!(e[1].getRational().getInt() > 0))
      throw ParserException("parameter must be an integer constant > 0.\n"
                            +e.toString());
    int bvsublength = e[1].getRational().getInt();
    Expr summand1 = parseExpr(e[2]);
    summand1 = pad(bvsublength, summand1);
    Expr summand2 = parseExpr(e[3]);
    summand2 = pad(bvsublength, summand2);
    return newBVSubExpr(summand1, summand2);
    break;
  }
  case BVMULT: {
    vector<Expr> k;
    Expr::iterator i = e.begin(), iend=e.end();
    if (!e[1].isRational()) {
      if (e.arity() != 3) {
        throw ParserException("TheoryBitvector::parseExprOp: BVMULT: "
                              "expected exactly 2 args:\n\n"
                              + e.toString());
      }
      int maxsize = 0;
      Expr child;
      // Parse the kids of e and push them into the vector 'k'
      for(++i; i!=iend; ++i) {
        child = parseExpr(*i);
        if (getBaseType(child).getExpr().getOpKind() != BITVECTOR) {
          throw ParserException("BVMULT argument is not bitvector");
        }
        if (BVSize(child) > maxsize) maxsize = BVSize(child);
        k.push_back(child);
      }
      if (e.arity() == 1) return k[0];
      return newBVMultPadExpr(maxsize, k[0], k[1]);
    }
    if(!(e.arity() == 4))
      throw ParserException("TheoryBitvector::parseExprOp: BVMULT: "
			    "expected exactly 3 args:\n\n"
			    + e.toString());
    if(!e[1].isRational() || !e[1].getRational().isInteger())
      throw ParserException("BVMULT: expected integer constant"
			    "as first argument:\n\n"
			    +e.toString());
    if(!(e[1].getRational().getInt() > 0))
      throw ParserException("parameter must be an integer constant > 0.\n"
			    +e.toString());
    return newBVMultPadExpr(e[1].getRational().getInt(),
                            parseExpr(e[2]), parseExpr(e[3]));
    break;
  }
  case BVUDIV:
  case BVSDIV:
  case BVUREM:
  case BVSREM:
  case BVSMOD:
  case BVSHL:
  case BVASHR:
  case BVLSHR: {
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp:"
			    "kind should have exactly 2 args:\n\n"
			    + e.toString());
    Expr e1 = parseExpr(e[1]);
    Expr e2 = parseExpr(e[2]);
    if (e1.getType().getExpr().getOpKind() != BITVECTOR ||
        e2.getType().getExpr().getOpKind() != BITVECTOR)
      throw ParserException("TheoryBitvector::parseExprOp:"
                            "Expected bitvector arguments:\n\n"
                            + e.toString());
    if (BVSize(e1) != BVSize(e2))
      throw ParserException("TheoryBitvector::parseExprOp:"
                            "Expected bitvectors of same size:\n\n"
                            + e.toString());
    if (kind == BVSHL) {
      if (e2.getKind() == BVCONST)
        return newFixedConstWidthLeftShiftExpr(e1,
                                               computeBVConst(e2).getInt());
    }
    else if (kind == BVLSHR) {
      if (e2.getKind() == BVCONST)
        return newFixedRightShiftExpr(e1, computeBVConst(e2).getInt());
    }
    return Expr(kind, e1, e2);
    break;
  }

  case BVLT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVLT"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVLTExpr(parseExpr(e[1]),parseExpr(e[2]));
    break;
  case BVLE:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVLE"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVLEExpr(parseExpr(e[1]),parseExpr(e[2]));
    break;
  case BVGT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVGT"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVLTExpr(parseExpr(e[2]),parseExpr(e[1]));
    break;
  case BVGE:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVGE"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVLEExpr(parseExpr(e[2]),parseExpr(e[1]));
    break;
  case BVSLT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVLT"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVSLTExpr(parseExpr(e[1]),parseExpr(e[2]));
    break;
  case BVSLE:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVLE"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVSLEExpr(parseExpr(e[1]),parseExpr(e[2]));
    break;
  case BVSGT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVGT"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVSLTExpr(parseExpr(e[2]),parseExpr(e[1]));
    break;
  case BVSGE:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVGE"
			    "kind should have exactly 2 arg:\n\n"
			    + e.toString());
    return newBVSLEExpr(parseExpr(e[2]),parseExpr(e[1]));
    break;

  case INTTOBV:
    throw ParserException("INTTOBV not implemented");
    break;
  case BVTOINT:
    throw ParserException("BVTOINT not implemented");
    break;

  case BVTYPEPRED:
    throw ParserException("BVTYPEPRED is used internally");
    break;

  default:
    FatalAssert(false,
		"TheoryBitvector::parseExprOp: unrecognized input operator"
		+e.toString());
    break;
  }
  return e;
}


///////////////////////////////////////////////////////////////////////////////
//helper functions
///////////////////////////////////////////////////////////////////////////////


Expr TheoryBitvector::newBitvectorTypeExpr(int bvLength)
{
  DebugAssert(bvLength > 0,
	      "TheoryBitvector::newBitvectorTypeExpr:\n"
	      "len of a BV must be a positive integer:\n bvlength = "+
	      int2string(bvLength));
  if (bvLength > d_maxLength)
    d_maxLength = bvLength;
  return Expr(BITVECTOR, getEM()->newRatExpr(bvLength));
}


Expr TheoryBitvector::newBitvectorTypePred(const Type& t, const Expr& e)
{
  return Expr(Expr(BVTYPEPRED, t.getExpr()).mkOp(), e);
}


Expr TheoryBitvector::newBVAndExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVAndExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise operator"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVAND, t1, t2);
}


Expr TheoryBitvector::newBVAndExpr(const vector<Expr>& kids)
{
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVAndExpr:"
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVAndExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
    if(i < kids.size()-1) {
      DebugAssert(BVSize(kids[i]) == BVSize(kids[i+1]),
		  "TheoryBitvector::bitwise operator"
		  "inputs must have same length:\n t1 = " + kids[i].toString()
		  + "\n t2 = " + kids[i+1].toString());
    }
  }
  return Expr(CVC3::BVAND, kids, getEM());
}


Expr TheoryBitvector::newBVOrExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVOrExpr: "
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise OR operator: "
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVOR, t1, t2);
}


Expr TheoryBitvector::newBVOrExpr(const vector<Expr>& kids)
{
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVOrExpr: "
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVOrExpr: "
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
    if(i < kids.size()-1) {
      DebugAssert(BVSize(kids[i]) == BVSize(kids[i+1]),
		  "TheoryBitvector::bitwise operator"
		  "inputs must have same length:\n t1 = " + kids[i].toString()
		  + "\n t2 = " + kids[i+1].toString());
    }
  }
  return Expr(CVC3::BVOR, kids, getEM());
}


Expr TheoryBitvector::newBVNandExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVNandExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise operator"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVNAND, t1, t2);
}


Expr TheoryBitvector::newBVNorExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVNorExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise operator"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVNOR, t1, t2);
}


Expr TheoryBitvector::newBVXorExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVXorExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise operator"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVXOR, t1, t2);
}


Expr TheoryBitvector::newBVXorExpr(const vector<Expr>& kids)
{
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVXorExpr:"
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVXorExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
    if(i < kids.size()-1) {
      DebugAssert(BVSize(kids[i]) ==  BVSize(kids[i+1]),
		  "TheoryBitvector::bitwise operator"
		  "inputs must have same length:\n t1 = " + kids[i].toString()
		  + "\n t2 = " + kids[i+1].toString());
    }
  }
  return Expr(CVC3::BVXOR, kids, getEM());
}


Expr TheoryBitvector::newBVXnorExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVXnorExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise operator"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVXNOR, t1, t2);
}


Expr TheoryBitvector::newBVCompExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVCompExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise operator"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVCOMP, t1, t2);
}


Expr TheoryBitvector::newBVXnorExpr(const vector<Expr>& kids)
{
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVXnorExpr:"
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVXnorExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
    if(i < kids.size()-1) {
      DebugAssert(BVSize(kids[i]) == BVSize(kids[i+1]),
		  "TheoryBitvector::bitwise operator"
		  "inputs must have same length:\n t1 = " + kids[i].toString()
		  + "\n t2 = " + kids[i+1].toString());
    }
  }
  return Expr(CVC3::BVXNOR, kids, getEM());
}


Expr TheoryBitvector::newBVLTExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVLTExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  return Expr(CVC3::BVLT, t1, t2);
}


Expr TheoryBitvector::newBVLEExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVLEExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  return Expr(CVC3::BVLE, t1, t2);
}


Expr TheoryBitvector::newSXExpr(const Expr& t1, int len)
{
  DebugAssert(len >=0,
	      " TheoryBitvector::newSXExpr:"
	      "SX index must be a non-negative integer"+
	      int2string(len));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newSXExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  if(len==0) return t1;
  return Expr(Expr(SX, getEM()->newRatExpr(len)).mkOp(), t1);
}


Expr TheoryBitvector::newBVIndexExpr(int kind, const Expr& t1, int len)
{
  DebugAssert(kind != BVREPEAT || len > 0,
              "repeat requires index > 0");
  DebugAssert(len >=0,
	      "TheoryBitvector::newBVIndexExpr:"
	      "index must be a non-negative integer"+
	      int2string(len));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVIndexExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  return Expr(Expr(kind, getEM()->newRatExpr(len)).mkOp(), t1);
}


Expr TheoryBitvector::newBVSLTExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVSLTExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  return Expr(CVC3::BVSLT, t1, t2);
}


Expr TheoryBitvector::newBVSLEExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVSLEExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  return Expr(CVC3::BVSLE, t1, t2);
}


Expr TheoryBitvector::newBVNegExpr(const Expr& t1)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVNegExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  return Expr(CVC3::BVNEG, t1);
}


Expr TheoryBitvector::newBVUminusExpr(const Expr& t1)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVNegExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  return Expr(CVC3::BVUMINUS, t1);
}


Expr TheoryBitvector::newBoolExtractExpr(const Expr& t1, int index)
{
  DebugAssert(index >=0,
	      " TheoryBitvector::newBoolExtractExpr:"
	      "bool_extract index must be a non-negative integer"+
	      int2string(index));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVBoolExtractExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  return Expr(Expr(BOOLEXTRACT, getEM()->newRatExpr(index)).mkOp(), t1);
}


Expr TheoryBitvector::newFixedLeftShiftExpr(const Expr& t1, int shiftLength)
{
  DebugAssert(shiftLength >=0,
	      " TheoryBitvector::newFixedleftshift:"
	      "fixed_shift index must be a non-negative integer"+
	      int2string(shiftLength));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVFixedleftshiftExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  return Expr(Expr(LEFTSHIFT, getEM()->newRatExpr(shiftLength)).mkOp(), t1);
}


Expr TheoryBitvector::newFixedConstWidthLeftShiftExpr(const Expr& t1, int shiftLength)
{
  DebugAssert(shiftLength >=0,
	      " TheoryBitvector::newFixedConstWidthLeftShift:"
	      "fixed_shift index must be a non-negative integer"+
	      int2string(shiftLength));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVFixedleftshiftExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  return Expr(Expr(CONST_WIDTH_LEFTSHIFT, getEM()->newRatExpr(shiftLength)).mkOp(), t1);
}


Expr TheoryBitvector::newFixedRightShiftExpr(const Expr& t1, int shiftLength)
{
  DebugAssert(shiftLength >=0,
	      " TheoryBitvector::newFixedRightShift:"
	      "fixed_shift index must be a non-negative integer"+
	      int2string(shiftLength));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVFixedRightShiftExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  if(shiftLength==0) return t1;
  return Expr(Expr(RIGHTSHIFT, getEM()->newRatExpr(shiftLength)).mkOp(), t1);
}


Expr TheoryBitvector::newConcatExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVConcatExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  return Expr(CONCAT, t1, t2);
}


Expr TheoryBitvector::newConcatExpr(const Expr& t1, const Expr& t2,
				    const Expr& t3)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind() &&
	      BITVECTOR == t3.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVConcatExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() +
	      "\n t2 = " +t2.toString() +
	      "\n t3 =" + t3.toString());
  return Expr(CONCAT, t1, t2, t3);
}


Expr TheoryBitvector::newConcatExpr(const vector<Expr>& kids)
{
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVConcatExpr:"
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVConcatExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
  }
  return Expr(CONCAT, kids, getEM());
}


Expr TheoryBitvector::newBVMultExpr(int bvLength,
				    const Expr& t1, const Expr& t2)
{
  DebugAssert(bvLength > 0,
	      "TheoryBitvector::newBVmultExpr:"
	      "bvLength must be an integer > 0: bvLength = " +
	      int2string(bvLength));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVmultExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(bvLength == BVSize(t1) &&
              bvLength == BVSize(t2), "Expected same length");
  return Expr(Expr(BVMULT, getEM()->newRatExpr(bvLength)).mkOp(), t1, t2);
}


Expr TheoryBitvector::newBVMultExpr(int bvLength, const vector<Expr>& kids)
{
  DebugAssert(bvLength > 0,
	      "TheoryBitvector::newBVmultExpr:"
	      "bvLength must be an integer > 0: bvLength = " +
	      int2string(bvLength));
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVPlusExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
    DebugAssert(BVSize(kids[i]) == bvLength, "Expected matching sizes");
  }
  return Expr(Expr(BVMULT, getEM()->newRatExpr(bvLength)).mkOp(), kids);
}


Expr TheoryBitvector::newBVMultPadExpr(int bvLength, const vector<Expr>& kids)
{
  vector<Expr> newKids;
  for (unsigned i = 0; i < kids.size(); ++i) {
    newKids.push_back(pad(bvLength, kids[i]));
  }
  return newBVMultExpr(bvLength, newKids);
}


Expr TheoryBitvector::newBVMultPadExpr(int bvLength,
                                       const Expr& t1, const Expr& t2)
{
  return newBVMultExpr(bvLength, pad(bvLength, t1), pad(bvLength, t2));
}

Expr TheoryBitvector::newBVUDivExpr(const Expr& t1, const Expr& t2)
{
	  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
		      BITVECTOR == t2.getType().getExpr().getOpKind(),
		      "TheoryBitvector::newBVUDivExpr:"
		      "inputs must have type BITVECTOR:\n t1 = " +
		      t1.toString() + "\n t2 = " +t2.toString());
	  DebugAssert(BVSize(t2) == BVSize(t1), "Expected same length");
	  return Expr(BVUDIV, t1, t2);
}

Expr TheoryBitvector::newBVURemExpr(const Expr& t1, const Expr& t2)
{
	  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
		      BITVECTOR == t2.getType().getExpr().getOpKind(),
		      "TheoryBitvector::newBVURemExpr:"
		      "inputs must have type BITVECTOR:\n t1 = " +
		      t1.toString() + "\n t2 = " +t2.toString());
	  DebugAssert(BVSize(t2) == BVSize(t1), "Expected same length");
	  return Expr(BVUREM, t1, t2);
}

Expr TheoryBitvector::newBVSDivExpr(const Expr& t1, const Expr& t2)
{
	  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
		      BITVECTOR == t2.getType().getExpr().getOpKind(),
		      "TheoryBitvector::newBVSDivExpr:"
		      "inputs must have type BITVECTOR:\n t1 = " +
		      t1.toString() + "\n t2 = " +t2.toString());
	  DebugAssert(BVSize(t1) == BVSize(t2), "Expected same length");
	  return Expr(BVSDIV, t1, t2);
}

Expr TheoryBitvector::newBVSRemExpr(const Expr& t1, const Expr& t2)
{
	  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
		      BITVECTOR == t2.getType().getExpr().getOpKind(),
		      "TheoryBitvector::newBVSRemExpr:"
		      "inputs must have type BITVECTOR:\n t1 = " +
		      t1.toString() + "\n t2 = " +t2.toString());
	  DebugAssert(BVSize(t1) == BVSize(t2), "Expected same length");
	  return Expr(BVSREM, t1, t2);
}

Expr TheoryBitvector::newBVSModExpr(const Expr& t1, const Expr& t2)
{
	  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
		      BITVECTOR == t2.getType().getExpr().getOpKind(),
		      "TheoryBitvector::newBVSModExpr:"
		      "inputs must have type BITVECTOR:\n t1 = " +
		      t1.toString() + "\n t2 = " +t2.toString());
	  DebugAssert(BVSize(t1) == BVSize(t2), "Expected same length");
	  return Expr(BVSMOD, t1, t2);
}

//! produces a string of 0's of length bvLength
Expr TheoryBitvector::newBVZeroString(int bvLength)
{
  DebugAssert(bvLength > 0,
	      "TheoryBitvector::newBVZeroString:must be >= 0: "
	      + int2string(bvLength));
  std::vector<bool> bits;
  for(int count=0; count < bvLength; count++) {
    bits.push_back(false);
  }
  return newBVConstExpr(bits);
}


//! produces a string of 1's of length bvLength
Expr TheoryBitvector::newBVOneString(int bvLength)
{
  DebugAssert(bvLength > 0,
	      "TheoryBitvector::newBVOneString:must be >= 0: "
	      + int2string(bvLength));
  std::vector<bool> bits;
  for(int count=0; count < bvLength; count++) {
    bits.push_back(true);
  }
  return newBVConstExpr(bits);
}


Expr TheoryBitvector::newBVConstExpr(const vector<bool>& bits)
{
  DebugAssert(bits.size() > 0,
	      "TheoryBitvector::newBVConstExpr:"
	      "size of bits should be > 0");
  BVConstExpr bv(getEM(), bits, d_bvConstExprIndex);
  return getEM()->newExpr(&bv);
}


Expr TheoryBitvector::newBVConstExpr(const Rational& r, int bvLength)
{
  DebugAssert(r.isInteger(),
	      "TheoryBitvector::newBVConstExpr: not an integer: "
	      + r.toString());
  DebugAssert(bvLength > 0,
	      "TheoryBitvector::newBVConstExpr: bvLength = "
	      + int2string(bvLength));
  string s(r.toString(2));
  size_t strsize = s.size();
  size_t length = bvLength;
  Expr res;
  if(length > 0 && length != strsize) {
    //either (length > strsize) or (length < strsize)
    if(length < strsize) {
      s = s.substr((strsize-length), length);
    } else {
      string zeros("");
      for(size_t i=0, pad=length-strsize; i < pad; ++i)
	zeros += "0";
      s = zeros+s;
    }

    res = newBVConstExpr(s, 2);
  }
  else
    res = newBVConstExpr(s, 2);

  return res;
}


Expr TheoryBitvector::newBVConstExpr(const std::string& s, int base)
{
  DebugAssert(s.size() > 0,
	      "TheoryBitvector::newBVConstExpr:"
	      "# of subterms must be at least 2");
  DebugAssert(base == 2 || base == 16,
	      "TheoryBitvector::newBVConstExpr: base = "
	      +int2string(base));
  //hexadecimal
  std::string str = s;
  if(16 == base) {
    Rational r(str, 16);
    return newBVConstExpr(r, str.size()*4);
  }
  else {
    BVConstExpr bv(getEM(), str, d_bvConstExprIndex);
    return getEM()->newExpr(&bv);
  }
}


Expr
TheoryBitvector::
newBVExtractExpr(const Expr& e, int hi, int low)
{
  DebugAssert(low>=0 && hi>=low,
	      " TheoryBitvector::newBVExtractExpr: "
	      "bad bv_extract indices: hi = "
	      + int2string(hi)
	      + ", low = "
	      + int2string(low));
  if (e.getOpKind() == LEFTSHIFT &&
      hi == BVSize(e[0])-1 &&
      low == 0) {
    return newFixedConstWidthLeftShiftExpr(e[0], getFixedLeftShiftParam(e));
  }
  DebugAssert(BITVECTOR == e.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVExtractExpr:"
	      "inputs must have type BITVECTOR:\n e = " +
	      e.toString());
  return Expr(Expr(EXTRACT,
                   getEM()->newRatExpr(hi),
                   getEM()->newRatExpr(low)).mkOp(), e);
}


Expr TheoryBitvector::newBVSubExpr(const Expr& t1, const Expr& t2)
{
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVSubExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::newBVSubExpr"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(BVSUB, t1, t2);
}


Expr TheoryBitvector::newBVPlusExpr(int bvLength, const Expr& k1, const Expr& k2)
{
  DebugAssert(bvLength > 0,
	      " TheoryBitvector::newBVPlusExpr:"
	      "bvplus length must be a positive integer: "+
	      int2string(bvLength));
  DebugAssert(BITVECTOR == k1.getType().getExpr().getOpKind(),
              "TheoryBitvector::newBVPlusExpr:"
              "inputs must have type BITVECTOR:\n t1 = " +
              k1.toString());
  DebugAssert(BVSize(k1) == bvLength, "Expected matching sizes");
  DebugAssert(BITVECTOR == k2.getType().getExpr().getOpKind(),
              "TheoryBitvector::newBVPlusExpr:"
              "inputs must have type BITVECTOR:\n t1 = " +
              k2.toString());
  DebugAssert(BVSize(k2) == bvLength, "Expected matching sizes");

  return Expr(Expr(BVPLUS, getEM()->newRatExpr(bvLength)).mkOp(), k1, k2);
}


Expr TheoryBitvector::newBVPlusExpr(int bvLength,
				    const vector<Expr>& k)
{
  DebugAssert(bvLength > 0,
	      " TheoryBitvector::newBVPlusExpr:"
	      "bvplus length must be a positive integer: "+
	      int2string(bvLength));
  DebugAssert(k.size() > 1,
	      " TheoryBitvector::newBVPlusExpr:"
	      " size of input vector must be greater than 0: ");
  for(unsigned int i=0; i<k.size(); ++i) {
    DebugAssert(BITVECTOR == k[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVPlusExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		k[i].toString());
    DebugAssert(BVSize(k[i]) == bvLength, "Expected matching sizes");
  }
  return Expr(Expr(BVPLUS, getEM()->newRatExpr(bvLength)).mkOp(), k);
}


Expr TheoryBitvector::newBVPlusPadExpr(int bvLength,
                                       const vector<Expr>& k)
{
  vector<Expr> newKids;
  for (unsigned i = 0; i < k.size(); ++i) {
    newKids.push_back(pad(bvLength, k[i]));
  }
  return newBVPlusExpr(bvLength, newKids);
}


// Accessors for expression parameters


int TheoryBitvector::getBitvectorTypeParam(const Expr& e)
{
  DebugAssert(BITVECTOR == e.getKind(),
	      "TheoryBitvector::getBitvectorTypeParam: wrong kind: " +
	      e.toString());
  return e[0].getRational().getInt();
}


Type TheoryBitvector::getTypePredType(const Expr& tp)
{
  DebugAssert(tp.getOpKind()==BVTYPEPRED && tp.isApply(),
	      "TheoryBitvector::getTypePredType:\n tp = "+tp.toString());
  return Type(tp.getOpExpr()[0]);
}


const Expr& TheoryBitvector::getTypePredExpr(const Expr& tp)
{
  DebugAssert(tp.getOpKind()==BVTYPEPRED,
	      "TheoryBitvector::getTypePredType:\n tp = "+tp.toString());
  return tp[0];
}


int TheoryBitvector::getBoolExtractIndex(const Expr& e)
{
  DebugAssert(BOOLEXTRACT == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getBoolExtractIndex: wrong kind" +
	      e.toString());
  return e.getOpExpr()[0].getRational().getInt();
}


int TheoryBitvector::getSXIndex(const Expr& e)
{
  DebugAssert(SX == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getSXIndex: wrong kind\n"+e.toString());
  return e.getOpExpr()[0].getRational().getInt();
}


int TheoryBitvector::getBVIndex(const Expr& e)
{
  DebugAssert(e.isApply() &&
              (e.getOpKind() == BVREPEAT ||
               e.getOpKind() == BVROTL ||
               e.getOpKind() == BVROTR ||
               e.getOpKind() == BVZEROEXTEND),
	      "TheoryBitvector::getBVIndex: wrong kind\n"+e.toString());
  return e.getOpExpr()[0].getRational().getInt();
}


int TheoryBitvector::getFixedLeftShiftParam(const Expr& e)
{
  DebugAssert(e.isApply() &&
              (LEFTSHIFT == e.getOpKind() ||
               CONST_WIDTH_LEFTSHIFT == e.getOpKind()),
	      "TheoryBitvector::getFixedLeftShiftParam: wrong kind" +
	      e.toString());
  return e.getOpExpr()[0].getRational().getInt();
}


int TheoryBitvector::getFixedRightShiftParam(const Expr& e)
{
  DebugAssert(RIGHTSHIFT == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getFixedRightShiftParam: wrong kind" +
	      e.toString());
  return e.getOpExpr()[0].getRational().getInt();
}


int TheoryBitvector::getExtractLow(const Expr& e)
{
  DebugAssert(EXTRACT == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getExtractLow: wrong kind" +
	      e.toString());
  return e.getOpExpr()[1].getRational().getInt();
}


int TheoryBitvector::getExtractHi(const Expr& e)
{
  DebugAssert(EXTRACT == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getExtractHi: wrong kind" +
	      e.toString());
  return e.getOpExpr()[0].getRational().getInt();
}


int TheoryBitvector::getBVPlusParam(const Expr& e)
{
  DebugAssert(BVPLUS == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getBVPlusParam: wrong kind" +
	      e.toString(AST_LANG));
  return e.getOpExpr()[0].getRational().getInt();
}

int TheoryBitvector::getBVMultParam(const Expr& e)
{
  DebugAssert(BVMULT == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getBVMultParam: wrong kind " +
	      e.toString(AST_LANG));
  return e.getOpExpr()[0].getRational().getInt();
}

unsigned TheoryBitvector::getBVConstSize(const Expr& e)
{
  DebugAssert(BVCONST == e.getKind(), "getBVConstSize called on non-bvconst");
  const BVConstExpr* bvc = dynamic_cast<const BVConstExpr*>(e.getExprValue());
  DebugAssert(bvc, "getBVConstSize: cast failed");
  return bvc->size();
}


bool TheoryBitvector::getBVConstValue(const Expr& e, int i)
{
  DebugAssert(BVCONST == e.getKind(), "getBVConstSize called on non-bvconst");
  const BVConstExpr* bvc = dynamic_cast<const BVConstExpr*>(e.getExprValue());
  DebugAssert(bvc, "getBVConstSize: cast failed");
  return bvc->getValue(i);
}


// as newBVConstExpr can not give the BV expr of a negative rational,
// I use this wrapper to do that
Expr TheoryBitvector::signed_newBVConstExpr( Rational c, int bv_size)
{
  if( c > 0)
    return newBVConstExpr( c, bv_size);
  else
    {
      c = -c;
      Expr tmp = newBVConstExpr( c, bv_size);
      Rational neg_tmp = computeNegBVConst( tmp );
      return newBVConstExpr( neg_tmp, bv_size );
    }
}


// Computes the integer value of a bitvector constant
Rational TheoryBitvector::computeBVConst(const Expr& e)
{
  DebugAssert(BVCONST == e.getKind(),
	      "TheoryBitvector::computeBVConst:"
	      "input must be a BITVECTOR CONST: " + e.toString());
  if(*d_bv32Flag) {
    int c(0);
    for(int j=(int)getBVConstSize(e)-1; j>=0; j--)
      c = 2*c + getBVConstValue(e, j) ? 1 : 0;
    Rational d(c);
    return d;
  } else {
    Rational c(0);
    for(int j=(int)getBVConstSize(e)-1; j>=0; j--)
      c = 2*c + (getBVConstValue(e, j) ? Rational(1) : Rational(0));
    return c;
  }
}


// Computes the integer value of ~c+1
Rational TheoryBitvector::computeNegBVConst(const Expr& e)
{
  DebugAssert(BVCONST == e.getKind(),
	      "TheoryBitvector::computeBVConst:"
	      "input must be a BITVECTOR CONST: " + e.toString());
  if(*d_bv32Flag) {
    int c(0);
    for(int j=(int)getBVConstSize(e)-1; j>=0; j--)
      c = 2*c + getBVConstValue(e, j) ? 0 : 1;
    Rational d(c+1);
    return d;
  } else {
    Rational c(0);
    for(int j=(int)getBVConstSize(e)-1; j>=0; j--)
      c = 2*c + (getBVConstValue(e, j) ? Rational(0) : Rational(1));
    return c+1;
  }
}


//////////////////////////////////////////////////////////////////////
// class BVConstExpr methods
/////////////////////////////////////////////////////////////////////


//! Constructor
BVConstExpr::BVConstExpr(ExprManager* em, std::string bvconst,
			 size_t mmIndex, ExprIndex idx)
  : ExprValue(em, BVCONST, idx), d_MMIndex(mmIndex)
{
  std::string::reverse_iterator i = bvconst.rbegin();
  std::string::reverse_iterator iend = bvconst.rend();
  DebugAssert(bvconst.size() > 0,
	      "TheoryBitvector::newBVConstExpr:"
	      "# of subterms must be at least 2");

  for(;i != iend; ++i) {
    TRACE("bitvector", "BVConstExpr: bit ", *i, "");
    if('0' == *i)
      d_bvconst.push_back(false);
    else {
      if('1' == *i)
	d_bvconst.push_back(true);
      else
	DebugAssert(false, "BVConstExpr: bad binary bit-vector: "
		    + bvconst);
    }
  }
  TRACE("bitvector", "BVConstExpr: #bits ", d_bvconst.size(), "");
}


BVConstExpr::BVConstExpr(ExprManager* em, std::vector<bool> bvconst,
                         size_t mmIndex, ExprIndex idx)
  : ExprValue(em, BVCONST, idx), d_bvconst(bvconst), d_MMIndex(mmIndex)
{
  TRACE("bitvector", "BVConstExpr(vector<bool>): arg. size = ", bvconst.size(),
	", d_bvconst.size = "+int2string(d_bvconst.size()));
}


size_t BVConstExpr::computeHash() const
{
  std::vector<bool>::const_iterator i = d_bvconst.begin();
  std::vector<bool>::const_iterator iend = d_bvconst.end();
  size_t hash_value = 0;
  hash_value = ExprValue::hash(BVCONST);
  for (;i != iend; i++)
    if(*i)
      hash_value = PRIME*hash_value + HASH_VALUE_ONE;
    else
      hash_value = PRIME*hash_value + HASH_VALUE_ZERO;
  return hash_value;
}

Expr TheoryBitvector::computeTCC(const Expr& e)
{
  // inline recursive computation for deeply nested bitvector Exprs

  vector<Expr> operatorStack;
  vector<Expr> operandStack;
  vector<int> childStack;
  Expr e2, tcc;

  operatorStack.push_back(e);
  childStack.push_back(0);

  while (!operatorStack.empty()) {
    DebugAssert(operatorStack.size() == childStack.size(), "Invariant violated");

    if (childStack.back() < operatorStack.back().arity()) {

      e2 = operatorStack.back()[childStack.back()++];

      if (e2.isVar()) {
        operandStack.push_back(trueExpr());
      }
      else {
        ExprMap<Expr>::iterator itccCache = theoryCore()->tccCache().find(e2);
        if (itccCache != theoryCore()->tccCache().end()) {
          operandStack.push_back((*itccCache).second);
        }
        else if (theoryOf(e2) == this) {
          if (e2.arity() == 0) {
            operandStack.push_back(trueExpr());
          }
          else {
            operatorStack.push_back(e2);
            childStack.push_back(0);
          }
        }
        else {
          operandStack.push_back(getTCC(e2));
        }
      }
    }
    else {
      e2 = operatorStack.back();
      operatorStack.pop_back();
      childStack.pop_back();
      vector<Expr> children;
      vector<Expr>::iterator childStart = operandStack.end() - (e2.arity());
      children.insert(children.begin(), childStart, operandStack.end());
      operandStack.erase(childStart, operandStack.end());
      tcc = (children.size() == 0) ? trueExpr() :
        (children.size() == 1) ? children[0] :
        getCommonRules()->rewriteAnd(andExpr(children)).getRHS();
      switch(e2.getKind()) {
        case BVUDIV:
        case BVSDIV:
        case BVUREM:
        case BVSREM:
        case BVSMOD: {
          DebugAssert(e2.arity() == 2, "");
          int size = BVSize(e2);
          tcc = getCommonRules()->rewriteAnd(tcc.andExpr(!(e2[1].eqExpr(newBVZeroString(size))))).getRHS();
          break;
        }
        default:
          break;
      }
      operandStack.push_back(tcc);
      theoryCore()->tccCache()[e2] = tcc;
    }
  }
  DebugAssert(childStack.empty(), "Invariant violated");
  DebugAssert(operandStack.size() == 1, "Expected single operand left");
  return operandStack.back();
}
