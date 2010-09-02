/*****************************************************************************/
/*!
 * \file core_theorem_producer.cpp
 * 
 * Author: Sergey Berezin
 * 
 * Created: Feb 05 03:40:36 GMT 2003
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
// CLASS: CoreTheoremProducer
//
// AUTHOR: Sergey Berezin, 12/09/2002
//         Vijay Ganesh, september 15th, 2004 (CNF Converter rules)
//
// Description: Implementation of the proof rules for ground
// equational logic (reflexivity, symmetry, transitivity, and
// substitutivity).
//
///////////////////////////////////////////////////////////////////////////////


// This code is trusted
#define _CVC3_TRUSTED_


#include "core_theorem_producer.h"
#include "theory_core.h"


using namespace CVC3;
using namespace std;


// The trusted method of TheoryCore which creates this theorem producer
CoreProofRules* TheoryCore::createProofRules(TheoremManager* tm) {
  return new CoreTheoremProducer(tm, this);
}


// e: T ==> |- typePred_T(e)  [asserting the type predicate of e]
Theorem
CoreTheoremProducer::typePred(const Expr& e) {
  Type tp(e.getType());
  Expr pred(d_core->getTypePred(tp, e));
  Proof pf;
  if(withProof()) {
    pf = newPf("type_pred", e, tp.getExpr());
  }
  return newTheorem(pred, Assumptions::emptyAssump(), pf);
}


Theorem
CoreTheoremProducer::rewriteLetDecl(const Expr& e) {
  if(CHECK_PROOFS)
    CHECK_SOUND(e.getKind() == LETDECL,
		"rewriteLetDecl: wrong expression: " + e.toString());
  Proof pf;
  if(withProof()) // FIXME: implement this in flea
    pf = newPf("rewrite_letdecl", e[1]);
  return newRWTheorem(e, e[1], Assumptions::emptyAssump(), pf);
}

// ==> NOT (AND e1 ... en) IFF (OR !e1 ... !en), takes (AND ...)
Theorem CoreTheoremProducer::rewriteNotAnd(const Expr& e) {
 if(CHECK_PROOFS)
  CHECK_SOUND(e.isNot() && e[0].isAnd(),
		"rewriteNotAnd: precondition violated: " + e.toString());

  
  vector<Expr> kids; // vector of <!e1,...,!en>
  for(Expr::iterator i=e[0].begin(), iend=e[0].end(); i!=iend; ++i)
    // Collapse double negations
    kids.push_back(i->negate());
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_not_and", e);
  return newRWTheorem(e, orExpr(kids), Assumptions::emptyAssump(), pf);
}

// ==> NOT (OR e1 ... en) IFF (AND !e1 ... !en), takes (OR ...)
Theorem
CoreTheoremProducer::rewriteNotOr(const Expr& e) {
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isNot() && e[0].isOr(),
		"rewriteNotOr: precondition violated: " + e.toString());
  vector<Expr> kids; // vector of <!e1,...,!en>
  for(Expr::iterator i=e[0].begin(), iend=e[0].end(); i!=iend; ++i)
    // Collapse double negations
    kids.push_back(i->negate());
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_not_or", e);
  return newRWTheorem(e, andExpr(kids), Assumptions::emptyAssump(), pf);
}


// ==> NOT IFF(e1,e2) IFF IFF(e1,NOT e2)
Theorem
CoreTheoremProducer::rewriteNotIff(const Expr& e) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isNot() && e[0].isIff(), "rewriteNotIff precondition violated");
  if(withProof()) {
    pf = newPf("rewrite_not_iff", e);
  }
  return newRWTheorem(e, e[0][0].iffExpr(!e[0][1]), Assumptions::emptyAssump(), pf);
}


// ==> NOT ITE(a,b,c) IFF ITE(a,NOT b,NOT c)
Theorem
CoreTheoremProducer::rewriteNotIte(const Expr& e) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isNot() && e[0].isITE(), "rewriteNotIte precondition violated");
  if(withProof()) {
    pf = newPf("rewrite_not_ite", e);
  }
  return newRWTheorem(e, e[0][0].iteExpr(!e[0][1], !e[0][2]), Assumptions::emptyAssump(), pf);
}


// a |- b == d ==> ITE(a, b, c) == ITE(a, d, c)
Theorem
CoreTheoremProducer::rewriteIteThen(const Expr& e, const Theorem& thenThm) {
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(withAssumptions(), "Cannot check proof without assumptions");
    CHECK_SOUND(e.isITE() && thenThm.isRewrite() && e[1] == thenThm.getLHS(),
		"rewriteIteThen precondition violated \n then expression: "
		+ thenThm.getExpr().toString() + "\n e = " + e.toString());
  }
  Assumptions a = thenThm.getAssumptionsRef() - e[0];
  if(withProof()) {
    Type t = e.getType();
    DebugAssert(!t.isNull(), "rewriteIteThen: e has no type: "
		+ e.toString());
    bool useIff = t.isBool();
    if(useIff)
      pf = newPf("rewrite_ite_then_iff", e, thenThm.getProof());
    else {
      pf = newPf("rewrite_ite_then", e, thenThm.getProof());
    }
  }
  return newRWTheorem(e, e[0].iteExpr(thenThm.getRHS(), e[2]), a, pf);
}

// !a |- c == d ==> ITE(a, b, c) == ITE(a, b, d)
Theorem
CoreTheoremProducer::rewriteIteElse(const Expr& e, const Theorem& elseThm) {
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(withAssumptions(), "Cannot check proof without assumptions");
    CHECK_SOUND(e.isITE() && elseThm.isRewrite() && e[2] == elseThm.getLHS(),
		"rewriteIteElse precondition violated \n else expression: "
		+ elseThm.getExpr().toString() + "\n e = " + e.toString());
  }
  Assumptions a = elseThm.getAssumptionsRef() - !e[0];
  if(withProof()) {
    Type t = e.getType();
    DebugAssert(!t.isNull(), "rewriteIteElse: e has no type: "
		+ e.toString());
    bool useIff = t.isBool();
    if(useIff)
      pf = newPf("rewrite_ite_else_iff", e, elseThm.getProof());
    else {
      pf = newPf("rewrite_ite_else", e, elseThm.getProof());
    }
  }
  return newRWTheorem(e, e[0].iteExpr(e[1], elseThm.getRHS()), a, pf);
}

// ==> ITE(c, e1, e2) <=> (!c OR e1) AND (c OR e2)
Theorem 
CoreTheoremProducer::rewriteIteBool(const Expr& c,
                                    const Expr& e1, const Expr& e2) {
  if(CHECK_PROOFS)
    CHECK_SOUND(e1.getType().isBool() && e2.getType().isBool(),
		"rewriteIteBool: Not a boolean ITE: "
		+ c.iteExpr(e1, e2).toString());
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_ite_bool", c, e1, e2);
  return newRWTheorem(c.iteExpr(e1,e2),
		      (e1.orExpr(!c).andExpr(c.orExpr(e2))), Assumptions::emptyAssump(), pf);
}


//! |= (A & B1) | (A & B2) | ... | (A & bn) <=> A & (B1 | B2 | ...| Bn)
Theorem
CoreTheoremProducer::orDistributivityRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isOr() && e.arity() >= 2,
		"CoreTheoremProducer::orDistributivityRule: "
		"input must be an OR expr: \n" + e.toString());
    const Expr& e0 = e[0];

    CHECK_SOUND(e0.isAnd() && e0.arity() == 2,
		"CoreTheoremProducer::orDistributivityRule: "
		"input must be an OR of binary ANDs: \n" + e.toString());
  }

  const Expr& A = e[0][0];

  if(CHECK_PROOFS) {
    for(Expr::iterator i=e.begin(),iend=e.end();i!=iend;++i) {
      const Expr& ei = *i;
      CHECK_SOUND(ei.isAnd() && ei.arity() == 2,
		"CoreTheoremProducer::orDistributivityRule: "
		"input must be an OR of binary ANDs: \n" + e.toString());
      CHECK_SOUND(A == ei[0],
		  "CoreTheoremProducer::orDistributivityRule: "
		  "input must have a common factor: \n" + e.toString());
    }
  }
  vector<Expr> output;
  for(Expr::iterator i=e.begin(),iend=e.end();i!=iend;++i) {
    Expr ei = *i;
    output.push_back(ei[1]);
  }
  Expr out = A.andExpr(orExpr(output));

  Proof pf;
  if(withProof())
    pf = newPf("or_distribuitivity_rule", e);
  
  return newRWTheorem(e, out, Assumptions::emptyAssump(), pf);
} 



//! |= (A | B1) & (A | B2) & ... & (A | bn) <=> A | (B1 & B2 & ...& Bn)
Theorem
CoreTheoremProducer::andDistributivityRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isAnd() && e.arity() >= 2,
		"CoreTheoremProducer::andDistributivityRule: "
		"input must be an AND expr: \n" + e.toString());
    const Expr& e0 = e[0];

    CHECK_SOUND(e0.isOr() && e0.arity() == 2,
		"CoreTheoremProducer::orDistributivityRule: "
		"input must be an AND of binary ORs: \n" + e.toString());
  }

  const Expr& A = e[0][0];

  if(CHECK_PROOFS) {
    for(Expr::iterator i=e.begin(),iend=e.end();i!=iend;++i) {
      const Expr& ei = *i;
      CHECK_SOUND(ei.isOr() && ei.arity() == 2,
		"CoreTheoremProducer::andDistributivityRule: "
		"input must be an AND of binary ORs: \n" + e.toString());
      CHECK_SOUND(A == ei[0],
		  "CoreTheoremProducer::andDistributivityRule: "
		  "input must have a common factor: \n" + e.toString());
    }
  }
  vector<Expr> output;
  for(Expr::iterator i=e.begin(),iend=e.end();i!=iend;++i) {
    output.push_back((*i)[1]);
  }
  Expr out = A.orExpr(andExpr(output));

  Proof pf;
  if(withProof())
    pf = newPf("and_distribuitivity_rule", e);
  
  return newRWTheorem(e, out, Assumptions::emptyAssump(), pf);
} 

// ==> IMPLIES(e1,e2) IFF OR(!e1, e2)
Theorem
CoreTheoremProducer::rewriteImplies(const Expr& e) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isImpl(), "rewriteImplies precondition violated");
  if(withProof()) {
    pf = newPf("rewrite_implies", e[0], e[1]);
  }
  return newRWTheorem(e, !e[0] || e[1], Assumptions::emptyAssump(), pf);
}

// ==> DISTINCT(e1,...,en) IFF AND 1 <= i < j <= n (e[i] /= e[j])
Theorem
CoreTheoremProducer::rewriteDistinct(const Expr& e) {
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == DISTINCT, "rewriteDistinct precondition violated");
    CHECK_SOUND(e.arity() > 0, "rewriteDistinct precondition violated");
  }
  Expr res;
  if (e.arity() == 1) {
    res = e.getEM()->trueExpr();
  }
  else if (e.arity() == 2) {
    res = !(e[0].eqExpr(e[1]));
  }
  else {
    vector<Expr> tmp;
    for (int i = 0; i < e.arity(); ++i) {
      for (int j = i+1; j < e.arity(); ++j) {
        tmp.push_back(!(e[i].eqExpr(e[j])));
      }
    }
    res = Expr(AND, tmp);
  }
  if(withProof()) {
    pf = newPf("rewrite_distinct", e , res);
  }

  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}

// ==> NOT(e) == ITE(e, FALSE, TRUE)
Theorem
CoreTheoremProducer::NotToIte(const Expr& not_e){
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(not_e.isNot() && not_e[0].getType().isBool(),
		"NotToIte precondition violated");
  if(withProof())
    pf = newPf("NotToIte", not_e[0]);
  if(not_e[0].isTrue())
    return d_core->getCommonRules()->rewriteNotTrue(not_e);
  else if(not_e[0].isFalse())
    return d_core->getCommonRules()->rewriteNotFalse(not_e);
  Expr ite(not_e[0].iteExpr(d_em->falseExpr(), d_em->trueExpr()));
  return newRWTheorem(not_e, ite, Assumptions::emptyAssump(), pf);  
}

// ==> Or(e) == ITE(e[1], TRUE, e[0])
Theorem
CoreTheoremProducer::OrToIte(const Expr& e){
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isOr(),
		"OrToIte: precondition violated: " + e.toString());
  Proof pf;
  if(withProof()) {
    pf = newPf("OrToIte", e);
  }
  const vector<Expr>& kids = e.getKids();
  unsigned k(kids.size());
  if(k==0)
    return newRWTheorem(e, d_em->falseExpr(), Assumptions::emptyAssump(), pf);
  if(k==1)
    return newRWTheorem(e, e[0], Assumptions::emptyAssump(), pf);
  Expr ite(kids[k-1]);
  if(CHECK_PROOFS)
    CHECK_SOUND(!ite.getType().isNull(),
		"OrToIte: kid " + int2string(k-1) + " has no type: "
		+ (ite).toString());
  for (; k > 1; k--) {
    if (kids[k-2].isTrue()) {
      ite = d_em->trueExpr();
      break;
    }
    else if(kids[k-2].isFalse()) continue;
    else{
      if(CHECK_PROOFS)
	CHECK_SOUND(!kids[k-2].getType().isNull(),
		  "OrToIte: kid " + int2string(k-2) + " has no type: "
		  + (kids[k-2]).toString());
      ite = ite.iteExpr(d_em->trueExpr(), kids[k-2]);
    }
  }
  return newRWTheorem(e, ite, Assumptions::emptyAssump(), pf);
}

// ==> And(e) == ITE(e[1], e[0], FALSE)
Theorem
CoreTheoremProducer::AndToIte(const Expr& e){
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isAnd(),
		"AndToIte: precondition violated: " + e.toString());
  Proof pf;
  if(withProof()) {
    pf = newPf("AndToIte", e);
  }
  const vector<Expr>& kids = e.getKids();
  unsigned k(kids.size());
  if(k==0)
    return newRWTheorem(e, d_em->trueExpr(), Assumptions::emptyAssump(), pf);
  if(k==1)
    return newRWTheorem(e, e[0], Assumptions::emptyAssump(), pf);
  Expr ite(kids[k-1]);
  if(CHECK_PROOFS)
    CHECK_SOUND(!ite.getType().isNull(),
		"AndToIte: kid " + int2string(k-1) + " has no type: "
		+ (ite).toString());
  for (; k > 1; k--) {
    if (kids[k-2].isFalse()) {
      ite = d_em->falseExpr();
      break;
    }
    else if(kids[k-2].isTrue()) {
      continue;
    }
    else{
      if(CHECK_PROOFS)
	CHECK_SOUND(!kids[k-2].getType().isNull(),
		    "AndToIte: kid " + int2string(k-2) + " has no type: "
		    + (kids[k-2]).toString());
      ite = ite.iteExpr(kids[k-2], d_em->falseExpr());
    }
  }
  return newRWTheorem(e, ite, Assumptions::emptyAssump(), pf);
}

// ==> IFF(a,b) == ITE(a, b, !b)
Theorem
CoreTheoremProducer::IffToIte(const Expr& e){
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isIff() && e[0].getType().isBool() && e[1].getType().isBool(),
		"IffToIte: precondition violated: " + e.toString());
  Proof pf;
  if(e[0] == e[1]) return d_core->getCommonRules()->reflexivityRule(e);
  Expr ite(e[0].iteExpr(e[1], e[1].iteExpr(d_em->falseExpr(),
					   d_em->trueExpr())));
  if(withProof()) {
    pf = newPf("iff_to_ite", e);
  }
  return newRWTheorem(e, ite, Assumptions::emptyAssump(), pf); 
}

// ==> IMPLIES(a,b) == ITE(a, b, TRUE)
Theorem
CoreTheoremProducer::ImpToIte(const Expr& e){
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isImpl() && e[0].getType().isBool() && e[1].getType().isBool(),
		"ImpToIte: precondition violated: " + e.toString());
  Proof pf;
  if(e[0] == e[1]) return d_core->getCommonRules()->reflexivityRule(e);
  Expr ite(e[0].iteExpr(e[1], d_em->trueExpr()));
  if(withProof()) {
    pf = newPf("imp_to_ite", e);
  }
  return newRWTheorem(e, ite, Assumptions::emptyAssump(), pf); 
}


// ==> ITE(e, FALSE, TRUE) IFF NOT(e)
Theorem
CoreTheoremProducer::rewriteIteToNot(const Expr& e)
{
  if (CHECK_PROOFS)
    CHECK_SOUND(e.isITE() && e[1].isFalse() && e[2].isTrue(),
		"rewriteIteToNot: " + e.toString());
  Proof pf;
  if (withProof()) pf = newPf("rewrite_ite_to_not", e);
  return newRWTheorem(e, e[0].negate(), Assumptions::emptyAssump(), pf);
}

// ==> ITE(a, TRUE, b) IFF OR(a, b)
Theorem
CoreTheoremProducer::rewriteIteToOr(const Expr& e)
{
  if (CHECK_PROOFS)
    CHECK_SOUND(e.isITE() && e[1].isTrue(),
		"rewriteIteToOr: " + e.toString());
  Proof pf;
  if (withProof()) pf = newPf("rewrite_ite_to_or", e);
  return newRWTheorem(e, e[0] || e[2], Assumptions::emptyAssump(), pf);
}

// ==> ITE(a, b, FALSE) IFF AND(a, b)
Theorem
CoreTheoremProducer::rewriteIteToAnd(const Expr& e)
{
  if (CHECK_PROOFS)
    CHECK_SOUND(e.isITE() && e[2].isFalse(),
		"rewriteIteToAnd: " + e.toString());
  Proof pf;
  if (withProof()) pf = newPf("rewrite_ite_to_and", e);
  return newRWTheorem(e, e[0] && e[1], Assumptions::emptyAssump(), pf);
}

// ==> ITE(a, b, !b) IFF IFF(a, b)
Theorem
CoreTheoremProducer::rewriteIteToIff(const Expr& e)
{
  if (CHECK_PROOFS)
    CHECK_SOUND(e.isITE() && e[1] == e[2].negate(),
		"rewriteIteToIff: " + e.toString());
  Proof pf;
  if (withProof()) pf = newPf("rewrite_ite_to_iff", e);
  return newRWTheorem(e, e[0].iffExpr(e[1]), Assumptions::emptyAssump(), pf);
}

// ==> ITE(a, b, TRUE) IFF IMPLIES(a, b)
Theorem
CoreTheoremProducer::rewriteIteToImp(const Expr& e)
{
  if (CHECK_PROOFS)
    CHECK_SOUND(e.isITE() && e[2].isTrue(),
		"rewriteIteToImp: " + e.toString());
  Proof pf;
  if (withProof()) pf = newPf("rewrite_ite_to_imp", e);
  return newRWTheorem(e, e[0].impExpr(e[1]), Assumptions::emptyAssump(), pf);
}


// ==> ITE(a, b(a), c(a)) IFF ITE(a, b(TRUE), c(FALSE))
// ==> ITE(x = y, b, c) IFF ITE(x = y b[x/y], c[x = y/FALSE])
Theorem CoreTheoremProducer::rewriteIteCond(const Expr& e)
{
  if (CHECK_PROOFS)
    CHECK_SOUND(e.isITE() && e.arity()==3, "rewriteIteCond: " + e.toString());

  vector<Expr> oldTerms, newTerms;
// //   if (e[0].isEq()) {
// //     oldTerms.push_back(e[0][0]);
// //     newTerms.push_back(e[0][1]);
// //   }
// //   else {
  oldTerms.push_back(e[0]);
  newTerms.push_back(d_em->trueExpr());
//   }
  
  Expr e1(e[1].substExpr(oldTerms, newTerms));
  oldTerms[0] = e[0];
  newTerms[0] = d_em->falseExpr();
  Expr e2(e[2].substExpr(oldTerms, newTerms));

  Proof pf;
  if (withProof()) pf = newPf("rewrite_ite_cond", e);
  return newRWTheorem(e, e[0].iteExpr(e1, e2), Assumptions::emptyAssump(), pf);
}


Theorem
CoreTheoremProducer::iffOrDistrib(const Expr& iff) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(iff.isIff() && iff.arity()==2, "iffOrDistrib("
		+iff.toString()+")");
    CHECK_SOUND(iff[0].isOr() && iff[0].arity()==2, "iffOrDistrib("
		+iff.toString()+")");
    CHECK_SOUND(iff[1].isOr() && iff[1].arity()==2, "iffOrDistrib("
		+iff.toString()+")");
    CHECK_SOUND(iff[0][0]==iff[1][0], "iffOrDistrib("
		+iff.toString()+")");
  }
  const Expr& a = iff[0][0];
  const Expr& b = iff[0][1];
  const Expr& c = iff[1][1];
  Proof pf;
  if(withProof())
    pf = newPf("iff_or_distrib", iff);
  return newRWTheorem(iff, (a || (b.iffExpr(c))), Assumptions::emptyAssump(), pf);
}


Theorem
CoreTheoremProducer::iffAndDistrib(const Expr& iff) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(iff.isIff() && iff.arity()==2, "iffAndDistrib("
		+iff.toString()+")");
    CHECK_SOUND(iff[0].isAnd() && iff[0].arity()==2, "iffAndDistrib("
		+iff.toString()+")");
    CHECK_SOUND(iff[1].isAnd() && iff[1].arity()==2, "iffAndDistrib("
		+iff.toString()+")");
    CHECK_SOUND(iff[0][0]==iff[1][0], "iffOrDistrib("
		+iff.toString()+")");
  }
  const Expr& a = iff[0][0];
  const Expr& b = iff[0][1];
  const Expr& c = iff[1][1];
  Proof pf;
  if(withProof())
    pf = newPf("iff_and_distrib", iff);
  return newRWTheorem(iff, (!a || (b.iffExpr(c))), Assumptions::emptyAssump(), pf);
}


// |- op(ITE(cond,a,b)) =/<=> ITE(cond,op(a),op(b))
Theorem
CoreTheoremProducer::ifLiftUnaryRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.arity()==1 && e[0].isITE(),
		"CoreTheoremProducer::ifLiftUnaryRule("
		"e = " + e.toString() + ")");
  }
  Op op(e.getOp());
  const Expr& ite = e[0];
  const Expr& cond = ite[0];
  const Expr& t1 = ite[1];
  const Expr& t2 = ite[2];

  if(CHECK_PROOFS) {
    CHECK_SOUND(cond.getType().isBool(),
		"CoreTheoremProducer::ifLiftUnaryRule("
		"e = " + e.toString()+")");      
  }    

  Expr e1 =  Expr(op, t1);
  Expr e2 =  Expr(op, t2);

  Expr resultITE = cond.iteExpr(e1, e2);

  Proof pf;
  if (withProof())
    pf = newPf("if_lift_unary_rule", e);
  return newRWTheorem(e, resultITE, Assumptions::emptyAssump(), pf);
}


// (a & b) <=> a & b[a/true]; takes the index of a and rewrites all
// the other conjuncts.
Theorem
CoreTheoremProducer::rewriteAndSubterms(const Expr& e, int idx) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isAnd() && 0 <= idx && idx < e.arity(),
		"rewriteAndSubterms("+e.toString()
		+", idx="+int2string(idx)
		+"):\n Expected an AND and a valid index of a child");
  }
  vector<Expr> kids;
  ExprHashMap<Expr> subst;
  subst.insert(e[idx], d_em->trueExpr());
  for(int i=0, iend=e.arity(); i<iend; ++i) {
    if(i==idx)
      kids.push_back(e[i]);
    else
      kids.push_back(e[i].substExpr(subst));
  }
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_and_subterms", e, d_em->newRatExpr(idx));
  return newRWTheorem(e, Expr(e.getOp(), kids), Assumptions::emptyAssump(), pf);
}


// (a | b) <=> a | b[a/false]; takes the index of a and rewrites all
// the other disjuncts.
Theorem
CoreTheoremProducer::rewriteOrSubterms(const Expr& e, int idx) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isOr() && 0 <= idx && idx < e.arity(),
		"rewriteOrSubterms("+e.toString()
		+", idx="+int2string(idx)
		+"):\n Expected an OR and a valid index of a child");
  }
  vector<Expr> kids;
  ExprHashMap<Expr> subst;
  subst.insert(e[idx], d_em->falseExpr());
  for(int i=0, iend=e.arity(); i<iend; ++i) {
    if(i==idx)
      kids.push_back(e[i]);
    else
      kids.push_back(e[i].substExpr(subst));
  }
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_or_subterms", e, d_em->newRatExpr(idx));
  return newRWTheorem(e, Expr(e.getOp(), kids), Assumptions::emptyAssump(), pf);
}


Theorem CoreTheoremProducer::dummyTheorem(const Expr& e)
{
  Proof pf;	
  return newTheorem(e, Assumptions::emptyAssump(), pf);
}
