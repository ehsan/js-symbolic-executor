/*****************************************************************************/
/*!
 *\file common_theorem_producer.cpp
 *\brief Implementation of common proof rules
 *
 * Author: Clark Barrett
 *
 * Created: Wed Jan 11 16:10:15 2006
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


#include "common_theorem_producer.h"


using namespace CVC3;
using namespace std;


// The trusted method of TheoremManager which creates this theorem producer
CommonProofRules* TheoremManager::createProofRules() {
  return new CommonTheoremProducer(this);
}


CommonTheoremProducer::CommonTheoremProducer(TheoremManager* tm)
  : TheoremProducer(tm),
    d_skolemized_thms(tm->getCM()->getCurrentContext()),
    d_skolemVars(tm->getCM()->getCurrentContext())
{}


////////////////////////////////////////////////////////////////////////
// TCC rules (3-valued logic)
////////////////////////////////////////////////////////////////////////

//  G1 |- phi   G2 |- D_phi
// -------------------------
//       G1,G2 |-_3 phi
Theorem3
CommonTheoremProducer::queryTCC(const Theorem& phi, const Theorem& D_phi) {
  Proof pf;
//   if(CHECK_PROOFS)
//     CHECK_SOUND(D_phi.getExpr() == d_core->getTCC(phi.getExpr()),
// 		"CoreTheoremProducer::queryTCC: "
// 		"bad TCC for a formula:\n\n  "
// 		+phi.getExpr().toString()
// 		+"\n\n  TCC must be the following:\n\n  "
// 		+d_core->getTCC(phi.getExpr()).toString()
// 		+"\n\nBut given this as a TCC:\n\n  "
// 		+D_phi.getExpr().toString());
  Assumptions a = phi.getAssumptionsRef();
  a.add(D_phi);
  if(withProof()) {
    vector<Expr> args;
    vector<Proof> pfs;
    args.push_back(phi.getExpr());
    args.push_back(D_phi.getExpr());
    pfs.push_back(phi.getProof());
    pfs.push_back(D_phi.getProof());
    pf = newPf("queryTCC", args, pfs);
    }
  return newTheorem3(phi.getExpr(), a, pf);
}


//  G0,a1,...,an |-_3 phi  G1 |- D_a1 ... Gn |- D_an
// -------------------------------------------------
//    G0,G1,...,Gn |-_3 (a1 & ... & an) -> phi
Theorem3
CommonTheoremProducer::implIntro3(const Theorem3& phi,
				  const std::vector<Expr>& assump,
				  const vector<Theorem>& tccs) {
  bool checkProofs(CHECK_PROOFS);
  // This rule only makes sense when runnnig with assumptions
  if(checkProofs) {
    CHECK_SOUND(withAssumptions(),
		"implIntro3: called while running without assumptions");
  }

  const Assumptions& phiAssump = phi.getAssumptionsRef();

  if(checkProofs) {
    CHECK_SOUND(assump.size() == tccs.size(),
		"implIntro3: number of assumptions ("
		+int2string(assump.size())+") and number of TCCs ("
		+int2string(tccs.size())
		+") does not match");
    for(size_t i=0; i<assump.size(); i++) {
      const Theorem& thm = phiAssump[assump[i]];
      CHECK_SOUND(!thm.isNull() && thm.isAssump(),
		  "implIntro3: this is not an assumption of phi:\n\n"
		  "  a["+int2string(i)+"] = "+assump[i].toString()
		  +"\n\n  phi = "+phi.getExpr().toString());
//       CHECK_SOUND(tccs[i].getExpr() == d_core->getTCC(assump[i]),
// 		  "implIntro3: Assumption does not match its TCC:\n\n"
// 		  "  a["+int2string(i)+"] = "+assump[i].toString()
// 		  +"  TCC(a["+int2string(i)+"]) = "
// 		  +d_core->getTCC(assump[i]).toString()
// 		  +"\n\n  tccs["+int2string(i)+"] = "
// 		  +tccs[i].getExpr().toString());
    }
  }

  // Proof compaction: trivial derivation
  if(assump.size() == 0) return phi;

  Assumptions a(phiAssump - assump);
  Assumptions b(tccs);
  a.add(b);
  Proof pf;
  if(withProof()) {
    vector<Proof> u; // Proof labels for assumptions
    for(vector<Expr>::const_iterator i=assump.begin(), iend=assump.end();
	i!=iend; ++i) {
      const Theorem& t = phiAssump[*i];
      u.push_back(t.getProof());
    }
    // Arguments to the proof rule:
    // impl_intro_3(phi, a1,...,an,tcc1,...tccn,pf_tcc1,...pf_tccn,
    //              [lambda(a1,...,an): pf_phi])
    vector<Expr> args;
    vector<Proof> pfs;
    args.push_back(phi.getExpr());
    args.insert(args.end(), assump.begin(), assump.end());
    for(vector<Theorem>::const_iterator i=tccs.begin(), iend=tccs.end();
	i!=iend; ++i) {
      args.push_back(i->getExpr());
      pfs.push_back(i->getProof());
    }
    // Lambda-abstraction of pf_phi
    pfs.push_back(newPf(u, assump, phi.getProof()));
    pf = newPf("impl_intro_3", args, pfs);
  }
  Expr conj(andExpr(assump));
  return newTheorem3(conj.impExpr(phi.getExpr()), a, pf);
}


Theorem CommonTheoremProducer::assumpRule(const Expr& e, int scope) {
  //  TRACE("assump", "assumpRule(", e, ")");
  Proof pf;
  if(withProof()) pf = newLabel(e);
  return newAssumption(e, pf, scope);
}


Theorem CommonTheoremProducer::reflexivityRule(const Expr& a) {
  return newReflTheorem(a);
}


// ==> (a == a) IFF TRUE
Theorem CommonTheoremProducer::rewriteReflexivity(const Expr& t) {
  if(CHECK_PROOFS)
    CHECK_SOUND((t.isEq() || t.isIff()) && t[0] == t[1],
		"rewriteReflexivity: wrong expression: "
		+ t.toString());
  Proof pf;
  if(withProof()) {
    if(t.isEq()) {
      DebugAssert(!t[0].getType().isNull(),
		  "rewriteReflexivity: t[0] has no type: "
		  + t[0].toString());
      pf = newPf("rewrite_eq_refl", t[0].getType().getExpr(), t[0]);
    } else
      pf = newPf("rewrite_iff_refl", t[0]);
  }
  return newRWTheorem(t, d_em->trueExpr(), Assumptions::emptyAssump(), pf);
}


Theorem CommonTheoremProducer::symmetryRule(const Theorem& a1_eq_a2) {
  if(CHECK_PROOFS)
    CHECK_SOUND(a1_eq_a2.isRewrite(),
		("CVC3::CommonTheoremProducer: "
		 "theorem is not an equality or iff:\n  "
		 + a1_eq_a2.getExpr().toString()).c_str());
  const Expr& a1 = a1_eq_a2.getLHS();
  const Expr& a2 = a1_eq_a2.getRHS();

  Proof pf;
  /////////////////////////////////////////////////////////////////////////
  //// Proof compaction
  /////////////////////////////////////////////////////////////////////////
  // If a1 == a2, use reflexivity
  if(a1 == a2) return reflexivityRule(a1);
  // Otherwise, do the work
  if(withProof()) {
    Type t = a1.getType();
    // Check the types
    IF_DEBUG(a1_eq_a2.getExpr().getType();)
    bool isEquality = !t.isBool();
    if(isEquality) {
      vector<Expr> args;
      args.push_back(t.getExpr());
      args.push_back(a1);
      args.push_back(a2);
      pf = newPf("eq_symm", args, a1_eq_a2.getProof());
    } else
      pf = newPf("iff_symm", a1, a2, a1_eq_a2.getProof());
  }
  return newRWTheorem(a2, a1, Assumptions(a1_eq_a2), pf);
}


Theorem CommonTheoremProducer::rewriteUsingSymmetry(const Expr& a1_eq_a2) {
  bool isIff = a1_eq_a2.isIff();
  if(CHECK_PROOFS)
    CHECK_SOUND(a1_eq_a2.isEq() || isIff, "rewriteUsingSymmetry precondition violated");
  const Expr& a1 = a1_eq_a2[0];
  const Expr& a2 = a1_eq_a2[1];
  // Proof compaction: if a1 == a2, use reflexivity
  if(a1 == a2) return reflexivityRule(a1_eq_a2);
  // Otherwise, do the work
  Proof pf;
  if(withProof()) {
    Type t = a1.getType();
    DebugAssert(!t.isNull(),
		"rewriteUsingSymmetry: a1 has no type: " + a1.toString());
    if(isIff)
      pf = newPf("rewrite_iff_symm", a1, a2);
    else {
      pf = newPf("rewrite_eq_symm", t.getExpr(), a1, a2);
    }
  }
  return newRWTheorem(a1_eq_a2, isIff ? a2.iffExpr(a1) : a2.eqExpr(a1), Assumptions::emptyAssump(), pf);
}


Theorem CommonTheoremProducer::transitivityRule(const Theorem& a1_eq_a2,
                                                const Theorem& a2_eq_a3) {
  DebugAssert(!a1_eq_a2.isNull(), "transitivityRule()");
  DebugAssert(!a2_eq_a3.isNull(), "transitivityRule()");
  if(CHECK_PROOFS) {
    CHECK_SOUND(a1_eq_a2.isRewrite() && a2_eq_a3.isRewrite(),  
		"CVC3::CommonTheoremProducer::transitivityRule:\n  "
		"Wrong premises: first = "
		+ a1_eq_a2.getExpr().toString() + ", second = "
		+ a2_eq_a3.getExpr().toString());
    CHECK_SOUND(a1_eq_a2.getRHS() == a2_eq_a3.getLHS(),
		"CVC3::CommonTheoremProducer::transitivityRule:\n  "
		"Wrong premises: first = "
		+ a1_eq_a2.getExpr().toString() + ", second = "
		+ a2_eq_a3.getExpr().toString());
  }
  const Expr& a1 = a1_eq_a2.getLHS();
  const Expr& a2 = a1_eq_a2.getRHS();
  const Expr& a3 = a2_eq_a3.getRHS();

  /////////////////////////////////////////////////////////////////////////
  //// Proof compaction
  /////////////////////////////////////////////////////////////////////////
  // if a1 == a3, use reflexivity (and lose all assumptions)
  if(a1 == a3) return reflexivityRule(a1);
  // if a1 == a2, or if a2 == a3, use only the non-trivial part
  if(a1 == a2) return a2_eq_a3;
  if(a2 == a3) return a1_eq_a2;

  ////////////////////////////////////////////////////////////////////////
  //// No shortcuts.  Do the work.
  ////////////////////////////////////////////////////////////////////////

  Proof pf;
  Assumptions a(a1_eq_a2, a2_eq_a3);
  // Build the proof
  if(withProof()) {
    Type t = a1.getType();
    bool isEquality = (!t.isBool());
    string name((isEquality)? "eq_trans" : "iff_trans");
    vector<Expr> args;
    vector<Proof> pfs;
    DebugAssert(!t.isNull(), "transitivityRule: "
		"Type is not computed for a1: " + a1.toString());
    // Type argument is needed only for equality
    if(isEquality) args.push_back(t.getExpr());
    args.push_back(a1);
    args.push_back(a2);
    args.push_back(a3);
    pfs.push_back(a1_eq_a2.getProof());
    pfs.push_back(a2_eq_a3.getProof());
    pf = newPf(name, args, pfs);
  }
  return newRWTheorem(a1, a3, a, pf);
}


Theorem CommonTheoremProducer::substitutivityRule(const Expr& e,
                                                  const Theorem& thm) {
  IF_DEBUG
    (static DebugTimer
       accum0(debugger.timer("substitutivityRule0 time"));
     static DebugTimer tmpTimer(debugger.newTimer());
     static DebugCounter count(debugger.counter("substitutivityRule0 calls"));
     debugger.setCurrentTime(tmpTimer);
     count++;)

  // Check that t is c == d or c IFF d
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.arity() == 1 && e[0] == thm.getLHS(),
                "Unexpected use of substitutivityRule0");
    CHECK_SOUND(thm.isRewrite(),
                "CVC3::CommonTheoremProducer::substitutivityRule0:\n  "
                "premis is not an equality or IFF: "
                + thm.getExpr().toString()
                + "\n  expr = " + e.toString());
  }
  Expr e2(e.getOp(), thm.getRHS());
  Proof pf;
  if(withProof())
    pf = newPf("basic_subst_op0",e, e2,thm.getProof());
  Theorem res = newRWTheorem(e, e2, Assumptions(thm), pf);
  if (!res.isRefl()) res.setSubst();
  return res;
}


Theorem CommonTheoremProducer::substitutivityRule(const Expr& e,
                                                  const Theorem& thm1,
                                                  const Theorem& thm2) {
  IF_DEBUG
    (static DebugTimer
       accum0(debugger.timer("substitutivityRule1 time"));
     static DebugTimer tmpTimer(debugger.newTimer());
     static DebugCounter count(debugger.counter("substitutivityRule1 calls"));
     debugger.setCurrentTime(tmpTimer);
     count++;)

  // Check that t is c == d or c IFF d
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.arity() == 2 && e[0] == thm1.getLHS() &&
                e[1] == thm2.getLHS(),
                "Unexpected use of substitutivityRule1");
    CHECK_SOUND(thm1.isRewrite(),
                "CVC3::CommonTheoremProducer::substitutivityRule1:\n  "
                "premis is not an equality or IFF: "
                + thm1.getExpr().toString()
                + "\n  expr = " + e.toString());
    CHECK_SOUND(thm2.isRewrite(),
                "CVC3::CommonTheoremProducer::substitutivityRule1:\n  "
                "premis is not an equality or IFF: "
                + thm2.getExpr().toString()
                + "\n  expr = " + e.toString());
  }
  Expr e2(e.getOp(), thm1.getRHS(), thm2.getRHS());
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(thm1.getProof());
    pfs.push_back(thm2.getProof());
    pf = newPf("basic_subst_op1", e, e2, pfs);
  }
  Theorem res = newRWTheorem(e, e2, Assumptions(thm1, thm2), pf);
  if (!res.isRefl()) res.setSubst();
  return res;
}


Theorem CommonTheoremProducer::substitutivityRule(const Op& op,
                                                  const vector<Theorem>& thms) {
  IF_DEBUG
    (static DebugTimer
       accum0(debugger.timer("substitutivityRule time"));
     static DebugTimer tmpTimer(debugger.newTimer());
     static DebugCounter count(debugger.counter("substitutivityRule calls"));
     debugger.setCurrentTime(tmpTimer);
     count++;)
  // Check for trivial case: no theorems, return (op == op)
  unsigned size(thms.size());
  if(size == 0)
    return reflexivityRule(d_tm->getEM()->newLeafExpr(op));
  // Check that theorems are of the form c_i == d_i and collect
  // vectors of c_i's and d_i's and the vector of proofs
  vector<Expr> c, d;
  vector<Proof> pfs;
  // Reserve memory for argument vectors.  Do not reserve memory for
  // pfs, they are rarely used and slow anyway.
  c.reserve(size); d.reserve(size);
  for(vector<Theorem>::const_iterator i = thms.begin(), iend = thms.end();
      i != iend; ++i) {
    // Check that t is c == d or c IFF d
    if(CHECK_PROOFS)
      CHECK_SOUND(i->isRewrite(),
		  "CVC3::CommonTheoremProducer::substitutivityRule:\n  "
		  "premis is not an equality or IFF: "
		  + i->getExpr().toString()
		  + "\n  op = " + op.toString());
    // Collect the pieces
    c.push_back(i->getLHS());
    d.push_back(i->getRHS());
    if(withProof()) pfs.push_back(i->getProof());
  }
  Expr e1(op, c), e2(op, d);
  // Proof compaction: if e1 == e2, use reflexivity
  if(e1 == e2) return reflexivityRule(e1);
  // Otherwise, do the work
  Assumptions a(thms);
  Proof pf;
  if(withProof())
    // FIXME: this rule is not directly expressible in flea
    pf = newPf("basic_subst_op",e1,e2,pfs);
  Theorem res = newRWTheorem(e1, e2, a, pf);
  IF_DEBUG(debugger.setElapsed(tmpTimer);
	   accum0 += tmpTimer;)
  res.setSubst();
  return res;
}


Theorem CommonTheoremProducer::substitutivityRule(const Expr& e,
                                                  const vector<unsigned>& changed,
                                                  const vector<Theorem>& thms) {
  IF_DEBUG
    (static DebugTimer
       accum0(debugger.timer("substitutivityRule2 time"));
     static DebugTimer tmpTimer(debugger.newTimer());
     static DebugCounter count(debugger.counter("substitutivityRule2 calls"));
     debugger.setCurrentTime(tmpTimer);
     count++;)
  DebugAssert(changed.size() > 0, "substitutivityRule2 should not be called");
  DebugAssert(changed.size() == thms.size(), "substitutivityRule2: wrong args");

  // Check that theorems are of the form c_i == d_i and collect
  // vectors of c_i's and d_i's and the vector of proofs
  unsigned size = e.arity();
  if (size == 1) return substitutivityRule(e, thms.back());
  unsigned csize = changed.size();
  if (size == 2) {
    if (csize == 2) return substitutivityRule(e, thms[0], thms[1]);
    if (changed[0] == 0) {
      return substitutivityRule(e, thms[0], reflexivityRule(e[1]));
    }
    else {
      return substitutivityRule(e, reflexivityRule(e[0]), thms[0]);
    }
  }
  DebugAssert(size >= csize, "Bad call to substitutivityRule2");

  vector<Expr> c;
  bool checkProofs(CHECK_PROOFS);
  for(unsigned j = 0, k = 0; k < size; ++k) {
    if (j == csize || changed[j] != k) {
      c.push_back(e[k]);
      continue;
    }
    // Check that t is c == d or c IFF d
    if(checkProofs)
      CHECK_SOUND(thms[j].isRewrite() && thms[j].getLHS() == e[k],
		  "CVC3::CommonTheoremProducer::substitutivityRule:\n  "
		  "premis is not an equality or IFF: "
		  + thms[j].getExpr().toString()
		  + "\n  e = " + e.toString());
    // Collect the pieces
    c.push_back(thms[j].getRHS());
    ++j;
  }
  Expr e2(e.getOp(), c);
  IF_DEBUG(if(e == e2) {
    ostream& os = debugger.getOS();
    os << "substitutivityRule2: e = " << e << "\n e2 = " << e2
       << "\n changed kids: [\n";
    for(unsigned j=0; j<changed.size(); j++)
      os << "  (" << changed[j] << ") " << thms[j] << "\n";
    os << "]\n";
  })
  DebugAssert(e != e2,
	      "substitutivityRule2 should not be called in this case:\n"
	      "e = "+e.toString());

  Proof pf;
  Assumptions a(thms);
  if(withProof()) {
    vector<Proof> pfs;
    for(vector<Theorem>::const_iterator i = thms.begin(), iend = thms.end();
        i != iend; ++i) {
      // Check that t is c == d or c IFF d
      if(CHECK_PROOFS)
        CHECK_SOUND(i->isRewrite(),
                    "CVC3::CommonTheoremProducer::substitutivityRule:\n  "
                    "premis is not an equality or IFF: "
                    + i->getExpr().toString());
                    // + "\n  op = " + ((Op) e.getOp).toString());
      pfs.push_back(i->getProof());
    }
    pf = newPf("optimized_subst_op",e,e2,pfs);
  }
  Theorem res = newRWTheorem(e, e2, a, pf);
  IF_DEBUG(debugger.setElapsed(tmpTimer);
	   accum0 += tmpTimer;)
  if (!res.isRefl()) res.setSubst();
  return res;
}


Theorem CommonTheoremProducer::substitutivityRule(const Expr& e,
                                                  const int changed,
                                                  const Theorem& thm)
{
  // Get the arity of the expression
  int size = e.arity();

  // The changed must be within the arity
  DebugAssert(size >= changed, "Bad call to substitutivityRule");

  // Check that t is c == d or c IFF d
  if(CHECK_PROOFS)
    CHECK_SOUND(thm.isRewrite() && thm.getLHS() == e[changed], "CVC3::CommonTheoremProducer::substitutivityRule:\n  "
                "premise is not an equality or IFF: " + thm.getExpr().toString() + "\n" +
                "e = " + e.toString());

  // Collect the new sub-expressions
  vector<Expr> c;
  for(int k = 0; k < size; ++ k)    	
    if (k != changed) c.push_back(e[k]);
    else c.push_back(thm.getRHS());

  // Construct the new expression
  Expr e2(e.getOp(), c);
	
  // Check if they are the same 
  IF_DEBUG(if(e == e2) {
    ostream& os = debugger.getOS();
    os << "substitutivityRule: e = " << e << "\n e2 = " << e2 << endl;
  })

  // The new expressions must not be equal
  DebugAssert(e != e2, "substitutivityRule should not be called in this case:\ne = "+e.toString());

  // Construct the proof object
  Proof pf;
  Assumptions a(thm);
  if(withProof()) {
    // Check that t is c == d or c IFF d
    if(CHECK_PROOFS)
      CHECK_SOUND(thm.isRewrite(), "CVC3::CommonTheoremProducer::substitutivityRule:\npremise is not an equality or IFF: " + thm.getExpr().toString());                 
    pf = newPf("optimized_subst_op2",e,e2,thm.getProof());
  }

  // Return the resulting theorem 
  Theorem res = newRWTheorem(e, e2, a, pf);;
  res.setSubst();
  return res;
}


// |- e,  |- !e ==> |- FALSE
Theorem CommonTheoremProducer::contradictionRule(const Theorem& e,
                                                 const Theorem& not_e) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(!e.getExpr() == not_e.getExpr(),
		"CommonTheoremProducer::contraditionRule: "
		"theorems don't match:\n e = "+e.toString()
		+"\n not_e = "+not_e.toString());
  Assumptions a(e, not_e);
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(e.getProof());
    pfs.push_back(not_e.getProof());
    pf = newPf("contradition", e.getExpr(), pfs);
  }
  return newTheorem(d_em->falseExpr(), a, pf);
}


Theorem CommonTheoremProducer::excludedMiddle(const Expr& e)
{
  Proof pf;
  if (withProof()) {
    pf = newPf("excludedMiddle", e);
  }
  return newTheorem(e.orExpr(!e), Assumptions::emptyAssump(), pf);
}


// e ==> e IFF TRUE
Theorem CommonTheoremProducer::iffTrue(const Theorem& e)
{
  Proof pf;
  if(withProof()) {
    pf = newPf("iff_true", e.getExpr(), e.getProof());
  }
  return newRWTheorem(e.getExpr(), d_em->trueExpr(), Assumptions(e), pf);
}


// e ==> !e IFF FALSE
Theorem CommonTheoremProducer::iffNotFalse(const Theorem& e) {
  Proof pf;
  if(withProof()) {
    pf = newPf("iff_not_false", e.getExpr(), e.getProof());
  }
  return newRWTheorem(!e.getExpr(), d_em->falseExpr(), Assumptions(e), pf);
}


// e IFF TRUE ==> e
Theorem CommonTheoremProducer::iffTrueElim(const Theorem& e) {
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isRewrite() && e.getRHS().isTrue(),
		"CommonTheoremProducer::iffTrueElim: "
		"theorem is not e<=>TRUE: "+ e.toString());
  Proof pf;
  if(withProof()) {
    pf = newPf("iff_true_elim", e.getLHS(), e.getProof());
  }
  return newTheorem(e.getLHS(), Assumptions(e), pf);
}


// e IFF FALSE ==> !e
Theorem CommonTheoremProducer::iffFalseElim(const Theorem& e) {
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isRewrite() && e.getRHS().isFalse(),
		"CommonTheoremProducer::iffFalseElim: "
		"theorem is not e<=>FALSE: "+ e.toString());
  const Expr& lhs = e.getLHS();
  Proof pf;
  if(withProof()) {
    pf = newPf("iff_false_elim", lhs, e.getProof());
  }
  return newTheorem(!lhs, Assumptions(e), pf);
}


// e1 <=> e2  ==>  ~e1 <=> ~e2
Theorem CommonTheoremProducer::iffContrapositive(const Theorem& e) {
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isRewrite() && e.getRHS().getType().isBool(),
		"CommonTheoremProducer::iffContrapositive: "
		"theorem is not e1<=>e2: "+ e.toString());
  Proof pf;
  if(withProof()) {
    pf = newPf("iff_contrapositive", e.getExpr(), e.getProof());
  }
  return newRWTheorem(e.getLHS().negate(),e.getRHS().negate(), Assumptions(e), pf);
}


// !!e ==> e
Theorem CommonTheoremProducer::notNotElim(const Theorem& not_not_e) {
  if(CHECK_PROOFS)
    CHECK_SOUND(not_not_e.getExpr().isNot() && not_not_e.getExpr()[0].isNot(),
		"CommonTheoremProducer::notNotElim: bad theorem: !!e = "
		+ not_not_e.toString());
  Proof pf;
  if(withProof())
    pf = newPf("not_not_elim", not_not_e.getExpr(), not_not_e.getProof());
  return newTheorem(not_not_e.getExpr()[0][0], Assumptions(not_not_e), pf);
}


Theorem CommonTheoremProducer::iffMP(const Theorem& e1, const Theorem& e1_iff_e2)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e1_iff_e2.isRewrite(),
		"iffMP: not IFF: "+e1_iff_e2.toString());
    CHECK_SOUND(e1.getExpr() == (e1_iff_e2.getLHS()),
		"iffMP: theorems don't match:\n  e1 = " + e1.toString()
		+ ", e1_iff_e2 = " + e1_iff_e2.toString());
  }
  const Expr& e2(e1_iff_e2.getRHS());
  // Avoid e1.getExpr(), it may cause unneeded Expr creation
  if (e1_iff_e2.getLHS() == e2) return e1;
  Proof pf;
  Assumptions a(e1, e1_iff_e2);
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(e1.getProof());
    pfs.push_back(e1_iff_e2.getProof());
    pf = newPf("iff_mp", e1.getExpr(), e2, pfs);
  }
  return newTheorem(e2, a, pf);
}


// e1 AND (e1 IMPLIES e2) ==> e2
Theorem CommonTheoremProducer::implMP(const Theorem& e1,
                                      const Theorem& e1_impl_e2) {
  const Expr& impl = e1_impl_e2.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(impl.isImpl() && impl.arity()==2,
		"implMP: not IMPLIES: "+impl.toString());
    CHECK_SOUND(e1.getExpr() == impl[0],
		"implMP: theorems don't match:\n  e1 = " + e1.toString()
		+ ", e1_impl_e2 = " + impl.toString());
  }
  const Expr& e2 = impl[1];
  // Avoid e1.getExpr(), it may cause unneeded Expr creation
  //  if (impl[0] == e2) return e1;  // this line commented by yeting because of proof translation
  Proof pf;
  Assumptions a(e1, e1_impl_e2);
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(e1.getProof());
    pfs.push_back(e1_impl_e2.getProof());
    pf = newPf("impl_mp", e1.getExpr(), e2, pfs);
  }
  return newTheorem(e2, a, pf);
}


// AND(e_0,...e_{n-1}) ==> e_i
Theorem CommonTheoremProducer::andElim(const Theorem& e, int i) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getExpr().isAnd(), "andElim: not an AND: " + e.toString());
    CHECK_SOUND(i < e.getExpr().arity(), "andElim: i = " + int2string(i)
		+ " >= arity = " + int2string(e.getExpr().arity())
		+ " in " + e.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("andE", d_em->newRatExpr(i), e.getExpr(), e.getProof());
  return newTheorem(e.getExpr()[i], Assumptions(e), pf);
}


//! e1, e2 ==> AND(e1, e2)
Theorem CommonTheoremProducer::andIntro(const Theorem& e1, const Theorem& e2) {
  vector<Theorem> thms;
  thms.push_back(e1);
  thms.push_back(e2);
  return andIntro(thms);
}


Theorem CommonTheoremProducer::andIntro(const vector<Theorem>& es) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(es.size() > 1,
		"andIntro(vector<Theorem>): vector must have more than 1 element");
  Assumptions a(es);
  /*
  if(withProof()) {
    vector<Proof> pfs;
    for(vector<Theorem>::const_iterator i=es.begin(), iend=es.end();
	i!=iend; ++i)
      pfs.push_back(i->getProof());
    //    pf = newPf("andI", andExpr(kids), pfs);
  }
  */
  vector<Expr> kids;
  for(vector<Theorem>::const_iterator i=es.begin(), iend=es.end();
      i!=iend; ++i)
    kids.push_back(i->getExpr());

  if(withProof()) {
    vector<Proof> pfs;
    for(vector<Theorem>::const_iterator i=es.begin(), iend=es.end();
	i!=iend; ++i)
      pfs.push_back(i->getProof());
    pf = newPf("andI", andExpr(kids), pfs);
  }
  return newTheorem(andExpr(kids), a, pf);
}


//  G,a1,...,an |- phi
// -------------------------------------------------
//  G |- (a1 & ... & an) -> phi
Theorem CommonTheoremProducer::implIntro(const Theorem& phi,
                                         const std::vector<Expr>& assump) {
  bool checkProofs(CHECK_PROOFS);
  // This rule only makes sense when runnnig with assumptions
  if(checkProofs) {
    CHECK_SOUND(withAssumptions(),
		"implIntro: called while running without assumptions");
  }

  const Assumptions& phiAssump = phi.getAssumptionsRef();

  if(checkProofs) {
    for(size_t i=0; i<assump.size(); i++) {
      const Theorem& thm = phiAssump[assump[i]];
      CHECK_SOUND(!thm.isNull() && thm.isAssump(),
		  "implIntro: this is not an assumption of phi:\n\n"
		  "  a["+int2string(i)+"] = "+assump[i].toString()
		  +"\n\n  phi = "+phi.getExpr().toString());
    }
  }

  // Proof compaction: trivial derivation
  if(assump.size() == 0) return phi;

  Assumptions a(phiAssump - assump);
  Proof pf;
  if(withProof()) {
    vector<Proof> u; // Proof labels for assumptions
    for(vector<Expr>::const_iterator i=assump.begin(), iend=assump.end();
	i!=iend; ++i) {
      const Theorem& t = phiAssump[*i];
      u.push_back(t.getProof());
    }
    // Arguments to the proof rule:
    // impl_intro_3(phi, a1,...,an,tcc1,...tccn,pf_tcc1,...pf_tccn,
    //              [lambda(a1,...,an): pf_phi])
    vector<Expr> args;
    vector<Proof> pfs;
    args.push_back(phi.getExpr());
    args.insert(args.end(), assump.begin(), assump.end());
    // Lambda-abstraction of pf_phi
    pfs.push_back(newPf(u, assump, phi.getProof()));
    pf = newPf("impl_intro", args, pfs);
  }
  Expr conj(andExpr(assump));
  return newTheorem(conj.impExpr(phi.getExpr()), a, pf);
}


// e1 => e2  ==>  ~e2 => ~e1
Theorem CommonTheoremProducer::implContrapositive(const Theorem& thm) {
  const Expr& impl = thm.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(impl.isImpl() && impl.arity()==2,
		"CommonTheoremProducer::implContrapositive: thm="
		+impl.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("impl_contrapositive", impl, thm.getProof());
  return newTheorem(impl[1].negate().impExpr(impl[0].negate()), Assumptions(thm), pf);
}


// ==> ITE(TRUE, e1, e2) == e1
Theorem
CommonTheoremProducer::rewriteIteTrue(const Expr& e) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isITE() && e[0].isTrue(),
		"rewriteIteTrue precondition violated");
  if(withProof()) {
    Type t = e[1].getType();
    DebugAssert(!t.isNull(), "rewriteIteTrue: e1 has no type: "
		+ e[1].toString());
    bool useIff = t.isBool();
    if(useIff)
      pf = newPf("rewrite_ite_true_iff", e[1], e[2]);
    else {
      pf = newPf("rewrite_ite_true", t.getExpr(), e[1], e[2]);
    }
  }
  return newRWTheorem(e, e[1], Assumptions::emptyAssump(), pf);
}


// ==> ITE(FALSE, e1, e2) == e2
Theorem
CommonTheoremProducer::rewriteIteFalse(const Expr& e) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isITE() && e[0].isFalse(),
		"rewriteIteFalse precondition violated");
  if(withProof()) {
    Type t = e[1].getType();
    DebugAssert(!t.isNull(), "rewriteIteFalse: e1 has no type: "
		+ e[1].toString());
    bool useIff = t.isBool();
    if(useIff)
      pf = newPf("rewrite_ite_false_iff", e[1], e[2]);
    else {
      pf = newPf("rewrite_ite_false", t.getExpr(), e[1], e[2]);
    }
  }
  return newRWTheorem(e, e[2], Assumptions::emptyAssump(), pf);
}


// ==> ITE(c, e, e) == e
Theorem
CommonTheoremProducer::rewriteIteSame(const Expr& e) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isITE() && e[1] == e[2],
		"rewriteIteSame precondition violated");
  if(withProof()) {
    Type t = e[1].getType();
    DebugAssert(!t.isNull(), "rewriteIteSame: e[1] has no type: "
		+ e[1].toString());
    bool useIff = t.isBool();
    if(useIff)
      pf = newPf("rewrite_ite_same_iff", e[0], e[1]);
    else {
      pf = newPf("rewrite_ite_same", t.getExpr(), e[0], e[1]);
    }
  }
  return newRWTheorem(e, e[1], Assumptions::emptyAssump(), pf);
}


// NOT e ==> e IFF FALSE
Theorem CommonTheoremProducer::notToIff(const Theorem& not_e)
{
  if(CHECK_PROOFS)
    CHECK_SOUND(not_e.getExpr().isNot(),
		"notToIff: not NOT: "+not_e.toString());

  // Make it an atomic rule (more efficient)
  Expr e(not_e.getExpr()[0]);
  Proof pf;
  if(withProof())
    pf=newPf("not_to_iff", e, not_e.getProof());
  return newRWTheorem(e, d_em->falseExpr(), Assumptions(not_e), pf);
}


// e1 XOR e2 ==> e1 IFF (NOT e2)
Theorem CommonTheoremProducer::xorToIff(const Expr& e)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isXor(), "xorToIff precondition violated");
    CHECK_SOUND(e.arity() >= 2, "Expected XOR of arity >= 2");
  }
  Expr res = e[e.arity()-1];
  for (int i = e.arity()-2; i >=0; --i) {
    res = (!e[i]).iffExpr(res);
  }
  Proof pf;
  if(withProof()) {
    pf = newPf("xorToIff");
  }
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


// ==> IFF(e1,e2) IFF <simplified expr>
Theorem CommonTheoremProducer::rewriteIff(const Expr& e) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isIff(), "rewriteIff precondition violated");
  if(withProof()) {
    pf = newPf("rewrite_iff", e[0], e[1]);
  }

  if(e[0] == e[1]) return rewriteReflexivity(e);

  switch(e[0].getKind()) {
  case TRUE_EXPR:
    return newRWTheorem(e, e[1], Assumptions::emptyAssump(), pf);
  case FALSE_EXPR:
    return newRWTheorem(e, !e[1], Assumptions::emptyAssump() ,pf);
  case NOT:
    if(e[0][0]==e[1]) 
      return newRWTheorem(e, d_em->falseExpr(), Assumptions::emptyAssump(), pf);
    break;
  default: break;
  }
  
  switch(e[1].getKind()) {
  case TRUE_EXPR:
    return newRWTheorem(e, e[0], Assumptions::emptyAssump(), pf);
  case FALSE_EXPR:
    return newRWTheorem(e, !e[0], Assumptions::emptyAssump(), pf);
  case NOT:
    if(e[0]==e[1][0]) 
      return newRWTheorem(e, d_em->falseExpr(), Assumptions::emptyAssump(), pf);
    break;
  default:
    break;
  }

  if(e[0] < e[1])
    return rewriteUsingSymmetry(e);
  else
    return reflexivityRule(e);
}


// ==> AND(e_1,...,e_n) IFF <simplified expr>
// 1) if e_i = FALSE then return FALSE
// 2) if e_i = TRUE, remove it from children
// 3) if e_i = AND(f_1,...,f_m) then AND(e_1,...,e_{i-1},f_1,...,f_m,e_{i+1},...,e_n)
// 4) if n=0 return TRUE
// 5) if n=1 return e_1
Theorem CommonTheoremProducer::rewriteAnd(const Expr& e) {
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isAnd(), "rewriteAnd: bad Expr: " + e.toString());
  Proof pf;
  ExprMap<bool> newKids;
  bool isFalse (false);
  for (Expr::iterator k=e.begin(), kend=e.end(); !isFalse && k != kend; ++k) {
    const Expr& ek = *k;
    if (ek.isFalse()) { isFalse=true; break; }
    if (ek.isAnd() && ek.arity() < 10) {
      for(Expr::iterator j=ek.begin(), jend=ek.end(); j!=jend; ++j) {
	if(newKids.count(j->negate()) > 0) { isFalse=true; break; }
	newKids[*j]=true;
      }
    } else if(!ek.isTrue()) {
      if(newKids.count(ek.negate()) > 0) { isFalse=true; break; }
      newKids[ek]=true;
    }
  }
  Expr res;
  if (isFalse) res = d_em->falseExpr();
  else if (newKids.size() == 0) res = d_em->trueExpr(); // All newKids were TRUE
  else if (newKids.size() == 1)
    res = newKids.begin()->first; // The only child
  else {
    vector<Expr> v;
    for(ExprMap<bool>::iterator i=newKids.begin(), iend=newKids.end();
        i!=iend; ++i)
      v.push_back(i->first);
    res = andExpr(v);
  }
  if(withProof()) {
    pf = newPf("rewrite_and", e,res);
  }
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


// ==> OR(e1,e2) IFF <simplified expr>
Theorem CommonTheoremProducer::rewriteOr(const Expr& e) {
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isOr(), "rewriteOr: bad Expr: " + e.toString());
  Proof pf;
  ExprMap<bool> newKids;
  bool isTrue (false);
  for (Expr::iterator k=e.begin(), kend=e.end(); !isTrue && k != kend; ++k) {
    const Expr& ek = *k;
    if (ek.isTrue()) { isTrue=true; break; }
    else if (ek.isOr() && ek.arity() < 10) {
      for(Expr::iterator j=ek.begin(), jend=ek.end(); j!=jend; ++j) {
	if(newKids.count(j->negate()) > 0) { isTrue=true; break; }
	newKids[*j]=true;
      }
    } else if(!ek.isFalse()) {
      if(newKids.count(ek.negate()) > 0) { isTrue=true; break; }
      newKids[ek]=true;
    }
  }
  Expr res;
  if (isTrue) res = d_em->trueExpr();
  else if (newKids.size() == 0) res = d_em->falseExpr(); // All kids were FALSE
  else if (newKids.size() == 1) res = newKids.begin()->first; // The only child
  else {
    vector<Expr> v;
    for(ExprMap<bool>::iterator i=newKids.begin(), iend=newKids.end();
        i!=iend; ++i)
      v.push_back(i->first);
    res = orExpr(v);
  }
  if(withProof()) {
    pf = newPf("rewrite_or", e, res);
  }
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


// ==> NOT TRUE IFF FALSE
Theorem CommonTheoremProducer::rewriteNotTrue(const Expr& e) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isNot() && e[0].isTrue(),
		"rewriteNotTrue precondition violated");
  if(withProof())
    pf = newPf("rewrite_not_true");
  return newRWTheorem(e, d_em->falseExpr(), Assumptions::emptyAssump(), pf);
}


// ==> NOT FALSE IFF TRUE
Theorem CommonTheoremProducer::rewriteNotFalse(const Expr& e) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isNot() && e[0].isFalse(),
		"rewriteNotFalse precondition violated");
  if(withProof())
    pf = newPf("rewrite_not_false");
  return newRWTheorem(e, d_em->trueExpr(), Assumptions::emptyAssump(), pf);
}


// ==> (NOT NOT e) IFF e, takes !!e
Theorem CommonTheoremProducer::rewriteNotNot(const Expr& e) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(e.isNot() && e[0].isNot(),
		"rewriteNotNot precondition violated");
  if(withProof())
    pf = newPf("rewrite_not_not", e[0][0]);
  return newRWTheorem(e, e[0][0], Assumptions::emptyAssump(), pf);
}


//! ==> NOT FORALL (vars): e  IFF EXISTS (vars) NOT e
Theorem CommonTheoremProducer::rewriteNotForall(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot() && e[0].isForall(),
		"rewriteNotForall: expr must be NOT FORALL:\n"
		+e.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_not_forall", e);
  return newRWTheorem(e, d_em->newClosureExpr(EXISTS, e[0].getVars(),
                                              !e[0].getBody()), Assumptions::emptyAssump(), pf);
}


//! ==> NOT EXISTS (vars): e  IFF FORALL (vars) NOT e
Theorem CommonTheoremProducer::rewriteNotExists(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot() && e[0].isExists(),
		"rewriteNotExists: expr must be NOT FORALL:\n"
		+e.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_not_exists", e);
  return newRWTheorem(e, d_em->newClosureExpr(FORALL, e[0].getVars(),
                                              !e[0].getBody()), Assumptions::emptyAssump(), pf);
}


Expr CommonTheoremProducer::skolemize(const Expr& e)
{
  vector<Expr> vars;
  const vector<Expr>& boundVars = e.getVars(); 
  for(unsigned int i=0; i<boundVars.size(); i++) {
    Expr skolV(e.skolemExpr(i));
    Type tp(e.getVars()[i].getType());
    skolV.setType(tp);
    vars.push_back(skolV);
  }
  return(e.getBody().substExpr(boundVars, vars));
}


Theorem CommonTheoremProducer::skolemizeRewrite(const Expr& e)
{
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isExists(), "skolemize rewrite called on non-existential: "
		+ e.toString());
  }
  Expr skol = skolemize(e);
  if(withProof()) {
    Expr rw(e.iffExpr(skol));
    pf = newLabel(rw);
  }
  TRACE("quantlevel", "skolemize ", skol, "");
  TRACE("quantlevel sko", "skolemize ", skol, "");
  TRACE("quantlevel sko", "skolemize from org ", e, "");
  return newRWTheorem(e, skol, Assumptions::emptyAssump(), pf);

}


Theorem CommonTheoremProducer::skolemizeRewriteVar(const Expr& e)
{
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isExists(), "skolemizeRewriteVar("
		+e.toString()+")");
  }

  const vector<Expr>& boundVars = e.getVars();
  const Expr& body = e.getBody();

  if(CHECK_PROOFS) {
    CHECK_SOUND(boundVars.size()==1, "skolemizeRewriteVar("
		+e.toString()+")");
    CHECK_SOUND(body.isEq() || body.isIff(), "skolemizeRewriteVar("
		+e.toString()+")");
    const Expr& v = boundVars[0];
    CHECK_SOUND(body[1] == v, "skolemizeRewriteVar("
		+e.toString()+")");
    CHECK_SOUND(!(v.subExprOf(body[0])), "skolemizeRewriteVar("
		+e.toString()+")");
  }
  // Create the Skolem constant appropriately
  Expr skolV(e.skolemExpr(0));
  Type tp(e.getVars()[0].getType());
  skolV.setType(tp);
  // Skolemized expression
  Expr skol = Expr(body.getOp(), body[0], skolV);

  if(withProof()) {
    Expr rw(e.iffExpr(skol));
    pf = newLabel(rw);
  }
  return newRWTheorem(e, skol, Assumptions::emptyAssump(), pf);
}


Theorem CommonTheoremProducer::varIntroRule(const Expr& phi) {
  // This rule is sound for all expressions phi
  Proof pf;
  const Expr boundVar = d_em->newBoundVarExpr(phi.getType());

  Expr body;  
  if(phi.getType().isBool())
    body = phi.iffExpr(boundVar);
  else
    body = phi.eqExpr(boundVar);

  std::vector<Expr> v; 
  v.push_back(boundVar);
  const Expr result = d_em->newClosureExpr(EXISTS, v, body);
  
  if(withProof()) 
    pf = newPf("var_intro", phi, boundVar);
  return newTheorem(result, Assumptions::emptyAssump(), pf);
}


Theorem CommonTheoremProducer::skolemize(const Theorem& thm) { 
  const Expr& e = thm.getExpr();
  if(e.isExists()) {
    TRACE("skolem", "Skolemizing existential:", "", "{");
    CDMap<Expr, Theorem>::iterator i=d_skolemized_thms.find(e),
      iend=d_skolemized_thms.end();
    if(i!=iend) {
      TRACE("skolem", "Skolemized theorem found in map: ", (*i).second, "}");
      return iffMP(thm, (*i).second);
    }
    Theorem skol = skolemizeRewrite(e);
    for(unsigned int i=0; i<e.getVars().size(); i++) {
      Expr skolV(e.skolemExpr(i));
      Type tp(e.getVars()[i].getType());
      skolV.setType(tp);
    }
    d_skolem_axioms.push_back(skol);
    d_skolemized_thms.insert(e, skol, 0);//d_coreSatAPI->getBottomScope());
    skol = iffMP(thm, skol); 

    TRACE("skolem", "skolemized new theorem: ", skol, "}");
    return skol;
  }
  return thm;
}


Theorem CommonTheoremProducer::varIntroSkolem(const Expr& e) {
  // First, look up the cache
  CDMap<Expr, Theorem>::iterator i=d_skolemVars.find(e),
    iend=d_skolemVars.end();
  if(i!=iend) return (*i).second;
  // Not in cache; create a new one
  Theorem thm = varIntroRule(e);
  const Expr& e2 = thm.getExpr();
  DebugAssert(e2.isExists() && e2.getVars().size()==1, "varIntroSkolem: e2 = "
	      +e2.toString());
  Theorem skolThm;
  // Check if we have a corresponding skolemized version already
  CDMap<Expr, Theorem>::iterator j=d_skolemized_thms.find(e2),
    jend=d_skolemized_thms.end();
  if(j!=jend) {
    skolThm = (*i).second;
  } else {
    skolThm = skolemizeRewriteVar(e2);
    d_skolem_axioms.push_back(skolThm);
    d_skolemized_thms.insert(e2, skolThm, 0); //d_coreSatAPI->getBottomScope());
  }
  thm = iffMP(thm, skolThm);
  d_skolemVars.insert(e, thm, 0); //d_coreSatAPI->getBottomScope());
  return thm;
}


// Derived Rules


Theorem CommonTheoremProducer::trueTheorem()
{
  return iffTrueElim(reflexivityRule(d_em->trueExpr()));
}


Theorem CommonTheoremProducer::rewriteAnd(const Theorem& e)
{
  return iffMP(e, rewriteAnd(e.getExpr()));
}


Theorem CommonTheoremProducer::rewriteOr(const Theorem& e)
{
  return iffMP(e, rewriteOr(e.getExpr()));
}


Theorem CommonTheoremProducer::ackermann(const Expr& e1, const Expr& e2)
{
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(e1.isApply() && e2.isApply() && e1.getOp() == e2.getOp(),
		"ackermann precondition violated");
  Expr hyp;
  int ar = e1.arity();
  if (ar == 1) {
    hyp = Expr(e1[0].eqExpr(e2[0]));
  }
  else {
    vector<Expr> vec;
    for (int i = 0; i != ar; ++i) {
      vec.push_back(e1[i].eqExpr(e2[i]));
    }
    hyp = Expr(AND, vec);
  }
  if(withProof())
    pf = newPf("ackermann", e1, e2);
  return newTheorem(hyp.impExpr(e1.eqExpr(e2)), Assumptions::emptyAssump(), pf);
}


void CommonTheoremProducer::findITE(const Expr& e, Expr& condition, Expr& thenpart, Expr& elsepart)
{
  if (!e.getType().isBool() && e.isITE()) {
    condition = e[0];
    if (!condition.containsTermITE()) {
      thenpart = e[1];
      elsepart = e[2];
      return;
    }
  }

  vector<Expr> kids;
  int i = 0;
  for (; i < e.arity(); ++i) {
    if (e[i].containsTermITE()) break;
    kids.push_back(e[i]);
  }

  if(CHECK_PROOFS) {
    CHECK_SOUND(i < e.arity(), "could not find ITE");
  }

  Expr t2, e2;
  findITE(e[i], condition, t2, e2);

  kids.push_back(t2);
  for(int k = i+1; k < e.arity(); ++k) {
    kids.push_back(e[k]);
  }

  thenpart = Expr(e.getOp(), kids);

  kids[i] = e2;
  elsepart = Expr(e.getOp(), kids);
}


Theorem CommonTheoremProducer::liftOneITE(const Expr& e) {

  if(CHECK_PROOFS) {
    CHECK_SOUND(e.containsTermITE(), "CommonTheoremProducer::liftOneITE: bad input" + e.toString());
  }

  Expr cond, thenpart, elsepart;

  findITE(e, cond, thenpart, elsepart);

  Proof pf;
  if(withProof())
    pf = newPf("lift_one_ite", e);

  return newRWTheorem(e, cond.iteExpr(thenpart, elsepart), Assumptions::emptyAssump(), pf);
}
