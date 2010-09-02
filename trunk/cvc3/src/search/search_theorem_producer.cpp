/*****************************************************************************/
/*!
 * \file search_theorem_producer.cpp
 * \brief Implementation of the proof rules for the simple search engine
 * 
 * Author: Sergey Berezin
 * 
 * Created: Mon Feb 24 14:51:51 2003
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

#include "search.h"
#include "theory_core.h"
#include "theorem_manager.h"
#include "common_proof_rules.h"
#include "command_line_flags.h"
#include "theory_arith.h"
// UNCOMMENT THIS FOR LFSC
#include "LFSCPrinter.h" // by liana for LFSC conversion

#define _CVC3_TRUSTED_
#include "search_theorem_producer.h"


using namespace std;
using namespace CVC3;


/////////////////////////////////////////////////////////////////////////////
// class SearchEngine trusted methods
/////////////////////////////////////////////////////////////////////////////



SearchEngineRules*
SearchEngine::createRules() {
  return new SearchEngineTheoremProducer(d_core->getTM());
}


// hack for printing original assumptions in LFSC by liana
bool lfsc_called = false;
SearchEngine* search_engine;

SearchEngineRules*
SearchEngine::createRules(SearchEngine* s_eng) {
  search_engine = s_eng;
  return new SearchEngineTheoremProducer(d_core->getTM());
}


SearchEngineTheoremProducer::SearchEngineTheoremProducer(TheoremManager* tm)
  : TheoremProducer(tm), d_commonRules(tm->getRules())
{ }


/////////////////////////////////////////////////////////////////////////////
// Proof rules
/////////////////////////////////////////////////////////////////////////////

// Proof by contradiction: !A |- FALSE ==> |- A.  "!A" doesn't
// have to be present in the assumptions.
Theorem
SearchEngineTheoremProducer::proofByContradiction(const Expr& a,
                                                  const Theorem& pfFalse) {
  if(CHECK_PROOFS)
    CHECK_SOUND(pfFalse.getExpr().isFalse(),
                "proofByContradiction: pfFalse = : " + pfFalse.toString());
  Expr not_a(!a);
  Assumptions assump(pfFalse.getAssumptionsRef() - not_a);
  Proof pf;
  if(withProof()) {
    // TODO: optimize with 1 traversal?
    Theorem thm(pfFalse.getAssumptionsRef()[not_a]);
    Proof u; // proof label for !aLFSCL
    if(!thm.isNull()) u = thm.getProof();
    // Proof compaction: if u is Null, use "FALSE => A" rule
    if(u.isNull()){
      pf = newPf("false_implies_anything", a, pfFalse.getProof());
      if(!lfsc_called){
        satProof(a, pf);
      }
    }
    else
      pf = newPf("pf_by_contradiction", a,
                 // LAMBDA-abstraction (LAMBDA (u: !a): pfFalse)
                 newPf(u, not_a, pfFalse.getProof()));
  }
  return newTheorem(a, assump, pf);
}
    
// Similar rule, only negation introduction:
// A |- FALSE ==> !A
Theorem
SearchEngineTheoremProducer::negIntro(const Expr& not_a,
                                      const Theorem& pfFalse) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(pfFalse.getExpr().isFalse(),
                "negIntro: pfFalse = : " + pfFalse.toString());
    CHECK_SOUND(not_a.isNot(), "negIntro: not_a = "+not_a.toString());
  }

  Expr a(not_a[0]);
  Assumptions assump(pfFalse.getAssumptionsRef() - a);
  Proof pf;
  if(withProof()) {
    Theorem thm(pfFalse.getAssumptionsRef()[a]);
    Proof u; // proof label for 'a'
    if(!thm.isNull()) u = thm.getProof();
    // Proof compaction: if u is Null, use "FALSE => !A" rule
    if(u.isNull())
      pf = newPf("false_implies_anything", not_a, pfFalse.getProof());

    else
      pf = newPf("neg_intro", not_a,
                 // LAMBDA-abstraction (LAMBDA (u: a): pfFalse)
                 newPf(u, a, pfFalse.getProof()));
  }
  return newTheorem(not_a, assump, pf);
}
    

// Case split: u1:A |- C, u2:!A |- C  ==>  |- C
Theorem
SearchEngineTheoremProducer::caseSplit(const Expr& a,
                                       const Theorem& a_proves_c,
                                       const Theorem& not_a_proves_c) {
  Expr c(a_proves_c.getExpr());

  if(CHECK_PROOFS) {
    CHECK_SOUND(c == not_a_proves_c.getExpr(), 
                "caseSplit: conclusions differ:\n  positive case C = "
                + c.toString() + "\n  negative case C = "
                + not_a_proves_c.getExpr().toString());
    // The opposite assumption should not appear in the theorems
    // Actually, this doesn't violate soundness, no reason to check
//     CHECK_SOUND(a_proves_c.getAssumptions()[!a].isNull(), 
//              "caseSplit: wrong assumption: " + (!a).toString()
//              +"\n in "+a_proves_c.toString());
//     CHECK_SOUND(not_a_proves_c.getAssumptions()[a].isNull(), 
//              "caseSplit: wrong assumption: " + a.toString()
//              +"\n in "+not_a_proves_c.toString());
  }

  const Assumptions& a1(a_proves_c.getAssumptionsRef());
  const Assumptions& a2(not_a_proves_c.getAssumptionsRef());
  Assumptions a3 = a1 - a;
  Assumptions a4 = a2 - !a;

  // Proof compaction: if either theorem proves C without a or !a,
  // then just use that theorem.  This only works if assumptions are
  // active.

  if (a1 == a3) return a_proves_c;
  if (a2 == a4) return not_a_proves_c;

  // No easy way out.  Do the work.
  Proof pf;
  a3.add(a4);

  if(withProof()) {
    // Create lambda-abstractions
    vector<Proof> pfs;
    pfs.push_back(newPf(a1[a].getProof(), 
                        a, a_proves_c.getProof()));
    pfs.push_back(newPf(a2[!a].getProof(), 
                        !a, not_a_proves_c.getProof()));
    pf = newPf("case_split", a, c, pfs);
  }
  return newTheorem(c, a3, pf);
}

// Conflict clause rule: 
// Gamma, A_1,...,A_n |- B ==> Gamma |- (OR B A_1 ... A_n)
// The assumptions A_i are given by the vector 'lits'.
// If B==FALSE, it is omitted from the result.

// NOTE: here "!A_i" means an inverse of A_i, not just a negation.
// That is, if A_i is NOT C, then !A_i is C.

// verification function used by conflictClause
void SearchEngineTheoremProducer::verifyConflict(const Theorem& thm, 
                                                 TheoremMap& m) {
  const Assumptions& a(thm.getAssumptionsRef());
  const Assumptions::iterator iend = a.end();
  for (Assumptions::iterator i = a.begin(); 
       i != iend; ++i) {
    CHECK_SOUND(!i->isNull(),
                "SearchEngineTheoremProducer::conflictClause: "
                "Found null theorem");
    if (!i->isRefl() && !i->isFlagged()) {
      i->setFlag();
      if (m.count(*i) == 0) {
        CHECK_SOUND(!i->isAssump(),
                    "SearchEngineTheoremProducer::conflictClause: "
                    "literal and gamma sets do not form a complete "
                    "cut of Theorem assumptions. Stray theorem: \n"
                    +i->toString());
        verifyConflict(*i, m);
      }
      else {
        m[*i] = true;
      }
    }
  }
}


Theorem
SearchEngineTheoremProducer::
conflictClause(const Theorem& thm, const vector<Theorem>& lits, 
               const vector<Theorem>& gamma) {
  //  TRACE("search proofs", "conflictClause(", thm.getExpr(), ") {");
  IF_DEBUG(if(debugger.trace("search proofs")) {
    ostream& os = debugger.getOS();
    os << "lits = [";
    for(vector<Theorem>::const_iterator i=lits.begin(), iend=lits.end();
        i!=iend; ++i)
      os << i->getExpr() << ",\n";
    os << "]\n\ngamma = [";
    for(vector<Theorem>::const_iterator i=gamma.begin(), iend=gamma.end();
        i!=iend; ++i)
      os << i->getExpr() << ",\n";
    os << "]" << endl;
  });
  bool checkProofs(CHECK_PROOFS);
  // This rule only makes sense when runnnig with assumptions
  if(checkProofs) {
    CHECK_SOUND(withAssumptions(),
                "conflictClause: called while running without assumptions");
  }

  // Assumptions aOrig(thm.getAssumptions());

  vector<Expr> literals;
  vector<Proof> u; // Vector of proof labels
  literals.reserve(lits.size() + 1);
  u.reserve(lits.size());
  const vector<Theorem>::const_iterator iend = lits.end();
  for(vector<Theorem>::const_iterator i=lits.begin(); i!=iend; ++i) {
    Expr neg(i->getExpr().negate());

    literals.push_back(neg);
    if(withProof()) u.push_back(i->getProof());
  }

  if(checkProofs) {
    TheoremMap m;
    //    TRACE_MSG("search proofs", "adding gamma to m: {");
    for(vector<Theorem>::const_iterator i = gamma.begin();
        i != gamma.end(); ++i) {
      //      TRACE("search proofs", "m[", *i, "]");
      m[*i] = false;
    }
    //    TRACE_MSG("search proofs", "}");

    for(vector<Theorem>::const_iterator i = lits.begin(); i!=iend; ++i) {
      //      TRACE("search proofs", "check lit: ", *i, "");
      CHECK_SOUND(m.count(*i) == 0, 
                  "SearchEngineTheoremProducer::conflictClause: "
                  "literal and gamma sets are not disjoint: lit = "
                  +i->toString());
      m[*i] = false;
    }
    thm.clearAllFlags();
    verifyConflict(thm, m);
    TheoremMap::iterator t = m.begin(), tend = m.end();
    for (; t != tend; ++t) {
      CHECK_SOUND(t->second == true,
                  "SearchEngineTheoremProducer::conflictClause: "
                  "literal or gamma set contains extra element : "
                  + t->first.toString());
    }
  }
 
  Assumptions a(gamma);

  if(!thm.getExpr().isFalse())
    literals.push_back(thm.getExpr());

  Proof pf;
  if(withProof()) {
    if(lits.size()>0) {
      vector<Expr> assump;
      // If assumptions are not leaves, we need to create new
      // variables for them and substitute them for their proofs in
      // the proof term
      ExprHashMap<Expr> subst;
      DebugAssert(u.size() == lits.size(), "");
      for(size_t i=0, iend=lits.size(); i<iend; ++i) {
        const Expr& e(lits[i].getExpr());
        assump.push_back(e);
        Proof& v = u[i];
        if(!v.getExpr().isVar()) {
          Proof label = newLabel(e);
          subst[v.getExpr()] = label.getExpr();
          v = label;
        }
      }
      Proof body(thm.getProof());
      if(!subst.empty())
        body = Proof(body.getExpr().substExpr(subst));
      pf = newPf("conflict_clause", newPf(u, assump, body));
    }
    else
      pf = newPf("false_to_empty_or", thm.getProof());
  }
  Theorem res(newTheorem(Expr(OR, literals, d_em), a, pf));
  //  TRACE("search proofs", "conflictClause => ", res.getExpr(), " }");
  return res;
}


// Theorem
// SearchEngineTheoremProducer::
// conflictClause(const Theorem& thm, const vector<Expr>& lits) {
//   bool checkProofs(CHECK_PROOFS);
//   // This rule only makes sense when runnnig with assumptions
//   if(checkProofs) {
//     CHECK_SOUND(withAssumptions(),
//              "conflictClause: called while running without assumptions");
//   }

//   Assumptions aOrig(thm.getAssumptions());

//   vector<Expr> literals;
//   vector<Expr> negations;
//   vector<Proof> u; // Vector of proof labels
//   literals.reserve(lits.size() + 1);
//   negations.reserve(lits.size());
//   u.reserve(lits.size());
//   for(vector<Expr>::const_iterator i=lits.begin(), iend=lits.end();
//       i!=iend; ++i) {
//     Expr neg(i->isNot()? (*i)[0] : !(*i));
//     if(checkProofs)
//       CHECK_SOUND(!aOrig[neg].isNull(), 
//                "SearchEngineTheoremProducer::conflictClause: "
//                "literal is not in the set of assumptions: neg = "
//                +neg.toString() + "\n Theorem = " + thm.toString());
//     literals.push_back(*i);
//     negations.push_back(neg);
//     if(withProof()) u.push_back(aOrig[neg].getProof());
//   }

//   Assumptions a = aOrig - negations;

//   if(!thm.getExpr().isFalse())
//     literals.push_back(thm.getExpr());

//   Proof pf;
//   if(withProof()) {
//     if(lits.size()>0)
//       pf = newPf("conflict_clause", newPf(u, literals, thm.getProof()));
//     else
//       pf = newPf("false_to_empty_or", thm.getProof());
//   }
//  // Use ExprManager in newExpr, since literals may be empty
//   return newTheorem(Expr(d_em, OR, literals), a, pf);
// }


// "Cut" rule: { G_i |- A_i };  G', { A_i } |- B ==> union(G_i)+G' |- B.
Theorem
SearchEngineTheoremProducer::
cutRule(const vector<Theorem>& thmsA,
        const Theorem& as_prove_b) {
  if(CHECK_PROOFS)
    CHECK_SOUND(withAssumptions(),
                "cutRule called without assumptions activated");
  // Optimization: use only those theorems that occur in B's assumptions.
  // *** No, take it back, it's a mis-optimization.  Most of the time,
  // cutRule is applied when we *know* thmsA are present in the
  // assumptions of 'as_proof_b'.

  Proof pf;
  vector<Expr> exprs;
  exprs.reserve(thmsA.size() + 1);
  const vector<Theorem>::const_iterator iend = thmsA.end();
  for(vector<Theorem>::const_iterator i=thmsA.begin(); i!=iend; ++i) {
    exprs.push_back(i->getExpr());
  }

  Assumptions a(thmsA); // add the As
  a.add(as_prove_b.getAssumptionsRef() - exprs); // Add G'
  
  if(withProof()) {
    vector<Proof> pfs;
    pfs.reserve(thmsA.size() + 1);
    for(vector<Theorem>::const_iterator i = thmsA.begin(); i != iend; ++i) {
      pfs.push_back(i->getProof());
    }
    exprs.push_back(as_prove_b.getExpr());
    pfs.push_back(as_prove_b.getProof());
    pf = newPf("cut_rule",exprs,pfs);
  }
  return newTheorem(as_prove_b.getExpr(), a, pf);
}


void 
SearchEngineTheoremProducer::checkSoundNoSkolems(const Expr& e, 
                                                 ExprMap<bool>& visited,
                                                 const ExprMap<bool>& skolems)
{
  if(visited.count(e)>0)
    return;
  else
    visited[e] = true;
  CHECK_SOUND(skolems.count(e) == 0, 
              "skolem constant found in axioms of false theorem: "
              + e.toString());
  for(Expr::iterator it = e.begin(), end = e.end(); it!= end; ++it)
    checkSoundNoSkolems(*it, visited, skolems);
  if(e.getKind() == FORALL || e.getKind() == EXISTS)
    checkSoundNoSkolems(e.getBody(), visited, skolems);       
}

void 
SearchEngineTheoremProducer::checkSoundNoSkolems(const Theorem& t, 
                                                 ExprMap<bool>& visited,
                                                 const ExprMap<bool>& skolems)
{
  if(t.isRefl() || t.isFlagged())
    return;
  t.setFlag();
  if(t.isAssump())
    checkSoundNoSkolems(t.getExpr(), visited, skolems);
  else
  {
    const Assumptions& a(t.getAssumptionsRef());
    Assumptions::iterator it = a.begin(), end = a.end();
    for(; it!=end; ++it)
      checkSoundNoSkolems(*it, visited, skolems);
   }
}

/*! Eliminate skolem axioms: 
 * Gamma, Delta |- false => Gamma|- false 
 * where Delta is a set of skolem axioms {|-Exists(x) phi (x) => phi(c)}
 * and gamma does not contain any of the skolem constants c.
 */

Theorem 
SearchEngineTheoremProducer::eliminateSkolemAxioms(const Theorem& tFalse, 
                                            const std::vector<Theorem>& delta)
{
  TRACE("skolem", "=>eliminateSkolemAxioms ", delta.size(), "{");
  if(delta.empty())
  {
    TRACE("skolem",  "eliminateSkolemAxioms","" , "}");
    return tFalse;
  }
  const Expr& falseExpr = tFalse.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(falseExpr.isFalse(),
                "eliminateSkolemAxiom called on non-false theorem");
    ExprMap<bool> visited;
    ExprMap<bool> skolems;
    vector<Theorem>::const_iterator it = delta.begin(), end = delta.end();
    for(; it!=end; ++it) {
      CHECK_SOUND(it->isRewrite(),
                  "eliminateSkolemAxioms(): Skolem axiom is not "
                  "an IFF: "+it->toString());
      const Expr& ex = it->getLHS();
      CHECK_SOUND(ex.isExists(), 
                  "Did not receive skolem axioms in Delta"
                  " of eliminateSkolemAxioms" + it->toString());
      // Collect the Skolem constants for further soundness checks
      for(unsigned int j=0; j<ex.getVars().size(); j++) {
        Expr sk_var(ex.skolemExpr(j));
        if(sk_var.getType().isBool()) {
          sk_var = d_em->newLeafExpr(sk_var.mkOp());
        }
        skolems[sk_var] = true;
        TRACE("skolem", ">> Eliminating variable: ", sk_var, "<<");
      }
    }
    tFalse.clearAllFlags();
    checkSoundNoSkolems(tFalse, visited, skolems);
  }
  Proof pf;
  if(!withProof()) return tFalse;
  else 
    {
      Proof origFalse = tFalse.getProof();
      std::vector<Proof>skolemizeLabels;
      std::vector<Expr> exprs;
      for(unsigned int i=0; i<delta.size(); i++)
        {
          exprs.push_back(delta[i].getExpr());
          skolemizeLabels.push_back(delta[i].getProof());
        }
      pf = newPf(skolemizeLabels, exprs, origFalse);
    }
  TRACE("skolem",  "eliminateSkolemAxioms","" , "}");
  return newTheorem(tFalse.getExpr(), tFalse.getAssumptionsRef(), pf);
}


Theorem
SearchEngineTheoremProducer::unitProp(const std::vector<Theorem>& thms,
                                      const Theorem& clause,
                                      unsigned i) {
  Expr e(clause.getExpr());
  if(CHECK_PROOFS) {
    // Soundness check: first, check the form of the 'clause' theorem
    CHECK_SOUND(e.isOr() && e.arity() > (int)i,
                "SearchEngineTheoremProducer::unitProp: bad theorem or i="
                +int2string(i)+" > arity="+int2string(e.arity())
                +" in clause = " + clause.toString());
    // Now, check correspondence of thms to the disjunction
    CHECK_SOUND(((int)thms.size()) == e.arity() - 1,
                "SearchEngineTheoremProducer::unitProp: "
                "wrong number of theorems"
                "\n  thms.size = " + int2string(thms.size())
                +"\n  clause.arity = " + int2string(e.arity()));

    for(unsigned j=0,k=0; j<thms.size(); j++) {
      if(j!=i) {
        Expr ej(e[j]), ek(thms[k].getExpr());
        CHECK_SOUND((ej.isNot() && ej[0] == ek) || (ek.isNot() && ej == ek[0]),
                    "SearchEngineTheoremProducer::unitProp: "
                    "wrong theorem["+int2string(k)+"]"
                    "\n  thm = " + thms[k].toString() +
                    "\n  literal = " + e[j].toString() +
                    "\n  clause = " + clause.toString());
        k++;
      }
    }
  }

  Assumptions a(thms);
  a.add(clause);
  Proof pf;

  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.reserve(thms.size() + 1);
    pfs.reserve(thms.size()+1);
    const vector<Theorem>::const_iterator iend = thms.end();
    for(vector<Theorem>::const_iterator i=thms.begin(); i!=iend; ++i) {
      exprs.push_back(i->getExpr());
      pfs.push_back(i->getProof());
    }
    exprs.push_back(clause.getExpr());
    pfs.push_back(clause.getProof());
    pf = newPf("unit_prop", exprs, pfs);
  }
  return newTheorem(e[i], a, pf);
}

Theorem
SearchEngineTheoremProducer::propAndrAF(const Theorem& andr_th,
                                        bool left,
                                        const Theorem& b_th) {
  const Expr& andr_e(andr_th.getExpr());
  if(CHECK_PROOFS) {
    CHECK_SOUND(andr_e.getKind() == AND_R &&
                ((left && b_th.refutes(andr_e[1])) ||
                 (!left && b_th.refutes(andr_e[2]))),
                "SearchEngineTheoremProducer::propAndrAF");
  }

  Assumptions a(andr_th, b_th);
  Proof pf;

  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(andr_th.getExpr());
    exprs.push_back(b_th.getExpr());
    pfs.push_back(andr_th.getProof());
    pfs.push_back(b_th.getProof());
    // can we note which branch to take?
    pf = newPf("prop_andr_af", exprs, pfs);
  }

  return newTheorem(andr_e[0].negate(), a, pf);
}

Theorem
SearchEngineTheoremProducer::propAndrAT(const Theorem& andr_th,
                                        const Theorem& l_th,
                                        const Theorem& r_th) {
  const Expr& andr_e(andr_th.getExpr());
  if(CHECK_PROOFS) {
    CHECK_SOUND(andr_e.getKind() == AND_R &&
                l_th.proves(andr_e[1]) && r_th.proves(andr_e[2]),
                "SearchEngineTheoremProducer::propAndrAT");
  }

  Assumptions a(andr_th, l_th);
  a.add(r_th);
  Proof pf;

  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(andr_th.getExpr());
    exprs.push_back(l_th.getExpr());
    exprs.push_back(r_th.getExpr());
    pfs.push_back(andr_th.getProof());
    pfs.push_back(l_th.getProof());
    pfs.push_back(r_th.getProof());
    pf = newPf("prop_andr_at", exprs, pfs);
  }

  return newTheorem(andr_e[0], a, pf);
}

void
SearchEngineTheoremProducer::propAndrLRT(const Theorem& andr_th,
                                         const Theorem& a_th,
                                         Theorem* l_th,
                                         Theorem* r_th) {
  const Expr& andr_e(andr_th.getExpr());
  if(CHECK_PROOFS) {
    CHECK_SOUND(andr_e.getKind() == AND_R && a_th.proves(andr_e[0]),
                "SearchEngineTheoremProducer::propAndrLRT");
  }

  Assumptions a(andr_th, a_th);
  Proof pf;

  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(andr_th.getExpr());
    exprs.push_back(a_th.getExpr());
    pfs.push_back(andr_th.getProof());
    pfs.push_back(a_th.getProof());
    pf = newPf("prop_andr_lrt", exprs, pfs);
  }

  if (l_th) *l_th = newTheorem(andr_e[1], a, pf);
  if (r_th) *r_th = newTheorem(andr_e[2], a, pf);
}

Theorem
SearchEngineTheoremProducer::propAndrLF(const Theorem& andr_th,
                                        const Theorem& a_th,
                                        const Theorem& r_th) {
  const Expr& andr_e(andr_th.getExpr());
  if(CHECK_PROOFS) {
    CHECK_SOUND(andr_e.getKind() == AND_R &&
                a_th.refutes(andr_e[0]) && r_th.proves(andr_e[2]),
                "SearchEngineTheoremProducer::propAndrLF");
  }

  Assumptions a(andr_th, a_th);
  a.add(r_th);
  Proof pf;

  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(andr_th.getExpr());
    exprs.push_back(a_th.getExpr());
    exprs.push_back(r_th.getExpr());
    pfs.push_back(andr_th.getProof());
    pfs.push_back(a_th.getProof());
    pfs.push_back(r_th.getProof());
    pf = newPf("prop_andr_lf", exprs, pfs);
  }

  return newTheorem(andr_e[1].negate(), a, pf);
}

Theorem
SearchEngineTheoremProducer::propAndrRF(const Theorem& andr_th,
                                        const Theorem& a_th,
                                        const Theorem& l_th) {
  const Expr& andr_e(andr_th.getExpr());
  if(CHECK_PROOFS) {
    CHECK_SOUND(andr_e.getKind() == AND_R &&
                a_th.refutes(andr_e[0]) && l_th.proves(andr_e[1]),
                "SearchEngineTheoremProducer::propAndrRF");
  }

  Assumptions a(andr_th, a_th);
  a.add(l_th);
  Proof pf;

  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(andr_th.getExpr());
    exprs.push_back(a_th.getExpr());
    exprs.push_back(l_th.getExpr());
    pfs.push_back(andr_th.getProof());
    pfs.push_back(a_th.getProof());
    pfs.push_back(l_th.getProof());
    pf = newPf("prop_andr_rf", exprs, pfs);
  }

  return newTheorem(andr_e[2].negate(), a, pf);
}

Theorem
SearchEngineTheoremProducer::confAndrAT(const Theorem& andr_th,
                                        const Theorem& a_th,
                                        bool left,
                                        const Theorem& b_th) {
  const Expr& andr_e(andr_th.getExpr());
  if(CHECK_PROOFS) {
    CHECK_SOUND(andr_e.getKind() == AND_R && a_th.proves(andr_e[0]) &&
                ((left && b_th.refutes(andr_e[1])) ||
                 (!left && b_th.refutes(andr_e[2]))),
                "SearchEngineTheoremProducer::confAndrAT");
  }

  Assumptions a(andr_th, a_th);
  a.add(b_th);
  Proof pf;

  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(andr_th.getExpr());
    exprs.push_back(a_th.getExpr());
    exprs.push_back(b_th.getExpr());
    pfs.push_back(andr_th.getProof());
    pfs.push_back(a_th.getProof());
    pfs.push_back(b_th.getProof());
    // can we note which branch to take?
    pf = newPf("conf_andr_at", exprs, pfs);
  }

  return newTheorem(d_em->falseExpr(), a, pf);
}

Theorem
SearchEngineTheoremProducer::confAndrAF(const Theorem& andr_th,
                                        const Theorem& a_th,
                                        const Theorem& l_th,
                                        const Theorem& r_th) {
  const Expr& andr_e(andr_th.getExpr());
  if(CHECK_PROOFS) {
    CHECK_SOUND(andr_e.getKind() == AND_R && a_th.refutes(andr_e[0]) &&
                l_th.proves(andr_e[1]) && r_th.proves(andr_e[2]),
                "SearchEngineTheoremProducer::confAndrAF");
  }

  Assumptions a;
  Proof pf;
  if(withAssumptions()) {
    a.add(andr_th);
    a.add(a_th);
    a.add(l_th);
    a.add(r_th);
  }

  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(andr_th.getExpr());
    exprs.push_back(a_th.getExpr());
    exprs.push_back(l_th.getExpr());
    exprs.push_back(r_th.getExpr());
    pfs.push_back(andr_th.getProof());
    pfs.push_back(a_th.getProof());
    pfs.push_back(l_th.getProof());
    pfs.push_back(r_th.getProof());
    pf = newPf("conf_andr_af", exprs, pfs);
  }

  return newTheorem(d_em->falseExpr(), a, pf);
}

Theorem
SearchEngineTheoremProducer::propIffr(const Theorem& iffr_th,
                                      int p,
                                      const Theorem& a_th,
                                      const Theorem& b_th)
{
  int a(-1), b(-1);
  if(CHECK_PROOFS)
    CHECK_SOUND(p == 0 || p == 1 || p == 2,
                "SearchEngineTheoremProducer::propIffr: p="
                +int2string(p));
  switch (p) {
  case 0: a = 1; b = 2; break;
  case 1: a = 0; b = 2; break;
  case 2: a = 0; b = 1; break;
  }

  const Expr& iffr_e(iffr_th.getExpr());

  bool v0 = a_th.proves(iffr_e[a]);
  bool v1 = b_th.proves(iffr_e[b]);

  if (CHECK_PROOFS) {
    CHECK_SOUND(iffr_e.getKind() == IFF_R &&
                (v0 || a_th.refutes(iffr_e[a])) &&
                (v1 || b_th.refutes(iffr_e[b])),
                "SearchEngineTheoremProducer::propIffr");
  }

  Assumptions aa;
  Proof pf;
  if (withAssumptions()) {
    aa.add(iffr_th);
    aa.add(a_th);
    aa.add(b_th);
  }

  if (withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(iffr_th.getExpr());
    exprs.push_back(a_th.getExpr());
    exprs.push_back(b_th.getExpr());
    pfs.push_back(iffr_th.getProof());
    pfs.push_back(a_th.getProof());
    pfs.push_back(b_th.getProof());
    pf = newPf("prop_iffr", exprs, pfs);
  }

  return newTheorem(v0 == v1 ? iffr_e[p] : iffr_e[p].negate(), aa, pf);
}

Theorem
SearchEngineTheoremProducer::confIffr(const Theorem& iffr_th,
                                      const Theorem& i_th,
                                      const Theorem& l_th,
                                      const Theorem& r_th)
{
  const Expr& iffr_e(iffr_th.getExpr());

  bool v0 = i_th.proves(iffr_e[0]);
  bool v1 = l_th.proves(iffr_e[1]);
  bool v2 = r_th.proves(iffr_e[2]);

  if (CHECK_PROOFS) {
    CHECK_SOUND(iffr_e.getKind() == IFF_R &&
                (v0 || i_th.refutes(iffr_e[0])) &&
                (v1 || l_th.refutes(iffr_e[1])) &&
                (v2 || r_th.refutes(iffr_e[2])) &&
                ((v0 && v1 != v2) || (!v0 && v1 == v2)),
                "SearchEngineTheoremProducer::confIffr");
  }

  Assumptions a;
  Proof pf;
  if (withAssumptions()) {
    a.add(iffr_th);
    a.add(i_th);
    a.add(l_th);
    a.add(r_th);
  }

  if (withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(iffr_th.getExpr());
    exprs.push_back(i_th.getExpr());
    exprs.push_back(l_th.getExpr());
    exprs.push_back(r_th.getExpr());
    pfs.push_back(iffr_th.getProof());
    pfs.push_back(i_th.getProof());
    pfs.push_back(l_th.getProof());
    pfs.push_back(r_th.getProof());
    pf = newPf("conf_iffr", exprs, pfs);
  }

  return newTheorem(d_em->falseExpr(), a, pf);
}

Theorem
SearchEngineTheoremProducer::propIterIte(const Theorem& iter_th,
                                         bool left,
                                         const Theorem& if_th,
                                         const Theorem& then_th)
{
  const Expr& iter_e(iter_th.getExpr());

  bool v0 = if_th.proves(iter_e[1]);
  bool v1 = then_th.proves(iter_e[left ? 2 : 3]);

  if (CHECK_PROOFS) {
    CHECK_SOUND(iter_e.getKind() == ITE_R &&
                (v0 || if_th.refutes(iter_e[1])) &&
                (v1 || then_th.refutes(iter_e[left ? 2 : 3])) &&
                v0 == left,
                "SearchEngineTheoremProducer::propIterIte");
  }

  Assumptions a;
  Proof pf;
  if (withAssumptions()) {
    a.add(iter_th);
    a.add(if_th);
    a.add(then_th);
  }

  if (withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(iter_th.getExpr());
    exprs.push_back(if_th.getExpr());
    exprs.push_back(then_th.getExpr());
    pfs.push_back(iter_th.getProof());
    pfs.push_back(if_th.getProof());
    pfs.push_back(then_th.getProof());
    pf = newPf("prop_iter_ite", exprs, pfs);
  }

  return newTheorem(v1 ? iter_e[0] : iter_e[0].negate(), a, pf);
}

void
SearchEngineTheoremProducer::propIterIfThen(const Theorem& iter_th,
                                            bool left,
                                            const Theorem& ite_th,
                                            const Theorem& then_th,
                                            Theorem* if_th,
                                            Theorem* else_th)
{
  const Expr& iter_e(iter_th.getExpr());

  bool v0 = ite_th.proves(iter_e[0]);
  bool v1 = then_th.proves(iter_e[left ? 2 : 3]);

  if (CHECK_PROOFS) {
    CHECK_SOUND(iter_e.getKind() == ITE_R &&
                (v0 || ite_th.refutes(iter_e[0])) &&
                (v1 || then_th.refutes(iter_e[left ? 2 : 3])) &&
                v0 != v1,
                "SearchEngineTheoremProducer::propIterIfThen");
  }

  Assumptions a;
  Proof pf;
  if (withAssumptions()) {
    a.add(iter_th);
    a.add(ite_th);
    a.add(then_th);
  }

  if (withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(iter_th.getExpr());
    exprs.push_back(ite_th.getExpr());
    exprs.push_back(then_th.getExpr());
    pfs.push_back(iter_th.getProof());
    pfs.push_back(ite_th.getProof());
    pfs.push_back(then_th.getExpr());
    pf = newPf("prop_iter_if_then", exprs, pfs);
  }

  if (if_th)
    *if_th = newTheorem(left ? iter_e[1].negate() : iter_e[1], a, pf);
  if (else_th)
    *else_th = newTheorem(v0 ? iter_e[left ? 3 : 2] : iter_e[left ? 3 : 2].negate(), a, pf);
}

Theorem
SearchEngineTheoremProducer::propIterThen(const Theorem& iter_th,
                                          const Theorem& ite_th,
                                          const Theorem& if_th)
{
  const Expr& iter_e(iter_th.getExpr());

  bool v0 = ite_th.proves(iter_e[0]);
  bool v1 = if_th.proves(iter_e[1]);

  if (CHECK_PROOFS) {
    CHECK_SOUND(iter_e.getKind() == ITE_R &&
                (v0 || ite_th.refutes(iter_e[0])) &&
                (v1 || if_th.refutes(iter_e[1])),
                "SearchEngineTheoremProducer::propIterThen");
  }

  Assumptions a;
  Proof pf;
  if (withAssumptions()) {
    a.add(iter_th);
    a.add(ite_th);
    a.add(if_th);
  }

  if (withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(iter_th.getExpr());
    exprs.push_back(ite_th.getExpr());
    exprs.push_back(if_th.getExpr());
    pfs.push_back(iter_th.getProof());
    pfs.push_back(ite_th.getProof());
    pfs.push_back(if_th.getExpr());
    pf = newPf("prop_iter_then", exprs, pfs);
  }

  return newTheorem(v1 ?
                    (v0 ? iter_e[2] : iter_e[2].negate()) :
                    (v0 ? iter_e[3] : iter_e[3].negate()), a, pf);
}

Theorem
SearchEngineTheoremProducer::confIterThenElse(const Theorem& iter_th,
                                              const Theorem& ite_th,
                                              const Theorem& then_th,
                                              const Theorem& else_th)
{
  const Expr& iter_e(iter_th.getExpr());

  bool v0 = ite_th.proves(iter_e[0]);
  bool v1 = then_th.proves(iter_e[2]);
  bool v2 = else_th.proves(iter_e[3]);

  if (CHECK_PROOFS) {
    CHECK_SOUND(iter_e.getKind() == ITE_R &&
                (v0 || ite_th.refutes(iter_e[0])) &&
                (v1 || then_th.refutes(iter_e[2])) &&
                (v2 || else_th.refutes(iter_e[3])) &&
                ((v0 && !v1 && !v2) || (!v0 && v1 && v2)),
                "SearchEngineTheoremProducer::confIterThenElse");
  }

  Assumptions a;
  Proof pf;
  if (withAssumptions()) {
    a.add(iter_th);
    a.add(ite_th);
    a.add(then_th);
    a.add(else_th);
  }

  if (withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(iter_th.getExpr());
    exprs.push_back(ite_th.getExpr());
    exprs.push_back(then_th.getExpr());
    exprs.push_back(else_th.getExpr());
    pfs.push_back(iter_th.getProof());
    pfs.push_back(ite_th.getProof());
    pfs.push_back(then_th.getExpr());
    pfs.push_back(else_th.getExpr());
    pf = newPf("conf_iter_then_else", exprs, pfs);
  }

  return newTheorem(d_em->falseExpr(), a, pf);
}

Theorem
SearchEngineTheoremProducer::confIterIfThen(const Theorem& iter_th,
                                            bool left,
                                            const Theorem& ite_th,
                                            const Theorem& if_th,
                                            const Theorem& then_th)
{
  const Expr& iter_e(iter_th.getExpr());

  bool v0 = ite_th.proves(iter_e[0]);
  bool v1 = if_th.proves(iter_e[1]);
  bool v2 = then_th.proves(iter_e[left ? 2 : 3]);

  if (CHECK_PROOFS) {
    CHECK_SOUND(iter_e.getKind() == ITE_R &&
                (v0 || ite_th.refutes(iter_e[0])) &&
                (v1 || if_th.refutes(iter_e[1])) &&
                (v2 || then_th.refutes(iter_e[left ? 2 : 3])) &&
                v1 == left && v0 != v2,
                "SearchEngineTheoremProducer::confIterThenElse");
  }

  Assumptions a;
  Proof pf;
  if (withAssumptions()) {
    a.add(iter_th);
    a.add(ite_th);
    a.add(if_th);
    a.add(then_th);
  }

  if (withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.push_back(iter_th.getExpr());
    exprs.push_back(ite_th.getExpr());
    exprs.push_back(if_th.getExpr());
    exprs.push_back(then_th.getExpr());
    pfs.push_back(iter_th.getProof());
    pfs.push_back(ite_th.getProof());
    pfs.push_back(if_th.getExpr());
    pfs.push_back(then_th.getExpr());
    pf = newPf("conf_iter_then_else", exprs, pfs);
  }

  return newTheorem(d_em->falseExpr(), a, pf);
}

// "Conflict" rule (all literals in a clause become FALSE)
// { G_j |- !l_j, j in [1..n] } , G |- (OR l_1 ... l_n) ==> FALSE
Theorem
SearchEngineTheoremProducer::conflictRule(const std::vector<Theorem>& thms,
                                          const Theorem& clause) {
  Expr e(clause.getExpr());
  if(CHECK_PROOFS) {
    // Soundness check: first, check the form of the 'clause' theorem
    CHECK_SOUND(e.isOr(),
                "SearchEngineTheoremProducer::unitProp: "
                "bad theorem in clause = "+clause.toString());
    // Now, check correspondence of thms to the disjunction
    CHECK_SOUND(((int)thms.size()) == e.arity(),
                "SearchEngineTheoremProducer::conflictRule: "
                "wrong number of theorems"
                "\n  thms.size = " + int2string(thms.size())
                +"\n  clause.arity = " + int2string(e.arity()));

    for(unsigned j=0; j<thms.size(); j++) {
      Expr ej(e[j]), ek(thms[j].getExpr());
      CHECK_SOUND((ej.isNot() && ej[0] == ek) || (ek.isNot() && ej == ek[0]),
                  "SearchEngineTheoremProducer::conflictRule: "
                  "wrong theorem["+int2string(j)+"]"
                  "\n  thm = " + thms[j].toString() +
                  "\n  literal = " + e[j].toString() +
                  "\n  clause = " + clause.toString());
    }
  }

  Assumptions a(thms);
  a.add(clause);
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> exprs;
    exprs.reserve(thms.size() + 1);
    pfs.reserve(thms.size()+1);
    const vector<Theorem>::const_iterator iend = thms.end();
    for(vector<Theorem>::const_iterator i=thms.begin(); i!=iend; ++i) {
      exprs.push_back(i->getExpr());
      pfs.push_back(i->getProof());
    }
    exprs.push_back(clause.getExpr());
    pfs.push_back(clause.getProof());
    pf = newPf("conflict", exprs, pfs);
  }
  return newTheorem(d_em->falseExpr(), a, pf);
}


///////////////////////////////////////////////////////////////////////
//// Conjunctive Normal Form (CNF) proof rules
///////////////////////////////////////////////////////////////////////
Theorem
SearchEngineTheoremProducer::andCNFRule(const Theorem& thm) {
  return opCNFRule(thm, AND, "and_cnf_rule");
}

Theorem
SearchEngineTheoremProducer::orCNFRule(const Theorem& thm) {
  return opCNFRule(thm, OR, "or_cnf_rule");
}

Theorem
SearchEngineTheoremProducer::impCNFRule(const Theorem& thm) {
  return opCNFRule(thm, IMPLIES, "implies_cnf_rule");
}

Theorem
SearchEngineTheoremProducer::iffCNFRule(const Theorem& thm) {
  return opCNFRule(thm, IFF, "iff_cnf_rule");
}

Theorem
SearchEngineTheoremProducer::iteCNFRule(const Theorem& thm) {
  return opCNFRule(thm, ITE, "ite_cnf_rule");
}


Theorem
SearchEngineTheoremProducer::iteToClauses(const Theorem& ite) {
  const Expr& iteExpr = ite.getExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(iteExpr.isITE() && iteExpr.getType().isBool(),
                "SearchEngineTheoremProducer::iteToClauses("+iteExpr.toString()
                +")\n Argument must be a Boolean ITE");
  }
  const Expr& cond = iteExpr[0];
  const Expr& t1 = iteExpr[1];
  const Expr& t2 = iteExpr[2];

  Proof pf;
  if(withProof())
    pf = newPf("ite_to_clauses", iteExpr, ite.getProof());
  return newTheorem((cond.negate() || t1) && (cond || t2), ite.getAssumptionsRef(), pf);
}


Theorem
SearchEngineTheoremProducer::iffToClauses(const Theorem& iff) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(iff.isRewrite() && iff.getLHS().getType().isBool(),
                "SearchEngineTheoremProducer::iffToClauses("+iff.getExpr().toString()
                +")\n Argument must be a Boolean IFF");
  }
  const Expr& t1 = iff.getLHS();
  const Expr& t2 = iff.getRHS();

  Proof pf;
  if(withProof())
    pf = newPf("iff_to_clauses", iff.getExpr(), iff.getProof());
  return newTheorem((t1.negate() || t2) && (t1 || t2.negate()), iff.getAssumptionsRef(), pf);
}


/////////////////////////////////////////////////////////////////////////
//// helper functions for CNF (Conjunctive Normal Form) conversion
/////////////////////////////////////////////////////////////////////////
Theorem
SearchEngineTheoremProducer::opCNFRule(const Theorem& thm, 
                                       int kind,
                                       const string& ruleName) {
  TRACE("mycnf", "opCNFRule["+d_em->getKindName(kind)+"](",
        thm.getExpr(), ") {");
  ExprMap<Expr> localCache;
  if(CHECK_PROOFS) {
    Expr phiIffVar = thm.getExpr();
    CHECK_SOUND(phiIffVar.isIff(),
                "SearchEngineTheoremProducer::opCNFRule("
                +d_em->getKindName(kind)+"): "
                "input must be an IFF: thm = " + phiIffVar.toString());
    CHECK_SOUND(phiIffVar[0].getKind() == kind,
                "SearchEngineTheoremProducer::opCNFRule("
                +d_em->getKindName(kind)+"): "
                "input phi has wrong kind: thm = " + phiIffVar.toString());
    CHECK_SOUND(phiIffVar[0] != phiIffVar[1],
                "SearchEngineTheoremProducer::opCNFRule("
                +d_em->getKindName(kind)+"): "
                "wrong input thm = " + phiIffVar.toString());
    for(Expr::iterator it=phiIffVar[0].begin(), itend=phiIffVar[0].end();
        it!=itend;++it){
      CHECK_SOUND(phiIffVar[1] != *it,
                  "SearchEngineTheoremProducer::opCNFRule("
                  +d_em->getKindName(kind)+"): "
                  "wrong input thm = " + phiIffVar.toString());
    }
  }
  const Expr& phi = thm.getExpr()[0];
  const Expr& phiVar = thm.getExpr()[1];

  std::vector<Expr> boundVars;
  std::vector<Expr> boundVarsAndLiterals;
  std::vector<Expr> equivs;
  for(Expr::iterator i=phi.begin(), iend=phi.end(); i != iend; i++) {
    // First, strip the negation and check if the formula is atomic
    Expr tmp(*i);
    while(tmp.isNot())
      tmp = tmp[0];

    if(tmp.isPropAtom())
      boundVarsAndLiterals.push_back(*i); 
    else
      boundVarsAndLiterals.push_back(findInLocalCache(*i, localCache,
                                                      boundVars));
  }
  
  for(ExprMap<Expr>::iterator it=localCache.begin(), itend=localCache.end(); 
      it != itend; it++) {
    DebugAssert((*it).second.isIff(),
                "SearchEngineTheoremProducer::opCNFRule: " +
                (*it).second.toString());
    DebugAssert(!(*it).second[0].isPropLiteral() && 
                (*it).second[1].isAbsLiteral(),
                "SearchEngineTheoremProducer::opCNFRule: " +
                (*it).second.toString());
    equivs.push_back((*it).second);
  }
  
  DebugAssert(boundVarsAndLiterals.size() == (unsigned)phi.arity(),
              "SearchEngineTheoremProducer::opCNFRule: "
              "wrong size of boundvars: phi = " + phi.toString());
  
  DebugAssert(boundVars.size() == equivs.size(),
              "SearchEngineTheoremProducer::opCNFRule: "
              "wrong size of boundvars: phi = " + phi.toString());

  Expr cnfInput = phi.arity() > 0 ? Expr(phi.getOp(), boundVarsAndLiterals) : phi;
  Expr  result = convertToCNF(phiVar, cnfInput);
  if(boundVars.size() > 0)
    result =
      d_em->newClosureExpr(EXISTS, boundVars, result.andExpr(andExpr(equivs)));
  
  Proof pf;
  if(withProof())
    pf = newPf(ruleName, thm.getExpr(), thm.getProof());
  Theorem res(newTheorem(result, thm.getAssumptionsRef(), pf));
  TRACE("mycnf", "opCNFRule["+d_em->getKindName(kind)+"] => ", res.getExpr(),
        " }");
  return res;
}

//! produces the CNF for the formula  v <==> phi 
Expr SearchEngineTheoremProducer::convertToCNF(const Expr& v, const Expr & phi) {
  //we assume that v \iff phi. v is the newVar corresponding to phi
  
  Expr::iterator i = phi.begin(), iend = phi.end();
  std::vector<Expr> clauses;
  std::vector<Expr> lastClause;
  switch(phi.getKind()) {
  case AND: {
    const Expr& negV = v.negate();
    lastClause.push_back(v);
    for(;i!=iend; ++i) {
      lastClause.push_back(i->negate());
    }
    clauses.push_back(orExpr(lastClause));
  }
    break;
  case OR:{
    lastClause.push_back(v.negate());
    for(;i!=iend; ++i) {
      clauses.push_back(v.orExpr(i->negate()));
      lastClause.push_back(*i);
    }
    clauses.push_back(orExpr(lastClause));
  }
    break;
  case IFF: {
    const Expr& v1 = phi[0];
    const Expr& v2 = phi[1];
    Expr negV = v.negate();    
    Expr negv1 = v1.negate();
    Expr negv2 = v2.negate();
    clauses.push_back(Expr(OR, negV, negv1, v2));
    clauses.push_back(Expr(OR, negV, v1, negv2));
    clauses.push_back(Expr(OR, v, v1, v2));
    clauses.push_back(Expr(OR, v, negv1, negv2));
  } break;
  case IMPLIES:{
    const Expr& v1 = phi[0];
    const Expr& v2 = phi[1];
    Expr negV = v.negate();    
    Expr negv1 = v1.negate();
    Expr negv2 = v2.negate();
    clauses.push_back(Expr(OR, negV, negv1, v2));
    clauses.push_back(v.orExpr(v1));
    clauses.push_back(v.orExpr(negv2));
  }
    break;
  case ITE: {
    const Expr& v1 = phi[0];
    const Expr& v2 = phi[1];
    const Expr& v3 = phi[2];
    const Expr& negV = v.negate();
    const Expr& negv1 = v1.negate();
    const Expr& negv2 = v2.negate();
    const Expr& negv3 = v3.negate();
    clauses.push_back(Expr(OR, negV, negv1, v2));
    clauses.push_back(Expr(OR, negV, v1, v3));
    clauses.push_back(Expr(OR, v, negv1, negv2));
    clauses.push_back(Expr(OR, v, v1, negv3));
  }
    break;
  default:
    DebugAssert(false, "SearchEngineTheoremProducer::convertToCNF: "
                "bad operator in phi = "+phi.toString());
    break;
  }
  return andExpr(clauses);
}

///////////////////////////////////////////////////////////////////////
// helper functions for CNF converters
///////////////////////////////////////////////////////////////////////

Expr SearchEngineTheoremProducer::findInLocalCache(const Expr& i, 
                                                   ExprMap<Expr>& localCache,
                                                   vector<Expr>& boundVars) {
  TRACE("mycnf", "findInLocalCache(", i.toString(), ") { ");
  Expr boundVar;
  unsigned int negationDepth = 0;
  ExprMap<Expr>::iterator it;
 
  Expr phi = i;
  while(phi.isNot()) {
    phi = phi[0];
    negationDepth++;
  }
  
  it = localCache.find(phi);
  Expr v;
  if(it != localCache.end()) {
    v = ((*it).second)[1];
    IF_DEBUG(debugger.counter("CNF Local Cache Hits")++;)
  }
  else {
    v = d_em->newBoundVarExpr(i.getType());
    boundVars.push_back(v);
    localCache[phi] = phi.iffExpr(v);
  }
  if(negationDepth % 2 != 0)
    v = !v;
  TRACE("mycnf", "findInLocalCache => ", v, " }");
  return v;
}



// for LFSC proof style, by yeting


// theorem for minisat generated proofs,  by yeting
Theorem SearchEngineTheoremProducer::satProof(const Expr& queryExpr, const Proof& satProof) {
  Proof pf;
  if(withProof())
    pf = newPf("minisat_proof", queryExpr, satProof);

  if ((d_tm->getFlags()["lfsc-mode"]).getInt()!= 0)
  {
    // UNCOMMENT THIS FOR LFSC

    if(!lfsc_called){
      int lfscm = (d_tm->getFlags()["lfsc-mode"]).getInt();
      std::vector<Expr> assumps;
      search_engine->getUserAssumptions(assumps);

      Expr pf_expr =  pf.getExpr()[2] ;
      if( lfscm == -1 ){
        cout << "CVC3 Proof: ";
        cout << pf.getExpr() << endl;
      }else{
        LFSCPrinter* lfsc_printer = new LFSCPrinter(pf_expr, queryExpr, assumps, lfscm, d_commonRules);
        lfsc_printer->print_LFSC(pf_expr);
        lfsc_called = true;
        exit( 0 );
      }
    }

  }

  return newTheorem(queryExpr, Assumptions::emptyAssump() , pf);
}


//  LocalWords:  clc
