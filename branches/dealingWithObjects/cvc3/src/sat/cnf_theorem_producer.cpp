/*****************************************************************************/
/*!
 *\file cnf_theorem_producer.cpp
 *\brief Implementation of CNF_TheoremProducer
 *
 * Author: Clark Barrett
 *
 * Created: Thu Jan  5 05:49:24 2006
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

#include "cnf_manager.h"

#define _CVC3_TRUSTED_
#include "cnf_theorem_producer.h"


using namespace std;
using namespace CVC3;
using namespace SAT;


/////////////////////////////////////////////////////////////////////////////
// class CNF_Manager trusted methods
/////////////////////////////////////////////////////////////////////////////


CNF_Rules* CNF_Manager::createProofRules(TheoremManager* tm, const CLFlags& flags) {
  return new CNF_TheoremProducer(tm, flags);
}


/////////////////////////////////////////////////////////////////////////////
// Proof rules
/////////////////////////////////////////////////////////////////////////////



void CNF_TheoremProducer::getSmartClauses(const Theorem& thm, vector<Theorem>& clauses)
{
  //  DebugAssert(!thm.getExpr().isDeductionLiteral(), "Expected unproved expr");
  vector<Theorem> assumptions;
  thm.clearAllFlags();
  thm.GetSatAssumptions(assumptions);  
//   Proof pf;
//   if (withProof()) {
//     pf = newPf("learned_clause_smart", thm.getProof());
//   }
  Theorem thm2; 
  vector<Expr> TempVec;
  vector<Proof> pfs; 
  if (!thm.getExpr().isFalse()) {
    TempVec.push_back(thm.getExpr());
    pfs.push_back(thm.getProof());
  }
  for (vector<Theorem>::size_type i = 0; i < assumptions.size(); i++) {
    if (thm.getExpr() == assumptions[i].getExpr()) {
      // skip this clause as it is trivial
      if (!(assumptions[i].isAssump())) {
        getSmartClauses(assumptions[i], clauses);
      }
      return;
    }
    TempVec.push_back(assumptions[i].getExpr().negate());
    pfs.push_back(assumptions[i].getProof());
  }

  Proof pf;
  if (TempVec.size() == 1){
    if (withProof()) {
      pf = newPf("learned_clause_smart", TempVec[0], pfs);
    }
    thm2 = newTheorem(TempVec[0], Assumptions::emptyAssump(), pf);
  }
  else if (TempVec.size() > 1) {   
    if (withProof()) {
      pf = newPf("learned_clause_smart", Expr(OR, TempVec), pfs);
    }
    thm2 = newTheorem(Expr(OR, TempVec), Assumptions::emptyAssump(), pf);
  }
  else {
    FatalAssert(false, "Should be unreachable");
  }
  thm2.setQuantLevel(thm.getQuantLevel());
  clauses.push_back(thm2);
  //  thm.getExpr().setDeductionLiteral();

  for (vector<Theorem>::iterator itr = assumptions.begin(); itr != assumptions.end(); itr++) {
    if (!((*itr).isAssump())) {// && !(*itr).getExpr().isDeductionLiteral()) {
      getSmartClauses((*itr), clauses);
    }
  }
}	  


void CNF_TheoremProducer::learnedClauses(const Theorem& thm,
                                         vector<Theorem>& clauses,
                                         bool newLemma)
{
  IF_DEBUG(if(debugger.trace("cnf proofs")) {
    ostream& os = debugger.getOS();
    os << "learnedClause {" << endl;
    os << thm;
  })
    
  if (!newLemma && d_smartClauses) {
    getSmartClauses(thm, clauses);
    return;
  }

//   if (newLemma || d_flags["dynack"].getInt() <= 0) {
// 	  if (NewClausel == true) {
// 	      return;
//     }

  vector<Expr> assumptions;
  Proof pf;
  thm.getLeafAssumptions(assumptions, true /*negate*/);

  vector<Expr>::iterator iend = assumptions.end();
  for (vector<Expr>::iterator i = assumptions.begin();
       i != iend; ++i) {
    DebugAssert(i->isAbsLiteral(), "Expected only literal assumptions");
  }

  if (!thm.getExpr().isFalse())
    assumptions.push_back(thm.getExpr());

  DebugAssert(assumptions.size() > 0, "Expected at least one entry");

  Theorem thm2;
  if (assumptions.size() == 1) {
    if(withProof()) {
      pf = newPf("learned_clause", thm.getProof());
    }
    thm2 = newTheorem(assumptions[0], Assumptions::emptyAssump(), pf);
  }
  else {
    Expr clauseExpr = Expr(OR, assumptions);
    if(withProof()) {
      pf = newPf("learned_clause", thm.getProof());
    }
    thm2 = newTheorem(clauseExpr, Assumptions::emptyAssump(), pf);
  }
  thm2.setQuantLevel(thm.getQuantLevel());
  clauses.push_back(thm2);
//   }
//   else {

//     vector<Expr> congruences;

//     thm.getAssumptionsAndCong(assumptions, congruences, true /*negate*/);

//     vector<Expr>::iterator i = assumptions.begin(), iend = assumptions.end();
//     for (; i != iend; ++i) {
//       DebugAssert(i->isAbsLiteral(), "Expected only literal assumptions");
//     }

//     if (!thm.getExpr().isFalse())
//       assumptions.push_back(thm.getExpr());

//     if(withProof()) {
//       pf = newPf("learned_clause", thm.getProof());
//     }

//     DebugAssert(assumptions.size() > 0, "Expected at least one entry");

//     Theorem thm2;
//     if (assumptions.size() == 1) {
//       Expr clauseExpr = assumptions[0];
//       if(withProof()) {
// 	pf = newPf("learned_clause", clauseExpr, thm.getProof());
//       }
//       thm2 = newTheorem(clauseExpr, Assumptions::emptyAssump(), pf);
//     }
//     else {
//       Expr clauseExpr = Expr(OR, assumptions);
//       if(withProof()) {
// 	pf = newPf("learned_clause", clauseExpr, thm.getProof());
//       }
//       thm2 = newTheorem(clauseExpr, Assumptions::emptyAssump(), pf);
//     }
//     thm2.setQuantLevel(thm.getQuantLevel());
//     clauses.push_back(thm2);

//     for (i = congruences.begin(), iend = congruences.end(); i != iend; ++i) {
//       if (withProof()) {
//         pf = newPf("congruence", *i);
//       }
//       thm2 = newTheorem(*i, Assumptions::emptyAssump(), pf);
//       thm2.setQuantLevel(thm.getQuantLevel());
//       clauses.push_back(thm2);
//     }
//   }
}


Theorem CNF_TheoremProducer::ifLiftRule(const Expr& e, int itePos) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getType().isBool(),
		"CNF_TheoremProducer::ifLiftRule("
		"input must be a Predicate: e = " + e.toString()+")");
    CHECK_SOUND(itePos >= 0, "itePos negative"+int2string(itePos));
    CHECK_SOUND(e.arity() > itePos && e[itePos].isITE(),
		"CNF_TheoremProducer::ifLiftRule("
		"input does not have an ITE: e = " + e.toString()+")");
  }
  const Expr& ite = e[itePos];
  const Expr& cond = ite[0];
  const Expr& t1 = ite[1];
  const Expr& t2 = ite[2];

  if(CHECK_PROOFS) {
    CHECK_SOUND(cond.getType().isBool(),
		"CNF_TheoremProducer::ifLiftRule("
		"input does not have an ITE: e = " + e.toString()+")");
  }    

  vector<Expr> k1 = e.getKids();
  Op op(e.getOp());

  k1[itePos] = t1;
  Expr pred1 =  Expr(op, k1);

  k1[itePos] = t2;
  Expr pred2 =  Expr(op, k1);

  Expr resultITE = cond.iteExpr(pred1, pred2);

  Proof pf;
  if (withProof())
    pf = newPf("if_lift_rule", e, resultITE, d_em->newRatExpr(itePos));
  return newRWTheorem(e, resultITE, Assumptions::emptyAssump(), pf);
}

Theorem CNF_TheoremProducer::CNFtranslate(const Expr& before, 
					  const Expr& after, 
					  std::string reason, 
					  int pos,
					  const vector<Theorem>& thms) {
  //well, this is assert the e as a theorem without any justification.
  //change this as soon as possible
  //  cout << "###" << before; 
  Proof pf;
  if (withProof()){
    vector<Expr> chs ;
    chs.push_back(d_em->newStringExpr(reason));
    chs.push_back(before);
    chs.push_back(after);
    chs.push_back(d_em->newRatExpr(pos));
    vector<Proof> pfs;
    for(vector<Theorem>::const_iterator i = thms.begin(), iend= thms.end();
	i != iend; i++){
      pfs.push_back((*i).getProof());
    }
    pf = newPf("CNF", chs, pfs );
  }
  return newTheorem(after, Assumptions(thms), pf);
}

Theorem CNF_TheoremProducer::CNFITEtranslate(const Expr& before, 
					     const vector<Expr>& after,
					     const vector<Theorem>& thms,
					     int pos){
  DebugAssert(3 == after.size(), "why this happens");
  DebugAssert(3 == thms.size(), "why this happens");

  Proof pf;
  if (withProof()){
    DebugAssert(thms[0].getRHS() == after[0] , "this never happens");
    DebugAssert(thms[1].getRHS() == after[1] , "this never happens");
    DebugAssert(thms[2].getRHS() == after[2] , "this never happens");
    DebugAssert(thms[0].getLHS() == before[0] , "this never happens");
    DebugAssert(thms[1].getLHS() == before[1] , "this never happens");
    DebugAssert(thms[2].getLHS() == before[2] , "this never happens");
    
    vector<Expr> chs ;
    chs.push_back(before);
    chs.push_back(after[0]);
    chs.push_back(after[1]);
    chs.push_back(after[2]);
    chs.push_back(d_em->newRatExpr(pos));
    vector<Proof> pfs;
    pfs.push_back(thms[0].getProof());
    pfs.push_back(thms[1].getProof());
    pfs.push_back(thms[2].getProof());
    pf = newPf("CNFITE", chs, pfs );
  }

  Expr newe0 = after[0];
  Expr afterExpr = newe0.iteExpr(after[1],after[2]);
  //we should produce a newRWTheorm whenever possible and then use iffmp rule to get the desired result
  return newTheorem(afterExpr, Assumptions(thms), pf);
}
  




// because the way of cnf translation, add unit means the theorem from other parts of cvc3, not from cnf translation
Theorem CNF_TheoremProducer::CNFAddUnit(const Theorem& thm){
  
  //wrap the thm so the hol light translator know this
  Proof pf;
  if (withProof()){
    pf = newPf("cnf_add_unit", thm.getExpr(), thm.getProof() );
  }
  return newTheorem(thm.getExpr(), thm.getAssumptionsRef(), pf);
}

Theorem CNF_TheoremProducer::CNFConvert(const Expr& e, const Theorem& thm){
  
  //wrap the thm so the hol light translator know this
  Proof pf;
  if (withProof()){
    pf = newPf("cnf_convert", e, thm.getExpr(), thm.getProof() );
  }
  DebugAssert(thm.getExpr().isOr(),"convert is not or exprs");
  return newTheorem(thm.getExpr(), thm.getAssumptionsRef(), pf);
}


