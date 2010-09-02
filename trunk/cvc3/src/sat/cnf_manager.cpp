/*****************************************************************************/
/*!
 *\file cnf_manager.cpp
 *\brief Implementation of CNF_Manager
 *
 * Author: Clark Barrett
 *
 * Created: Thu Jan  5 02:30:02 2006
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 */
/*****************************************************************************/


#include "cnf_manager.h"
#include "cnf_rules.h"
#include "common_proof_rules.h"
#include "theorem_manager.h"
#include "vc.h"
#include "command_line_flags.h"


using namespace std;
using namespace CVC3;
using namespace SAT;


CNF_Manager::CNF_Manager(TheoremManager* tm, Statistics& statistics,
                         const CLFlags& flags)
  : d_vc(NULL),
    d_commonRules(tm->getRules()),
    //    d_theorems(tm->getCM()->getCurrentContext()),
    d_clauseIdNext(0),
    //    d_translated(tm->getCM()->getCurrentContext()),
    d_bottomScope(-1),
    d_statistics(statistics),
    d_flags(flags),
    d_nullExpr(tm->getEM()->getNullExpr()),
    d_cnfCallback(NULL)
{
  d_rules = createProofRules(tm, flags);
  // Push dummy varinfo onto d_varInfo since Var's are indexed from 1 not 0
  Varinfo v;
  d_varInfo.push_back(v);
  if (flags["minimizeClauses"].getBool()) {
    CLFlags flags = ValidityChecker::createFlags();
    flags.setFlag("minimizeClauses",false);
    d_vc = ValidityChecker::create(flags);
  }
}


CNF_Manager::~CNF_Manager()
{
  if (d_vc) delete d_vc;
  delete d_rules;
}


void CNF_Manager::registerAtom(const Expr& e, const Theorem& thm)
{
  DebugAssert(!e.isRegisteredAtom() || e.isUserRegisteredAtom(), "Atom already registered");
  if (d_cnfCallback && !e.isRegisteredAtom()) d_cnfCallback->registerAtom(e, thm);
}


Theorem CNF_Manager::replaceITErec(const Expr& e, Var v, bool translateOnly)
{
  // Quick exit for atomic expressions
  if (e.isAtomic()) return d_commonRules->reflexivityRule(e);

  // Check cache
  Theorem thm;
  bool foundInCache = false;
  ExprHashMap<Theorem>::iterator iMap = d_iteMap.find(e);
  if (iMap != d_iteMap.end()) {
    thm = (*iMap).second;
    foundInCache = true;
  }

  if (e.getKind() == ITE) {
    // Replace non-Bool ITE expressions
    DebugAssert(!e.getType().isBool(), "Expected non-Bool ITE");
    // generate e = x for new x
    if (!foundInCache) thm = d_commonRules->varIntroSkolem(e);
    Theorem thm2 = d_commonRules->symmetryRule(thm);
    thm2 = d_commonRules->iffMP(thm2, d_rules->ifLiftRule(thm2.getExpr(), 1));
    d_translateQueueVars.push_back(v);
    d_translateQueueThms.push_back(thm2);
    d_translateQueueFlags.push_back(translateOnly);
  }
  else {
    // Recursively traverse, replacing ITE's
    vector<Theorem> thms;
    vector<unsigned> changed;
    unsigned index = 0;
    Expr::iterator i, iend;
    if (foundInCache) {
      for(i = e.begin(), iend = e.end(); i!=iend; ++i, ++index) {
        replaceITErec(*i, v, translateOnly);
      }
    }
    else {
      for(i = e.begin(), iend = e.end(); i!=iend; ++i, ++index) {
        thm = replaceITErec(*i, v, translateOnly);
        if (!thm.isRefl()) {
          thms.push_back(thm);
          changed.push_back(index);
        }
      }
      if(changed.size() > 0) {
        thm = d_commonRules->substitutivityRule(e, changed, thms);
      }
      else thm = d_commonRules->reflexivityRule(e);
    }
  }

  // Update cache and return
  if (!foundInCache) d_iteMap[e] = thm;
  return thm;
}


Expr CNF_Manager::concreteExpr(const CVC3::Expr& e, const Lit& literal){
  if ( e.isTrue() || e.isFalse() || 
       (e.isNot() && (e[0].isTrue() || e[0].isFalse()))) 
    return e;
  else 
    return concreteLit(literal);
}

Theorem CNF_Manager::concreteThm(const CVC3::Expr& ine){
  Theorem ret = d_iteMap[ine];
  if (ret.isNull()) {
    ret  = d_commonRules->reflexivityRule(ine);
  }
  return ret;
}

Lit CNF_Manager::translateExprRec(const Expr& e, CNF_Formula& cnf, const Theorem& thmIn)
{
  if (e.isFalse()) return Lit::getFalse();
  if (e.isTrue()) return Lit::getTrue();
  if (e.isNot()) return !translateExprRec(e[0], cnf, thmIn);

  ExprHashMap<Var>::iterator iMap = d_cnfVars.find(e);

  if (e.isTranslated()) {
    DebugAssert(iMap != d_cnfVars.end(), "Translated expr should be in map");
    return Lit((*iMap).second);
  }
  else e.setTranslated(d_bottomScope);

  Var v(int(d_varInfo.size()));
  bool translateOnly = false;

  if (iMap != d_cnfVars.end()) {
    v = (*iMap).second;
    translateOnly = true;
    d_varInfo[v].fanouts.clear();
  }
  else {
    d_varInfo.resize(v+1);
    d_varInfo.back().expr = e;
    d_cnfVars[e] = v;
  }

  Expr::iterator i, iend;
  bool isAnd = false;
  switch (e.getKind()) {
    case AND:
      isAnd = true;
    case OR: {
      
      vector<Lit> lits;
      unsigned idx;
      for (i = e.begin(), iend = e.end(); i != iend; ++i) {
        lits.push_back(translateExprRec(*i, cnf, thmIn));
      }

      vector<Expr> new_chls;
      vector<Theorem> thms;
      for (idx = 0; idx < lits.size(); ++idx) {
	new_chls.push_back(concreteExpr(e[idx],lits[idx]));
	thms.push_back(concreteThm(e[idx]));
      }
      
      Expr after = (isAnd ? Expr(AND,new_chls) : Expr(OR,new_chls)) ;    

      //      DebugAssert(concreteExpr(e,Lit(v)) == e,"why here");

      for (idx = 0; idx < lits.size(); ++idx) {
        cnf.newClause();
        cnf.addLiteral(Lit(v),isAnd);
        cnf.addLiteral(lits[idx], !isAnd);
	
	//	DebugAssert(concreteExpr(e[idx],lits[idx]) == e[idx], "why here");

	std::string reasonStr = (isAnd ? "and_mid" : "or_mid");

	cnf.getCurrentClause().setClauseTheorem(d_rules->CNFtranslate(e, after, reasonStr, idx,thms)); // by yeting
      }

      cnf.newClause();
      cnf.addLiteral(Lit(v),!isAnd);
      for (idx = 0; idx < lits.size(); ++idx) {
        cnf.addLiteral(lits[idx], isAnd);
      }

      std::string reasonStr = (isAnd ? "and_final" : "or_final") ;   
      
      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFtranslate(e, after, reasonStr, 0, thms)); // by yeting
      DebugAssert(!d_flags["cnf-formula"].getBool(), "Found impossible case when cnf-formula is enabled");
      break;
    }
    case IMPLIES: {
      Lit arg0 = translateExprRec(e[0], cnf, thmIn);
      Lit arg1 = translateExprRec(e[1], cnf, thmIn);

      vector<Theorem> thms;
      thms.push_back(concreteThm(e[0]));
      thms.push_back(concreteThm(e[1]));

      Expr left = (concreteExpr(e[0],arg0));
      Expr right = (concreteExpr(e[1],arg1));
      Expr after = left.impExpr(right);


      //      DebugAssert(concreteExpr(e, Lit(v)) == e, "why here");
      //      DebugAssert(concreteExpr(e[0], arg0) == e[0], "why here");
      //      DebugAssert(concreteExpr(e[1], arg1) == e[1], "why here");

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0);

      cnf.getCurrentClause().setClauseTheorem( d_rules->CNFtranslate(e, after, "imp", 0,thms)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg1,true);

      cnf.getCurrentClause().setClauseTheorem( d_rules->CNFtranslate(e, after, "imp", 1, thms)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1);

      cnf.getCurrentClause().setClauseTheorem( d_rules->CNFtranslate(e, after, "imp", 2,thms)); // by yeting
      DebugAssert(!d_flags["cnf-formula"].getBool(), "Found impossible case when cnf-formula is enabled");
      break;
    }
    case IFF: {
      Lit arg0 = translateExprRec(e[0], cnf, thmIn);
      Lit arg1 = translateExprRec(e[1], cnf, thmIn);

      //      DebugAssert(concreteExpr(e, Lit(v)) == e, "why here");
      //      DebugAssert(concreteExpr(e[0], arg0) == e[0], "why here");
      //      DebugAssert(concreteExpr(e[1], arg1) == e[1], "why here");
      vector<Theorem> thms;
      thms.push_back(concreteThm(e[0]));
      thms.push_back(concreteThm(e[1]));

      Expr left = (concreteExpr(e[0],arg0));
      Expr right = (concreteExpr(e[1],arg1));
      Expr after = left.iffExpr(right);


      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg1);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFtranslate(e, after, "iff", 0, thms)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1,true);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFtranslate(e, after, "iff", 1, thms)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFtranslate(e, after, "iff", 2, thms)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg1,true);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFtranslate(e, after, "iff", 3, thms)); // by yeting
      DebugAssert(!d_flags["cnf-formula"].getBool(), "Found impossible case when cnf-formula is enabled");
      break;
    }
    case XOR: {

      Lit arg0 = translateExprRec(e[0], cnf, thmIn);
      Lit arg1 = translateExprRec(e[1], cnf, thmIn);

      //      DebugAssert(concreteExpr(e, Lit(v)) == e, "why here");
      //      DebugAssert(concreteExpr(e[0], arg0) == e[0], "why here");
      //      DebugAssert(concreteExpr(e[1], arg1) == e[1], "why here");

      vector<Theorem> thms;
      thms.push_back(concreteThm(e[0]));
      thms.push_back(concreteThm(e[1]));

      Expr left = (concreteExpr(e[0],arg0));
      Expr right = (concreteExpr(e[1],arg1));
      Expr after = left.xorExpr(right);


      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg1);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFtranslate(e, after, "xor", 0, thms)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1,true);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFtranslate(e, after, "xor", 1, thms)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFtranslate(e, after, "xor", 2, thms)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg1,true);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFtranslate(e, after, "xor", 3,thms)); // by yeting
      DebugAssert(!d_flags["cnf-formula"].getBool(), "Found impossible case when cnf-formula is enabled");
      break;
    }
    case ITE:
    {

      Lit arg0 = translateExprRec(e[0], cnf, thmIn);
      Lit arg1 = translateExprRec(e[1], cnf, thmIn);
      Lit arg2 = translateExprRec(e[2], cnf, thmIn);


      Expr aftere0 = concreteExpr(e[0], arg0);
      Expr aftere1 = concreteExpr(e[1], arg1);
      Expr aftere2 = concreteExpr(e[2], arg2);
      
      vector<Expr> after ;
      after.push_back(aftere0);
      after.push_back(aftere1);
      after.push_back(aftere2);
      
      Theorem e0thm;
      Theorem e1thm;
      Theorem e2thm;

      { e0thm = d_iteMap[e[0]];
	if (e0thm.isNull()) e0thm = d_commonRules->reflexivityRule(e[0]);
	e1thm = d_iteMap[e[1]];
	if (e1thm.isNull()) e1thm = d_commonRules->reflexivityRule(e[1]);
	e2thm = d_iteMap[e[2]];
	if (e2thm.isNull()) e2thm = d_commonRules->reflexivityRule(e[2]);
      }

      vector<Theorem> thms ;
      thms.push_back(e0thm);
      thms.push_back(e1thm);      
      thms.push_back(e2thm);

 

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg2);
      
      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFITEtranslate(e, after,thms, 1)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg2,true);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFITEtranslate(e, after,thms, 2)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1,true);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFITEtranslate(e, after,thms, 3)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFITEtranslate(e, after,thms, 4)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg1,true);
      cnf.addLiteral(arg2,true);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFITEtranslate(e, after,thms, 5)); // by yeting

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg1);
      cnf.addLiteral(arg2);

      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFITEtranslate(e, after,thms, 6)); // by yeting
      DebugAssert(!d_flags["cnf-formula"].getBool(), "Found impossible case when cnf-formula is enabled");
      break;
    }
    default:
    {
      DebugAssert(!e.isAbsAtomicFormula() || d_varInfo[v].expr == e,
                  "Corrupted Varinfo");
      if (e.isAbsAtomicFormula()) {
        registerAtom(e, thmIn);
        return Lit(v);
      }

      DebugAssert(!d_flags["cnf-formula"].getBool(), "Found impossible case when cnf-formula is enabled");

      Theorem thm = replaceITErec(e, v, translateOnly);
      const Expr& e2 = thm.getRHS();
      DebugAssert(e2.isAbsAtomicFormula(), "Expected AbsAtomicFormula");
      if (e2.isTranslated()) {
        // Ugly corner case: we happen to create an expression that has been
        // created before.  We remove the current variable and fix up the
        // translation stack.
        if (translateOnly) {
          DebugAssert(v == d_cnfVars[e2], "Expected literal match");
        }
        else {
          d_varInfo.resize(v);
          while (!d_translateQueueVars.empty() &&
                 d_translateQueueVars.back() == v) {
            d_translateQueueVars.pop_back();
          }
          DebugAssert(d_cnfVars.find(e2) != d_cnfVars.end(),
                      "Expected existing literal");
          v = d_cnfVars[e2];
          d_cnfVars[e] = v;
          while (d_translateQueueVars.size() < d_translateQueueThms.size()) {
            d_translateQueueVars.push_back(v);
          }
        }
      }
      else {
        e2.setTranslated(d_bottomScope);
        // Corner case: don't register reflexive equality
        if (!e2.isEq() || e2[0] != e2[1]) registerAtom(e2, thmIn);
        if (!translateOnly) {
          if (d_cnfVars.find(e2) == d_cnfVars.end()) {
            d_varInfo[v].expr = e2;
            d_cnfVars[e2] = v;
          }
          else {
            // Same corner case in an untranslated expr
            d_varInfo.resize(v);
            while (!d_translateQueueVars.empty() &&
                   d_translateQueueVars.back() == v) {
              d_translateQueueVars.pop_back();
            }
            v = d_cnfVars[e2];
            d_cnfVars[e] = v;
            while (d_translateQueueVars.size() < d_translateQueueThms.size()) {
              d_translateQueueVars.push_back(v);
            }
          }
        }
      }
      return Lit(v);
    }
  }

  // Record fanins / fanouts
  Lit l;
  for (i = e.begin(), iend = e.end(); i != iend; ++i) {
    l = getCNFLit(*i);
    DebugAssert(!l.isNull(), "Expected non-null literal");
    if (!translateOnly) d_varInfo[v].fanins.push_back(l);
    if (l.isVar()) d_varInfo[l.getVar()].fanouts.push_back(v);
  }
  return Lit(v);
}

Lit CNF_Manager::translateExpr(const Theorem& thmIn, CNF_Formula& cnf)
{
  Lit l;
  Var v;
  Expr e = thmIn.getExpr();
  Theorem thm;
  bool translateOnly;

  Lit ret = translateExprRec(e, cnf, thmIn);

  while (d_translateQueueVars.size()) {
    v = d_translateQueueVars.front();
    d_translateQueueVars.pop_front();
    thm = d_translateQueueThms.front();
    d_translateQueueThms.pop_front();
    translateOnly = d_translateQueueFlags.front();
    d_translateQueueFlags.pop_front();
    l = translateExprRec(thm.getExpr(), cnf, thmIn);
    cnf.newClause();
    cnf.addLiteral(l);
    cnf.registerUnit();

    Theorem newThm = d_rules->CNFAddUnit(thm);
    //    d_theorems.insert(d_clauseIdNext, thm);
    //    cnf.getCurrentClause().setClauseTheorem(thmIn); // by yeting
    cnf.getCurrentClause().setClauseTheorem(newThm); // by yeting

    /*
    cout<<"set clause theorem 1" << thm << endl;
    cout<<"set clause theorem 2 " << thmIn << endl;
    cout<<"set clause print" ;  cnf.getCurrentClause().print() ; cout<<endl;
    cout<<"set clause id " << d_clauseIdNext << endl;
    */
    if (!translateOnly) d_varInfo[v].fanins.push_back(l);
    d_varInfo[l.getVar()].fanouts.push_back(v);
  }
  return ret;
}


void CNF_Manager::cons(unsigned lb, unsigned ub, const Expr& e2, vector<unsigned>& newLits)
{
  if (lb == ub) {
    newLits.push_back(lb);
    return;
  }
  unsigned new_lb = (ub-lb+1)/2 + lb;
  unsigned index;
  QueryResult res;
  d_vc->push();
  for (index = new_lb; index <= ub; ++index) {
    d_vc->assertFormula(e2[index].negate());
  }
  res = d_vc->query(d_vc->falseExpr());
  d_vc->pop();
  if (res == VALID) {
    cons(new_lb, ub, e2, newLits);
    return;
  }

  unsigned new_ub = new_lb-1;
  d_vc->push();
  for (index = lb; index <= new_ub; ++index) {
    d_vc->assertFormula(e2[index].negate());
  }
  res = d_vc->query(d_vc->falseExpr());
  if (res == VALID) {
    d_vc->pop();
    cons(lb, new_ub, e2, newLits);
    return;
  }

  cons(new_lb, ub, e2, newLits);
  d_vc->pop();
  d_vc->push();
  for (index = 0; index < newLits.size(); ++index) {
    d_vc->assertFormula(e2[newLits[index]].negate());
  }
  cons(lb, new_ub, e2, newLits);
  d_vc->pop();
}


void CNF_Manager::convertLemma(const Theorem& thm, CNF_Formula& cnf)
{
  DebugAssert(cnf.empty(), "Expected empty cnf");
  vector<Theorem> clauses;

  d_rules->learnedClauses(thm, clauses, false);

  vector<Theorem>::iterator i = clauses.begin(), iend = clauses.end();
  for (; i < iend; ++i) {
    // for dumping lemmas:
    cnf.newClause();
    Expr e = (*i).getExpr();
    if (!e.isOr()) {
      DebugAssert(!getCNFLit(e).isNull(), "Unknown literal");
      cnf.addLiteral(getCNFLit(e));
      cnf.registerUnit();
      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFAddUnit(*i));
    }
    else {
      Expr::iterator jend = e.end();
      for (Expr::iterator j = e.begin(); j != jend; ++j) {
        DebugAssert(!getCNFLit(*j).isNull(), "Unknown literal");
        cnf.addLiteral(getCNFLit(*j));
      }
      cnf.getCurrentClause().setClauseTheorem(d_rules->CNFConvert(e, *i));
    }
  }
}


Lit CNF_Manager::addAssumption(const Theorem& thm, CNF_Formula& cnf)
{
  if (d_flags["cnf-formula"].getBool()) {
    Expr e = thm.getExpr();
    DebugAssert(e.isOr() 
		|| (e.isNot() && e[0].isFalse()) 
		|| (e.isNot() && e[0].isTrue()), 
		"expr:" + e.toString() + " is not an OR Expr or Ture or False" ); 
    cnf.newClause();
    if (e.isOr()){
      for (int i = 0; i < e.arity(); i++){
	Lit l = (translateExprRec(e[i], cnf, thm));
	cnf.addLiteral(l);
      }
      cnf.getCurrentClause().setClauseTheorem(thm);
      return translateExprRec(e[0], cnf, thm) ;;
    }
    else  {
      Lit l = translateExpr(thm, cnf);
      cnf.addLiteral(l);
      cnf.registerUnit();
      cnf.getCurrentClause().setClauseTheorem(thm);
      return l;
    }
  }
  

  Lit l = translateExpr(thm, cnf);
  cnf.newClause();
  cnf.addLiteral(l);
  cnf.registerUnit();


//   if(concreteLit(l) != thm.getExpr()){
//     cout<<"fail addunit 3" << endl;
//   }

  Theorem newThm = d_rules->CNFAddUnit(thm);
  //  d_theorems[d_clauseIdNext] = thm;
  cnf.getCurrentClause().setClauseTheorem(newThm); // by yeting
  /*
  cout<<"set clause theorem  addassumption" << thm << endl;
  cout<<"set clause print" ;  
  cnf.getCurrentClause().print() ; 
  cout<<endl;
  cout<<"set clause id " << d_clauseIdNext << endl;
  */
  return l;
}


Lit CNF_Manager::addLemma(Theorem thm, CNF_Formula& cnf)
{

  vector<Theorem> clauses;
  d_rules->learnedClauses(thm, clauses, true);
  DebugAssert(clauses.size() == 1, "expected single clause");

  Lit l = translateExpr(clauses[0], cnf);
  cnf.newClause();
  cnf.addLiteral(l);
  cnf.registerUnit();

 
//    if(concreteLit(l) != clauses[0].getExpr()){
//     cout<<"fail addunit 4" << endl;
//   }

  Theorem newThm = d_rules->CNFAddUnit(clauses[0]); 
  //  d_theorems.insert(d_clauseIdNext, clause);
  cnf.getCurrentClause().setClauseTheorem(newThm); //by yeting

  /*
  cout<<"set clause theorem  addlemma" << thm << endl;
  cout<<"set clause print" ;  
  cnf.getCurrentClause().print() ; 
  cout<<endl;
  cout<<"set clause id " << d_clauseIdNext << endl;
  */
  return l;
}

