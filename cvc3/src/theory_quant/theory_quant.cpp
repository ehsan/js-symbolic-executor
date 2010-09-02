/*****************************************************************************/
/*!
 * \File theory_quant.cpp
 *
 * Author: Daniel Wichs, Yeting Ge
 *
 * Created: Wednesday July 2, 2003
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
#include "theory_quant.h"
#include "theory_arith.h"
#include "theory_array.h"
#include "typecheck_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
#include "quant_proof_rules.h"
#include "theory_core.h"
#include "command_line_flags.h"
#include "vcl.h"
#include<string>
#include<string.h>
#include <algorithm>
#include "assumptions.h"

using namespace std;
using namespace CVC3;

///////////////////////////////////////////////////////////////////////////////
// TheoryQuant Public Methods                                                 //
///////////////////////////////////////////////////////////////////////////////

static const Expr null_expr;
const int FOUND_FALSE = 1;

Trigger::Trigger(TheoryCore* core, Expr e, Polarity pol, std::set<Expr> boundVars){
  trig=e ;
  polarity=pol;
  head=null_expr;
  hasRWOp=false;
  hasTrans=false;
  hasT2=false;
  isSimple=false;
  isSuperSimple=false;
  isMulti=false;
  multiIndex = 99999;
  multiId = 99999;
  for(std::set<Expr>::const_iterator i=boundVars.begin(),iend=boundVars.end(); i!=iend; ++i)
    bvs.push_back(*i);
}

bool Trigger::isPos(){
  return (Pos==polarity||PosNeg==polarity);
}

bool Trigger::isNeg(){
  return (Neg==polarity || PosNeg==polarity);
}

std::vector<Expr> Trigger::getBVs(){
  return bvs;
}

Expr Trigger::getEx(){
  return trig;
}

void Trigger::setHead(Expr h){
  head=h;
}

Expr Trigger::getHead(){
  return head;
}

void Trigger::setRWOp(bool b){
  hasRWOp =b ;
}

bool Trigger::hasRW(){
  return hasRWOp;
}

void Trigger::setTrans(bool b){
  hasTrans =b ;
}

bool Trigger::hasTr(){
  return hasTrans;
}

void Trigger::setTrans2(bool b){
  hasT2 =b ;
}

bool Trigger::hasTr2(){
  return hasT2;
}

void Trigger::setSimp(){
  isSimple =true ;
}

bool Trigger::isSimp(){
  return isSimple;
}

void Trigger::setSuperSimp(){
  isSuperSimple =true ;
}

bool Trigger::isSuperSimp(){
  return isSuperSimple;
}

void Trigger::setMultiTrig(){
  isMulti = true ;
}

bool Trigger::isMultiTrig(){
  return isMulti;
}


dynTrig::dynTrig(Trigger t, ExprMap<Expr> b, size_t id)
  :trig(t),
   univ_id(id),
   binds(b)
{}

TheoryQuant::TheoryQuant(TheoryCore* core) //!< Constructor
  : Theory(core, "Quantified Expressions"),
    d_univs(core->getCM()->getCurrentContext()),
    d_rawUnivs(core->getCM()->getCurrentContext()),
    d_arrayTrigs(core->getCM()->getCurrentContext()),
    d_lastArrayPos(core->getCM()->getCurrentContext(), 0 , 0),
    d_lastPredsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_lastTermsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_lastPartPredsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_lastPartTermsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_univsPartSavedPos(core->getCM()->getCurrentContext(), 0, 0),
    d_lastPartLevel(core->getCM()->getCurrentContext(), 0, 0),
    d_partCalled(core->getCM()->getCurrentContext(),false,0),
    d_maxILReached(core->getCM()->getCurrentContext(),false,0),
    d_usefulGterms(core->getCM()->getCurrentContext()),
    d_lastUsefulGtermsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_savedTermsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_univsSavedPos(core->getCM()->getCurrentContext(), 0, 0),
    d_rawUnivsSavedPos(core->getCM()->getCurrentContext(), 0, 0),
    d_univsPosFull(core->getCM()->getCurrentContext(), 0, 0),
    d_univsContextPos(core->getCM()->getCurrentContext(), 0, 0),
    d_instCount(core->getCM()->getCurrentContext(), 0,0),
    d_contextTerms(core->getCM()->getCurrentContext()),
    d_contextCache(core->getCM()->getCurrentContext()),
    d_maxQuantInst(&(core->getFlags()["max-quant-inst"].getInt())),
    d_useNew(&(core->getFlags()["quant-new"].getBool())),
    d_useLazyInst(&(core->getFlags()["quant-lazy"].getBool())),
    d_useSemMatch(&(core->getFlags()["quant-sem-match"].getBool())),
    d_useCompleteInst(&(core->getFlags()["quant-complete-inst"].getBool())),
    d_translate(&(core->getFlags()["translate"].getBool())),
    //    d_usePart(&(core->getFlags()["quant-inst-part"].getBool())),
    //    d_useMult(&(core->getFlags()["quant-inst-mult"].getBool())),
    d_useInstLCache(&(core->getFlags()["quant-inst-lcache"].getBool())),
    d_useInstGCache(&(core->getFlags()["quant-inst-gcache"].getBool())),
    d_useInstThmCache(&(core->getFlags()["quant-inst-tcache"].getBool())),
    d_useInstTrue(&(core->getFlags()["quant-inst-true"].getBool())),
    d_usePullVar(&(core->getFlags()["quant-pullvar"].getBool())),
    d_useExprScore(&(core->getFlags()["quant-score"].getBool())),
    d_maxIL(&(core->getFlags()["quant-max-IL"].getInt())),
    d_useTrans(&(core->getFlags()["quant-trans3"].getBool())),
    d_useTrans2(&(core->getFlags()["quant-trans2"].getBool())),
    d_useManTrig(&(core->getFlags()["quant-man-trig"].getBool())),
    d_useGFact(&(core->getFlags()["quant-gfact"].getBool())),
    d_gfactLimit(&(core->getFlags()["quant-glimit"].getInt())),
    d_usePolarity(&(core->getFlags()["quant-polarity"].getBool())),
    d_useNewEqu(&(core->getFlags()["quant-eqnew"].getBool())),
    d_maxNaiveCall(&(core->getFlags()["quant-naive-num"].getInt())),
    d_useNaiveInst(&(core->getFlags()["quant-naive-inst"].getBool())),
    d_curMaxExprScore(core->getCM()->getCurrentContext(), (core->getFlags()["quant-max-score"].getInt()),0),
    d_arrayIndic(core->getCM()->getCurrentContext()),
    d_exprLastUpdatedPos(core->getCM()->getCurrentContext(),0 ,0),
    d_trans_found(core->getCM()->getCurrentContext()),
    d_trans2_found(core->getCM()->getCurrentContext()),
    null_cdlist(core->getCM()->getCurrentContext()),
    d_eqsUpdate(core->getCM()->getCurrentContext()),
    d_lastEqsUpdatePos(core->getCM()->getCurrentContext(), 0, 0),
    d_eqs(core->getCM()->getCurrentContext()),
    d_eqs_pos(core->getCM()->getCurrentContext(), 0, 0),
    d_allInstCount(core->getStatistics().counter("quantifier instantiations")),
    d_allInstCount2(core->getStatistics().counter("quantifier instantiations2")),
    d_totalInstCount(core->getStatistics().counter("quant total instantiations")),
    d_trueInstCount(core->getStatistics().counter("quant true instantiations")),
    d_abInstCount(core->getStatistics().counter("quant abandoned instantiations")),
    d_instHistory(core->getCM()->getCurrentContext()),
    d_alltrig_list(core->getCM()->getCurrentContext())
{
  IF_DEBUG(d_univs.setName("CDList[TheoryQuant::d_univs]");)
  vector<int> kinds;
  d_instCount = 0;
  d_cacheThmPos=0;
  d_trans_num=0;
  d_trans2_num=0;
  d_rules=createProofRules();
  kinds.push_back(EXISTS);
  kinds.push_back(FORALL);
  registerTheory(this, kinds);
  d_partCalled=false;
  d_offset_multi_trig=2;
  d_initMaxScore=(theoryCore()->getFlags()["quant-max-score"].getInt());
  for(size_t i=0; i<MAX_TRIG_BVS; i++){
    d_mybvs[i] = getEM()->newBoundVarExpr("_genbv", int2string(i), Type::anyType(getEM()));
  }
  core->addNotifyEq(this, null_expr);
  defaultReadExpr = theoryCore()->getEM()->newStringExpr("read");
  defaultWriteExpr = theoryCore()->getEM()->newStringExpr("write");
  defaultPlusExpr= theoryCore()->getEM()->newStringExpr("+");
  defaultMinusExpr= theoryCore()->getEM()->newStringExpr("-");
  defaultMultExpr= theoryCore()->getEM()->newStringExpr("*");
  defaultDivideExpr= theoryCore()->getEM()->newStringExpr("/");
  defaultPowExpr= theoryCore()->getEM()->newStringExpr("pow");

}

//! Destructor
TheoryQuant::~TheoryQuant() {
  if(d_rules != NULL) delete d_rules;
  for(std::map<Type, CDList<size_t>* ,TypeComp>::iterator
	it = d_contextMap.begin(), iend = d_contextMap.end();
      it!= iend; ++it) {
    delete it->second;
     free(it->second);
  }

}
std::string vectorExpr2string(const std::vector<Expr> & vec){
  std::string buf;
  for(size_t i=0; i<vec.size(); i++){
    buf.append(vec[i].toString());
    buf.append(" # ");
  }
  return buf;
}


Theorem TheoryQuant::rewrite(const Expr& e){
  //  return reflexivityRule(e);
  // should combined with packvar, rewriet_not_all, etc,
  if(e.isForall() || e.isExists() ){
    Theorem resThm =  d_rules->normalizeQuant(e);
    //    Expr newE = resThm.getRHS();
    return resThm;
  }
  else{
    if (e.isNot() && e[0].isForall()){
      //      cout<<vectorExpr2string(e[0].getVars()) << endl;
    }
    else {
      //      cout<<e<<endl;
    }
    return reflexivityRule(e);
  }
}


int inline TheoryQuant::getExprScore(const Expr& e){
  return theoryCore()->getQuantLevelForTerm(e);
}

bool isSysPred(const Expr& e){
  return ( isLE(e) || isLT(e) || isGE(e) || isGT(e) || e.isEq());
}

bool canGetHead(const Expr& e){
  //  return (e.getKind() == APPLY || e.getKind() == READ || e.getKind() == WRITE);
  return (e.getKind() == APPLY 
	  || e.getKind() == READ 
	  || e.getKind() == WRITE
	  || isPlus(e) 
	  || isMinus(e) 
	  || isMult(e)
	  || isDivide(e)
	  || isPow(e)
	  );
}

bool isSimpleTrig(const Expr& t){
  if(!canGetHead(t)) return false;
  for(int i = 0; i < t.arity(); i++){
    if (t[i].arity()>0 && t[i].containsBoundVar()) return false;
    if (BOUND_VAR == t[i].getKind()){
      for(int j = 0; j < i; j++){
	if(t[i] == t[j]) return false;
      }
    }
  }
  return true;
}

bool isSuperSimpleTrig(const Expr& t){
  if(!isSimpleTrig(t)) return false;
  if(t.getKind() == READ || t.getKind() == WRITE){
    return false; //in case var1[var2]
  }
  for(int i = 0; i < t.arity(); i++){
    if (t[i].arity()>0 ) return false;
    if (BOUND_VAR != t[i].getKind()){
      return false;
    }
  }
  return true;
}


bool usefulInMatch(const Expr& e){
  if(e.arity() == 0){
    TRACE("usefulInMatch", e.toString()+": ",e.arity(), "");
    TRACE("usefulInMatch", e.isRational(), "", "");
  }
  //  cout << "is useful in match" << (canGetHead(e) || (isSysPred(e) && (!e.isEq()) )) << "#" <<  e<< endl;
  //  if (e.getKind() == APPLY){
  //    cout << (e.getKind() == APPLY) << endl;
  //    cout << e.getOp().getExpr() << endl;
  //    cout << e.getOp() << endl;
  //  }
  return ( canGetHead(e) || (isSysPred(e) && (!e.isEq()) ) );
}

void TheoryQuant::setup(const Expr& e) {}

int TheoryQuant::help(int i) {
  return d_curMaxExprScore;
}

void TheoryQuant::debug(int i){
  
  cout<<"in debug " << endl;
  cout << "max expr score " << d_curMaxExprScore << endl;
  cout << "all gterms " << endl;
  for(size_t gtermIndex =0; gtermIndex <  d_usefulGterms.size() ; gtermIndex++){
    cout << gtermIndex << " :: " << getExprScore(d_usefulGterms[gtermIndex]) << " | " << d_usefulGterms[gtermIndex] << endl;
  }

  cout << " =============  all terms ========================== " << endl;
  const CDList<Expr>&  allterms = theoryCore()->getTerms();
  for(size_t gtermIndex =0; gtermIndex <  allterms.size() ; gtermIndex++){
    const Expr& curGterm = allterms[gtermIndex];
    cout << gtermIndex << " :: " << getExprScore(curGterm) << " | " << curGterm << endl;
    cout << "--- ";
    if (curGterm.isApply() && curGterm.hasRep()){
      Expr curRep = curGterm.getRep().getRHS() ;
      if(curRep != curGterm){
	cout<<"DIFF " <<curRep << endl;
      }
    }
    else {
      cout << "No Rep" ;
    }
    cout << endl ;

    cout << "=== ";
    if (curGterm.isApply() && curGterm.hasSig()){
      Expr curSig = curGterm.getSig().getRHS() ;
      if(curSig != curGterm){
	cout<<"DIFF " <<curSig << endl;
      }
    }
    else {
      cout << "No Sig" ;
    }
    cout << endl ;


  }
  cout << " =============  all preds  ========================== " << endl;
  const CDList<Expr>&  allpreds = theoryCore()->getPredicates();
  for(size_t gtermIndex =0; gtermIndex <  allpreds.size() ; gtermIndex++){
    const Expr& curGterm = allpreds[gtermIndex];
    cout << gtermIndex << " :: " << getExprScore(curGterm) << " | " << curGterm << endl;
    cout << "--- ";
    if (curGterm.isApply() && curGterm.hasRep()){
      Expr curRep = curGterm.getRep().getRHS() ;
      if(curRep != curGterm){
	cout<<"DIFF " <<curRep << endl;
      }
    }
    else {
      cout << "No Rep" ;
    }
    cout << endl ;

    cout << "=== ";
    if (curGterm.isApply() && curGterm.hasSig()){
      Expr curSig = curGterm.getSig().getRHS() ;
      if(curSig != curGterm){
	cout<<"DIFF " <<curSig << endl;
      }
    }
    else {
      cout << "No Sig" ;
    }
    cout << endl ;
  }

  cout<<"let us try more"<<endl;

  //  checkSat(true);
  
}

void TheoryQuant::update(const Theorem& t, const Expr& e) {

  TRACE("quant update", "eqs updated: ",  t.getExpr(), "");

  //  if(! (*d_useNewEqu)) return;
  //  cout<<" ===== eqs in update =================== " <<endl;

  d_eqsUpdate.push_back(t);

  return;

  const Expr& leftTerm = t.getLHS();
  const Expr& rightTerm = t.getRHS();
  /*
  NotifyList* leftUpList = leftTerm.getNotify();

  cout<<"left term is " << leftTerm << endl;

  if(NULL == leftUpList) return;


  cout<<"the left notify list" <<endl;
  NotifyList& l = *leftUpList;
  for(size_t i=0,iend=l.size(); i<iend; ++i) {
    if(l.getTheory(i)->getName() == "Uninterpreted Functions"){
    cout << "[" << l.getTheory(i)->getName() << ", " << l.getExpr(i) << "] " << l.getExpr(i).getSig().isNull() << endl;
    }
  }

  const Expr& rightTerm = t.getRHS();
  cout<<"right term is " << rightTerm << endl;
  NotifyList* rightUpList = rightTerm.getNotify();
  if(NULL == rightUpList) return;

  cout<<"the right notify list" << endl;

  NotifyList& ll = *rightUpList;
  for(size_t i=0,iend=ll.size(); i<iend; ++i) {
    if(ll.getTheory(i)->getName() == "Uninterpreted Functions"){
    cout << "[" << ll.getTheory(i)->getName() << ", " << ll.getExpr(i) << "] " << ll.getExpr(i).getSig().isNull() << endl;
    }
  }


//   cout<<"------------" << leftTerm << " # " << rightTerm <<endl;
//   cout<<"$$$$$$$$$$$$" << leftTerm.hasFind() << " # " << rightTerm.hasFind() <<endl;
//   if(theoryOf(leftTerm)->getName() == "Uninterpreted Functions"){
//     cout<<"%%%%%%%%%%%%" << (leftTerm.getSig()).isNull() << " # " << (rightTerm.getSig()).isNull() <<endl;
//   }
//   else{
//     cout<<"tttt" <<theoryOf(leftTerm)->getName()<<endl;
//   }
*/
  if(false)
  {
    CDList<Expr>& backL = backList(leftTerm);
    CDList<Expr>& forwL = forwList(rightTerm);

    size_t backLen = backL.size();
    size_t forwLen = forwL.size();
    for(size_t i =0; i < backLen; i++){
      for(size_t j =0; j < forwLen; j++){
	//	cout<<backL[i] << " # " << leftTerm << " # " << forwL[j] << endl;
      }
    }
  }
  {
    CDList<Expr>& backL = backList(rightTerm);
    CDList<Expr>& forwL = forwList(leftTerm);
    size_t backLen = backL.size();
    size_t forwLen = forwL.size();
    for(size_t i = 0; i < backLen; i++){
      for(size_t j = 0; j < forwLen; j++){
	//	cout<<backL[i] << " # " << rightTerm << " # " << forwL[j] << endl;
      }
    }
  }

}


std::string TheoryQuant::exprMap2string(const ExprMap<Expr>& vec){
  string result;
//   for( ExprMap<Expr>::iterator i = vec.begin(), iend = vec.end(); i != iend; i++){
//     result.append((i->first).toString());
//     result.append(" # ");
//     result.append((i->second).toString());
//     result.append("\n");
//   }
//   result.append("------ end map ------\n");
  return result;
}



std::string TheoryQuant::exprMap2stringSimplify(const ExprMap<Expr>& vec){
  string result;
//   for( ExprMap<Expr>::iterator i = vec.begin(), iend = vec.end(); i != iend; i++){
//     result.append((i->first).toString());
//     result.append(" # ");
//     result.append((simplifyExpr(i->second)).toString());
//     result.append("\n");
//   }
  result.append("------ end map ------\n");
  return result;
}

std::string TheoryQuant::exprMap2stringSig(const ExprMap<Expr>& vec){
  string result;
//     for( ExprMap<Expr>::iterator i = vec.begin(), iend = vec.end(); i != iend; i++){
//     result.append((i->first).toString());
//     result.append(" # ");
//     Expr isecond = i->second;
//     if(simplifyExpr(isecond) == isecond && isecond.isApply() && isecond.hasSig()){
//       result.append((isecond.getSig().getRHS()).toString());
//     }
//     else{
//       //      result.append(isecond.toString());
//     }
//     result.append("\n");
//   }
  result.append("------ end map ------\n");
  return result;
}


void TheoryQuant::simplifyExprMap(ExprMap<Expr>& orgExprMap){
  ExprMap<Expr> newExprMap;
  for( ExprMap<Expr>::iterator i = orgExprMap.begin(), iend = orgExprMap.end(); i != iend; i++){
    newExprMap[(*i).first] = simplifyExpr((*i).second);
  }
  orgExprMap = newExprMap;
}

void TheoryQuant::simplifyVectorExprMap(vector<ExprMap<Expr> >& orgVectorExprMap){
  std::vector<ExprMap<Expr> > newVectorExprMap;
  for( size_t orgVectorIndex = 0; orgVectorIndex < orgVectorExprMap.size(); orgVectorIndex++){
    ExprMap<Expr> curExprMap = orgVectorExprMap[orgVectorIndex];
    simplifyExprMap(curExprMap);
    newVectorExprMap.push_back(curExprMap);
  }
  orgVectorExprMap = newVectorExprMap;
}

static void recursiveGetSubTrig(const Expr& e, std::vector<Expr> & res) {
  if(e.getFlag())
   return;

  if(e.isClosure())
    return recursiveGetSubTrig(e.getBody(),res);

  if (e.isApply()|| isSysPred(e)){
    res.push_back(e);
  }
  else
    if ( e.isTerm() && (!e.isVar()) && (e.getKind()!=RATIONAL_EXPR) ) {
	res.push_back(e);
      }

  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)    {
      recursiveGetSubTrig(*i,res);
    }

  e.setFlag();
  return ;
}

std::vector<Expr> getSubTrig(const Expr& e){
  e.clearFlags();
  std::vector<Expr> res;
  recursiveGetSubTrig(e,res);
  e.clearFlags();
  TRACE("getsub","e is ", e.toString(),"");
  TRACE("getsub","have ", res.size()," subterms");
  return res;
}

static void recGetSubTerms(const Expr& e, std::vector<Expr> & res) {
  if(e.getFlag())
   return;

  if(e.isClosure())
    return recGetSubTerms(e.getBody(),res);

  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)  {
    recGetSubTerms(*i,res);
  }

  res.push_back(e);

  e.setFlag();
  return ;
}

const std::vector<Expr>& TheoryQuant::getSubTerms(const Expr& e){
  //the last item in res is e itself
  ExprMap<std::vector<Expr> >::iterator iter= d_subTermsMap.find(e);
  if( d_subTermsMap.end() == iter){
    e.clearFlags();
    std::vector<Expr> res;
    recGetSubTerms(e,res);
    e.clearFlags();

    TRACE("getsubs", "getsubs, e is: ", e, "");
    TRACE("getsubs", "e has ", res.size(), " subterms");

    d_subTermsMap[e] = res;
    return d_subTermsMap[e];
  }
  else{
    return (*iter).second;
  }
}

void TheoryQuant::enqueueInst(const Theorem& univ, const vector<Expr>& bind, const Expr& gterm){
  static int max_score =-1;

  bool partInst=false;
  if(bind.size() < univ.getExpr().getVars().size()){
    partInst=false;
    TRACE("sendinst","partinst",partInst,"");
  }

  Expr bind_expr(RAW_LIST, bind, getEM());

  if (*d_useInstLCache){
    const Expr& e = univ.getExpr();
    ExprMap<CDMap<Expr,bool>*>::iterator iterCache = d_bindHistory.find(e);
    if (iterCache != d_bindHistory.end()){
      CDMap<Expr,bool>* cache = (*iterCache).second;
      if(cache->find(bind_expr) !=cache->end()){
	return ;
      }
      else{
	(*cache)[bind_expr] = true;
      }
    }
    else{
      CDMap<Expr,bool>* new_cache = new(true) CDMap<Expr,bool> (theoryCore()->getCM()->getCurrentContext());
      (*new_cache)[bind_expr] = true;
      d_bindHistory[e] = new_cache;
    }

  }

  Theorem thm ;
  if(null_expr == gterm ){//it is from naive instantiation or multi-inst
    TRACE("sendinst","gterm",gterm,"");
    if(partInst) {
      thm = d_rules->partialUniversalInst(univ, bind, 0);
    }
    else{
      //      thm = d_rules->universalInst(univ, bind, 0);
      thm = d_rules->universalInst(univ, bind, 0, gterm);
    }
  }
  else{
    int gscore = theoryCore()->getQuantLevelForTerm(gterm);
    if(gscore > max_score){
      max_score = gscore;
      //      cout<<"max score "<<max_score<<endl;
    }
    if(partInst) {
      thm = d_rules->partialUniversalInst(univ, bind, gscore);
    }
    else{
      //      thm = d_rules->universalInst(univ, bind, gscore);
      thm = d_rules->universalInst(univ, bind, gscore, gterm);
    }
  }

  d_totalInstCount++;
  d_totalThmCount[thm.getExpr()]++;
  Theorem simpThm = simplify(thm.getExpr());

  if(*d_useInstTrue){
    Expr res = simpThm.getRHS();
    if(res.isTrue()){
      d_trueInstCount++;
      return;
    }
    if(res.isFalse() ){
      d_thmCount[thm.getExpr()]++;
      //      enqueueSE(thm);
      //      if(*d_useGFact || d_totalThmCount[thm.getExpr()] > *d_gfactLimit){
      if(*d_useGFact || d_thmCount[thm.getExpr()] > *d_gfactLimit){
	//      if(*d_useGFact || ){
	//	addGlobalLemma(thm, -1);
	enqueueFact(thm);
      }
      else{
	enqueueFact(thm);
      }
      //
      //      cout<<"false found "<<endl;
      //      setInconsistent(simpThm);
      d_allInstCount++;
      d_instThisRound++;

      throw FOUND_FALSE;
    }
  }

  d_simplifiedThmQueue.push(thm);

  TRACE("quant sendinst", "= gterm:",gterm, "");
  //  TRACE("quant sendinst", "= IL: ", theoryCore()->getQuantLevelForTerm(gterm), "");
  TRACE("quant sendinst", "= add fact simp: ", simplifyExpr(thm.getExpr()), "");
  TRACE("quant sendinst", "= add fact org: ", thm.getExpr(), "");
  TRACE("quant sendinst", "= add fact from: ", univ.getExpr(), "\n===: "+vectorExpr2string(bind));
}


//void TheoryQuant::enqueueInst(size_t univ_id , const std::vector<Expr>& bind, const Expr& gterm){
void TheoryQuant::enqueueInst(size_t univ_id , const std::vector<Expr>& orgBind, const Expr& gterm){
  //  static int max_score =-1;
  TRACE("quant sendinst", "= begin univ id: ", univ_id, "");
  TRACE("quant sendinst", "= begin bind: ", vectorExpr2string(orgBind), "");
  TRACE("quant sendinst", "= begin gterm: ", gterm, "");
  const Theorem& univ = d_univs[univ_id];

  //  static vector<Theorem> storage ;
  //  storage.push_back(univ);

  bool partInst=false;
  if(orgBind.size() < univ.getExpr().getVars().size()){
    partInst=false;
    TRACE("sendinst","partinst",partInst,"");
  }

  vector<Expr> simpBind(orgBind);
  for(size_t orgBindIndex = 0; orgBindIndex < orgBind.size(); orgBindIndex++){
    simpBind [orgBindIndex] = simplifyExpr(orgBind[orgBindIndex]);
  }

  Expr orgBindList(RAW_LIST, orgBind, getEM());
  Expr simpBindList(RAW_LIST, simpBind, getEM());

//   if(orgBindList != simpBindList){
//     cout<<"debugerror" << endl;
//     cout<< "-orgBind " << vectorExpr2string(orgBind) << endl;
//     cout<< "-simpBind " << vectorExpr2string(simpBind) << endl;
//   }

  vector<Expr> bind(simpBind);
  Expr bind_expr(simpBindList);

//   vector<Expr> bind(orgBind);
//   Expr bind_expr(orgBindList);

  TRACE("quant sendinst", "==add fact from= ", univ.getExpr(), "\n===: "+vectorExpr2string(bind));

  if (*d_useInstLCache){
    const Expr& e = univ.getExpr();
    ExprMap<CDMap<Expr,bool>*>::iterator iterCache = d_bindHistory.find(e);
    if (iterCache != d_bindHistory.end()){
      CDMap<Expr,bool>* cache = (*iterCache).second;
      if(cache->find(bind_expr) != cache->end()){
	//	cout<<"return inst 1"<<endl;
	return ;
      }
      else{
	(*cache)[bind_expr] = true;
      }
    }
    else{
      CDMap<Expr,bool>* new_cache = new(true) CDMap<Expr,bool> (theoryCore()->getCM()->getCurrentContext());
      (*new_cache)[bind_expr] = true;
      d_bindHistory[e] = new_cache;
    }
  }

  if (*d_useInstGCache){
    const Expr& e = univ.getExpr();
    ExprMap<std::hash_map<Expr,bool>*>::iterator iterCache = d_bindGlobalHistory.find(e);
    if (iterCache != d_bindGlobalHistory.end()){
      std::hash_map<Expr,bool>* cache = (*iterCache).second;
      if(cache->find(bind_expr) != cache->end()){
	//	cout<<"return inst 1"<<endl;

	//	int gscore = theoryCore()->getQuantLevelForTerm(gterm);
	//	Theorem local_thm = d_rules->universalInst(univ, bind, gscore);
	/*
	if(!(simplifyExpr(local_thm.getExpr())).isTrue()){
	  cout<<"en?" <<endl;
	  TRACE("quant sendinst", "==add fact simp =", simplifyExpr(local_thm.getExpr()), "");
	  TRACE("quant sendinst", "==add fact org =", local_thm.getExpr(), "");
	  TRACE("quant sendinst", "==add fact from= ", univ.getExpr(), "\n===: "+vectorExpr2string(bind));
	  TRACE("quant sendinst", "== end === ", "=========", "============");
	  }
	*/
	d_allInstCount2++;
	return ;
      }
      /*
      else{
	(*cache)[bind_expr] = true;

	d_allInstCount2++;
      }
    }
    else{
      std::hash_map<Expr,bool>* new_cache = new std::hash_map<Expr,bool> ;
      (*new_cache)[bind_expr] = true;
      d_bindGlobalHistory[e] = new_cache;
      d_allInstCount2++;
      */
    }
  }

  Theorem thm ;

  if (*d_useInstThmCache){
    const Expr& e = univ.getExpr();
    ExprMap<std::hash_map<Expr,Theorem>* >::iterator iterCache = d_bindGlobalThmHistory.find(e);
    if (iterCache != d_bindGlobalThmHistory.end()){
      std::hash_map<Expr,Theorem>* cache = (*iterCache).second;
      std::hash_map<Expr,Theorem>::iterator thm_iter = cache->find(bind_expr);

      if(thm_iter != cache->end()){
	thm = thm_iter->second;
      }
      else{
	{
	  if(null_expr == gterm ){//it is from naive instantiation or multi-inst
	    TRACE("sendinst","gterm",gterm,"");
	    if(partInst) {
	      thm = d_rules->partialUniversalInst(univ, bind, 0);
	    }
	    else{
	      //	      thm = d_rules->universalInst(univ, bind, 0);
	      thm = d_rules->universalInst(univ, bind, 0, gterm);
	    }
	  }
	  else{
	    int gscore = theoryCore()->getQuantLevelForTerm(gterm);
	    if(partInst) {
	      thm = d_rules->partialUniversalInst(univ, bind, gscore);
	    }
	    else{
	      //	      thm = d_rules->universalInst(univ, bind, gscore);
	      thm = d_rules->universalInst(univ, bind, gscore, gterm);
	    }
	  }
	}

	(*cache)[bind_expr] = thm;
	d_allInstCount2++;
      }
    }
    else{
      {
	if(null_expr == gterm ){//it is from naive instantiation or multi-inst
	  TRACE("sendinst","gterm",gterm,"");
	  if(partInst) {
	    thm = d_rules->partialUniversalInst(univ, bind, 0);
	  }
	  else{
	    //	    thm = d_rules->universalInst(univ, bind, 0);
	    thm = d_rules->universalInst(univ, bind, 0, gterm);
	  }
	}
	else{
	  int gscore = theoryCore()->getQuantLevelForTerm(gterm);
	  if(partInst) {
	    thm = d_rules->partialUniversalInst(univ, bind, gscore);
	  }
	  else{
	    //	    thm = d_rules->universalInst(univ, bind, gscore);
	    thm = d_rules->universalInst(univ, bind, gscore, gterm);
	  }
	}
      }

      std::hash_map<Expr,Theorem>* new_cache = new std::hash_map<Expr,Theorem> ;
      (*new_cache)[bind_expr] = thm;
      d_bindGlobalThmHistory[e] = new_cache;
      d_allInstCount2++;
    }
  }
  else{
    if(null_expr == gterm ){//it is from naive instantiation or multi-inst
      TRACE("sendinst","gterm",gterm,"");
      if(partInst) {
	thm = d_rules->partialUniversalInst(univ, bind, 0);
      }
      else{
	//thm = d_rules->universalInst(univ, bind, 0);
	thm = d_rules->universalInst(univ, bind, 0, gterm);
      }
    }
    else{
      int gscore = theoryCore()->getQuantLevelForTerm(gterm);
            /*
	if(gscore > max_score){
	max_score = gscore;
	cout<<"max score "<<max_score<<endl;
	}
      */
      if(partInst) {
	thm = d_rules->partialUniversalInst(univ, bind, gscore);
      }
      else{
	//	thm = d_rules->universalInst(univ, bind, gscore);
	thm = d_rules->universalInst(univ, bind, gscore, gterm);
      }
    }
  }

  d_totalInstCount++;
  d_totalThmCount[thm.getExpr()]++;
  Theorem simpThm = simplify(thm.getExpr());

  if(*d_useInstTrue){
    Expr res = simpThm.getRHS();
    if(res.isTrue()){
      d_trueInstCount++;
      
//        cout<<"return because true"<<endl;
//        cout<<"true thm expr: " <<thm.getExpr()<<endl;
//        cout<<"true thm: " <<thm<<endl;
      
//        cout<<"return inst 2"<<endl;
      return;
    }
    if(res.isFalse() ){
      d_thmCount[thm.getExpr()]++;
      //      if(*d_useGFact || d_totalThmCount[thm.getExpr()] > *d_gfactLimit ){

      if(*d_useGFact || d_thmCount[thm.getExpr()] > *d_gfactLimit ){

	//      if(*d_useGFact){
	//	addGlobalLemma(thm, -1);
	enqueueFact(thm);
      }
      else{
	enqueueFact(thm);
      }
      //      enqueueSE(thm);
      //
      //      setInconsistent(simpThm);
      d_allInstCount++;
      d_instThisRound++;
      //      cout<<"false found 2"<<endl;
      /*
      if (*d_useInstGCache){
	sendInstNew();
      }
      */
      //      cout<<"return inst 3"<<endl;
      throw FOUND_FALSE;
    }
  }

  d_simplifiedThmQueue.push(thm);
  d_gUnivQueue.push(univ);
  d_gBindQueue.push(bind_expr);

  //  cout<<"enqueue inst"<<thm << endl;
  TRACE("quant sendinst", "=gterm: ",gterm, "");
  /*
  if(true || 0 == theoryCore()->getQuantLevelForTerm(gterm)){
    cout<<"gterm" << gterm <<endl;;
    cout<<"IL=== "<<theoryCore()->getQuantLevelForTerm(gterm)<<endl;;
  }
  */
  
  //  cout << "gterm: " <<  gterm << endl;
  TRACE("quant sendinst", "= add fact simp: ", simplifyExpr(thm.getExpr()), "");
  TRACE("quant sendinst", "= add fact org: ", thm.getExpr(), "");
  TRACE("quant sendinst", "= add fact from:  ", univ.getExpr(), "\n===: "+vectorExpr2string(bind));
  TRACE("quant sendinst", "= end === ", "=========", "============");
}


void TheoryQuant::enqueueInst(const Theorem& univ, Trigger& trig,  const std::vector<Expr>& binds,  const Expr& gterm) {
  return enqueueInst(univ,binds,gterm);
}

int TheoryQuant::sendInstNew(){
  int resNum = 0 ;

  while(!d_simplifiedThmQueue.empty()){
    const Theorem thm = d_simplifiedThmQueue.front();
    d_simplifiedThmQueue.pop();

    d_allInstCount++;
    d_instThisRound++;
    resNum++;
    if (*d_useInstGCache){
      const Theorem & univ = d_gUnivQueue.front();
      const Expr & bind = d_gBindQueue.front();

      const Expr& e = univ.getExpr();
      ExprMap<std::hash_map<Expr,bool>*>::iterator iterCache = d_bindGlobalHistory.find(e);
      if (iterCache != d_bindGlobalHistory.end()){
	std::hash_map<Expr,bool>* cache = (*iterCache).second;
	(*cache)[bind] = true;
      }
      else{
	std::hash_map<Expr,bool>* new_cache = new std::hash_map<Expr,bool> ;
	(*new_cache)[bind] = true;
	d_bindGlobalHistory[e] = new_cache;
      }
    }
    d_thmCount[thm.getExpr()]++;
    //    if(*d_useGFact || d_totalThmCount[thm.getExpr()] > *d_gfactLimit ){
    if(*d_useGFact || d_thmCount[thm.getExpr()] > *d_gfactLimit ){
      //      addGlobalLemma(thm, -1);
      enqueueFact(thm);
    }
    else{
      enqueueFact(thm);
    }
    //    enqueueSE(thm);
    //
  }

  return resNum;
}

void TheoryQuant::addNotify(const Expr& e){}

int recursiveExprScore(const Expr& e) {
  int res=0;
  DebugAssert(!(e.isClosure()), "exprScore called on closure");

  if(e.arity()== 0){
    res = 0;
  }
  else{
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)  {
      res += recursiveExprScore(*i);
    }
  }
  res++;
  return res;
}


int exprScore(const Expr& e){
  return recursiveExprScore(e);
}

Expr TheoryQuant::getHeadExpr(const Expr& e){
  if (e.getKind() == APPLY){
    return e.getOp().getExpr();
  }

  if ( READ == e.getKind() ){
    return defaultReadExpr;
  }
  if ( WRITE == e.getKind() ){
    return defaultWriteExpr;
  }
  if (isPlus(e)){
    return defaultPlusExpr;
  }
  if (isMinus(e)){
    return defaultMinusExpr;
  }
  if (isMult(e)){
    return defaultMultExpr;
  }
  if (isDivide(e)){
    return defaultDivideExpr;
  }
  if (isPow(e)){
    return defaultPowExpr;
  }

//   if ( READ == e.getKind() || WRITE == e.getKind() )  {
//     int kind = e[0].getKind();
//     if (UCONST==kind) {
//       return e[0];
//     }
//     else if (APPLY==kind || UFUNC == kind || READ == kind || WRITE == kind){
//       return getHeadExpr(e[0]);
//     }
//     else if(e[0].isSkolem()){
//       return e[0];
//     }
//   }

  return null_expr;
}

Expr  TheoryQuant::getHead(const Expr& e) {
  return getHeadExpr(e);
}

//! get the bound vars in term e,
static bool recursiveGetBoundVars(const Expr& e, std::set<Expr>& result) {
  bool res(false);
  if(e.getFlag()){
    return e.containsBoundVar();
  }
  else if(e.isClosure()){
    res = recursiveGetBoundVars(e.getBody(),result);
  }
  else if (BOUND_VAR == e.getKind() ){
    result.insert(e);
    e.setContainsBoundVar();
    res = true;
  }
  else {
    res = false;
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i){
      if(recursiveGetBoundVars(*i,result)){
	res = true;
      }
    }
  }

  e.setFlag();

  if(res) {
    e.setContainsBoundVar();
  }

  return res;
}


//! get bound vars in term e,
std::set<Expr>  getBoundVars(const Expr& e){

  //  static ExprMap<std::set<Expr> > bvsCache;

  //  static std::map<Expr, std::set<Expr> > bvsCache;
  //  std::map<Expr, std::set<Expr> >::iterator iterCache = bvsCache.find(e);

  //ExprMap<std::set<Expr> >::iterator iterCache = bvsCache.find(e);

  //  if (iterCache != bvsCache.end()){
  //    //    return iterCache->second;
  //    return (*iterCache).second;
  //  }

  e.clearFlags();
  std::set<Expr> result ;
  recursiveGetBoundVars(e,result);
  e.clearFlags();
  //  bvsCache[e]=result;
  return  result;
}

void findPolarity(const Expr& e, ExprMap<Polarity>& res, Polarity  pol){
  if(!e.getType().isBool()) return;
  //now a AND b will be given a polarity too, this is not necessary.
  if(res.count(e)>0){
    if ((Neg == res[e] && Pos == pol) || (Neg == res[e] && Pos == pol) ){
      res[e]=PosNeg;
    }
  }
  else{
    res[e]=pol;
  }

  TRACE("find-polarity", e, "has ", (int)pol);
 
  if(PosNeg==pol){
    for(int i=0; i<e.arity(); i++){
      findPolarity(e[i], res, pol);
    }
  }
  else{
    Polarity neg_pol=Ukn;
    if(Pos == pol) {
      neg_pol = Neg;
    }
    else if(Neg == pol){
      neg_pol = Pos;
    }

    if(e.isImpl()){
      findPolarity(e[0], res, neg_pol);
      findPolarity(e[1], res, pol);
    }
    else if(e.isAnd() || e.isOr()){
      for(int i=0; i<e.arity(); i++){
	findPolarity(e[i], res, pol);
      }
    }
    else if(e.isNot()){
      findPolarity(e[0], res, neg_pol);
    }
    else if(e.isITE()){
      findPolarity(e[0], res, PosNeg);
      findPolarity(e[1], res, pol);
      findPolarity(e[2], res, pol);
    }
    else if(e.isClosure()){
      findPolarity(e.getBody(), res, pol);
    }
    else if(e.isIff()){
      findPolarity(e[0], res, PosNeg);
      findPolarity(e[1], res, PosNeg);
    }
    else if(e.isXor()){
      findPolarity(e[0], res, neg_pol);
      findPolarity(e[1], res, neg_pol);
    }
    else if(e.isAtomicFormula()){
      return;
    }
    else{
      //      DebugAssert(false, "Error in find polarity in "+e.toString());
    }
  }
}

bool isUniterpFunc(const Expr & e){
  if ( e.isApply() && e.getOpKind() == UFUNC){
    return true;
  }
  return false;
}
//   if (e.getKind() == READ || e.getKind() == WRITE){
//     return true;
//   }
//   return false;
// }

bool isGround(const Expr& e){
  //be careful, this function must be called after some calls to getBoundVar() because containsBoundVar() will be set only in getBoundVar() method.
  //if e contains a closed quantifier, e is not ground. 
  return ! e.containsBoundVar();
}

Expr CompleteInstPreProcessor::pullVarOut(const Expr& thm_expr){

  const Expr outBody = thm_expr.getBody();

//   if(((outBody.isAnd() && outBody[1].isForall()) ||
//        (outBody.isImpl() && outBody[1].isForall()) ||
//        (outBody.isNot() && outBody[0].isAnd() && outBody[0][1].isExists()) )){
//     return t1;
//   }

  if (thm_expr.isForall()){
    if((outBody.isNot() && outBody[0].isAnd() && outBody[0][1].isExists())){
      
      vector<Expr> bVarsOut = thm_expr.getVars();
      
      const Expr innerExists =outBody[0][1];
      const Expr innerBody = innerExists.getBody();
      vector<Expr> bVarsIn = innerExists.getVars();
      
      for(vector<Expr>::iterator i=bVarsIn.begin(), iend=bVarsIn.end(); i!=iend; i++){
	bVarsOut.push_back(*i);
      }
      
      Expr newbody;
      
      newbody=(outBody[0][0].notExpr()).orExpr(innerBody.notExpr());
      
      Expr newQuantExpr;
      newQuantExpr = d_theoryCore->getEM()->newClosureExpr(FORALL, bVarsOut, newbody);
      
      return newQuantExpr ;
    }
    
    else if ((outBody.isAnd() && outBody[1].isForall()) ||
	     (outBody.isImpl() && outBody[1].isForall())){
      
      vector<Expr> bVarsOut = thm_expr.getVars();
      
      const Expr innerForall=outBody[1];
      const Expr innerBody = innerForall.getBody();
      vector<Expr> bVarsIn = innerForall.getVars();
      
      for(vector<Expr>::iterator i=bVarsIn.begin(), iend=bVarsIn.end(); i!=iend; i++){
	bVarsOut.push_back(*i);
      }
      
      
      Expr newbody;
      if(outBody.isAnd()){
	newbody=outBody[0].andExpr(innerBody);
      }
      else if(outBody.isImpl()){
	newbody=outBody[0].impExpr(innerBody);
      }
      
      Expr newQuantExpr;
      newQuantExpr = d_theoryCore->getEM()->newClosureExpr(FORALL, bVarsOut, newbody);
      
      return(newQuantExpr);
    }
    return thm_expr; // case cannot be handled now. 
  }
  
  else if (thm_expr.isExists()){
    if ((outBody.isAnd() && outBody[1].isExists()) ||
	(outBody.isImpl() && outBody[1].isExists())){
      
      vector<Expr> bVarsOut = thm_expr.getVars();
      
      const Expr innerExists = outBody[1];
      const Expr innerBody = innerExists.getBody();
      vector<Expr> bVarsIn = innerExists.getVars();
      
      for(vector<Expr>::iterator i=bVarsIn.begin(), iend=bVarsIn.end(); i!=iend; i++){
	bVarsOut.push_back(*i);
      }
      
      Expr newbody;
      if(outBody.isAnd()){
	newbody=outBody[0].andExpr(innerBody);
      }
      else if(outBody.isImpl()){
	newbody=outBody[0].impExpr(innerBody);
      }
      
      Expr newQuantExpr;
      newQuantExpr = d_theoryCore->getEM()->newClosureExpr(EXISTS, bVarsOut, newbody);
      
      return newQuantExpr;
    }
  }
  return thm_expr; 
}


CompleteInstPreProcessor::CompleteInstPreProcessor(TheoryCore * core, QuantProofRules* quant_rule):
  d_theoryCore(core),
  d_quant_rules(quant_rule)
{}

// collect all uninterpreted pedidates in assert
void CompleteInstPreProcessor::collectHeads(const Expr& assert, set<Expr>& heads){
  if ( ! assert.getType().isBool()){
    return;
  }
  else if ( ! assert.isAbsAtomicFormula()){
    for (int i = 0 ; i < assert.arity(); i++){
      collectHeads(assert[i], heads);    
    }
    return;
  }
  else if (assert.isClosure()){
    collectHeads(assert.getBody(), heads);    
  }
  else if (assert.isAtomicFormula()){
    if (isUniterpFunc(assert)){
      heads.insert(assert.getOp().getExpr());
    }
  }
  else{
    //    cout << " error in collect heads" << endl;
  }
}

bool CompleteInstPreProcessor::isMacro(const Expr& assert){
  if (d_is_macro_def.count(assert) > 0 ) {
    return true;
  }

  if (assert.isForall()){
    Expr body = assert.getBody();
    if (body.isIff()){
      Expr right = body[0];
      Expr left = body[1];
      if ((isUniterpFunc(right) && left.isForall())
	  || (right.isForall() && isUniterpFunc(left) )){
	    Expr macro_lhs ;
	    Expr macro_def;
	    if (isUniterpFunc(right)){
	      macro_lhs = right;
	      macro_def = left;
	    }
	    else{
	      macro_lhs = left;
	      macro_def = right;
	    }
	    
	    Expr test_def_exists = d_theoryCore->getEM()->newClosureExpr(EXISTS, assert.getVars(), macro_def);
	    
	    Expr test_def_sko = d_theoryCore->getCommonRules()->skolemize(test_def_exists);

	    if (isGoodQuant(test_def_sko)){
	      Expr macro_head = macro_lhs.getOp().getExpr();
	      set<Expr> heads_set;
	      collectHeads(macro_def, heads_set);
	      if (heads_set.count(macro_head) <= 0 ){
		d_is_macro_def[assert] = true;
		d_macro_quant[macro_head] = assert;
		d_macro_def[macro_head] = macro_def;
		d_macro_lhs[macro_head] = macro_lhs;
		return true;
	      }
	    }
	    else {
	      //     cout << "NOT good DEF" << def<< endl;
	    }
      }
    }
  }
  return false;
}

bool CompleteInstPreProcessor::hasMacros(const vector<Expr>& asserts){
  bool has_macros = false;
  for (size_t i = 0 ; i < asserts.size(); i++){
    if (isMacro(asserts[i])){
      has_macros = true;
    }
  }
  return has_macros;
}


Expr CompleteInstPreProcessor::substMacro(const Expr& old){
  Expr head = old.getOp().getExpr();
  
  DebugAssert(d_macro_lhs.count(head)>0, "macro lhs not found");
  DebugAssert(d_macro_def.count(head)>0, "macro def not found");
  DebugAssert(d_macro_quant.count(head)>0, "macro quant not found");

  Expr macro_lhs = d_macro_lhs[head];
  Expr macro_def = d_macro_def[head];
  Expr macro_quant = d_macro_quant[head];

  DebugAssert(head == macro_lhs.getOp().getExpr(), "impossible in substMacro");
  
  ExprMap<Expr> binding;
  for (int i = 0; i < macro_lhs.arity(); i++){
    if (macro_lhs[i].isBoundVar()){
      binding[macro_lhs[i]] = old[i];
    }
  }
  
  vector<Expr> quant_vars = macro_quant.getVars();
  
  vector<Expr> gterms;
  for (size_t i = 0 ; i < binding.size(); i++){
    gterms.push_back(binding[quant_vars[i]]);
  }
  
  return macro_def.substExpr(quant_vars,gterms);
}

Expr CompleteInstPreProcessor::simplifyEq(const Expr& assert){
  if ( ! assert.getType().isBool()){
    return assert;
  }
  else if ( ! assert.isAbsAtomicFormula()){
    vector<Expr> children ;
    for (int i = 0 ; i < assert.arity(); i++){
      children.push_back(simplifyEq(assert[i]));
    }
    return Expr(assert.getOp(),children);
  }
  else if (assert.isClosure()){
    Expr new_body = simplifyEq(assert.getBody());
    if (assert.isForall()){
      d_theoryCore->getEM()->newClosureExpr(FORALL, assert.getVars(), new_body);    
    }
    else if (assert.isExists()){
      d_theoryCore->getEM()->newClosureExpr(EXISTS, assert.getVars(), new_body);    
    }
    else{
      DebugAssert(false, "impossible case in recInstMacros");
    }
  }
  else if (assert.isAtomicFormula()){
    if (assert.isEq() && assert[0] == assert[1]){
      return d_theoryCore->trueExpr();
    }
    else {
      return assert;
    }
  }
  cout <<assert<<endl;
  DebugAssert(false, "impossible case in simplifyEq");
  return assert;
}


Expr CompleteInstPreProcessor::recInstMacros(const Expr& assert){
  if ( ! assert.getType().isBool()){
    return assert;
  }
  else if ( ! assert.isAbsAtomicFormula()){
    vector<Expr> children ;
    for (int i = 0 ; i < assert.arity(); i++){
      children.push_back(recInstMacros(assert[i]));
    }
    return Expr(assert.getOp(),children);
  }
  else if (assert.isClosure()){
    Expr new_body = recInstMacros(assert.getBody());
    if (assert.isForall()){
      d_theoryCore->getEM()->newClosureExpr(FORALL, assert.getVars(), new_body);    
    }
    else if (assert.isExists()){
      d_theoryCore->getEM()->newClosureExpr(EXISTS, assert.getVars(), new_body);    
    }
    else{
      DebugAssert(false, "impossible case in recInstMacros");
    }
  }
  else if (assert.isAtomicFormula()){

    if (isUniterpFunc(assert)){
      Expr assert_op = assert.getOp().getExpr();
      if ( d_macro_def.count(assert_op) > 0 ){
	return substMacro(assert);
      }
      else{
	return assert;
      }
    }
    else {
      return assert;
    }
  }

  DebugAssert(false, "impossible case in recInstMacors");
  return assert;

}

// if assert is a macro quant, then replace it with macro_quant_sub
Expr CompleteInstPreProcessor::instMacros(const Expr& assert, const Expr macro_quant_sub ){

  if (isMacro(assert)){
    return macro_quant_sub;
  }
  
  return recInstMacros(assert);
}

//if bound vars only appear as argument of uninterpreted function/predidate and array reads/writes. 
bool CompleteInstPreProcessor::isShield(const Expr& e){
  if (isGround(e)){
    return true;
  }
  else if (isUniterpFunc(e) && e.arity() > 0 ){
    for (int i = 0; i<e.arity(); i++){
      //      if ( ! ( isShield(e[i]) || e[i].isBoundVar())){
      if ( e[i].containsBoundVar() &&  ( ! e[i].isBoundVar() )){ //no nested   
	return false;
      }
    }
    return true;
  }
  else if (e.getKind() == READ){
    if ( isShield(e[0]) 
	 //	 && (e[1].isBoundVar()  || isShield(e[1])){
	 && (e[1].isBoundVar() || isGround(e[1]))){
      return true;
    }
    else {
      return false;
    }
  }
  else if (e.getKind() == WRITE){
    if ( isShield( e[0] ) 
      //	 && (e[1].isBoundVar() || isShield(e[1]))
	 && (e[1].isBoundVar() || isGround( e[1] ))
	 && ( isGround( e[2] ))){
      return true;
    }
    else {
      return false;
    }
  }
  else if (e.arity() > 0 ){
    for (int i = 0; i<e.arity(); i++){
      if (!isShield(e[i])){
	return false;
      }
    }
    return true;
  }
  else if (e.arity () == 0){
    return true;
  }
  DebugAssert(false, "impossible case in isShield");
  return false;
}

void findPolarityAtomic(const Expr& e, ExprMap<Polarity>& res, Polarity  pol){
  if(!e.getType().isBool()) return;
  //now a AND b will be given a polarity too, this is not necessary.
  if(res.count(e)>0){
    if ((Neg == res[e] && Pos == pol) || (Neg == res[e] && Pos == pol) ){
      res[e]=PosNeg;
    }
  }
  else{
    res[e]=pol;
  }

  //  cout <<"finding " << e << endl;

  if(PosNeg == pol){
    for(int i=0; i<e.arity(); i++){
      findPolarityAtomic(e[i], res, pol);
    }
  }
  else{
    Polarity neg_pol=Ukn;
    if(Pos == pol) {
      neg_pol = Neg;
    }
    else if(Neg == pol){
      neg_pol = Pos;
    }

    if(e.isImpl()){
      findPolarityAtomic(e[0], res, neg_pol);
      findPolarityAtomic(e[1], res, pol);
    }
    else if(e.isAnd() || e.isOr()){
      for(int i=0; i<e.arity(); i++){
	findPolarityAtomic(e[i], res, pol);
      }
    }
    else if(e.isNot()){
      findPolarityAtomic(e[0], res, neg_pol);
    }
    else if(e.isITE()){
      findPolarityAtomic(e[0], res, PosNeg);
      findPolarityAtomic(e[1], res, pol);
      findPolarityAtomic(e[2], res, pol);
    }
    else if(e.isClosure()){
      //      cout << " found closure " << endl;
      //      cout << e << endl;
      //findPolarityAtomic(e.getBody(), res, pol);
    }
    else if(e.isIff()){
      findPolarityAtomic(e[0], res, PosNeg);
      findPolarityAtomic(e[1], res, PosNeg);
    }
    else if(e.isXor()){
      findPolarityAtomic(e[0], res, neg_pol);
      findPolarityAtomic(e[1], res, neg_pol);
    }
    else if(e.isAtomicFormula()){
      return;
    }
    else{
      DebugAssert(false, "Error in find polarity in "+e.toString());
    }
  }
}

Expr CompleteInstPreProcessor::recSkolemize(const Expr& e, ExprMap<Polarity>& pol_map){

  if ( ! e.getType().isBool()){
    return e;
  }
  else if (e.isClosure()){
    if (e.isForall()) {
      return e;
    } 
    else if (e.isExists() && Pos == pol_map[e]){
      Expr new_body = recSkolemize(e.getBody(), pol_map);
      Expr new_quant = d_theoryCore->getEM()->newClosureExpr(EXISTS, e.getVars(), new_body);
      return d_theoryCore->getCommonRules()->skolemize(new_quant);
    }
  }
  else if (e.arity() > 0 ) {
    vector<Expr> children; 
    for (int i = 0 ; i < e.arity(); i++){
      Expr new_child = recSkolemize(e[i], pol_map);
      if (new_child.isNot() && new_child[0].isNot()){
	children.push_back(new_child[0][0]); //(not not expr) --> expr 
      }
      else{
	children.push_back(new_child);
      }
    }
    Expr new_expr = Expr(e.getOp(), children);
    if (new_expr.isNot() && new_expr[0].isNot()){
      return new_expr[0][0];
    }
    else {
      return new_expr;
    }
  }

  return e;
}

Expr CompleteInstPreProcessor::simplifyQuant(const Expr& e){
  //put all quant into postive form
  Expr pos_expr = rewriteNot(e);
  TRACE("simp-quant", e , "\n ---rewriteNot---> \n", pos_expr);

  Expr next_expr;
  if(e.isForall()){
    Theorem atoa = d_theoryCore->getCommonRules()->assumpRule(pos_expr);
    Theorem packVarThm = d_quant_rules->packVar(atoa);
    next_expr = packVarThm.getExpr();
  }
  else{
    next_expr = pos_expr;
  }
  //skolemize all postive exists, because we only care for satisfiablility now. 
  ExprMap<Polarity> pol_map;
  //  findPolarity(pos_expr, pol_map, Pos);
  findPolarity(next_expr, pol_map, Pos);
  //  Expr ret = recSkolemize(pos_expr, pol_map);
  Expr ret = recSkolemize(next_expr, pol_map);
  TRACE("simp-quant", e , "\n ---skolemize---> \n", ret);
  return ret;
}


Expr CompleteInstPreProcessor::rewriteNot(const Expr& e){
  ExprMap<Polarity> pol_map;
  findPolarity(e, pol_map, Pos);
  set<Expr> t = getBoundVars(e); //set containsBoundVar flag
  return recRewriteNot(e, pol_map);
}

Expr CompleteInstPreProcessor::recRewriteNot(const Expr & e,  ExprMap<Polarity>& pol_map){
  if ( ! e.getType().isBool()){
    return e;
  }

  if (isGround(e)){
    return e;
  }

  if (e.isClosure()){
    DebugAssert(pol_map.find(e) != pol_map.end(), "cannot find polarity" );
    if ( Neg == pol_map[e]){
      Expr body = recRewriteNot(e.getBody(), pol_map);
      Expr new_body = body.notExpr();
      Kind new_kind = e.isForall() ? EXISTS : FORALL;
      Expr new_quant = d_theoryCore->getEM()->newClosureExpr(new_kind,e.getVars(),new_body);
      Expr new_expr = new_quant.notExpr();
      return new_expr;
    }
    else { 
      //it is too much to deal with the case PosNeg == pol_map[e]
      //becasue PosNeg will be introduced for IFF and IF, 
      return e;
    }
  }
  else if (e.arity() > 0 ) {
    vector<Expr> children; 
    
    for (int i = 0 ; i < e.arity(); i++){
      Expr new_child = recRewriteNot(e[i], pol_map);
      if (new_child.isNot() && new_child[0].isNot()){
	children.push_back(new_child[0][0]); //(not not expr) --> expr 
      }
      else{
	children.push_back(new_child);
      }
    }
    
    Expr new_expr = Expr(e.getOp(), children);
    if (new_expr.isNot() && new_expr[0].isNot()){
      return new_expr[0][0];
    }
    else {
      return new_expr;
    }
  }
  else if (0 == e.arity() ){
    return e;
  }

  DebugAssert(false, "impossible in rewriteNot");
  return e;
}

void CompleteInstPreProcessor::addIndex(const Expr& e){
  if ( ! isInt(e.getType())) return;
  d_allIndex.insert(d_theoryCore->simplifyExpr(e));
}

Expr CompleteInstPreProcessor::plusOne(const Expr& e){
  Expr one = d_theoryCore->getEM()->newRatExpr(1);
  return Expr(PLUS, e, one);
}

Expr CompleteInstPreProcessor::minusOne(const Expr& e){
  Expr one = d_theoryCore->getEM()->newRatExpr(1);
  return Expr(MINUS, e, one);
}

void CompleteInstPreProcessor::collect_shield_index(const Expr& e){
  if (isUniterpFunc(e) && e.arity() > 0 ){
    for (int i = 0; i<e.arity(); i++){
      if ( isGround(e[i])){
	addIndex(e[i]);
      }
    }
  }
  else if (e.getKind() == READ){
    collect_shield_index(e[0]);
    if (isGround(e[1])){
      addIndex(e[1]);
    }
  }
  else if (e.getKind() == WRITE){
    collect_shield_index(e[0]);
    if ( isGround( e[1] )){
      addIndex(e[1]);
      addIndex(plusOne(e[1]));
      addIndex(minusOne(e[1]));
    }
  }
  else if (e.arity() > 0 ){
    for (int i = 0; i<e.arity(); i++){
      collect_shield_index(e[i]);
    }
  }
}

void CompleteInstPreProcessor::collect_forall_index(const Expr& forall_quant){
  ExprMap<Polarity> cur_expr_pol;
  findPolarity(forall_quant, cur_expr_pol, Pos);
  
  for (ExprMap<Polarity>::iterator i = cur_expr_pol.begin(), iend = cur_expr_pol.end(); i != iend ; i++){
    Expr cur_expr = i->first;
    Polarity pol = i->second; 
    
    if (isLE(cur_expr)){
      const Expr& left = cur_expr[0];
      const Expr& right = cur_expr[1];
      if (left.isBoundVar() && isGround(right)){
	if (Pos == pol || PosNeg == pol){
	  addIndex(plusOne(right));
	}
	if (Neg == pol || PosNeg == pol){
	  addIndex(right);
	}
      }
      else if (right.isBoundVar() && isGround(left)){
	if (Pos == pol || PosNeg == pol){
	  addIndex(plusOne(left));
	}
	if (Neg == pol || PosNeg == pol){
	  addIndex(left);
	}
      }
      else if (left.isBoundVar() && right.isBoundVar()){
	//do nothing
      }
      //well, neither left nor right is a bound var. 
      else if (isShield(left) && isShield(right)){
	collect_shield_index(left);
	collect_shield_index(right);
      }
      else{
	cout << " foall is " << forall_quant << endl; 
	DebugAssert(false, "impossible case in collect index ");
      } 
    }
    else if (cur_expr.isEq()){
      const Expr& left = cur_expr[0];
      const Expr& right = cur_expr[1];
      if (left.isBoundVar() && isGround(right)){
	if (Pos == pol || PosNeg == pol){
	  addIndex(minusOne(right));
	  addIndex(plusOne(right));
	}
	if (Neg == pol || PosNeg == pol){
	  addIndex(minusOne(right));
	}
      }
      else if (right.isBoundVar() && isGround(left)){
	if (Pos == pol || PosNeg == pol){
	  addIndex(minusOne(left));
	  addIndex(plusOne(left));
	}
	if (Neg == pol || PosNeg == pol){
	  addIndex(left);
	}
      }
      else if (left.isBoundVar() && right.isBoundVar()){
	DebugAssert(false, "impossible case collect index");
      }
      //well, neither left nor right is a bound var. 
      else if (isShield(left) && isShield(right)){
	collect_shield_index(left);
	collect_shield_index(right);
      }
      else{
	DebugAssert(false, "impossible case in collect index");
      } 
    }
    else if (isLT(cur_expr)){
      const Expr& left = cur_expr[0];
      const Expr& right = cur_expr[1];
      if (left.isBoundVar() && isGround(right)){
	if (Pos == pol || PosNeg == pol){
	  addIndex(plusOne(right));
	}
	if (Neg == pol || PosNeg == pol){
	  addIndex(right);
	}
      }
      else if (right.isBoundVar() && isGround(left)){
	if (Pos == pol || PosNeg == pol){
	  addIndex(plusOne(left));
	}
	if (Neg == pol || PosNeg == pol){
	  addIndex(left);
	}
      }
      else if (left.isBoundVar() && right.isBoundVar()){
	//do nothing
      }
      //well, neither left nor right is a bound var. 
      else if (isShield(left) && isShield(right)){
	collect_shield_index(left);
	collect_shield_index(right);
      }
      else{
	DebugAssert(false,  "impossible case in collect index");
      } 
    }
    else{
      collect_shield_index(cur_expr);
    }
  }
}


void CompleteInstPreProcessor::collectIndex(const Expr& assert){
  //  cout <<"BEGIN COLLECTING " << assert << endl;        
  //must be called after isGoodForCompleteInst;
  if(isGround(assert)){
    collect_shield_index(assert);
    return;
  }
  

  ExprMap<Polarity> cur_expr_pol;
  findPolarityAtomic(assert, cur_expr_pol, Pos);
  
  for(ExprMap<Polarity>::iterator i = cur_expr_pol.begin(), iend = cur_expr_pol.end(); i != iend; i++) {

    const Expr& cur_expr = i->first;
    Polarity pol = i->second;
    //    cout <<"NOW COLLECTING " << cur_expr << endl;        
    if (cur_expr.isAtomicFormula()){
      if (cur_expr.containsBoundVar()){
	DebugAssert(false, "error in collecting ");
	return;
      }
      collect_shield_index(cur_expr);
    }
    else if (cur_expr.isForall()){
      if (Pos != pol){
	DebugAssert(false, "error in polarity ");
	return;
      }
      Expr newQuant = pullVarOut(cur_expr);
      collect_forall_index(newQuant);
      //      cout <<"PUSH FORALL" << cur_expr << endl;
      d_quant_equiv_map[cur_expr] = newQuant;
    }
    else if (cur_expr.isExists()){
      if (Pos != pol){
	DebugAssert(false, "error in polarity " );
	return;
      }
      Expr newQuant = pullVarOut(cur_expr);
      Expr sko_expr = d_theoryCore->getCommonRules()->skolemize(newQuant);
      collect_forall_index(sko_expr);
      //      cout <<"PUSH EXISTS" << cur_expr << endl;
      d_quant_equiv_map[cur_expr] = sko_expr;
    }
  }   
  return;
}


bool CompleteInstPreProcessor::isGood(const Expr& assert){
  //  cout << " in isgood " << assert << endl;
  const std::set<Expr>& bvs = getBoundVars(assert);
  if (bvs.size() <= 0 ) {
    //    d_gnd_cache.push_back(e);
    //    cout << " return in isgood because no bound vars" << assert << endl;
    return true; //this is a ground formula, 
  }

  ExprMap<Polarity> cur_expr_pol;
  findPolarityAtomic(assert, cur_expr_pol, Pos);

  for(ExprMap<Polarity>::iterator i = cur_expr_pol.begin(),
	iend = cur_expr_pol.end();
      i != iend; i++) {
    
    const Expr& cur_expr = i->first;
    Polarity pol = i->second;
    
    //    cout <<"isgood cur expr " << cur_expr << endl;

    if(cur_expr.isForall()) {
      if (Pos == pol){
	if( isGoodQuant(cur_expr)){
	}
	else{
	  d_all_good = false;
	  return false;
	}
      }
      else {
	DebugAssert(false, "error, Neg polarity in isGood ");
	return false;
      }
    }
    else if (cur_expr.isExists()){
      DebugAssert(false, "error, found exists in is good");
      if (Neg == pol || PosNeg == pol){
	DebugAssert(false, "error, neg polarity in isGood ");
	return false;
      }
    }
  }
  return true;
}   
 
    //    if (cur_expr.isClosure()){ 
      
//       if( Pos == pol){
// 	Theorem newQuant;
// 	newQuant = (d_rules->pullVarOut(d_rules->addNewConst(cur_expr))).getExpr();
// 	if (cur_expr.isExists()){
// 	  Expr t = getCommonRules()->skolemize(newQuant);
// 	  d_quant_equiv_map[cur_expr] = t;
// 	  d_gnd_cache.push_Back(t); //used later by isGoodQuant and collectIndex
// 	}
// 	else if (cur_expr.isForall()){

// 	  if( isGoodQuantCompleteInst()){
// 	    d_quant_equiv_map[cur_expr] = newQuant;
// 	  }
// 	  else{
// 	    d_all_good = false;
// 	    return false;
// 	  }
// 	}
//       }
//       else{
// 	cout << "cannot deal with neg polarity now " << endl;
//       }
//     }
//     else if (cur_expr.isAtomicFormula()){
//       findPolarity(cur_expr, d_expr_pol, Pos); //used later by isGoodQuant and collectIndex
//     }
//   }
//  return true;
//}

bool CompleteInstPreProcessor::isGoodQuant(const Expr& e){
  //  cout << " test is good quant" << endl;
  //  const std::set<Expr>& bvs = getBoundVars(e);

  //  if (bvs.size() <= 0 ) {
  //    return true; //this is a ground formula, 
  //  }

  //  if (e.getVars().size() != bvs.size()){
  //    return false; // we can do more on this case later.
  //  }
  
  vector<Expr> bvs = e.getVars();
  
  for (vector<Expr>::iterator i = bvs.begin(), iend = bvs.end(); i != iend; i++){
    if ( ! isInt(i->getType() ) ){
      return false; //now only inteter can be handled
    }
  }

//   if (e.isExists()){
//     return true;
//   }

//  findPolarity(newQuant, d_expr_pol, Pos); //used later by isGoodQuant and collectIndex  
  ExprMap<Polarity> body_pol ;
  findPolarity(e, body_pol, Pos);

  for(ExprMap<Polarity>::iterator i = body_pol.begin(), iend = body_pol.end(); i != iend; i++) {
    if ((i->first).isAtomicFormula()){
      const Expr& cur_expr = i->first;
      Polarity pol = i->second;

      //      cout <<" good " << cur_expr << endl;
      if (!cur_expr.containsBoundVar()){
	continue; // this is a ground term, no need to do anything
      }
      else if (isShield(cur_expr)){
	continue; // this is good 
      }
      else if (isLE(cur_expr) || isLT(cur_expr) || cur_expr.isEq()){
	const Expr& left = cur_expr[0];
	const Expr& right = cur_expr[1];
	if (left.isBoundVar() && !right.containsBoundVar()){
	  continue; //good case
	}
	else if (right.isBoundVar() && !left.containsBoundVar()){
	  continue;
	}
	else if (left.isBoundVar() && right.isBoundVar()){
	  if (Neg == pol && isLE(cur_expr)){
	    continue;
	  }
	}
	//well, neither left nor right is a bound var. 
	else if (isShield(left) && isShield(right)){
	  continue;
	}
	//	cout << "RETURN 1 " << cur_expr << endl;
	return false; 
      }
      else{
	//	cout << "RETURN 2 " << cur_expr << endl;
	return false;
      }
    }
  }   
  return true;
}

class recCompleteInster{
  const Expr& d_body;
  const std::vector<Expr>& d_bvs;
  std::vector<Expr> d_buff;
  const std::set<Expr>& d_all_index;
  std::vector<Expr> d_exprs;
  Expr d_result;
  void inst_helper(int num_vars);
  Expr& build_tree();
public:
  recCompleteInster(const Expr&, const std::vector<Expr>&, std::set<Expr>& , Expr);
  Expr inst();
};

recCompleteInster::recCompleteInster(const Expr& body, const std::vector<Expr>& bvs, std::set<Expr>& all_index, Expr res): d_body(body),d_bvs(bvs), d_all_index(all_index),d_result(res){}

Expr recCompleteInster::inst(){
  d_buff.resize(d_bvs.size());
  //  cout << "there are " << d_all_index.size() << " gterms" << endl;
  inst_helper(d_bvs.size());
  return build_tree();
}

void recCompleteInster::inst_helper(int num_vars){
  if (1 == num_vars){
    for (set<Expr>::const_iterator i = d_all_index.begin(), iend = d_all_index.end();  i != iend; i++ ){
      d_buff[num_vars-1] = *i;
      d_exprs.push_back(d_body.substExpr(d_bvs,d_buff));
    }
  }
  else{
    for (set<Expr>::const_iterator i = d_all_index.begin(), iend = d_all_index.end();  i != iend; i++ ){
      d_buff[num_vars-1] = *i;
      inst_helper(num_vars-1);
    }
  }
}

Expr& recCompleteInster::build_tree() {
    std::vector<Expr>& d_old = d_exprs, d_new;
    while (d_old.size() > 1) {
        int old_size = d_old.size();
        for (int i = 0; i < old_size - 1; i += 2) {
            d_new.push_back(d_old[i].andExpr(d_old[i + 1]));
        }
        if (old_size % 2 == 1) {
            d_new.push_back(d_old[old_size - 1]);
        }
        d_old.clear();
        d_old.swap(d_new);
    }
    if (d_old.size() > 0) d_result = d_result.andExpr(d_old[0]);
    d_old.clear();
    return d_result;
}

Expr CompleteInstPreProcessor::inst(const Expr& assert){
  if(isGround(assert)){
    return assert;
  }
  else  if (assert.isExists()){
    DebugAssert(d_quant_equiv_map.count(assert) > 0,"assert not found" ) ;
    return d_quant_equiv_map[assert];
  }
  else if( ! assert.isForall()){
    if (assert.arity() > 0){
      vector<Expr> children;      
      for (int i = 0 ; i < assert.arity(); i++){
	Expr rep_child;
	rep_child = inst(assert[i]);
	children.push_back(rep_child);
      }
      return Expr(assert.getOp(), children);
    }
    else{
      DebugAssert(false, "error in inst");
      return assert;
    }
  }
  
  DebugAssert(assert.isForall(), "not a forall");
  DebugAssert(d_quant_equiv_map.count(assert) > 0, "assert not found" ) ;
  Expr forall = d_quant_equiv_map[assert];

  const vector<Expr>& bvs = forall.getVars(); 
  const Expr body = forall.getBody();
  vector<Expr> and_list;

  if(d_allIndex.size() == 0){
    addIndex(d_theoryCore->getEM()->newRatExpr(0));
  }

  if(bvs.size() == 1 ) {
    //    getBoundVars(body);
    for (set<Expr>::const_iterator i = d_allIndex.begin(), iend = d_allIndex.end(); 
	 i != iend; i++ ){
      vector<Expr> inst_st;
     
      inst_st.push_back(*i);

//       if(body.substExprQuant(bvs,inst_st) != body.substExpr(bvs,inst_st)){
// 	cout << "old " << body.substExpr(bvs,inst_st) << endl ;
// 	cout << "new " << body.substExprQuant(bvs,inst_st) << endl; 
//       }
	
      //and_list.push_back(body.substExprQuant(bvs,inst_st));
      and_list.push_back(body.substExpr(bvs,inst_st));
    }
    return Expr(AND,and_list);
  }
  else if (bvs.size() == 2 ){
    //    getBoundVars(body);
    for (set<Expr>::const_iterator i = d_allIndex.begin(), iend = d_allIndex.end(); 
	 i != iend; i++ ){
      for (set<Expr>::const_iterator j = d_allIndex.begin(), jend = d_allIndex.end(); 
	   j != jend; j++ ){
	vector<Expr> inst_st;
	inst_st.push_back(*i);
	inst_st.push_back(*j);
	
	//	cout << "== " << inst_st[0] << " " << inst_st[1] << endl;

// 	if(body.substExprQuant(bvs,inst_st) != body.substExpr(bvs,inst_st)){
// 	  cout << "old " << body.substExpr(bvs,inst_st) << endl ;
// 	  cout << "new " << body.substExprQuant(bvs,inst_st) << endl; 
// 	}

	//and_list.push_back(body.substExprQuant(bvs,inst_st));
	and_list.push_back(body.substExpr(bvs,inst_st));
	//	cout << "INST: " <<  body.substExpr(bvs,inst_st) << endl;
      }
    }
    //    cout << "we have " << and_list.size() << " ands " << endl;
    return Expr(AND,and_list);
  }
  //  else if ( 0 < bvs.size()  && bvs.size() <= 5 ){
  else{
    Expr init_expr = d_theoryCore->trueExpr();
    //    cout <<"we have " << bvs.size() << endl;
    recCompleteInster inster(body, bvs, d_allIndex, init_expr);
    //    cout<<inster.inst();
    return inster.inst();
  }
//   else{
//     DebugAssert(false, "More than five vars, too many.");
//   }
  return assert;
}

void flatAnds(const Expr& ands, vector<Expr>& results){
  if (ands.isAnd()){
    for(Expr::iterator i=ands.begin(), iend=ands.end(); i!=iend; ++i)    {
      flatAnds(*i,results);
    }
  }
  else if (ands.isNot() && ands[0].isOr()){
    for(Expr::iterator i=ands[0].begin(), iend=ands[0].end(); i!=iend; ++i)    {
      if(i->isNot()){
	flatAnds((*i)[0], results);
      }
      else{
	flatAnds(i->notExpr(), results);
      }
    }
  }
  else{
    results.push_back(ands);
  }
}

Theorem TheoryQuant::theoryPreprocess(const Expr& e){
  //  cout<<"theory process " << e << endl;

  if ( ! theoryCore()->getFlags()["quant-complete-inst"].getBool()){
    return reflexivityRule(e);
  }
  
  const std::set<Expr>& bvs = getBoundVars(e);
  if (bvs.size() <= 0){
    return reflexivityRule(e);
  }

  std::vector<Expr> assertList;
  flatAnds(e, assertList);
  
  CompleteInstPreProcessor comp_inst_proc(theoryCore(), d_rules);

  if (comp_inst_proc.hasMacros(assertList)){
    for(size_t i = 0; i < assertList.size();i++){
      //    cout << "== assert: " << i << " : " << assertList[i] << endl;
      assertList[i] = comp_inst_proc.instMacros(assertList[i], trueExpr().notExpr().notExpr());
    }
  }

  for(size_t i = 0; i < assertList.size() ; i++){
    //    cout << "BEFORE: " << assertList[i] << endl; 
    assertList[i] = comp_inst_proc.simplifyQuant(assertList[i]);
    //    cout << "AFTER: " << assertList[i] << endl; 
  }
  
  for(size_t i = 0; i < assertList.size() ; i++){
    if ( ! comp_inst_proc.isGood(assertList[i])){
      //      cout << " no good " << endl;
      //      cout << " because of " <<  assertList[i] << endl;
      return reflexivityRule(e);
    }
  }
  
  for(size_t i = 0; i < assertList.size() ; i++){
    //    cout << "collecting " << assertList[i] << endl;
    comp_inst_proc.collectIndex(assertList[i]);
  }

  vector<Expr> new_asserts; 
  for(size_t i = 0; i < assertList.size() ; i++){
    Expr new_asser = comp_inst_proc.inst(assertList[i]);
    getBoundVars(new_asser);
    if (new_asser.containsBoundVar()){
      return reflexivityRule(e);
    }
    else{
      new_asserts.push_back(new_asser);
    }
  }
    

  //  vector<Expr> all_index; 
  //  for(size_t i = 0; i < assertList.size() ; i++){
  //    collectIndex(assertList[i], all_index);
  //  }
  
  
//   set<Expr> inst_index;
//   for(size_t i = 0; i < all_index.size() ; i++){
//     if (isInt(all_index[i].getType())){
//       inst_index.insert(all_index[i]);
//     }
//     else{
//       cout <<"strange" << all_index[i] << endl;
//     }
//   }

//   int j(0);
//   for(set<Expr>::iterator i = inst_index.begin(), iend = inst_index.end();
//       i != iend; i++){
//     cout << "i=" << j++ << " " << *i << endl;
//   }
  

//   for(size_t i = 0; i < assertList.size() ; i++){
//     Expr& cur_expr = assertList[i];
//     if(cur_expr.isForall()){
//       Expr new_inst = instIndex(cur_expr, inst_index);
//       assertList[i] = new_inst;
//       //      cout << "new inst " << new_inst << endl;
//     }
//   }
  
//   for(size_t i = 0; i < assertList.size() ; i++){
//     //    cout << "AFTER i=" << i << " " << assertList[i] << endl;
//   }

  for(size_t i = 0; i < new_asserts.size() ; i++){
    new_asserts[i] = comp_inst_proc.simplifyEq(new_asserts[i]);
  }

  for(size_t i = 0; i < new_asserts.size() ; i++){
    //cout << ":assumption "  << new_asserts[i] << endl;
    //    cout << "NEW" << comp_inst_proc.inst(assertList[i]) << endl;
  }

  
  //this is really a bad way, add a new proof rule here
  Expr res = Expr(AND, new_asserts);
  Theorem ret_thm = d_rules->addNewConst(e.iffExpr(res));
  //  cout << "NEW THM " << ret_thm << endl;
  return ret_thm;
}




bool isGoodSysPredTrigger(const Expr& e){
  if(!isSysPred(e)) return false;
  if(usefulInMatch(e[0]) || usefulInMatch(e[1])) return true;
  return false;
}

bool isGoodFullTrigger(const Expr& e, const std::vector<Expr>& bVarsThm){
  if( !usefulInMatch(e))
    return false;

  const std::set<Expr>& bvs = getBoundVars(e);

  if (bvs.size() >= bVarsThm.size()){
     for(size_t i=0; i<bVarsThm.size(); i++)	{
       if (bvs.find(bVarsThm[i]) == bvs.end()){
	 return false;
       }
     }
     return true;
  }
  else {
    return false;
  }
}

bool isGoodMultiTrigger(const Expr& e, const std::vector<Expr>& bVarsThm, int offset){
  if( !usefulInMatch(e) )
    return false;

  int bvar_missing = 0;
  const std::set<Expr>& bvs = getBoundVars(e);

  if(bvs.size() <= 0) return false;

  for(size_t i=0; i<bVarsThm.size(); i++)	{
    if (bvs.find(bVarsThm[i]) == bvs.end()){
      bvar_missing++; // found one bound var missing in the e.
    }
  }

  if (0 == bvar_missing){ //it is a full triggers
    return false;
  }

  if(bvar_missing <= offset){
    if(isSysPred(e)){
      if (isGoodSysPredTrigger(e)) {
	return true;
      }
      else {
	return false;
      }
    }
    else {
      return true;
    }
  }
  return false;
}

bool isGoodPartTrigger(const Expr& e, const std::vector<Expr>& bVarsThm){
  if( !usefulInMatch(e) )
    return false;

  size_t bvar_missing = 0;
  const std::set<Expr>& bvs = getBoundVars(e);

  for(size_t i=0; i<bVarsThm.size(); i++)	{
    if (bvs.find(bVarsThm[i]) == bvs.end()){
      bvar_missing++; // found one bound var missing in the e.
    }
  }

  if (0 == bvar_missing){ //it is a full triggers
    return false;
  }

  if(0 == bvs.size()){
    return false;
  }

  if(bvar_missing < bVarsThm.size()){
    if(isSysPred(e)){
      if (isGoodSysPredTrigger(e)) {
	return true;
      }
      else {
	return false;
      }
    }
    else {
      return true;
    }
  }
  return false;
}


static bool recursiveGetPartTriggers(const Expr& e, std::vector<Expr>& res) {
  if(e.getFlag())
   return false;

  if(e.isClosure())
    return recursiveGetPartTriggers(e.getBody(), res);

  if(0 == e.arity()){
    if(BOUND_VAR == e.getKind()){
      return false;
    }
    else{
      return true;
    }
  }

  bool good=true;
  bool no_bound =true;

  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
    if(BOUND_VAR == i->getKind()){
      no_bound=false;
      continue;
    }
    bool temp = recursiveGetPartTriggers(*i,res);
    if(false == temp) {
      good=false;
    }
  }

  e.setFlag();

  if(good && no_bound) {
    return true;
  }
  else if(good && !no_bound){
    res.push_back(e);
    return false;
  }
  else{
    return false;
  }
}


std::vector<Expr> getPartTriggers(const Expr& e){
  e.clearFlags();
  std::vector<Expr> res;
  recursiveGetPartTriggers(e,res);
  e.clearFlags();
  return res;
}

int trigInitScore(const Expr& e){
  if( isSysPred(e) && !isGoodSysPredTrigger(e)){
    return 1;
  }
  else {
    return 0;
  }
}


void TheoryQuant::arrayIndexName(const Expr& e){
  std::vector<Expr> res;

  const std::vector<Expr>& subs=getSubTerms(e);

  for(size_t i=0; i<subs.size(); i++){
    int kind = subs[i].getKind();
    if (READ == kind || WRITE == kind){
      const Expr& name = subs[i][0];
      const Expr& index = subs[i][1];
      if(getBoundVars(name).size() <= 0 && (getBoundVars(index).size() <=0)){
	std::vector<Expr> tp = d_arrayIndic[name];
	tp.push_back(index);
	d_arrayIndic[name]=tp;
      }
      else {
      }
    }
  }
}

void TheoryQuant::registerTrig(ExprMap<ExprMap<std::vector<dynTrig>* >* >& cur_trig_map,
			       Trigger trig,
			       const std::vector<Expr> thmBVs,
			       size_t univ_id){
  {
    if(trig.hasRWOp){
      ExprMap<Expr> bv_map;
      dynTrig newDynTrig(trig, bv_map,univ_id);
      d_arrayTrigs.push_back(newDynTrig);
    }
  }

  ExprMap<Expr> bv_map;
  /*
  for(size_t i = 0; i<thmBVs.size(); i++){
    bv_map[thmBVs[i]] = null_expr;
  }
  */

//temp fix,
   for(size_t i = 0; i<thmBVs.size(); i++){
     bv_map[thmBVs[i]] = thmBVs[i];
   }



  const Expr& trig_ex = trig.getEx();

  Expr genTrig = trig_ex;
  //  Expr genTrig = generalTrig(trig_ex, bv_map);

  dynTrig newDynTrig(trig,bv_map,univ_id);

  Expr head = trig.getHead();

  ExprMap<ExprMap<vector<dynTrig>* >* >::iterator iter = cur_trig_map.find(head);
  if(cur_trig_map.end() == iter){
    ExprMap<vector<dynTrig>* >* new_cd_map= new  ExprMap<vector<dynTrig>* > ;
    cur_trig_map[head] = new_cd_map;
    vector<dynTrig>* new_dyntrig_list = new vector<dynTrig>;
    (*new_cd_map)[genTrig] = new_dyntrig_list;
    (*new_dyntrig_list).push_back(newDynTrig);
  }
  else{
    ExprMap<vector<dynTrig>* >* cd_map = iter->second;
    ExprMap<vector<dynTrig>* >::iterator iter_map = cd_map->find(genTrig);
    if(cd_map->end() == iter_map){
      vector<dynTrig>* new_dyntrig_list = new vector<dynTrig>;
      (*cd_map)[genTrig] = new_dyntrig_list;
      (*new_dyntrig_list).push_back(newDynTrig);
    }
    else{
      //      cout<<"never happen here" << endl;
      //      (*((*cd_map)[generalTrig])).push_back(newDynTrig);
      (*(iter_map->second)).push_back(newDynTrig);
    }
  }
}

/*
void TheoryQuant::registerTrigReal(Trigger trig, const std::vector<Expr> thmBVs, size_t univ_id){
  cout<<"register: "<<trig.getEx()<<endl;
  ExprMap<Expr> bv_map;
  for(size_t i = 0; i<thmBVs.size(); i++){
    bv_map[thmBVs[i]] = null_expr;
  }
  const Expr& trig_ex = trig.getEx();

  Expr genTrig = generalTrig(trig_ex, bv_map);

  dynTrig newDynTrig(trig,bv_map,univ_id);

  Expr head = trig.getHead();

  ExprMap<CDMap<Expr, CDList<dynTrig>* >* >::iterator iter = d_allmap_trigs.find(head);
  if(d_allmap_trigs.end() == iter){
    CDMap<Expr, CDList<dynTrig>* >* new_cd_map=
      new(true) CDMap<Expr, CDList<dynTrig>* > (theoryCore()->getCM()->getCurrentContext());
    d_allmap_trigs[head] = new_cd_map;
    CDList<dynTrig>* new_dyntrig_list = new(true) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
    (*new_cd_map)[genTrig] = new_dyntrig_list;
    (*new_dyntrig_list).push_back(newDynTrig);
  }
  else{
    CDMap<Expr, CDList<dynTrig>* >* cd_map = iter->second;
    CDMap<Expr, CDList<dynTrig>* >::iterator iter_map = cd_map->find(genTrig);
    if(cd_map->end() == iter_map){
      CDList<dynTrig>* new_dyntrig_list = new(true) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
      (*cd_map)[genTrig] = new_dyntrig_list;
      (*new_dyntrig_list).push_back(newDynTrig);
    }
    else{
      //      (*((*cd_map)[generalTrig])).push_back(newDynTrig);
      (*((*iter_map).second)).push_back(newDynTrig);
      cout<<"once more"<<endl;
    }
  }

}
*/

/*
Expr TheoryQuant::generalTrig(const Expr& trig, ExprMap<Expr>& bvs){
  //temp fix
  return trig;

  Expr newtrig = trig;
  getBoundVars(newtrig);


  size_t count =0 ;
  Expr res = recGeneralTrig(trig, bvs, count);
  getBoundVars(res);
  return res;

}


Expr TheoryQuant::recGeneralTrig(const Expr& trig, ExprMap<Expr>& bvs, size_t& mybvs_count){

  if (!trig.containsBoundVar()) return trig;
  if (BOUND_VAR == trig.getKind()){
    if (bvs.find(trig) != bvs.end()){
      const Expr& ubv = bvs[trig];
      if(null_expr ==ubv){
	Expr new_bv = d_mybvs[mybvs_count++];
	bvs[trig] = new_bv ;
	if((mybvs_count) >= MAX_TRIG_BVS ){
	  //	  cout<< "general trig error" <<endl;
	}
	else{
	  return new_bv;
	}
      }
      else{
	return bvs[trig];
      }
    }
    else{
      return d_mybvs[0];
    }
  }
  else{
    vector<Expr> children;
      for(Expr::iterator i=trig.begin(), iend=trig.end(); i!=iend; ++i){
	Expr repChild;
	if(i->containsBoundVar()){
	  repChild = recGeneralTrig(*i, bvs, mybvs_count);
	}
	else{
	  repChild = *i;
	}
	children.push_back(repChild);
      }
      return Expr(trig.getOp(), children);
  }
}

*/
//this function is used to check if two triggers can match with eath other
bool TheoryQuant::canMatch(const Expr& t1, const Expr& t2, ExprMap<Expr>& env){
  if(getBaseType(t1) != getBaseType(t2)) return false;

  if (BOUND_VAR == t1.getKind() || BOUND_VAR == t2.getKind()) {
    return true;
  }

  if ( (t1.arity() != t2.arity()) || (t1.getKind() != t2.getKind() )) {
    return false;
  }
  if (canGetHead(t1) && canGetHead(t2)) {
    if ( getHead(t1) != getHead(t2) ){
      return false;
    }
    for(int i=0; i<t1.arity(); i++){
      if (false == canMatch(t1[i], t2[i] , env))
	return false;
    }
    return true;
  }
  else{
    return false;
  }
}

bool TheoryQuant::isTransLike (const vector<Expr>& cur_trig){
  if(!(*d_useTrans)){
    return false;
  }
  if(3==cur_trig.size()){
    const Expr& t1=cur_trig[0];
    const Expr& t2=cur_trig[1];
    const Expr& t3=cur_trig[2];
    if ( canGetHead(t1) && canGetHead(t2) && canGetHead(t3) &&
	 (getHead(t1) == getHead(t2)) &&  (getHead(t2) == getHead(t3))){
      const std::set<Expr>& ts1 = getBoundVars(t1);
      const std::set<Expr>& ts2 = getBoundVars(t2);
      const std::set<Expr>& ts3 = getBoundVars(t3);
      if ( 2==ts1.size() && 2==ts2.size() && 2==ts2.size() &&
	   (ts1 != ts2) && (ts2 != ts3) && (ts3 != ts1)){
	std::set<Expr> all;
	for(set<Expr>::const_iterator i=ts1.begin(), iend = ts1.end(); i != iend; i++){
	  all.insert(*i);
	}
	for(set<Expr>::const_iterator i=ts2.begin(), iend = ts2.end(); i != iend; i++){
	  all.insert(*i);
	}
	for(set<Expr>::const_iterator i=ts3.begin(), iend = ts3.end(); i != iend; i++){
	  all.insert(*i);
	}
	bool res = true;
	if(3==all.size()){
	  for(set<Expr>::const_iterator i=all.begin(), iend = all.end(); i != iend; i++){
	    if(!i->isVar()) {
	      res = false;
	      break;
	    }
	  }
	  if(res) {
	  }
	  return res;
	}
      }
    }
  }
  return false;
}

bool TheoryQuant::isTrans2Like (const std::vector<Expr>& all_terms, const Expr& tr2){
  if(!(*d_useTrans2)){
    return false;
  }
  for(size_t i = 0; i < all_terms.size(); i++){
    if(all_terms[i].isEq()){
      const Expr& cur = all_terms[i];
      if(cur[0] != cur[1] && ( (cur[0]==tr2[0] && cur[1]==tr2[1]) || (cur[0]==tr2[1] && cur[1]==tr2[0]))){
	return true;
      }
    }
  }
  return false;
}


bool goodMultiTriggers(const std::vector<Expr>& exprs, const std::vector<Expr> bVars){
  ExprMap<bool> bvar_found;

  for( std::vector<Expr>::const_iterator i = bVars.begin(),  iend= bVars.end();  i!=iend; i++) {
    bvar_found[*i]=false;
  }

  for (size_t  i=0; i< exprs.size();i++){
    const std::set<Expr> & bv_in_trig = getBoundVars(exprs[i]);
    for(std::set<Expr>::const_iterator j=bv_in_trig.begin(), jend = bv_in_trig.end();  j != jend; j++){
      if(bvar_found.find(*j) != bvar_found.end()){
	bvar_found[*j]=true;
      }
    }
  }

  for( std::vector<Expr>::const_iterator i = bVars.begin(), iend= bVars.end();  i!=iend;  i++) {
    if(false == bvar_found[*i]){
      return false ;
    }
  }
  return true;
}


inline size_t locVar(const vector<Expr>& bvsThm, const Expr& bv){
  for(size_t i=0, iend = bvsThm.size(); i < iend; i++){
    if (bvsThm[i] == bv){
      return i;
    }
  }
  return 999; //this number should be big enough
}


void TheoryQuant::setupTriggers(ExprMap<ExprMap<vector<dynTrig>* >*>& trig_maps, const Theorem& thm, size_t univs_id){

  //  static std::vector<Expr> libQuant;
  const Expr& e = thm.getExpr();

  TRACE("triggers", "setup : "+int2string(e.getIndex()),  " | " , e.toString());

  d_univs.push_back(thm);
  const std::vector<Expr>& bVarsThm = e.getVars();
  if  (d_hasTriggers.count(e) > 0 ) {

    if(d_fullTrigs.count(e)>0){
      std::vector<Trigger>& new_trigs = d_fullTrigs[e];
      for(size_t i=0; i<new_trigs.size(); i++){
	registerTrig(trig_maps, new_trigs[i], bVarsThm, univs_id);
      }
    }
    //    if(0 == new_trigs.size() && d_multTrigs.count(e) > 0){
    if( d_multTrigs.count(e) > 0){
      std::vector<Trigger>& new_mult_trigs = d_multTrigs[e];
      for(size_t j=0; j<new_mult_trigs.size(); j++){
	registerTrig(trig_maps, new_mult_trigs[j], bVarsThm, univs_id);
      }
    }
    return;
  }

  if  (*d_useManTrig  ) {
    if(e.getTriggers().size() > 0) {
      //      cout<<"manual trig found"<<endl;
      //      cout<<vectorExpr2string(e.getTriggers())<<endl;
    }
  }

  d_hasTriggers[e]=true;

  TRACE("triggers-new", "setup : "+int2string(e.getIndex()),  " | " , e.toString());
  //  libQuant.push_back(e);

  //  const std::vector<Expr>& subterms = getSubTrig(e);
  const std::vector<Expr> subterms = getSubTrig(e);


// #ifdef _CVC3_DEBUG_MODE
//   if( CVC3::debugger.trace("triggers")  ){
//     cout<<"===========all sub terms =========="<<endl;
//     for (size_t i=0; i<subterms.size(); i++){
//       const Expr& sub = subterms[i];
//       cout<<"i="<< i << " : " << findExpr(sub) << " | " << sub << " and type is " << sub.getType()
// 	  << " and kind is " << sub.getEM()->getKindName(sub.getKind()) << endl;
//     }
//   }
// #endif

  ExprMap<Polarity> exprPol;
  findPolarity(e, exprPol, Pos);

  {// for full triggers
    std::vector<Expr> trig_list;
    std::vector<Expr> trig_cadt;
    for(std::vector<Expr>::const_iterator i = subterms.begin(),iend=subterms.end(); i!=iend; i++){
      if(isGoodFullTrigger(*i, bVarsThm)) {
	trig_cadt.push_back(*i);
      }
    }


    if(*d_useManTrig && e.getTriggers().size() > 0  ){
      std::vector<std::vector<Expr> > man_trigs = e.getTriggers();
      for(std::vector<std::vector<Expr> >::const_iterator i=man_trigs.begin(), iend=man_trigs.end(); i != iend; i++){
	if(1 == i->size()){
	  if (isGoodFullTrigger((*i)[0],bVarsThm)){
	    trig_list.push_back((*i)[0]);
	    //	    cout<<"full manual pushed "<<(*i)[0] << endl;
	  }
	  else{
	    //	    cout<<"full manual discarded "<<(*i)[0] << endl;
	  }
	  
	}
	//	else if(2 == i->arity()){
	else if(2 == i->size()){
	  if (isGoodFullTrigger((*i)[0], bVarsThm) && isGoodFullTrigger((*i)[1], bVarsThm)){
	    trig_list.push_back((*i)[0]);
	    trig_list.push_back((*i)[1]);
	    break; // it must be trans2like
	  }
	}
      }
    }
    else{
      for(size_t iter =0; iter < trig_cadt.size(); iter++) {
	Expr* i = &(trig_cadt[iter]);
	bool notfound = true;

	for(size_t index=0; index< trig_list.size(); index++){
	  if (i->subExprOf(trig_list[index])) {
	    trig_list[index]=*i;
	    notfound=false;
	    break;
	  }
	  if (trig_list[index].subExprOf(*i)) {
	    notfound=false;
	    break;
	  }
	}
	if (notfound) {
	  trig_list.push_back(*i);
	}
      }
    }

    std::vector<Trigger> trig_ex;

    for (size_t  i=0; i< trig_list.size();i++){
      const Expr& cur = trig_list[i];
      const std::set<Expr> cur_bvs = getBoundVars(cur);
      int score = trigInitScore(cur);
      if(score > 0) continue;

      //1. test trans2
      //2. test whether a trigger can trig a bigger instance of itself, now we have no actions for such case because we use expr score and dynamic loop prevention.

      for(size_t j=0; j< trig_cadt.size(); j++){
	if (trig_list[i] == trig_cadt[j]) continue;
	ExprMap<Expr> null;
	if (canMatch(trig_list[i], trig_cadt[j], null)){
	  if(exprScore(trig_list[i]) < exprScore(trig_cadt[j])){
	  }
	  else if(*d_useTrans2 &&
		  trig_list.size() == 2 &&
		  trig_list[i].arity() == 2 &&
		  BOUND_VAR == trig_list[i][0].getKind() &&
		  BOUND_VAR == trig_list[i][1].getKind() &&
		  BOUND_VAR == trig_cadt[j][0].getKind() &&
		  BOUND_VAR == trig_cadt[j][1].getKind() &&
		  isTrans2Like(subterms, trig_list[i])
		  ){

	    score =0; //useless, to delete;
	    d_trans2_num++;

	    DebugAssert(d_trans2_num<=1, "more than 2 trans2 found");
	    TRACE("triggers",  "trans2 found ", trig_list[i], "");

	    Trigger t(theoryCore(), cur, Neg, cur_bvs);
	    t.setTrans2(true);
	    t.setHead(getHeadExpr(cur));
	    if(isSimpleTrig(cur)){
	      t.setSimp();
	    }
	    if(isSuperSimpleTrig(cur)){
	      t.setSuperSimp();
	    }
	    d_fullTrigs[e].push_back(t);
	    registerTrig(trig_maps,t, bVarsThm, univs_id);
	    return;
	  }
	  else{
	    score =0;
	  }
	}
      }

      Polarity pol= Ukn;

      if(cur.getType().isBool()){
	DebugAssert(exprPol.count(e)>0,"unknown polarity:"+cur.toString());
	pol = exprPol[cur];
      }

      Trigger* t;
      Trigger* t_ex; //so, if a pred is PosNeg, we actually put two triggers into the list, one pos and the other neg

      if(PosNeg == pol && *d_usePolarity){
	t = new Trigger(theoryCore(), cur, Pos, cur_bvs);
	t_ex = new Trigger(theoryCore(), cur, Neg, cur_bvs);
	if(isSimpleTrig(cur)){
	  t->setSimp();
	  t_ex->setSimp();
	}
	if(isSuperSimpleTrig(cur)){
	  t->setSuperSimp();
	  t_ex->setSuperSimp();
	}

      }
      else{
	t = new Trigger(theoryCore(), cur, pol, cur_bvs);
	if(isSimpleTrig(cur)){
	  t->setSimp();
	}
	if(isSuperSimpleTrig(cur)){
	  t->setSuperSimp();
	}
	t_ex = NULL;
      }

      if(canGetHead(cur)) {
	t->setHead(getHeadExpr(cur));
	if(NULL != t_ex){
	  t_ex->setHead(getHeadExpr(cur));
	}
      }
      else{
	if(!isSysPred(cur)){
	  //	  cout<<"cur " << cur <<endl;
	  //	  DebugAssert(false, "why this is a trigger");
	}
      }

      t->setRWOp(false);

      if(READ == cur.getKind() || WRITE == cur.getKind()){
	arrayIndexName(cur);
      }

      if(READ == cur.getKind() && WRITE== cur[0].getKind() && 1 == bVarsThm.size() ){
	//	cout<<t->trig<<endl;
	t->setRWOp(true);
	if(t_ex != NULL) t_ex->setRWOp(true);
      }

      if(t_ex != NULL)  {
	trig_ex.push_back(*t_ex);
      }

      d_fullTrigs[e].push_back(*t);
      registerTrig(trig_maps,*t, bVarsThm, univs_id);

      TRACE("triggers", "new:full triggers:", cur.toString(),"");
      TRACE("triggers", "new:full trigger score:", score,"");
      TRACE("triggers", "new:full trigger pol:", pol,"");
    }

    if(e.getTriggers().size() > 0) {
      //      cout<<"#### manual_trig: ";
      //      cout<<vectorExpr2string(e.getTriggers())<<endl;
    }


    for(size_t i=0; i<trig_ex.size(); i++){
      d_fullTrigs[e].push_back(trig_ex[i]);
      registerTrig(trig_maps,trig_ex[i], bVarsThm, univs_id);
      TRACE("triggers", "new extra :full triggers:", trig_ex[i].getEx().toString(),"");
    }

    if(d_fullTrigs[e].size() == 0){
      TRACE("triggers warning", "no full trig: ", e , "");
    }
  }

  //  if(0 == d_fullTrigs[e].size() && *d_useMult )
  if(0 == d_fullTrigs[e].size())
    {  //setup multriggers
      std::vector<Expr>& cur_trig = d_multTriggers[e];
      if(*d_useManTrig && e.getTriggers().size() > 0 ){
	std::vector<std::vector<Expr> > man_trig = e.getTriggers();
	int count(0);
	for(std::vector<std::vector<Expr> >::const_iterator i = man_trig.begin(), iend = man_trig.end(); i != iend; i++){
	  //	  if (i->arity() > 1) count++;
	  if (i->size() > 1) count++;
	  //	  cout << "count" << count << " " <<  *i << endl;
	}
	/*
	if(count > 1){
	  
	  //cout<<"en, cannot handle this now"<<endl;

	}
	//	if(man_trig[count-1].arity() != 2){
	if(man_trig[count-1].size() != 2){
	  //	  cout<<man_trig[count-1]<<endl;
	  //	  cout<<"sorry, only two exprs are handled now"<<endl;
	  //cout<<man_trig[count-1]<<endl;
	  //cout<<"sorry, only two exprs are handled now"<<endl;

	  }*/
	if (1 == count && 2 == man_trig[count-1].size()){
	  for(std::vector<Expr>::const_iterator j = man_trig[count-1].begin(), jend = man_trig[count-1].end(); j != jend; ++j){
	    cur_trig.push_back(*j);
	  }
	  if (! goodMultiTriggers(cur_trig, bVarsThm)){
	    cur_trig.clear();
	    return;
	  }
	}
      }
      else{
	for( std::vector<Expr>::const_iterator i = subterms.begin(),  iend=subterms.end();  i!=iend;  i++) {
	  if(isGoodMultiTrigger(*i, bVarsThm, d_offset_multi_trig))  {
	    bool notfound = true;
	    for(size_t index=0; index<d_multTriggers[e].size(); index++){
	      if (i->subExprOf(d_multTriggers[e][index]))    {
		(d_multTriggers[e][index])=*i;
		notfound=false;
	      }
	    }
	    if (notfound){
	      d_multTriggers[e].push_back(*i);
	    }
	  }
	}

	if (goodMultiTriggers(cur_trig, bVarsThm)){
	  //	cout<<"good multi triggers"<<endl;
	  TRACE("multi-triggers", "good set of multi triggers","","");
	  for (size_t  i=0; i< d_multTriggers[e].size();i++){
	    //	  cout<<"multi-triggers" <<d_multTriggers[e][i]<<endl;
	    TRACE("multi-triggers", "multi-triggers:", d_multTriggers[e][i].toString(),"");
	  }
	}
	else{
	  cur_trig.clear();
	  //	  cout<<"bad multi triggers"<<endl;
	  TRACE("multi-triggers", "bad set of multi triggers","","");
	  return;
	}

      }

      //special code for transitive pred,
      {
	if(isTransLike(cur_trig)){
	  d_trans_num++;
	  DebugAssert(d_trans_num <= 1, "more than one trans found");

	  Expr ex = cur_trig[0];

	  Trigger* trans_trig = new Trigger(theoryCore(), ex, Neg, getBoundVars(ex));
	  trans_trig->setHead(getHeadExpr(ex));
	  if(isSimpleTrig(ex)){
	    trans_trig->setSimp();
	  }
	  if(isSuperSimpleTrig(ex)){
	    trans_trig->setSuperSimp();
	  }

	  trans_trig->setTrans(true);

	  d_fullTrigs[e].push_back(*trans_trig);
	  registerTrig(trig_maps,*trans_trig, bVarsThm, univs_id);
	  cur_trig.clear();
	  TRACE("triggers", " trans like found ", ex, "");
	  d_transThm = thm;
	}
      }

      //enhanced multi-triggers
      //      if(cur_trig.size() >0 && !(*d_useManTrig)){
      if(cur_trig.size() >0 ){
	//  if(cur_trig.size() >0 ){
	std::vector<Expr> posList, negList;
	for(size_t k=0; k<cur_trig.size(); k++){
	  const Expr& cur_item = cur_trig[k];
	  if (cur_item.getType().isBool()){
	    Polarity pol = exprPol[cur_item];
	    if(PosNeg == pol || Pos == pol){
	      posList.push_back(cur_item);
	    }
	    if(PosNeg == pol || Neg == pol){
	      negList.push_back(cur_item);
	    }
	  }
	}
	if (goodMultiTriggers(posList, bVarsThm)){
	  TRACE("multi-triggers", "good set of multi triggers pos","","");
	  for (size_t  i=0; i< posList.size();i++){
	    TRACE("multi-triggers", "multi-triggers:", posList[i].toString(),"");
	  }
	  cur_trig.clear();
	  for(size_t m=0; m<posList.size(); m++){
	    cur_trig.push_back(posList[m]);
	  }
	}
	if (goodMultiTriggers(negList, bVarsThm) && negList.size() < cur_trig.size()){
	  TRACE("multi-triggers", "good set of multi triggers neg","","");
	  for (size_t  i=0; i< negList.size();i++){
	    TRACE("multi-triggers", "multi-triggers:", negList[i].toString(),"");
	  }
	  cur_trig.clear();
	  for(size_t m=0; m<negList.size(); m++){
	    cur_trig.push_back(negList[m]);
	  }
	}
      }

      {//new way of multi trigger

	if(!(*d_useManTrig) || e.getTriggers().size() <= 0){
	//	if(!(*d_useManTrig)){
	  if( 3 == cur_trig.size() ||  4 == cur_trig.size() || 5 == cur_trig.size() || 6 == cur_trig.size()  ){
	    for(size_t i = 0; i < cur_trig.size(); i++){
	      for(size_t j = 0; j < i; j++){
		vector<Expr> tempList;
		tempList.clear();
		tempList.push_back(cur_trig[i]);
		tempList.push_back(cur_trig[j]);
		//	      cout<<i<<" | "<<j<<endl;
		//	      cout<<vectorExpr2string(tempList)<<endl;
		if (goodMultiTriggers(tempList, bVarsThm)){
		  cur_trig.clear();
		  cur_trig.push_back(tempList[0]);
		  cur_trig.push_back(tempList[1]);
		  //		  cout << "good multi triggers" << endl;
		  //		  cout << (tempList[0]) << endl;
		  //		  cout << (tempList[1]) << endl;
		  break;
	      }
	      }
	    }
	  }
	}

	if(cur_trig.size() != 2){
	  if( 0 == cur_trig.size()){
	    return;
	  }
	  //	  FatalAssert(false, "unsupported multi-triggers");
	  //	  cout<<"e: "<<e<<endl;
	  //	  cout<<cur_trig.size()<<endl;
	  //	  cout<<bVarsThm.size()<<endl;

	  //	  cout<<vectorExpr2string(bVarsThm)<<endl;
	  //	  for(size_t i =0; i<cur_trig.size(); i++){
	  //	    cout<<cur_trig[i]<<endl;
	  //	  }
	  return;
	}

	//	cout<<"== new multi-trig ==" << endl;
	for(size_t i = 0 ; i<cur_trig.size(); i++){
	  set<Expr> bvs = getBoundVars(cur_trig[i]);
	  Trigger trig(theoryCore(), cur_trig[i], Ukn, bvs); //
	  //	  cout<<"new way of multi-trig"<<cur_trig[i]<<endl;
	  trig.setHead(getHead(cur_trig[i]));
	  trig.setMultiTrig();
	  trig.multiIndex = i;
	  trig.multiId=d_all_multTrigsInfo.size();
	  d_multTrigs[e].push_back(trig);
	  registerTrig(trig_maps, trig, bVarsThm, univs_id);
	}

	{
	  multTrigsInfo multTrigs;
	  for(size_t i =0, iend = d_multTrigs[e].size(); i<iend; i++){
	    const std::vector<Expr>& one_set_bvs = d_multTrigs[e][i].bvs;
	    std::vector<size_t> one_set_pos;

	    for(size_t v = 0, vend = one_set_bvs.size(); v<vend; v++){
	      size_t loc = locVar(bVarsThm, one_set_bvs[v]);
	      if( 999 != loc ){
		one_set_pos.push_back(loc);
	      }
	    }

	    sort(one_set_pos.begin(), one_set_pos.end());

	    for(size_t v = 0, vend = one_set_pos.size(); v<vend; v++){
	    }

	    multTrigs.var_pos.push_back(one_set_pos);
	  }//setup pos of all multi tirggers

	  //now we only consider two multi triggers
	  vector<size_t> common;
	  std::vector<size_t>& tar1 = multTrigs.var_pos[0];
	  std::vector<size_t>& tar2 = multTrigs.var_pos[1];
	  vector<size_t>::iterator t1(tar1.begin()), t2(tar2.begin());
	  while(t1 != tar1.end() && t2!= tar2.end()){
	    size_t pos1 = *t1;
	    size_t pos2 = *t2;
	    if( pos1  == pos2 ) {
	      common.push_back(pos1);
	      t1=tar1.erase(t1);
	      t2=tar2.erase(t2);
	    }
	    else if( pos1 > pos2 ){
	      t2++;
	    }
	    else {
	      t1++;
	    }
	  }
	  multTrigs.common_pos.push_back(common);

	  size_t multi_size = d_multTrigs[e].size(); //should be 2
	  for(size_t i =0; i< multi_size; i++){
	    multTrigs.var_binds_found.push_back(new (true) CDMap<Expr, bool> (theoryCore()->getCM()->getCurrentContext()));
	  }
	  multTrigs.uncomm_list.push_back(new ExprMap<CDList<Expr>* >);
	  multTrigs.uncomm_list.push_back(new ExprMap<CDList<Expr>* >);
	  multTrigs.univThm = thm;
	  multTrigs.univ_id = univs_id;
	  d_multitrigs_maps[e] = multTrigs;
	  d_all_multTrigsInfo.push_back(multTrigs);
	}
      }
    }

  /*
  //setup partial triggers
  if(*d_usePart)    {
    std::vector<Trigger> trig_ex;

    trig_ex.clear();
    for( std::vector<Expr>::const_iterator i = subterms.begin(),  iend=subterms.end();  i!=iend;  i++) {
      if(isGoodPartTrigger(*i, bVarsThm))  {
	bool notfound = true;
	for(size_t index=0; index<d_partTriggers[e].size(); index++){
	  if (i->subExprOf(d_partTriggers[e][index]))    {
	    (d_partTriggers[e][index])=*i;
	    notfound=false;
	  }
	}
	if (notfound)
	  d_partTriggers[e].push_back(*i);
      }
    }

    for (size_t  i=0; i< d_partTriggers[e].size();i++){
      TRACE("triggers", "partial triggers:", d_partTriggers[e][i].toString(),"");
    }

    for (size_t  i=0; i< d_partTriggers[e].size();i++){
      Polarity pol= Ukn;
      const Expr& cur = d_partTriggers[e][i];
      const std::set<Expr> cur_bvs = getBoundVars(cur);
      if(cur.getType().isBool()){
	DebugAssert(exprPol.count(e)>0,"unknown polarity:"+cur.toString());
	pol = exprPol[cur];
      }

      Trigger* t;
      Trigger* t_ex; //so, if a pred is PosNeg, we actually put two triggers into the list, one pos and the other neg

      if(PosNeg == pol && *d_usePolarity){
	t = new Trigger(theoryCore(), cur, Pos, cur_bvs);
	t_ex = new Trigger(theoryCore(), cur, Neg, cur_bvs);
      }
      else{
	t = new Trigger(theoryCore(), cur, pol, cur_bvs);
	t_ex = NULL;
      }

      if(canGetHead(cur)) {
	t->setHead(getHeadExpr(cur));
      }

      if(t_ex != NULL)  trig_ex.push_back(*t_ex);

      d_partTrigs[e].push_back(*t);

      TRACE("triggers", "new:part trigger pol:", pol,cur.toString());
    }

    for(size_t i=0; i<trig_ex.size(); i++){
      d_partTrigs[e].push_back(trig_ex[i]);
      TRACE("triggers", "new extra :part triggers:", trig_ex[i].getEx().toString(),"");
    }
  }
  */
}


//! test if a sub-term contains more bounded vars than quantified by out-most quantifier.
int hasMoreBVs(const Expr& thm){
  DebugAssert(thm.isForall(), "hasMoreBVS called by non-forall exprs");

  const std::vector<Expr>& bvsOutmost = thm.getVars();
  const std::set<Expr>& bvs = getBoundVars(thm);

  return int(bvs.size()-bvsOutmost.size());

}

/*! \brief Theory interface function to assert quantified formulas
 *
 * pushes in negations and converts to either universally or existentially
 * quantified theorems. Universals are stored in a database while
 * existentials are enqueued to be handled by the search engine.
 */

//static ExprMap<bool> found_exist;

void TheoryQuant::assertFact(const Theorem& thm){

  if(d_maxILReached){
    return;
  }
  if(*d_translate) return;

  TRACE("quant assertfact", "assertFact => ", thm.toString(), "{");
  Theorem rule, result;
  const Expr& expr = thm.getExpr();

  // Ignore existentials
  if(expr.isExists()) {
    TRACE("quant assertfact", "assertFact => (ignoring existential) }", expr.toString(), "");
    return;
  }

  DebugAssert(expr.isForall() || (expr.isNot() && (expr[0].isExists() || expr[0].isForall())),
	      "Theory of quantifiers cannot handle expression "
	     + expr.toString());

 if(expr.isNot()) {//find the right rule to eliminate negation
   if(expr[0].isForall()) {
     rule = d_rules->rewriteNotForall(expr);
   }
   else if(expr[0].isExists()) {
     rule = d_rules->rewriteNotExists(expr);
   }
   result = iffMP(thm, rule);
 }
 else{
   result = thm;
 }

 result = d_rules->boundVarElim(result); //eliminate useless bound variables


 if(result.getExpr().isForall()){

   // Added by Clark:
   // If domain of quantified variable is finite and not too big, just do complete instantiation
   const vector<Expr>& vars = result.getExpr().getVars();
   Unsigned u, count = 1;
   Cardinality card;
   vector<Expr>::const_iterator it = vars.begin(), iend = vars.end();
   for (; it != iend; ++it) {
     card = (*it).getType().card();
     if (card != CARD_FINITE) {
       count = 0;
       break;
     }
     u = (*it).getType().sizeFinite();
     if (u > 100) u = 0;
     count = count * u;
     if (count == 0 || count > 100) {
       count = 0;
       break;
     }
   }
   bool incomplete = false;
   if (count > 0 && count <= 100) {
     vector<Expr> terms(vars.size());
     vector<Unsigned> indices(vars.size());
     for (unsigned i = 0; i < vars.size(); ++i) {
       indices[i] = 0;
       terms[i] = vars[i].getType().enumerateFinite(0);
       if (terms[i].isNull()) {
         incomplete = true;
         break;
       }
     }
     Theorem thm;
     unsigned i = 0;
     for (;;) {
       thm = d_rules->universalInst(result, terms, 0);
       enqueueFact(thm);
       while (i < indices.size()) {
         indices[i] = indices[i] + 1;
         if (indices[i] < vars[i].getType().sizeFinite()) {
           terms[i] = vars[i].getType().enumerateFinite(indices[i]);
           if (terms[i].isNull()) {
             incomplete = true;
             i = indices.size();
           }
           break;
         }
         ++i;
       }
       if (i > 0) {
         if (i == indices.size()) break;
         for (unsigned j = 0; j < i; ++j) {
           indices[j] = 0;
           terms[j] = vars[j].getType().enumerateFinite(0);
         }
         i = 0;
       }
     }
     if (!incomplete) return;
   }

   if(*d_useNew){

     if(result.getExpr().getBody().isForall()){ // if it is of the form forall x. forall. y
       result=d_rules->packVar(result);
     }
     result = d_rules->boundVarElim(result); //eliminate useless bound variables
     
     //      int nBVs = hasMoreBVs(result.getExpr());
     //      if( nBVs >= 1){
     //	d_hasMoreBVs[result.getExpr()]=true;
     //      }

     if(result.getExpr().isForall()){
       d_rawUnivs.push_back(result);
     }
     else{
       enqueueFact(result);
     }
     return;
     /* -------------------------------------- */
     //      int nBVs = hasMoreBVs(result.getExpr());

     /*

     if(0 == nBVs){//good
     TRACE("quant assertfact", "assertFact => forall enqueueing: ", result.toString(), "}");
      	d_univs.push_back(result);
	setupTriggers(result, d_univs.size()-1);
      }
      else if(1== nBVs){
	d_hasMoreBVs[result.getExpr()]=true;
	const Expr& body = result.getExpr().getBody();

	if(*d_usePullVar){
	  if((body.isAnd() && body[1].isForall()) || (body.isImpl() && body[1].isForall()) ){
	    result=d_rules->pullVarOut(result);

	    TRACE("quant assertfact", "assertFact => pull-var enqueueing: ", result.toString(), "}");

	    d_univs.push_back(result);
	    setupTriggers(result,  d_univs.size()-1);
	  }
	}
	else{
	  TRACE("quant assertfact", "debug:not recognized case", result.toString(), thm.toString());

	  d_univs.push_back(result);
	  setupTriggers(result,  d_univs.size()-1);
	  return;
	}
      }
      else{
	d_hasMoreBVs[result.getExpr()]=true;
	d_univs.push_back(result);
	setupTriggers(result,  d_univs.size()-1);
	return;
      }
      */
   }
   else{

     TRACE("quant assertfact", "assertFact => old-fashoin enqueueing: ", result.toString(), "}");
     //      cout<<"error"<<endl;
     d_univs.push_back(result);
   }
 }
 else { //quantifier got eliminated or is an existantial formula
   TRACE("quant assertfact", "assertFact => non-forall enqueueing: ", result.toString(), "}");
   if(*d_useGFact || true ){
     //      addGlobalLemma(result, -1);
     enqueueFact(result);
   }
   else{
     enqueueFact(result);
     //    enqueueSE(result);
   }
   /*
     {
     Expr expr = result.getExpr();
     if(expr.isNot()) {
     expr = expr[0];
     }  ;
     if (expr.isExists()){
     if(found_exist.find(expr) != found_exist.end()) {
     //	  cout<<"again " << expr<<endl;
     return;
     }
     else  found_exist[expr]=true;
     }
     }
   */

   //
 }
}

void TheoryQuant::recGoodSemMatch(const Expr& e,
				  const std::vector<Expr>& bVars,
				  std::vector<Expr>& newInst,
				  std::set<std::vector<Expr> >& instSet)
{
  size_t curPos = newInst.size();
  if (bVars.size() == curPos)    {
    Expr simpleExpr = simplifyExpr(e.substExpr(bVars,newInst));
    if (simpleExpr.hasFind()){
      std::vector<Expr> temp = newInst;
      instSet.insert(temp);
      TRACE("quant yeting", "new inst found for ", e.toString()+" ==> ", simpleExpr.toString());
    };
  }
  else {
    Type t = getBaseType(bVars[curPos]);
    std::vector<Expr> tyExprs= d_typeExprMap[t];
    if (0 == tyExprs.size())  {
      return;//has some problem
    }
    else{
      for (size_t i=0;i<tyExprs.size();i++){
	newInst.push_back(tyExprs[i]);
	recGoodSemMatch(e,bVars,newInst,instSet);
	newInst.pop_back();
      }
    }
  }
}


bool isIntx(const Expr& e, const Rational& x){
  if(e.isRational() && e.getRational()==x)
    return true;
  else return false;
}


Expr getLeft(const Expr& e){
  if(e.getKind()!= PLUS) return null_expr;
  if(e.arity() != 3) return null_expr;
  Expr const_expr, minus ,pos;
  int numMinus=0, numPos=0, numConst=0;;
  for(int i=0; i<e.arity(); i++){
    if((e[i]).getKind() == MULT){
      if(isIntx(e[i][0], -1)){
	numMinus++;
	minus=e[i][1];
      }
      else{
	numPos++;
	pos=e[i];
      }
    }
    else if(e[i].isRational())      {
      const_expr = e[i];
      numConst++;
    }
    else{
      numPos++;
      pos=e[i];
    }
  }
  if(1==numPos && 1==numConst && 1==numMinus){
    return minus;
  }
  else{
    return null_expr;
  }
}

Expr getRight(const Expr& e){
  if(e.getKind()!= PLUS) return null_expr;
  if(e.arity() != 3) return null_expr;
  Expr const_expr, minus ,pos;
  int numMinus=0, numPos=0, numConst=0;;

  for(int i=0; i<e.arity(); i++){
    if((e[i]).getKind() == MULT){
      if(isIntx(e[i][0], -1)){
	numMinus++;
	minus=e[i][1];
      }
      else{
	numPos++;
	pos=e[i];
      }
    }
    else if(e[i].isRational())      {
      const_expr = e[i];
      numConst++;
    }
    else{
      numPos++;
      pos=e[i];
    }
  }

  if(1==numPos && 1==numConst && 1==numMinus){
    if(isIntx(const_expr,0)){
      return pos;
    }
    else{
      //      return null_expr;
      return Expr(PLUS, const_expr, pos);
    }
  }
  else{
    return null_expr;
  }
  return null_expr;
}

inline void TheoryQuant::add_parent(const Expr& parent){
  ExprMap<CDList<Expr>* >::iterator iter;
  for(int i=0; i< parent.arity(); i++){
    const Expr& child = parent[i];
    iter = d_parent_list.find(child);
    if(d_parent_list.end() == iter){
      d_parent_list[child] = new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
      d_parent_list[child]->push_back(parent);
    }
    else{
      iter->second->push_back(parent);
    }
  }
}

void TheoryQuant::collectChangedTerms(CDList<Expr>& changed){
  ExprMap<bool> eqs_hash;
  ExprMap<bool> changed_hash;
  /*
  {
    for(ExprMap<CDList<Expr>* >::iterator iter = d_eq_list.begin(), iter_end=d_eq_list.end();
	iter != iter_end; iter++){
      CDList<Expr>* cur_eqs = iter->second;
      int begin_pos;
      Expr head = iter->first;
      if(d_eq_pos.find(head) == d_eq_pos.end()){
	begin_pos=0;
	d_eq_pos[head]= new(true) CDO<size_t>(theoryCore()->getCM()->getCurrentContext(), 0, 0);

      }
      else{
	begin_pos = *(d_eq_pos[head]);
      }
      for(size_t i=begin_pos; i<cur_eqs->size(); i++){
	eqs_hash[(*cur_eqs)[i]]=true;
      }
      (d_eq_pos[head])->set(cur_eqs->size());
    }
    }*/
  for(size_t i=d_eqs_pos; i<d_eqs.size(); i++){
    eqs_hash[d_eqs[i]]=true;
  }
  d_eqs_pos.set(d_eqs.size());
  {
    for(ExprMap<bool>::iterator iter = eqs_hash.begin(), iter_end = eqs_hash.end(); iter != iter_end; iter++){
      const Expr& cur_ex = iter->first;
      ExprMap<CDList<Expr>* >::iterator iter_parent = d_parent_list.find(cur_ex);
      if(d_parent_list.end() != iter_parent){
	CDList<Expr>* cur_parents = iter_parent->second;
	for(size_t i=0; i<cur_parents->size(); i++){
	  changed_hash[(*cur_parents)[i]]=true;
	}
      }
    }
  }
  {
    for(ExprMap<bool>::iterator iter = changed_hash.begin(), iter_end = changed_hash.end(); iter != iter_end; iter++){
      changed.push_back(iter->first);
    }
  }
}

/*
inline bool TheoryQuant::matchChild(const Expr& gterm, const Expr& vterm, ExprMap<Expr>& env){
  cout<<"error, should not be called, matchChild" << endl;
  if(gterm.arity() != vterm.arity()) {
    return false;
  }
  for(int i = 0 ; i< gterm.arity(); i++){ //we should make the matching "flat"
    const Expr& cur_v = vterm[i];
    const Expr& cur_g = gterm[i];
    if(BOUND_VAR == cur_v.getKind()){
      ExprMap<Expr>::iterator p = env.find(cur_v);
      if ( p != env.end()){
	if (simplifyExpr(cur_g) != simplifyExpr(p->second)){
	  return false;
	}
      }
      else {
	env[cur_v] = simplifyExpr(cur_g);
      }
    }
    else if (!cur_v.containsBoundVar()){
      if(simplifyExpr(cur_v) != simplifyExpr(cur_g)){
	return false;
      }
    }
    else{
      if (false == recSynMatch(cur_g, cur_v, env)){
	return false;
      }
    }
  }
  return true;
}

inline void TheoryQuant::matchChild(const Expr& gterm, const Expr& vterm, vector<ExprMap<Expr> >& binds){
  cout<<"-error, should not be called more, matchChild" << endl;
  ExprMap<Expr> env;
  if(gterm.arity() != vterm.arity()) {
    return;
  }

  for(int i = 0 ; i< gterm.arity(); i++){
    const Expr& cur_v = vterm[i];
    const Expr& cur_g = gterm[i];
    if(BOUND_VAR == cur_v.getKind()){
      ExprMap<Expr>::iterator p = env.find(cur_v);
      if ( p != env.end()){
	if (simplifyExpr(cur_g) != simplifyExpr(p->second)){
	  return;
	}
      }
      else {
	env[cur_v] = simplifyExpr(cur_g);
      }
    }
    else if (!cur_v.containsBoundVar()){
      if(simplifyExpr(cur_v) != simplifyExpr(cur_g)){
	return ;
      }
    }
    else{
      if (false == recSynMatch(cur_g, cur_v, env)){
	return;
      }
    }
  }
  binds.push_back(env);
  return;
}
*/

/* multMatchChild
  input : partial bindings in binds
  output: successful bindings in binds
*/
inline bool TheoryQuant::multMatchChild(const Expr& gterm, const Expr& vterm, vector<ExprMap<Expr> >& binds, bool top){
  if(gterm.arity() != vterm.arity()) {
    TRACE("multmatch", "not same kind", gterm , vterm);
    return false;
  }

  //  if (binds.size()>1) {cout<<"match child >1 " <<endl;};

  vector<Expr> allGterms;
  allGterms.push_back(gterm);


 if(!gterm.getSig().isNull() ){
    Expr gtermSig = gterm.getSig().getRHS();
    if(!top && gterm.hasFind() && !gterm.isAtomicFormula() ) {
      Expr curCandidateGterm = gterm.getEqNext().getRHS();
      while (curCandidateGterm != gterm){
	if(getHead(curCandidateGterm) == getHead(gterm) 
	   &&	!curCandidateGterm.getSig().isNull() 
	   &&   curCandidateGterm.getSig().getRHS() != gtermSig
	   &&	getExprScore(curCandidateGterm) <= d_curMaxExprScore
	   ){
	  allGterms.push_back(curCandidateGterm);
	}
	curCandidateGterm = curCandidateGterm.getEqNext().getRHS();
      }
    }
  }


  vector<ExprMap<Expr> > returnBinds;
  for(size_t curGtermIndex =0; curGtermIndex < allGterms.size(); curGtermIndex++)
  {
    vector<ExprMap<Expr> > currentBinds(binds);

    if(0 == currentBinds.size()){//we need something to work on, even it is empty
      ExprMap<Expr> emptyEnv;
      currentBinds.push_back(emptyEnv);
    }

    Expr gterm = allGterms[curGtermIndex]; //be careful, this gterm hides the gterm in the beginning. fix this soon

    vector<ExprMap<Expr> > nextBinds;

    for(int i = 0 ; i< gterm.arity(); i++){
      const Expr& curVterm = vterm[i];
      const Expr& curGterm = gterm[i];

      for(size_t curEnvIndex =0; curEnvIndex < currentBinds.size(); curEnvIndex++){
	//maybe we should exchange the iteration of ith child and curentBinds.
	ExprMap<Expr>& curEnv(currentBinds[curEnvIndex]);
	if(BOUND_VAR == curVterm.getKind()){
	  ExprMap<Expr>::iterator iterVterm = curEnv.find(curVterm);
	  if ( iterVterm != curEnv.end()){
	    if (simplifyExpr(curGterm) == simplifyExpr(iterVterm->second)){
	      nextBinds.push_back(curEnv); //success, record the good binding
	    } //else do nothing
	  }
	  else {
	    curEnv[curVterm] = simplifyExpr(curGterm);
	    nextBinds.push_back(curEnv); // success, record the good binding
	  }
	}
	else if (!curVterm.containsBoundVar()){
	  if(simplifyExpr(curVterm) == simplifyExpr(curGterm)){
	    nextBinds.push_back(curEnv); // sueecess, record the good
	  } //else do nothing
	}
	else{
	  vector<ExprMap<Expr> > newBinds;
	  newBinds.push_back(curEnv);
	  bool goodChild = recMultMatch(curGterm, curVterm, newBinds);
	  if(goodChild){
	    for(vector<ExprMap<Expr> >::iterator i = newBinds.begin(), iend = newBinds.end(); i != iend; i++){
	      nextBinds.push_back(*i);
	    }
	  }
	}
      }
      currentBinds = nextBinds; //nextBinds are good bindings
      nextBinds.clear();
    }
    for(size_t curBindsIndex=0; curBindsIndex < currentBinds.size(); curBindsIndex++){
      returnBinds.push_back(currentBinds[curBindsIndex]);
    }

  }

  //  binds = currentBinds;
  binds = returnBinds;
  return (binds.size() > 0) ? true : false;
}


//multMatchTop can be called anywhere
inline bool TheoryQuant::multMatchTop(const Expr& gterm, const Expr& vterm, vector<ExprMap<Expr> >& binds){
  vector<ExprMap<Expr> > currentBinds(binds);

  if(0 == currentBinds.size()){//we need something to work on, even it is empty
    ExprMap<Expr> emptyEnv;
    currentBinds.push_back(emptyEnv);
  }

  vector<ExprMap<Expr> > nextBinds;

  const Expr& curVterm = vterm;
  const Expr& curGterm = gterm;

  for(size_t curEnvIndex =0; curEnvIndex < currentBinds.size(); curEnvIndex++){
    ExprMap<Expr>& curEnv(currentBinds[curEnvIndex]);
    vector<ExprMap<Expr> > newBinds;
    newBinds.push_back(curEnv);
    bool goodChild = recMultMatch(curGterm, curVterm, newBinds);
    if(goodChild){
      for(vector<ExprMap<Expr> >::iterator i = newBinds.begin(), iend = newBinds.end(); i != iend; i++){
	nextBinds.push_back(*i);
      }
    }
  }
  binds = nextBinds; //nextBinds stores the good bindings
  return (binds.size() > 0) ? true : false;
}


//match a gterm against all the trigs in d_allmap_trigs
void TheoryQuant::matchListOld(const CDList<Expr>& glist, size_t gbegin, size_t gend){
  for(size_t g_index = gbegin; g_index < gend; g_index++){

    const Expr& gterm = glist[g_index];
    //    cout<<"matching old "<<gterm<<endl;
    if(gterm.isEq()){
      continue; // we do not match with equality
    }

     if(gterm.getSig().isNull() ){
       if ( ! ( (gterm.hasFind() && !canGetHead(gterm.getFind().getRHS())) || gterm.getType().isBool() )  ){
// 	 cout<<"gterm skipped " << gterm << endl;
// 	 cout<<"Find? " << (gterm.hasFind() ? gterm.getFind().getExpr().toString() : "NO " ) << endl;
// 	 cout<<"Rep?  " << (gterm.hasRep() ? gterm.getRep().getExpr().toString() : "NO " ) << endl;
	 continue;
       }
     }

    Expr head = getHead(gterm);

    ExprMap<CDMap<Expr, CDList<dynTrig>* > *>::iterator iter = d_allmap_trigs.find(head);
    if(d_allmap_trigs.end() == iter) continue;
    CDMap<Expr, CDList<dynTrig>*>* cd_map = iter->second;

//     if(cd_map->size()>10){
//       cout<<"map size1:"<<cd_map->size()<<endl;
//       cout<<head<<endl;
//     }

    CDMap<Expr, CDList<dynTrig>*>::iterator iter_trig = (*cd_map).begin();
    CDMap<Expr, CDList<dynTrig>*>::iterator iter_trig_end = (*cd_map).end();

    for(;iter_trig != iter_trig_end; iter_trig++){
      CDList<dynTrig>* cur_list = (*iter_trig).second;
      if(1 == cur_list->size() || null_expr == head || gterm.getType().isBool() ){
	for(size_t cur_index =0; cur_index < cur_list->size(); cur_index++){

	  const Trigger& cur_trig = (*cur_list)[cur_index].trig;
	  size_t univ_id = (*cur_list)[cur_index].univ_id;
	  vector<ExprMap<Expr> > binds;
	  const Expr& vterm = cur_trig.trig;
	  if(vterm.getKind() != gterm.getKind()) continue;


// 	  if(*d_useNewEqu){
// 	    if  ( d_allout && cur_trig.isSuperSimple ) continue; //delete this after test yeting
// 	  }

	  if  ( d_allout && cur_trig.isSuperSimple && !cur_trig.hasTrans && !cur_trig.isMulti) continue;
	    //      if  ( d_allout && cur_trig.isSimple ) continue;

	  newTopMatch(gterm, vterm, binds, cur_trig);

	  for(size_t i=0; i<binds.size(); i++){
	    ExprMap<Expr>& cur_map = binds[i];
	    vector<Expr> bind_vec;
	    const vector<Expr>& bVarsThm = d_univs[univ_id].getExpr().getVars();
	    for(size_t j=0; j< bVarsThm.size(); j++){
	      bind_vec.push_back(cur_map[bVarsThm[j]]);
	    }
	    synNewInst(univ_id, bind_vec, gterm, cur_trig);
	  }
	}
      }
      else if ( cur_list->size() > 1){

	const Trigger& cur_trig = (*cur_list)[0].trig;//here we have a polarity problem

	const Expr& general_vterm = (*iter_trig).first;

	//	cout<<"matching new trig case 2:"<<general_vterm<<endl;

	if(general_vterm.getKind() != gterm.getKind()) continue;
	vector<ExprMap<Expr> > binds;

// 	if(*d_useNewEqu){
// 	  if  ( d_allout && cur_trig.isSuperSimple ) continue; //delete this after test yeting
// 	}
	if  ( d_allout && cur_trig.isSuperSimple && !cur_trig.hasTrans && !cur_trig.isMulti) continue;
	//if  ( d_allout && cur_trig.isSimple ) continue;

	newTopMatch(gterm, general_vterm, binds, cur_trig);

 	for(size_t bindsIndex = 0 ; bindsIndex < binds.size() ; bindsIndex++){
	  // 	  cout<<"i = " << bindsIndex << " : " << exprMap2string(binds[bindsIndex]) << endl ;
 	}

	if(binds.size() <= 0) continue;

	for(size_t trig_index = 0; trig_index< cur_list->size(); trig_index++){
	  size_t univ_id = (*cur_list)[trig_index].univ_id;
	  const ExprMap<Expr>& trig_map = (*cur_list)[trig_index].binds;
	  const Trigger& ind_cur_trig = (*cur_list)[trig_index].trig;
	  for(size_t i=0; i<binds.size(); i++){
	    ExprMap<Expr>& cur_map = binds[i];
	    vector<Expr> bind_vec;
	    const vector<Expr>& bVarsThm = d_univs[univ_id].getExpr().getVars();
	    for(size_t j=0; j< bVarsThm.size(); j++){
	      const Expr& inter=(*(trig_map.find(bVarsThm[j]))).second;
	      const Expr& inter2 = cur_map[inter];
	      bind_vec.push_back(inter2);
	    }
	    //	    cout<<"==++ for instantiation " << d_univs[univ_id] <<endl;
	    //	    cout<<"==--  bings " << vectorExpr2string(bind_vec) <<endl;
	    synNewInst(univ_id, bind_vec, gterm, ind_cur_trig);
	  }
	  //	  cout<<"==** end \n";
	}
      }
      else{
	FatalAssert(false, "error in matchlistold");
      }
    }//end of for each trig begins with head
  }//end of each gterm
}

void TheoryQuant::delNewTrigs(ExprMap<ExprMap<std::vector<dynTrig>*>*>& new_trigs){
  //return;
  ExprMap<ExprMap<std::vector<dynTrig>*>*>::iterator i = new_trigs.begin();
  ExprMap<ExprMap<std::vector<dynTrig>*>*>::iterator iend = new_trigs.end();
  for(; i!=iend; i++){
    ExprMap<std::vector<dynTrig>*>* cur_new_cd_map = i->second;
    ExprMap<vector<dynTrig>* >::iterator j = cur_new_cd_map->begin();
    ExprMap<vector<dynTrig>* >::iterator jend = cur_new_cd_map->end();
      for(; j!=jend; j++){
	Expr general_trig = j->first;
	vector<dynTrig>* trigs = j->second;
	delete trigs;
      }
      delete cur_new_cd_map;
    }
  new_trigs.clear();
}


void TheoryQuant::combineOldNewTrigs(ExprMap<ExprMap<std::vector<dynTrig>*>*>& new_trigs){
  ExprMap<ExprMap<std::vector<dynTrig>*>*>::iterator i = new_trigs.begin();
  ExprMap<ExprMap<std::vector<dynTrig>*>*>::iterator iend = new_trigs.end();
  for(; i!=iend; i++){
    ExprMap<std::vector<dynTrig>*>* cur_new_cd_map = i->second;
    Expr head = i->first;
    ExprMap<CDMap<Expr, CDList<dynTrig>* >* >::iterator old_iter = d_allmap_trigs.find(head);
    if(d_allmap_trigs.end() == old_iter){
      CDMap<Expr, CDList<dynTrig>* >* old_cd_map =
	//	new(true) CDMap<Expr, CDList<dynTrig>* > (theoryCore()->getCM()->getCurrentContext());
	new(false) CDMap<Expr, CDList<dynTrig>* > (theoryCore()->getCM()->getCurrentContext());
      d_allmap_trigs[head] = old_cd_map;
      ExprMap<vector<dynTrig>* >::iterator j = cur_new_cd_map->begin();
      ExprMap<vector<dynTrig>* >::iterator jend = cur_new_cd_map->end();
      for(; j!=jend; j++){
	Expr general_trig = j->first;
	vector<dynTrig>* trigs = j->second;
	CDList<dynTrig>* old_cd_list =
	  //new(true) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
	  new(false) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
	(*old_cd_map)[general_trig] = old_cd_list;
	for(size_t k=0; k<trigs->size(); k++){
	  (*old_cd_list).push_back((*trigs)[k]);
	  //	  cout<<"combined 1 "<<(*trigs)[k].trig.getEx()<<endl;
	}
	//	delete trigs;
      }
      //      delete cur_new_cd_map;
    }
    else{
      CDMap<Expr, CDList<dynTrig>* >* old_cd_map = old_iter->second;
      ExprMap<std::vector<dynTrig>*>::iterator j = cur_new_cd_map->begin();
      ExprMap<std::vector<dynTrig>*>::iterator jend = cur_new_cd_map->end();
      for(; j!=jend; j++){
	Expr general_trig = j->first;
	vector<dynTrig>* trigs = j->second;
	CDMap<Expr, CDList<dynTrig>* >::iterator old_trigs_iter = old_cd_map->find(general_trig);
	CDList<dynTrig>* old_cd_list;
	if(old_cd_map->end() == old_trigs_iter){
	 old_cd_list =
	   //new(true) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
	   new(false) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
	 (*old_cd_map)[general_trig] = old_cd_list;
	}
	else{
	  old_cd_list = (*old_trigs_iter).second;
	}
	for(size_t k=0; k<trigs->size(); k++){
	  (*old_cd_list).push_back((*trigs)[k]);
	  //	  cout<<"combined 2 "<<(*trigs)[k].trig.getEx()<<endl;
	}
	//	delete trigs;
      }
      //      delete cur_new_cd_map;
    }
  }
  delNewTrigs(new_trigs);
  new_trigs.clear();
}

//match a gterm against all the trigs in d_allmap_trigs
void TheoryQuant::matchListNew(ExprMap<ExprMap<vector<dynTrig>*>*>& new_trigs,
			       const CDList<Expr>& glist,
			       size_t gbegin,
			       size_t gend){
  //return;
  //  if(!d_allout) return;
  for(size_t g_index = gbegin; g_index<gend; g_index++){

    const Expr& gterm = glist[g_index];
    //    cout<<"matching new "<<gterm<<endl;
    if(gterm.isEq()){
      continue; // we do not match with equality
    }

    if(gterm.getSig().isNull()){
      //add the code as in matchlistold

//      continue;
    }

    Expr head = getHead(gterm);

    ExprMap<ExprMap<vector<dynTrig>* > *>::iterator iter = new_trigs.find(head);
    if(new_trigs.end() == iter) continue;
    ExprMap<vector<dynTrig>*>* cd_map = iter->second;
//     if(cd_map->size()>10){
//       cout<<"map size2:"<<cd_map->size()<<endl;
//       cout<<head<<endl;
//     }

    ExprMap<vector<dynTrig>*>::iterator iter_trig = (*cd_map).begin();
    ExprMap<vector<dynTrig>*>::iterator iter_trig_end = (*cd_map).end();

    for(;iter_trig != iter_trig_end; iter_trig++){

      vector<dynTrig>* cur_list = (*iter_trig).second;
      if(1 == cur_list->size() || null_expr == head ||  gterm.getType().isBool() ){
	for(size_t cur_index =0; cur_index < cur_list->size(); cur_index++){
	  const Trigger& cur_trig = (*cur_list)[cur_index].trig;

// 	  if(*d_useNewEqu){
//	  if  ( d_allout &&  cur_trig.isSuperSimple ) continue; //delete this after test yeting
// 	  }

	  if  ( d_allout && cur_trig.isSuperSimple && !cur_trig.hasTrans) continue;

	  size_t univ_id = (*cur_list)[cur_index].univ_id;
	  vector<ExprMap<Expr> > binds;
	  const Expr& vterm = cur_trig.trig;
	  if(vterm.getKind() != gterm.getKind()) continue;
	  newTopMatch(gterm, vterm, binds, cur_trig);
	  for(size_t i=0; i<binds.size(); i++){
	    ExprMap<Expr>& cur_map = binds[i];
	    vector<Expr> bind_vec;
	    const vector<Expr>& bVarsThm = d_univs[univ_id].getExpr().getVars();
	    for(size_t j=0; j< bVarsThm.size(); j++){
	      bind_vec.push_back(cur_map[bVarsThm[j]]);
	    }
	    synNewInst(univ_id, bind_vec, gterm, cur_trig);
	  }
	}
      }
      else if ( cur_list->size() > 1){

	const Trigger& cur_trig = (*cur_list)[0].trig;//here we have a polarity problem

// 	if(*d_useNewEqu){
// 	  if  ( d_allout &&  cur_trig.isSuperSimple ) continue; //delete this after test yeting
// 	}

//	if  ( d_allout && cur_trig.isSuperSimple && !cur_trig.hasTrans) continue;

	const Expr& general_vterm = (*iter_trig).first;
	if(general_vterm.getKind() != gterm.getKind()) continue;
	vector<ExprMap<Expr> > binds;
	newTopMatch(gterm, general_vterm, binds, cur_trig);

	if(binds.size() <= 0) continue;
	for(size_t trig_index = 0; trig_index< cur_list->size(); trig_index++){
	  size_t univ_id = (*cur_list)[trig_index].univ_id;
	  const Trigger& ind_cur_trig = (*cur_list)[trig_index].trig;
	  const ExprMap<Expr>& trig_map = (*cur_list)[trig_index].binds;

	  for(size_t i=0; i<binds.size(); i++){
	    ExprMap<Expr>& cur_map = binds[i];
	    vector<Expr> bind_vec;
	    const vector<Expr>& bVarsThm = d_univs[univ_id].getExpr().getVars();
	    for(size_t j=0; j< bVarsThm.size(); j++){
	      const Expr& inter=(*(trig_map.find(bVarsThm[j]))).second;
	      const Expr& inter2 = cur_map[inter];
	      bind_vec.push_back(inter2);
	    }
	    synNewInst(univ_id, bind_vec, gterm, ind_cur_trig);
	  }
	}
      }
      else{
	FatalAssert(false, "error in matchlistnew");
      }
    }//end of for each trig begins with head
  }// end of each gterm
}



//void TheoryQuant::newTopMatchNoSig(const Expr& gtermOrg,
void TheoryQuant::newTopMatchNoSig(const Expr& gterm,
				   const Expr& vterm,
				   vector<ExprMap<Expr> >& binds,
				   const Trigger& trig){

  //  cout<<"matching " << gterm << endl << "----" << endl << vterm << endl;

  if(trig.isSuperSimple){
    ExprMap<Expr>  cur_bind;
    for(int i = vterm.arity()-1; i>=0 ; i--){
      cur_bind[vterm[i]] = simplifyExpr(gterm[i]);
    }
    binds.push_back(cur_bind);
    return;
  }

  if(trig.isSimple){
    ExprMap<Expr>  cur_bind;
    for(int i = vterm.arity()-1; i>=0 ; i--){
      if(BOUND_VAR != vterm[i].getKind()){
	if(simplifyExpr(gterm[i]) != simplifyExpr(vterm[i])) {
	  return ;
	}
      }
      else{
	if(getBaseType(vterm[i]) == (getBaseType(gterm[i]))){
	  cur_bind[vterm[i]] = simplifyExpr(gterm[i]);
	}
	else return;
      }
    }
    binds.push_back(cur_bind);
    return;
  }

  if(!isSysPred(vterm)){ //then gterm cannot be a syspred
    if(!gterm.getType().isBool()){
      //      res2= recSynMatch(gterm, vterm, env);
      multMatchChild(gterm, vterm, binds, true);
      return;
    }

    //    DebugAssert(falseExpr()==findExpr(gterm) || trueExpr()==findExpr(gterm), " why ");

    multMatchChild(gterm, vterm, binds, true);
    return;

    if(!*d_usePolarity){
      //      return recSynMatch(gterm, vterm, env);
      multMatchChild(gterm, vterm, binds);
      return;
    }

    const bool gtrue = (trueExpr()==findExpr(gterm));
    //    const bool gtrue = (trueExpr()==simplifyExpr(gterm));
    if(gtrue ){
      if((Neg==trig.polarity || PosNeg==trig.polarity)) {
	//	return recSynMatch(gterm, vterm, env);
	multMatchChild(gterm, vterm, binds);
	return;
      }
      else{
	//	cout<<"returned 1"<<endl;
	return;
      }
    }
    const bool gfalse = (falseExpr()==findExpr(gterm));
    //const bool gfalse = (falseExpr()==simplifyExpr(gterm));
    if(gfalse){
      if((Pos==trig.polarity || PosNeg==trig.polarity)) {
	//	return recSynMatch(gterm, vterm, env);
	multMatchChild(gterm, vterm, binds); //it is possible that we need binds here, not a single bind
	return;
      }
      else{
	//	cout<<"returned 2"<<endl;
	return;
      }
    }

//     cout<<"impossible here in new top match"<<endl;
//     cout<<"vterm "<<vterm<<endl;
//     cout<<"gterm " <<gterm<<endl;
//     cout<<trig.polarity<<endl;
//     cout<<"gtrue and gfalse: " << gtrue<<" |and| " <<gfalse<<endl;
//     return;
    multMatchChild(gterm, vterm, binds);

    return;
  }
  else{ // must be syspreds
    //we can move the work to split vterm into left and right into setuptriggers
    Expr gl = getLeft(gterm[1]);
    Expr gr = getRight(gterm[1]);

    if(null_expr == gr || null_expr == gl){
      gl = gterm[0];
      gr = gterm[1];
    }

    Expr vr, vl;
    Expr tvr, tvl;

    tvr=null_expr;
    tvl=null_expr;

    if(isGE(vterm) || isGT(vterm)){
      vr = vterm[0];
      vl = vterm[1];
    }
    else if(isLE(vterm) || isLT(vterm)){
      vr = vterm[1];
      vl = vterm[0];
    }
    else{
      FatalAssert(false, "impossilbe in toppred");
    }

    if(isIntx(vl,0)){
      tvl = getLeft(vr);
      tvr = getRight(vr);
    }
    else if(isIntx(vr,0)) {
      tvl = getLeft(vl);
      tvr = getRight(vl);
    }

    if( (null_expr != tvl) && (null_expr != tvr)){
      vl = tvl;
      vr = tvr;
    }


    const bool gtrue = (trueExpr()==findExpr(gterm));
    const bool gfalse = (falseExpr()==findExpr(gterm));

    TRACE("quant toppred"," vl, gl, vr, gr:", vl.toString()+"::"+gl.toString()+"||", vr.toString()+"::"+gr.toString());

    //    DebugAssert(!(trig.isNeg() && trig.isPos()), "expr in both pos and neg");

    if(!*d_usePolarity){
      if((multMatchTop(gl, vl, binds) && multMatchTop(gr, vr, binds))){
	return;
      }
      else{
	return;
      }
    }
    if((Neg==trig.polarity || PosNeg==trig.polarity)) {
      if (( gtrue ) )  {
	if (multMatchTop(gl, vl, binds) && multMatchTop(gr, vr, binds)){
	  return;
	}
	else{
	  return;
	}
      }
      else {
	if(multMatchTop(gl, vr, binds) && multMatchTop(gr, vl, binds)){
	  return;
	}
	else{
	  return;
	}
      }
    }
    else if((Pos==trig.polarity || PosNeg==trig.polarity)) {
      if (( gfalse )) {
	if(multMatchTop(gl, vl, binds) && multMatchTop(gr, vr, binds)){
	  return;
	}
	else{
	  return;
	}
      }
      else {
	if(multMatchTop(gl, vr, binds) && multMatchTop(gr, vl, binds)){
	  return;
	}
	else{
	  return;
	}
      }
    }
    else {
      if((multMatchTop(gl, vl, binds) && multMatchTop(gr, vr, binds))){
	// it is possible that cur_bind will be binds
	return;
      }
      else{
	return;
      }
      return;
    }
  }
}



// std::string exprChild2string(const Expr& expr){
//   std::string result;
//   result.append("head is: ");
//   result.append(getHead(expr).toString());
//   result.append("\n");
//   for(int i = 0; i < expr.arity(); i++){
//     result.append(int2string(i));
//     result.append(": ");
//     result.append(expr[i].toString());
//     result.append("\n");
//   }
//   result.append("---- end ---- \n");
//   return result;
// }

//wrap function for newTopMatch, for test only
void TheoryQuant::newTopMatch(const Expr& gtermOrg,
			      const Expr& vterm,
			      vector<ExprMap<Expr> >& binds,
			      const Trigger& trig){

  //return   newTopMatchSig(gtermOrg,vterm, binds, trig);

  return   newTopMatchNoSig(gtermOrg,vterm, binds, trig);

//   cout<<"gterm org: " << gtermOrg << endl;
//   cout<<"vterm org: " << vterm << endl;

//   if(isPow(gtermOrg)){
//     if(isIntx(gtermOrg[0],2)){
//       vector<Expr> mults;
//       mults.push_back(gtermOrg[1]);
//       mults.push_back(gtermOrg[1]);
//       cout<<"new expr" << multExpr(mults) << endl;;
//     }
//     else{
//       cout <<"cannot do this"<<endl;
//     }

//   }

  vector<ExprMap<Expr> > oldBinds;
  newTopMatchNoSig(gtermOrg,vterm, oldBinds, trig);
  vector<ExprMap<Expr> > newBinds;
  newTopMatchSig(gtermOrg,vterm, newBinds, trig);

  vector<ExprMap<Expr> > oldBindsBack(oldBinds);
  vector<ExprMap<Expr> > newBindsBack(newBinds);

  simplifyVectorExprMap(oldBinds);
  simplifyVectorExprMap(newBinds);

  if (false && oldBinds != newBinds){

    cout<<"let us see" << endl;
    cout<< "===gterm is    : " << gtermOrg << endl ;;
//     cout<< exprChild2string(gtermOrg) << endl;
//     cout<< exprChild2string(gtermOrg[0]) << endl;
//     cout<< exprChild2string(gtermOrg[1]) << endl;
    if(gtermOrg.isApply() && gtermOrg.hasSig()){
      Expr sig = gtermOrg.getSig().getRHS();
      cout << "\n---gterm sig is: " << sig << endl;
//       cout << exprChild2string(sig) << endl;
//       cout << exprChild2string(sig[0]) << endl;
//       cout << exprChild2string(sig[1]) << endl;
    }
    //    cout << "vterm is " << vterm << endl << exprChild2string(vterm) << endl;
//     cout << exprChild2string(vterm[0]) << endl;
//     cout << exprChild2string(vterm[1]) << endl;

    for(size_t oldBindsIndex = 0; oldBindsIndex < oldBinds.size(); oldBindsIndex++){
      cout << "--O- " << oldBindsIndex << endl;
      cout << exprMap2string(oldBindsBack[oldBindsIndex]) << endl;
      cout << exprMap2string(oldBinds[oldBindsIndex]) << endl;
      cout << exprMap2stringSimplify(oldBinds[oldBindsIndex]) << endl;
      cout << exprMap2stringSig(oldBinds[oldBindsIndex]) << endl;
    }

    for(size_t newBindsIndex = 0; newBindsIndex < newBinds.size(); newBindsIndex++){
      cout << "--N- " << newBindsIndex << endl;
      cout << exprMap2string(newBindsBack[newBindsIndex]) << endl;
      cout << exprMap2string(newBinds[newBindsIndex]) << endl;
      cout << exprMap2stringSimplify(newBinds[newBindsIndex]) << endl;
      cout << exprMap2stringSig(newBinds[newBindsIndex]) << endl;
    }

  }


    //binds = newBinds;
  //  cout<<"newbinds size" << newBinds.size() << endl;
  binds = oldBinds;
  return;
}

void TheoryQuant::newTopMatchSig(const Expr& gtermOrg,
				 const Expr& vterm,
				 vector<ExprMap<Expr> >& binds,
				 const Trigger& trig){

  //  cout<<"matching " << gterm << endl << "----" << endl << vterm << endl;
  Expr gterm;
  if(gtermOrg.isApply() && gtermOrg.hasSig()){
    gterm = gtermOrg.getSig().getRHS();
  }
  else{
    gterm = gtermOrg;
  }


  if(trig.isSuperSimple){
    ExprMap<Expr>  cur_bind;
    for(int i = vterm.arity()-1; i>=0 ; i--){
      cur_bind[vterm[i]] = simplifyExpr(gterm[i]);
    }
    binds.push_back(cur_bind);
    return;
  }

  if(trig.isSimple){
    ExprMap<Expr>  cur_bind;
    for(int i = vterm.arity()-1; i>=0 ; i--){
      if(BOUND_VAR != vterm[i].getKind()){
	if(simplifyExpr(gterm[i]) != simplifyExpr(vterm[i])) {
	  return ;
	}
      }
      else{
	if (getBaseType(vterm[i])==getBaseType(gterm[i])){
	  cur_bind[vterm[i]] = simplifyExpr(gterm[i]);
	}
	else return;
      }
    }
    binds.push_back(cur_bind);
    return;
  }

  if(!isSysPred(vterm)){ //then gterm cannot be a syspred
    if(!gterm.getType().isBool()){
      //      res2= recSynMatch(gterm, vterm, env);
      multMatchChild(gterm, vterm, binds);
      return;
    }


    //    DebugAssert(falseExpr()==findExpr(gterm) || trueExpr()==findExpr(gterm), " why ");

    //    multMatchChild(gterm, vterm, binds);
    //    return;

    // when man trig is enabled, we should not use polarity because the manual triggers do not have polairities.
    // should I fix this?
    if(!*d_usePolarity || d_useManTrig){
      //      return recSynMatch(gterm, vterm, env);
      multMatchChild(gterm, vterm, binds);
      return;
    }

    const bool gtrue = (trueExpr()==findExpr(gterm));
    //    const bool gtrue = (trueExpr()==simplifyExpr(gterm));
    if(gtrue ){
      if((Neg==trig.polarity || PosNeg==trig.polarity)) {
	//	return recSynMatch(gterm, vterm, env);
	multMatchChild(gterm, vterm, binds);
	return;
      }
      else{
	//	cout<<"returned 1"<<endl;
	return;
      }
    }
    const bool gfalse = (falseExpr()==findExpr(gterm));
    //const bool gfalse = (falseExpr()==simplifyExpr(gterm));
    if(gfalse){
      if((Pos==trig.polarity || PosNeg==trig.polarity)) {
	//	return recSynMatch(gterm, vterm, env);
	multMatchChild(gterm, vterm, binds); //it is possible that we need binds here, not a single bind
	return;
      }
      else{
	//	cout<<"returned 2"<<endl;
	return;
      }
    }


    FatalAssert(false, "impossible");
    cout<<"impossible here in new top match"<<endl;
    cout<<"vterm "<<vterm<<endl;
    cout<<"gterm " <<gterm<<endl;
    cout<<trig.polarity<<endl;
    cout<<"gtrue and gfalse: " << gtrue<<" |and| " <<gfalse<<endl;
    return;
    multMatchChild(gterm, vterm, binds);

    return;
  }
  else{ // must be syspreds
    //we can move the work to split vterm into left and right into setuptriggers
    Expr gl = getLeft(gterm[1]);
    Expr gr = getRight(gterm[1]);

    if(null_expr == gr || null_expr == gl){
      gl = gterm[0];
      gr = gterm[1];
    }

    Expr vr, vl;
    Expr tvr, tvl;

    tvr=null_expr;
    tvl=null_expr;

    if(isGE(vterm) || isGT(vterm)){
      vr = vterm[0];
      vl = vterm[1];
    }
    else if(isLE(vterm) || isLT(vterm)){
      vr = vterm[1];
      vl = vterm[0];
    }
    else{
      FatalAssert(false, "impossilbe in toppred");
    }

    if(isIntx(vl,0)){
      tvl = getLeft(vr);
      tvr = getRight(vr);
    }
    else if(isIntx(vr,0)) {
      tvl = getLeft(vl);
      tvr = getRight(vl);
    }

    if( (null_expr != tvl) && (null_expr != tvr)){
      vl = tvl;
      vr = tvr;
    }


    const bool gtrue = (trueExpr()==findExpr(gterm));
    const bool gfalse = (falseExpr()==findExpr(gterm));

    TRACE("quant toppred"," vl, gl, vr, gr:", vl.toString()+"::"+gl.toString()+"||", vr.toString()+"::"+gr.toString());

    //    DebugAssert(!(trig.isNeg() && trig.isPos()), "expr in both pos and neg");

    if(!*d_usePolarity){
      if((multMatchTop(gl, vl, binds) && multMatchTop(gr, vr, binds))){
	return;
      }
      else{
	return;
      }
    }
    if((Neg==trig.polarity || PosNeg==trig.polarity)) {
      if (( gtrue ) )  {
	if (multMatchTop(gl, vl, binds) && multMatchTop(gr, vr, binds)){
	  return;
	}
	else{
	  return;
	}
      }
      else {
	if(multMatchTop(gl, vr, binds) && multMatchTop(gr, vl, binds)){
	  return;
	}
	else{
	  return;
	}
      }
    }
    else if((Pos==trig.polarity || PosNeg==trig.polarity)) {
      if (( gfalse )) {
	if(multMatchTop(gl, vl, binds) && multMatchTop(gr, vr, binds)){
	  return;
	}
	else{
	  return;
	}
      }
      else {
	if(multMatchTop(gl, vr, binds) && multMatchTop(gr, vl, binds)){
	  return;
	}
	else{
	  return;
	}
      }
    }
    else {
      if((multMatchTop(gl, vl, binds) && multMatchTop(gr, vr, binds))){
	// it is possible that cur_bind will be binds
	return;
      }
      else{
	return;
      }
      return;
    }
  }
}


/*
void TheoryQuant::newTopMatchBackupOnly(const Expr& gterm,
					const Expr& vterm,
					vector<ExprMap<Expr> >& binds,
					const Trigger& trig){
  cout<<"-error should not be called more,  newTopMatchBackupOnly" << endl;
  ExprMap<Expr>  cur_bind;
  //  cout<<"matching " << gterm << " +++ " <<vterm<<endl;
  if(trig.isSuperSimple){
    for(int i = vterm.arity()-1; i>=0 ; i--){
      cur_bind[vterm[i]] = simplifyExpr(gterm[i]);
    }
    binds.push_back(cur_bind);
    return;
  }

  if(trig.isSimple){
    for(int i = vterm.arity()-1; i>=0 ; i--){
      if(BOUND_VAR != vterm[i].getKind()){
	if(simplifyExpr(gterm[i]) != simplifyExpr(vterm[i])) {
	  return ;
	}
      }
      else{
	cur_bind[vterm[i]] = simplifyExpr(gterm[i]);
      }
    }
    binds.push_back(cur_bind);
    return;
  }


  if(!isSysPred(vterm)){ //then gterm cannot be a syspred
    if(!gterm.getType().isBool()){
      //      res2= recSynMatch(gterm, vterm, env);
      matchChild(gterm, vterm, binds);
      return;
    }

    matchChild(gterm, vterm, binds);
    return;


    if(!*d_usePolarity){
      //      return recSynMatch(gterm, vterm, env);
      matchChild(gterm, vterm, binds);
      return;
    }

    const bool gtrue = (trueExpr()==findExpr(gterm));
    //    const bool gtrue = (trueExpr()==simplifyExpr(gterm));
    if(gtrue ){
      if((Neg==trig.polarity || PosNeg==trig.polarity)) {
	//	return recSynMatch(gterm, vterm, env);
	matchChild(gterm, vterm, binds);
	return;
      }
      else{
	//	cout<<"returned 1"<<endl;
	return;
      }
    }
    const bool gfalse = (falseExpr()==findExpr(gterm));
    //const bool gfalse = (falseExpr()==simplifyExpr(gterm));
    if(gfalse){
      if((Pos==trig.polarity || PosNeg==trig.polarity)) {
	//	return recSynMatch(gterm, vterm, env);
	matchChild(gterm, vterm, binds); //it is possible that we need binds here, not a single bind
	return;
      }
      else{
	//	cout<<"returned 2"<<endl;
	return;
      }
    }


//     cout<<"immpossible here in new top match"<<endl;
//     cout<<"vterm "<<vterm<<endl;
//     cout<<trig.polarity<<endl;
//     cout<<gtrue<<" | " <<gfalse<<endl;
//     cout<<"gterm " <<gterm<<endl;
//     cout<<"gterm " <<simplifyExpr(gterm)<<endl;

    matchChild(gterm, vterm, binds);
    return;

    return;
  }
  else{ // must be syspreds
    //we can move the work to split vterm into left and right into setuptriggers
    Expr gl = getLeft(gterm[1]);
    Expr gr = getRight(gterm[1]);

    if(null_expr == gr || null_expr == gl){
      gl = gterm[0];
      gr = gterm[1];
    }

    Expr vr, vl;
    Expr tvr, tvl;

    tvr=null_expr;
    tvl=null_expr;

    if(isGE(vterm) || isGT(vterm)){
      vr = vterm[0];
      vl = vterm[1];
    }
    else if(isLE(vterm) || isLT(vterm)){
      vr = vterm[1];
      vl = vterm[0];
    }
    else{
      FatalAssert(false, "impossilbe in toppred");
    }

    if(isIntx(vl,0)){
      tvl = getLeft(vr);
      tvr = getRight(vr);
    }
    else if(isIntx(vr,0)) {
      tvl = getLeft(vl);
      tvr = getRight(vl);
    }

    if( (null_expr != tvl) && (null_expr != tvr)){
      vl = tvl;
      vr = tvr;
    }


    const bool gtrue = (trueExpr()==findExpr(gterm));
    const bool gfalse = (falseExpr()==findExpr(gterm));

    TRACE("quant toppred"," vl, gl, vr, gr:", vl.toString()+"::"+gl.toString()+"||", vr.toString()+"::"+gr.toString());

    //    DebugAssert(!(trig.isNeg() && trig.isPos()), "expr in both pos and neg");

    if(!*d_usePolarity){
      if((recSynMatch(gl, vl, cur_bind) && recSynMatch(gr, vr, cur_bind))){
	binds.push_back(cur_bind); // it is possible that cur_bind will be binds
	return;
      }
      else{
	return;
      }
    }
    if((Neg==trig.polarity || PosNeg==trig.polarity)) {
      if (( gtrue ) )  {
	if (recSynMatch(gl, vl, cur_bind) && recSynMatch(gr, vr, cur_bind)){
	  binds.push_back(cur_bind);
	  return;
	}
	else{
	  return;
	}
      }
      else {
	if(recSynMatch(gl, vr, cur_bind) && recSynMatch(gr, vl, cur_bind)){
	  binds.push_back(cur_bind);
	  return;
	}
	else{
	  return;
	}
      }
    }
    else if((Pos==trig.polarity || PosNeg==trig.polarity)) {
      if (( gfalse )) {
	if(recSynMatch(gl, vl, cur_bind) && recSynMatch(gr, vr, cur_bind)){
	  binds.push_back(cur_bind);
	  return;
	}
	else{
	  return;
	}
      }
      else {
	if(recSynMatch(gl, vr, cur_bind) && recSynMatch(gr, vl, cur_bind)){
	  binds.push_back(cur_bind);
	  return;
	}
	else{
	  return;
	}
      }
    }
    else {
      //      FatalAssert(false, "impossible polarity for trig");
	//DebugAssert(false, "impossible polarity for trig");
//      res = false;
      if((recSynMatch(gl, vl, cur_bind) && recSynMatch(gr, vr, cur_bind))){
	binds.push_back(cur_bind); // it is possible that cur_bind will be binds
	return;
      }
      else{
	return;
      }

      return;
    }
  }
}
*/

/*
bool TheoryQuant::synMatchTopPred(const Expr& gterm, Trigger trig, ExprMap<Expr>& env){


  Expr vterm = trig.getEx();

  TRACE("quant toppred", "top pred: gterm:| "+gterm.toString()," vterm:| "+vterm.toString(),"");

  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");
  DebugAssert ((BOUND_VAR != vterm.getKind()),"top pred match "+gterm.toString()+" has bound var");

  if(gterm.isEq() || vterm.isEq()){
    return false; // we do not match with equality
  }

  bool res2=false;

  if(vterm.arity() != gterm.arity()) return false;

  if(trig.isSuperSimp()){
    if(trig.getHead() == getHead(gterm) ){
      for(int i = vterm.arity()-1; i>=0 ; i--){
	env[vterm[i]] = simplifyExpr(gterm[i]);
      }
      return true;
    }
    return false;
  }



  if(trig.isSimp()){
    if(trig.getHead() == getHead(gterm) ){
       for(int i = vterm.arity()-1; i>=0 ; i--){
 	if(BOUND_VAR != vterm[i].getKind()){
 	  if(simplifyExpr(gterm[i]) != simplifyExpr(vterm[i])) {
 	    return false;
 	  }
 	}
       }
      for(int i = vterm.arity()-1; i>=0 ; i--){
	if(BOUND_VAR == vterm[i].getKind()){
	  if(d_allout){
	    env[vterm[i]] = simplifyExpr(gterm[i]);
	  }
	  else {
	    env[vterm[i]] = simplifyExpr(gterm[i]);
	  }
	}
      }
      return true;
    }
    else{
      return false;
    }
  }

  if(!(isSysPred(vterm) && isSysPred(gterm))){
    if(isSysPred(vterm) || isSysPred(gterm)) {
      return false;
    }
    if(!usefulInMatch(gterm)){
      return false;
    }
    if(trig.getHead() != getHead(gterm)){
      return false;
    }

    if(!gterm.getType().isBool()){
      //      res2= recSynMatch(gterm, vterm, env);
      res2= matchChild(gterm, vterm, env);
      return res2;
    }

    if(!*d_usePolarity){
      //      return recSynMatch(gterm, vterm, env);
      return matchChild(gterm, vterm, env);
    }

    const bool gtrue = (trueExpr()==findExpr(gterm));
    if(gtrue ){
      if(trig.isNeg()) {
	//	return recSynMatch(gterm, vterm, env);
	return matchChild(gterm, vterm, env);
      }
      else{
	return false;
      }
    }
    const bool gfalse = (falseExpr()==findExpr(gterm));
    if(gfalse){
      if (trig.isPos()){
	//	return recSynMatch(gterm, vterm, env);
	return matchChild(gterm, vterm, env);
      }
      else{
	return false;
      }
    }
    else {
      return false;
    }
  }
  else{
    DebugAssert((2==gterm.arity() && 2==vterm.arity()), "impossible situation in top pred");
    DebugAssert(!((isLE(gterm) || isLT(gterm)) && !isIntx(gterm[0],0)), "canonical form changed");

#ifdef _CVC3_DEBUG_MODE
    if( CVC3::debugger.trace("quant toppred")  ){
      cout << "toppred gterm, vterm" << gterm << "::" << vterm << endl;
      cout << findExpr(gterm) << "::" << trig.isPos() << "|" << trig.isNeg() << endl;
    }
#endif


    Expr gl = getLeft(gterm[1]);
    Expr gr = getRight(gterm[1]);

    if(null_expr == gr || null_expr == gl){
      gl = gterm[0];
      gr = gterm[1];
    }

    Expr vr, vl;
    Expr tvr, tvl;

    tvr=null_expr;
    tvl=null_expr;

    if(isGE(vterm) || isGT(vterm)){
      vr = vterm[0];
      vl = vterm[1];
    }
    else if(isLE(vterm) || isLT(vterm)){
      vr = vterm[1];
      vl = vterm[0];
    }
    else{
      DebugAssert(false, "impossilbe in toppred");
    }

    if(isIntx(vl,0)){
      tvl = getLeft(vr);
      tvr = getRight(vr);
    }
    else if(isIntx(vr,0)) {
      tvl = getLeft(vl);
      tvr = getRight(vl);
    }

    if( (null_expr != tvl) && (null_expr != tvr)){
      vl = tvl;
      vr = tvr;
    }


    const bool gtrue = (trueExpr()==findExpr(gterm));
    const bool gfalse = (falseExpr()==findExpr(gterm));

    TRACE("quant toppred"," vl, gl, vr, gr:", vl.toString()+"::"+gl.toString()+"||", vr.toString()+"::"+gr.toString());

    bool res;

    DebugAssert(!(trig.isNeg() && trig.isPos()), "expr in both pos and neg");

    if(!*d_usePolarity){
      return (recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env));
    }

    if(trig.isNeg()){
      if (( gtrue ) )  {
	res=(recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env));
      }
      else {
	res=(recSynMatch(gl, vr, env) && recSynMatch(gr, vl, env));
      }
    }
    else if(trig.isPos()){
      if (( gfalse )) {
	res=(recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env));
      }
      else {
	res=(recSynMatch(gl, vr, env) && recSynMatch(gr, vl, env));
      }
    }
    else {
      DebugAssert(false, "impossible polarity for trig");
      res = false;
    }

#ifdef _CVC3_DEBUG_MODE
    if( CVC3::debugger.trace("quant toppred")  ){
      cout<<"res| "<< res << " | " << gtrue << " | " << gfalse << endl;
    }
#endif
    return res;
  }
}
*/

/*
  Idealy, once a successful mathing is found here, the search should continue to check if there are more matchings.  For example, suppose vterm is f(g(x)) and gterm is f(a), and a=g(c)=g(d), c!=d.  The algorithm used now will only return the matching x=c.  There is no reason to leave x=d out.  However, testing of all quantified cases in SMT LIB, as of 11/28/2007, shows that the above senario never happens.  So, the search algorithm here returns once a successful matching is found
  This is not true for set1.smt
*/

bool cmpExpr( Expr e1, Expr e2){

  if(e1.isNull()) return true;
  if(e2.isNull()) return false;
  return (e1.getIndex() < e2.getIndex());
}

/*
  recMultMatch:
      syntax match, will return multiple bindings if possible
      must be called by multMatchChild or multMatchTop
      requires binds.size() == 1;

  input: one partial (empty) bindings in binds.
  output: successful bindings in binds
*/

bool TheoryQuant::recMultMatchDebug(const Expr& gterm,const Expr& vterm, vector<ExprMap<Expr> >& binds){
  //bool TheoryQuant::recMultMatch(const Expr& gterm,const Expr& vterm, vector<ExprMap<Expr> >& binds){
  TRACE("quant match", gterm , " VS ", vterm);
  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");
  DebugAssert (!isSysPred(vterm) && !isSysPred(gterm), "pred found in recMultMatch");
  DebugAssert (binds.size() == 1, "binds.size() > 1");


  if (BOUND_VAR == vterm.getKind() )  {
    ExprMap<Expr>& curEnv = binds[0]; //curEnv is both input and output
    ExprMap<Expr>::iterator iterVterm = curEnv.find(vterm);
    if ( iterVterm != curEnv.end()){
      return (simplifyExpr(gterm) == simplifyExpr(iterVterm->second)) ? true : false ;
    }
    else {
      curEnv[vterm] = simplifyExpr(gterm);
      return true;
    }
  }
  else if (!vterm.containsBoundVar()){
    return (simplifyExpr(vterm) == simplifyExpr(gterm)) ? true : false ;
  }
  else{ //let's do matching
    if(canGetHead(vterm)){
      Expr vhead = getHead(vterm);
      if(vterm.isAtomicFormula()){ //we do not want to match predicate up to equality here.  why? //more, if all pridicate is equilvent to true or false, we can just match the vterm with true or flase, we do not need a special case in theory, but the way here is more efficient for the current impelemention.

	// anoher problem is the interaction between matching and term's signature, I need to figure this out.

	if (canGetHead(gterm)) {
	  if ( vhead != getHead(gterm) ){
	    return false;
	  }
	  return multMatchChild(gterm, vterm, binds);
	}
	else{
	  return false;
	}
      }
      if ( (canGetHead(gterm)) && vhead == getHead(gterm)){
	return multMatchChild(gterm, vterm, binds);
      }

      //      cout<<"-- begin multi equality matching -- " << endl;
      //      cout<<"vterm: " << vterm << endl;
      //      cout<<"gterm: " << gterm << endl;

      ExprMap<Expr> orginalEnv = binds[0];
      vector<ExprMap<Expr> > candidateNewEnvs;
      bool newwayResult(false);

      if(*d_useNewEqu){
	vector<Expr> candidateGterms;
	{
	  Expr curCandidateGterm = gterm.getEqNext().getRHS();
	  while (curCandidateGterm != gterm){
	    DebugAssert(simplifyExpr(curCandidateGterm) == simplifyExpr(gterm), "curCandidateGterm != gterm");
            //	    cout<<"pushed candidate gterm " << getExprScore(curCandidateGterm) << " # " << curCandidateGterm << endl;
	    if(getExprScore(curCandidateGterm) <= d_curMaxExprScore || true){
	      candidateGterms.push_back(curCandidateGterm);
	    }
	    curCandidateGterm = curCandidateGterm.getEqNext().getRHS();
	  }
	}
	//	std::sort(candidateGterms.begin(), candidateGterms.end());
	//	for(int curGtermIndex = candidateGterms.size()-1; curGtermIndex >=0 ; curGtermIndex--){
	for(size_t curGtermIndex = 0 ; curGtermIndex < candidateGterms.size(); curGtermIndex++){
	  const Expr& curGterm = candidateGterms[curGtermIndex];
	  if(getHead(curGterm) == vhead){
	    vector<ExprMap<Expr> > newBinds;
	    newBinds.push_back(orginalEnv);
	    bool res =  multMatchChild(curGterm, vterm, newBinds);
	    if (res) 	{
              //	      cout << "found new match: " << endl;
              //	      cout << "curGterm: " <<  curGterm << endl;
              //	      cout << "simplified Gterm: " << simplifyExpr(gterm) << endl;
              //	      cout << "simplified curGterm: " << simplifyExpr(curGterm) << endl;
	      for(size_t newBindsIndex = 0; newBindsIndex < newBinds.size(); newBindsIndex++){
		candidateNewEnvs.push_back(newBinds[newBindsIndex]);
	      }
              //	      cout << "pushed newEnvs " << newBinds.size() << endl;
	    }
	  }
	}

	if (candidateNewEnvs.size() >= 1){
          //	  cout<<"found more matcings: " << candidateNewEnvs.size() << endl;
	  newwayResult = true;
	}
	else{
	  newwayResult = false;
	}
      } //end of new way of matching
      // let's do matching in the old way

      vector<ExprMap<Expr> > candidateOldEnvs;

      if( d_same_head_expr.count(vhead) > 0 ) {
	const Expr& findGterm = simplifyExpr(gterm);
	//if(isIntx(findGterm,0) || isIntx(findGterm,1)) return false;//special for simplify benchmark
	CDList<Expr>* gls = d_same_head_expr[vhead];
	for(size_t i = 0; i < gls->size(); i++){
	  const Expr& curGterm = (*gls)[i];
	  if(getExprScore(curGterm)> d_curMaxExprScore){
	    continue;
	  }
          //	  cout<<"same head term " << curGterm << endl;
	  if (simplifyExpr(curGterm) == findGterm){
	    DebugAssert((*gls)[i].arity() == vterm.arity(), "gls has different arity");

	    vector<ExprMap<Expr> > newBinds ;
	    newBinds.push_back(orginalEnv);
	    bool goodMatching(false);
	    goodMatching = multMatchChild(curGterm, vterm, newBinds);

	    if(goodMatching){
              //	      cout << "old curGterm: " << curGterm << endl;
              //	      cout << "old simplifed  curGterm: " << simplifyExpr(curGterm) << endl;
	      for(size_t newBindsIndex = 0; newBindsIndex < newBinds.size(); newBindsIndex++){
		candidateOldEnvs.push_back(newBinds[newBindsIndex]);
	      }
              //	      cout << "pushed oldEnvs " << newBinds.size() << endl;
	    }
	  }
	}//end of same head list
      }

      bool oldwayResult(false);

      if(candidateOldEnvs.size() >= 1){
	oldwayResult = true;
      }
      else{
	oldwayResult = false;
      }

      //      cout<<"new env size" << candidateNewEnvs.size() << endl;
      //      cout<<"old env size" << candidateOldEnvs.size() << endl;
      if( candidateNewEnvs.size() != candidateOldEnvs.size()){
        ;
        //	cout<<"found error?" << endl;
      }

      if(oldwayResult != newwayResult){
        ;
        //	cout << "-found bug in multMatch " << endl;
      }

      // binds = candidateNewEnvs;
      binds = candidateOldEnvs;

      return oldwayResult;
    }
    else{
      if( (gterm.getKind() == vterm.getKind()) &&
	  (gterm.arity() == vterm.arity()) &&
	  gterm.arity()>0 ){
        //	cout<<"why"<<endl;
	return multMatchChild(gterm, vterm, binds);
      }
      else {
	return false;
      }
    }
  }
  return false;
}

bool TheoryQuant::recMultMatchOldWay(const Expr& gterm,const Expr& vterm, vector<ExprMap<Expr> >& binds){
  //bool TheoryQuant::recMultMatch(const Expr& gterm,const Expr& vterm, vector<ExprMap<Expr> >& binds){
  TRACE("quant match",  "==recMultMatch\n", "---"+gterm.toString(), "\n+++"+vterm.toString());
  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");
  DebugAssert (!isSysPred(vterm) && !isSysPred(gterm), "pred found in recMultMatch");
  DebugAssert (binds.size() == 1, "binds.size() > 1");


  if (BOUND_VAR == vterm.getKind() )  {
    ExprMap<Expr>& curEnv = binds[0]; //curEnv is both input and output
    ExprMap<Expr>::iterator iterVterm = curEnv.find(vterm);
    if ( iterVterm != curEnv.end()){
      return (simplifyExpr(gterm) == simplifyExpr(iterVterm->second)) ? true : false ;
    }
    else {
      curEnv[vterm] = simplifyExpr(gterm);
      return true;
    }
  }
  else if (!vterm.containsBoundVar()){
    return (simplifyExpr(vterm) == simplifyExpr(gterm)) ? true : false ;
  }
  else{ //let's do matching
    if(canGetHead(vterm)){
      Expr vhead = getHead(vterm);
      if(vterm.isAtomicFormula()){ //we do not want to match predicate up to equality here.  why?
	if (canGetHead(gterm)) {
	  if ( vhead != getHead(gterm) ){
	    return false;
	  }
	  return multMatchChild(gterm, vterm, binds);
	}
	else{
	  return false;
	}
      }
      if ( (canGetHead(gterm)) && vhead == getHead(gterm)){
	return multMatchChild(gterm, vterm, binds);
      }

      TRACE("quant multmatch", "-- begin multi equality matching -- ", "" ,"");
      TRACE("quant multmatch", "vterm: " ,  vterm, "");
      TRACE("quant multmatch", "gterm: " ,  gterm, "");

      ExprMap<Expr> orginalEnv = binds[0];

      vector<ExprMap<Expr> > candidateOldEnvs;

      if( d_same_head_expr.count(vhead) > 0 ) {
	const Expr& findGterm = simplifyExpr(gterm);
	TRACE("quant multmatch", "simp gterm: " ,  simplifyExpr(gterm), "");
	//if(isIntx(findGterm,0) || isIntx(findGterm,1)) return false;//special for simplify benchmark
	CDList<Expr>* gls = d_same_head_expr[vhead];
	for(size_t i = 0; i < gls->size(); i++){
	  const Expr& curGterm = (*gls)[i];
   	  if(getExprScore(curGterm)> d_curMaxExprScore){
   	    continue;
   	  }
	  TRACE("quant multmatch", "same head term ", curGterm, "");
	  TRACE("quant multmatch", "simp same head term ", simplifyExpr(curGterm), "");
	  if (simplifyExpr(curGterm) == findGterm){
	    DebugAssert((*gls)[i].arity() == vterm.arity(), "gls has different arity");
	    vector<ExprMap<Expr> > newBinds ;
	    newBinds.push_back(orginalEnv);
	    bool goodMatching(false);
	    goodMatching = multMatchChild(curGterm, vterm, newBinds);

	    if(goodMatching){
	      TRACE("quant multmatch", "old curGterm: ", curGterm, "");
	      TRACE("quant multmatch", "old simplifed  curGterm: ", simplifyExpr(curGterm), "");
	      for(size_t newBindsIndex = 0; newBindsIndex < newBinds.size(); newBindsIndex++){
		candidateOldEnvs.push_back(newBinds[newBindsIndex]);
	      }
	      TRACE("quant multmatch", "pushed oldEnvs " , newBinds.size(), "");
	    }
	  }
	}//end of same head list
      }

      bool oldwayResult(false);

      if(candidateOldEnvs.size() >= 1){
	oldwayResult = true;
      }
      else{
	oldwayResult = false;
      }

      TRACE("quant multmatch", "old env size" ,candidateOldEnvs.size(), "");
      binds = candidateOldEnvs;
      return oldwayResult;
    }
    else{
      if( (gterm.getKind() == vterm.getKind()) &&
	  (gterm.arity() == vterm.arity()) &&
	  gterm.arity()>0 ){
	return multMatchChild(gterm, vterm, binds);
      }
      else {
	return false;
      }
    }
  }
  return false;
}



//bool TheoryQuant::recMultMatchNewWay(const Expr& gterm,const Expr& vterm, vector<ExprMap<Expr> >& binds){
bool TheoryQuant::recMultMatch(const Expr& gterm,const Expr& vterm, vector<ExprMap<Expr> >& binds){
  TRACE("quant match", gterm , " VS ", vterm);
  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");
  DebugAssert (!isSysPred(vterm) && !isSysPred(gterm), "pred found in recMultMatch");
  DebugAssert (binds.size() == 1, "binds.size() > 1");

  if (BOUND_VAR == vterm.getKind() )  {
    ExprMap<Expr>& curEnv = binds[0]; //curEnv is both input and output
    ExprMap<Expr>::iterator iterVterm = curEnv.find(vterm);
    if ( iterVterm != curEnv.end()){
      return (simplifyExpr(gterm) == simplifyExpr(iterVterm->second)) ? true : false ;
    }
    else {
      curEnv[vterm] = simplifyExpr(gterm);
      return true;
    }
  }
  else if (!vterm.containsBoundVar()){
    return (simplifyExpr(vterm) == simplifyExpr(gterm)) ? true : false ;
  }
  else{ //let's do matching
    if(canGetHead(vterm)){
      Expr vhead = getHead(vterm);
      if(vterm.isAtomicFormula()){ //we do not want to match predicate up to equality here.  why?
	if (canGetHead(gterm)) {
	  if ( vhead != getHead(gterm) ){
	    return false;
	  }
	  return multMatchChild(gterm, vterm, binds);
	}
	else{
	  return false;
	}
      }
      if ( (canGetHead(gterm)) && vhead == getHead(gterm)){
	//well, what if gterm and vterm cannot match later, but vterm can match some guys in the equivalent class of gterm?
	return multMatchChild(gterm, vterm, binds);
      }

      TRACE("quant multmatch", "-- begin multi equality matching -- ", "" ,"");
      TRACE("qunat multmatch", "vterm: " ,  vterm, "");
      TRACE("qunat multmatch", "gterm: " ,  gterm, "");

      ExprMap<Expr> orginalEnv = binds[0];
      vector<ExprMap<Expr> > candidateNewEnvs;
      bool newwayResult(false);

      if(*d_useNewEqu){
	vector<Expr> candidateGterms;
	{
	  if(!gterm.hasFind()) {
	    return false;
	  }
	  Expr curCandidateGterm = gterm.getEqNext().getRHS();
	  while (curCandidateGterm != gterm){
	    DebugAssert(simplifyExpr(curCandidateGterm) == simplifyExpr(gterm), "curCandidateGterm != gterm");
	    TRACE("quant multmatch", "pushed candidate gterm ", getExprScore(curCandidateGterm),  " # " + curCandidateGterm.toString());
	    //maybe we should not check the score here, but we need check sig .
	    if(getExprScore(curCandidateGterm) <= d_curMaxExprScore || true ){
 	      candidateGterms.push_back(curCandidateGterm);
	    }
	    curCandidateGterm = curCandidateGterm.getEqNext().getRHS();
	  }
	}
	for(size_t curGtermIndex = 0 ; curGtermIndex < candidateGterms.size(); curGtermIndex++){
	  const Expr& curGterm = candidateGterms[curGtermIndex];
	  if(getHead(curGterm) == vhead){
	    vector<ExprMap<Expr> > newBinds;
	    newBinds.push_back(orginalEnv);
	    bool res =  multMatchChild(curGterm, vterm, newBinds, true);
	    if (res) 	{
	      TRACE("quant multmatch", "found new match: ", "" ,"");
	      TRACE("quant multmatch", "curGterm: ",  curGterm , "");
	      TRACE("quant multmatch", "simplified Gterm: ", simplifyExpr(gterm), "" );
	      TRACE("quant multmatch", "simplified curGterm: ",  simplifyExpr(curGterm), "");
	      for(size_t newBindsIndex = 0; newBindsIndex < newBinds.size(); newBindsIndex++){
		candidateNewEnvs.push_back(newBinds[newBindsIndex]);
	      }
	      TRACE("quant multmathc", "pushed newEnvs ", newBinds.size(), "");
	    }
	  }
	}

	if (candidateNewEnvs.size() >= 1){
	  TRACE("quant multmacht", "found more matcings: " , candidateNewEnvs.size(), "");
	  newwayResult = true;
	}
	else{
	  newwayResult = false;
	}
      } //end of new way of matching

      TRACE("quant multmatch", "new env size " , candidateNewEnvs.size(), "");
      binds = candidateNewEnvs;
      return newwayResult;
    }
    else{
      if  ( (gterm.getKind() == vterm.getKind()) &&
	    (gterm.arity() == vterm.arity()) &&
	    gterm.arity()>0 )
	{
	  return multMatchChild(gterm, vterm, binds);
	}
      else {
	return false;
      }
    }
  }
  return false;
}


/*
bool TheoryQuant::recSynMatch(const Expr& gterm, const Expr& vterm, ExprMap<Expr>& env){
  cout << "-error: should not be called, recSynMatch" << endl;
  TRACE("quant match", gterm , " VS ", vterm);
  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");
  DebugAssert (!isSysPred(vterm) && !isSysPred(gterm), "pred found");

  if (BOUND_VAR == vterm.getKind() )  {
    ExprMap<Expr>::iterator p = env.find(vterm);
    if ( p != env.end()){
      return (simplifyExpr(gterm) == simplifyExpr(p->second)) ? true : false ;
    }
    else {
      env[vterm] = simplifyExpr(gterm);
      return true;
    }
  }
  else if (!vterm.containsBoundVar()){
    return (simplifyExpr(vterm) == simplifyExpr(gterm)) ? true : false ;
  }
  else{ //let's do matching
    if(canGetHead(vterm)){
      Expr vhead = getHead(vterm);
      if(vterm.isAtomicFormula()){ //we do not want to match predicate up to equality here.  why?
	if (canGetHead(gterm)) {
	  if ( vhead != getHead(gterm) ){
	    return false;
	  }
	  return matchChild(gterm, vterm, env);
	}
	else{
	  return false;
	}
      }
      if ( (canGetHead(gterm)) && vhead == getHead(gterm)){
	return matchChild(gterm, vterm, env);
      }

      if(!*d_useEqu){
	return false;
      }

      cout<<"-- begin equality matching -- " << endl;
      cout<<"vterm: " << vterm << endl;
      cout<<"gterm: " << gterm << endl;

      ExprMap<Expr> orginalEnv = env;

      vector<ExprMap<Expr> > candidateNewEnvs;

      //      if(*d_useNewEqu){

	vector<Expr> candidateGterms;
	{
	  Expr curCandidateGterm = gterm.getEqNext().getRHS();
	  while (curCandidateGterm != gterm){
	    DebugAssert(simplifyExpr(curCandidateGterm) == simplifyExpr(gterm), "curCandidateGterm != gterm");
	    cout<<"pushed candidate gterm " << curCandidateGterm << endl;
	    candidateGterms.push_back(curCandidateGterm);
	    curCandidateGterm = curCandidateGterm.getEqNext().getRHS();
	  }
	}
	std::sort(candidateGterms.begin(), candidateGterms.end());
	//	for(int curGtermIndex = candidateGterms.size()-1; curGtermIndex >=0 ; curGtermIndex--){
	for(size_t curGtermIndex = 0 ; curGtermIndex < candidateGterms.size(); curGtermIndex++){
	  const Expr& curGterm = candidateGterms[curGtermIndex];
	  if(getHead(curGterm) == vhead){
	    ExprMap<Expr> newEnv = orginalEnv;
	    bool res =  matchChild(curGterm, vterm, newEnv);
	    if (res) 	{
	      cout << "found new match: " << endl;
	      cout << "curGterm: " <<  curGterm << endl;
	      cout << "simplified Gterm: " << simplifyExpr(gterm) << endl;
	      cout << "simplified curGterm: " << simplifyExpr(curGterm) << endl;
	      candidateNewEnvs.push_back(newEnv);
	    }
	  }
	}

	ExprMap<Expr> newwayEnv;
	bool newwayResult(false);

	if (candidateNewEnvs.size() >= 1){
	  cout<<"found more matcings: " << candidateNewEnvs.size() << endl;
	  newwayEnv = candidateNewEnvs[0]; // we have a choice here
	  //	  newwayEnv = candidateNewEnvs.back(); // we have a choice here
	  newwayResult = true;
	}
	else{
	  newwayResult = false;
	}
	//      } //end of new way of matching
      // let's do matching in the old way

      vector<ExprMap<Expr> > candidateOldEnvs;

      if( d_same_head_expr.count(vhead) > 0 ) {
	const Expr& findGterm = simplifyExpr(gterm);
	//if(isIntx(findGterm,0) || isIntx(findGterm,1)) return false;//special for simplify benchmark
	CDList<Expr>* gls = d_same_head_expr[vhead];
	for(size_t i = 0; i < gls->size(); i++){
	  cout<<"same head term " << (*gls)[i] << endl;
	  if (simplifyExpr((*gls)[i]) == findGterm){
	    DebugAssert((*gls)[i].arity() == vterm.arity(), "gls has different arity");

	    ExprMap<Expr> curEnv = orginalEnv;
	    const Expr& curGterm = (*gls)[i];

	    bool goodMatching(false);
	    goodMatching = matchChild(curGterm, vterm, curEnv);

	    if(goodMatching){
	      cout << "old curGterm: " << curGterm << endl;
	      cout << "old simplifed  curGterm: " << simplifyExpr(curGterm) << endl;
	      candidateOldEnvs.push_back(curEnv);
;
	    }
	  }
	}//end of same head list
      }

      ExprMap<Expr> oldwayEnv;
      bool oldwayResult(false);

      if(candidateOldEnvs.size() >= 1){
	oldwayResult = true;
	oldwayEnv = candidateOldEnvs[0];
      }
      else{
	oldwayResult = false;
      }

      cout<<"new env size" << candidateNewEnvs.size() << endl;
      cout<<"old env size" << candidateOldEnvs.size() << endl;
      if( candidateNewEnvs.size() != candidateOldEnvs.size()){
	cout<<"found error?" << endl;
      }

      if(oldwayResult != newwayResult){
	cout<<"found bug" << endl;
	cout<<"oldway result: " << oldwayResult << endl;
	cout<<"newway result: " << newwayResult << endl;
      }

      if(false == oldwayResult ) return false;

      if(newwayEnv != oldwayEnv){
	bool notFound(true);
	int foundIndex(-1);
	for(size_t i = 0; i <candidateNewEnvs.size(); i++){
	  if (candidateNewEnvs[i] == oldwayEnv){
	    foundIndex = i;
	    cout<<"found env " << i << endl;
	    notFound = false;
	  }
	}
	if (notFound){
	  cout<<"found strange env" << endl;;
	  cout<<gterm << " " << gterm.getIndex()<<endl;
	  cout<<vterm << " " << vterm.getIndex()<<endl;
	  cout<<exprMap2string(newwayEnv)<<endl;
	  cout<<exprMap2string(oldwayEnv)<<endl;
	}
      }
      //env = oldwayEnv;
      env = newwayEnv;
      return true;
    }
    else{
      if( (gterm.getKind() == vterm.getKind()) &&
	  (gterm.arity() == vterm.arity()) &&
	  gterm.arity()>0 ){
	return matchChild(gterm, vterm, env);
      }
      else {
	return false;
      }
    }
  }
  return false;
}

*/

/*
//the following is not used anymore, the code is here for refreence.
bool TheoryQuant::recSynMatchBackupOnly(const Expr& gterm, const Expr& vterm, ExprMap<Expr>& env){
  cout<<"-error: should not be called: recSynMatchBackupOnly " << endl;
  TRACE("quant match", "gterm:| "+gterm.toString()," vterm:| "+vterm.toString(),"");
  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");

  if (BOUND_VAR == vterm.getKind() )  {
    TRACE("quant match", "bound var found;", vterm.toString(),"");
    ExprMap<Expr>::iterator p = env.find(vterm);
    if ( p != env.end()){
      if (simplifyExpr(gterm) != simplifyExpr(p->second)){
	return false;
      }
      else
	return true;
    }
    else {
      env[vterm] = simplifyExpr(gterm);
      return true;
    }
  }
  else if (!vterm.containsBoundVar()){
    //    return true;
    //    cout<<"vterm and gterm"<<vterm << " # " <<gterm<<endl;
    if(simplifyExpr(vterm) == simplifyExpr(gterm)) {
      return true;
    }
    else{
      return false;
    }
  }

  else if(false && isSysPred(vterm) && isSysPred(gterm)){

    TRACE("quant syspred"," vterm, gterm ", vterm.toString()+" :|: ", gterm.toString());
    TRACE("quant syspred"," simplified vterm, gterm ", simplifyExpr(vterm).toString()+" :|: ", simplifyExpr(gterm).toString());
    FatalAssert(false, "should not be here in synmatch");
    exit(3);
  }
  else{ //let's do matching
    if(canGetHead(vterm)){
      Expr vhead = getHead(vterm);
      TRACE("quant match", "head vterm:", getHead(vterm), "");
      if(vterm.isAtomicFormula()){
	if (canGetHead(gterm)) {
	  if ( vhead != getHead(gterm) ){
	    return false;
	  }
	  return matchChild(gterm, vterm, env);
	  // 	    for(int i=vterm.arity()-1; i >= 0; i--){
	  // 	      if (false == recSynMatch(gterm[i], vterm[i] , env))
	  // 		return false;
	  // 	    }
	  // 	    return true;
	}
	else{
	  return false;
	}
      }
      if ( (canGetHead(gterm)) && vhead == getHead(gterm)){
	//	  if(gterm.arity() != vterm.arity()){
	//	    return false;
	//	  }
	// 	  for(int i=vterm.arity()-1; i >= 0; i--){
	// 	    if (false == recSynMatch(gterm[i], vterm[i] , env)) {
	// 	      return false;
	// 	    }
// 	  }
// 	  return true;
	return matchChild(gterm, vterm, env);
      }

      if(!*d_useEqu){
	return false;
      }

      cout<<"-- begin equality matching -- " << endl;
      cout<<"vterm: " << vterm << endl;
      cout<<"gterm: " << gterm << endl;
      bool newwayResult(false);
      bool oldwayResult(false);
      ExprMap<Expr> orgEnv = env;
      ExprMap<Expr> newwayEnv;
      ExprMap<Expr> oldwayEnv;

      vector<ExprMap<Expr> > candidateEnv; // here just for test
      if(*d_useNewEqu){
// 	int debug1= vterm.getIndex();
// 	int debug2= gterm.getIndex();
// 	if(debug1 == 311 && debug2 == 361){
// 	  cout<<"begin here" << endl;
// 	}


	Expr cur_next = gterm.getEqNext().getRHS();
	Expr vhead = getHead(vterm);
	TRACE("quant newequ", "gterm: " ,gterm, "");
	TRACE("quant newequ", "v: " , vterm, "" );
	//
	  Idealy, once a successful mathing is found here, the search should continue to checkif there are more matchings.  For example, suppose vterm is f(g(x)) and gterm is f(a), and a=g(c)=g(d), c!=d.  The algorithm used now will only return the matching x=c.  There is no reason to leave x=d out.  However, testing of all quantified cases in SMT LIB, as of 11/28/2007, shows that the above senario never happens.  So, the search algorithm here returns once a successful matching is found
	  //	  This is not true for set1.smt
	//	vector<ExprMap<Expr> > candidateEnv;
	vector<Expr> candidateGterms;

	while (cur_next != gterm){
	  if(simplifyExpr(cur_next) != simplifyExpr(gterm)){
	    cout<<" impossible"<<endl;
	  }
	  cout<<"pushed candidate gterm " << cur_next << endl;
	  candidateGterms.push_back(cur_next);
	  cur_next = cur_next.getEqNext().getRHS();
	}

	//	for(int curGtermIndex = candidateGterms.size()-1; curGtermIndex >=0 ; curGtermIndex--){
	for(size_t curGtermIndex = 0 ; curGtermIndex < candidateGterms.size(); curGtermIndex++){
	  Expr curGterm = candidateGterms[curGtermIndex];
	  if(getHead(curGterm) == vhead){
	    TRACE("quant newequ", " matched good", "", "");
	    ExprMap<Expr> newEnv = orgEnv;
	    bool res =  matchChild(curGterm, vterm, newEnv);
	    TRACE("quant newequ", "final result: ",res ,"");
	    if (res) 	{
	      env=newEnv;
	      //	return res;
	      cout << "found new match: " << endl;
	      cout << "curGterm: " <<  curGterm << endl;
	      cout << "simplified Gterm: " << simplifyExpr(gterm) << endl;
	      cout << "simplified curGterm: " << simplifyExpr(curGterm) << endl;
	      newwayEnv = newEnv;
	      newwayResult = res; //break;;
	      candidateEnv.push_back(newEnv);
	    }
	  }
	}



	while (cur_next != gterm) {
	  TRACE("quant newequ", "g: " ,cur_next, "");
	  TRACE("quant newequ", "vhead: ", vhead, "");
	  TRACE("quant newequ", "g head: ", getHead(cur_next), "");
	  TRACE("quant newequ", "g score: ", getExprScore(cur_next), "");
	  //	    if(getExprScore(cur_next)>15) continue;

	  if(getHead(cur_next) == vhead){

	    TRACE("quant newequ", " matched good", "", "");
	    ExprMap<Expr> newEnv = env;
	    bool res =  matchChild(cur_next, vterm, newEnv);
	    TRACE("quant newequ", "final result: ",res ,"");
	    if (res) 	{
	      env=newEnv;
	      //	return res;
	      newwayEnv = newEnv;
	      newwayResult = res; //break;;
	      candidateEnv.push_back(newEnv);
	    }
	  }
	  cur_next = cur_next.getEqNext().getRHS();
	}


// 	if(candidateEnv.size() == 1){
// 	  env = candidateEnv[0];
// 	  return true;
// 	}
// 	else if (candidateEnv.size() > 1){
// 	  env = candidateEnv[0];
// 	  return true;
// 	  cout<<"found more matcings" << endl;
// 	}


	if (candidateEnv.size() > 1){
	  cout<<"found more matcings" << endl;
	  //	  newwayEnv = candidateEnv[0];
	}

	TRACE("quant newequ", " not matched ", vterm, gterm);
	  //	  return false;
	if(newwayResult) {
	}
	else{
	newwayResult = false ;
	}
      }

      vector<ExprMap<Expr> > candidateOldEnv; //for test only
      //      else { //else we use old equ algorithm
	env = orgEnv;
	//	cout<<"==============================="<<endl;
	//	cout<<gterm<<" # " <<vterm<<endl;

	if(false)
	  { //
	  //	  std::set<Expr> eq_set;
	  std::map<Expr,bool> eq_set;
	  eq_set.clear();
	  eq_set[gterm]=true;

	  std::queue<Expr> eq_queue;

	  ExprMap<CDList<Expr>* >::iterator iter = d_eq_list.find(gterm);

	  if(iter != d_eq_list.end()){
	    for(size_t len =0; len< iter->second->size(); len++){
	      eq_queue.push((*(iter->second))[len]);
	    }
	    int count =0;
	    while(eq_queue.size()>0){
	      count++;
	      const Expr& cur = eq_queue.front();
	      eq_queue.pop();
	      if(eq_set.find(cur) == eq_set.end()){
		if(canGetHead(cur) && getHead(cur) == vhead){
// 		  	      cout<<"VTERM: "<<vterm<<endl;
// 		  	      cout<<"FOUND: "<<cur<<endl;
// 		  	      cout<<"GTERM:  "<<gterm<<endl;
		  //		  cout<<"--good match: " << count << "  // " << gterm << " # " << cur << endl;
		  //		  cout<<"===good simple: " << count << "  // " << simplifyExpr(gterm) << " # " << simplifyExpr(cur) << endl;

		  if(simplifyExpr(cur) != simplifyExpr(gterm)){
		    // return false;
		    //		    return matchChild(cur, vterm, env);
		    //		    cout<<"en? "<<gterm<<" # " <<cur <<" # " <<vterm<<endl;
		  }
		  else{
		    //		    cout<<"--good match: " << count << "  // " << gterm << " # " << cur << endl;
		    //		    cout<<"===good simple: " << count << "  // " << simplifyExpr(gterm) << " # " << simplifyExpr(cur) << endl;
		    //		    return matchChild(cur, vterm, env);
		  }
		}

		eq_set[cur]=true;
		ExprMap<CDList<Expr>* >::iterator iter = d_eq_list.find(cur);

		if(iter != d_eq_list.end()){
		  for(size_t len =0; len< iter->second->size(); len++){
		    eq_queue.push((*(iter->second))[len]);
		  }
		}
	      }
	    }
	  }
	  //	  return false;
	}

	if( d_same_head_expr.count(vhead) > 0 ) {
	  const Expr& findGterm = simplifyExpr(gterm);
	  //if(isIntx(findGterm,0) || isIntx(findGterm,1)) return false;//special for simplify benchmark
	  TRACE("quant match", "find gterm:", findGterm.toString(),"");
	  CDList<Expr>* gls = d_same_head_expr[vhead];
	  if (false)
	    { int count =0;
	      for(size_t i = 0; i<gls->size(); i++){
	      if (simplifyExpr((*gls)[i]) == findGterm){
	      count++;
	      }
	      }
	      if(count>1){
	      cout<<"count " << count << " # " << gls->size() << " | "<<gterm<<endl;
	      for(size_t i = 0; i<gls->size(); i++){
	      if (simplifyExpr((*gls)[i]) == findGterm){
	      cout<<"eq "<<(*gls)[i]<<endl;
	      }
	      }
	      }
	      }

	  for(size_t i = 0; i<gls->size(); i++){
	    cout<<"same head term " << (*gls)[i] << endl;
	    if (simplifyExpr((*gls)[i]) == findGterm){
	      env = orgEnv;
	      oldwayResult = true;
	      TRACE("quant match", "find matched gterm:", (*gls)[i].toString(),"");
	      DebugAssert((*gls)[i].arity() == vterm.arity(), "gls has different arity");

	      const Expr& newgterm = (*gls)[i];
	      for(int child=vterm.arity()-1; child >= 0 ; child--){
		if (false == recSynMatch(newgterm[child], vterm[child] , env)){
		  TRACE("quant match", "match false", (*gls)[i][child].toString(), vterm[child].toString());
		  //		    return false;
		  oldwayEnv = env; oldwayResult = false; break;
		}
	      }
	      TRACE("quant match", "good match, return true:", gterm, vterm.toString());
	      //	      cout<<"quant good match: " <<i<<" // "<<gterm << " # "<<vterm<<endl;
	      //	      cout<<"quant simple: " <<i<<" // "<<simplifyExpr(gterm) << " # "<<vterm<<endl;
		//		return true;
	      //problem
	      if(oldwayResult){
		cout << "old curGterm: " << newgterm << endl;
		cout << "old simplifed  curGterm: " << simplifyExpr(newgterm) << endl;
		oldwayResult = true; oldwayEnv = env; //break;
		candidateOldEnv.push_back(oldwayEnv);
	      }
	      else{
		oldwayResult = false;
	      }
	    }
	  }//end of for
	  //	do not forget this    return false;

	}
	else  {
	  oldwayResult = false;
	  //	    return false;//end of if
	}
	//      }

	cout<<"new env size" << candidateEnv.size() << endl;
	cout<<"old env size" << candidateOldEnv.size() << endl;
	if( candidateEnv.size() != candidateOldEnv.size()){
	  cout<<"error?" << endl;
	}
	if(newwayEnv != oldwayEnv && oldwayResult == newwayResult){
	bool notFound(true);
	int foundIndex(-1);
	for(size_t i = 0; i <candidateEnv.size(); i++){
	  if (candidateEnv[i] == oldwayEnv){
	    foundIndex = i;
	    cout<<"found env " << i << endl;
	    notFound = false;
	  }
	}
	if (notFound){
	  cout<<"found strange env" << endl;;
	  cout<<"new way find " << candidateEnv.size()<<endl;
	  cout<<gterm << " " << gterm.getIndex()<<endl;
	  cout<<vterm << " " << vterm.getIndex()<<endl;
	  cout << "oldEnv" << candidateOldEnv.size() << endl;
	  cout<<exprMap2string(newwayEnv)<<endl;
	  cout<<exprMap2string(oldwayEnv)<<endl;

	}
      }
      if(oldwayResult != newwayResult){
	cout<<"found strange" << endl;
	cout<<gterm << " " << gterm.getIndex()<<endl;
	cout<<vterm << " " << vterm.getIndex()<<endl;
      }
      else{
	//	env = newwayEnv;
	return oldwayResult;
      }

    }
    else{
      TRACE("quant match more", "match more", gterm.toString()+" # ", vterm.toString());
      if( (gterm.getKind() == vterm.getKind()) &&
	  (gterm.arity() == vterm.arity()) &&
	  gterm.arity()>0 ){
	//   	  for(int child=0; child < vterm.arity() ; child++){
	//   	    if (false == recSynMatch(gterm[child], vterm[child] , env)){
	//   	      TRACE("quant match", "match false", gterm[child].toString(), vterm[child].toString());
//   	      return false;
//   	    }
//   	  }
//   	  return true;
//   	  if( gterm.getKind() == PLUS || gterm.getKind() == MINUS){
//   	    cout<<"g v"<<gterm<< " # " <<vterm<<endl;
//   	  }

	return matchChild(gterm, vterm, env);
      }
      else {
//   	  if( gterm.getKind() == PLUS || gterm.getKind() == MINUS){
// 	    static bool gvfound = false;
//   	    if(!gvfound){
// 	      cout<<"g v 1"<<endl;
// 	      gvfound =true;
// 	    }
	    //gterm<< " # " <<vterm<<endl;
	  //  }
	return false;
      }
    }
  }
}
*/

/*

bool TheoryQuant::synMatchTopPred(const Expr& gterm, Trigger trig, ExprMap<Expr>& env){

  const Expr vterm = trig.getEx();

  TRACE("quant toppred", "top pred: gterm:| "+gterm.toString()," vterm:| "+vterm.toString(),"");

  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");
  DebugAssert ((BOUND_VAR != vterm.getKind()),"top pred match "+gterm.toString()+" has bound var");

  if(gterm.isEq() || vterm.isEq()){
    return false; // we do not match with equality
  }

  bool res2=false;

  //  if(vterm.arity() != gterm.arity()) return false;

  if(trig.isSimp()){
    if(trig.getHead() == getHead(gterm) ){
      for(int i = vterm.arity()-1; i>=0 ; i--){
	if(BOUND_VAR != vterm[i].getKind()){
	  if(simplifyExpr(gterm[i]) != simplifyExpr(vterm[i])) {
	    return false;
	  }
	}
      }
      for(int i = vterm.arity()-1; i>=0 ; i--){
	if(BOUND_VAR == vterm[i].getKind()){
	  if(d_allout){
	    env[vterm[i]] = simplifyExpr(gterm[i]);
	  }
	  else {
	    env[vterm[i]] = simplifyExpr(gterm[i]);
	  }
	}
      }
      return true;
    }
    else{
      return false;
    }
  }

  if(!(isSysPred(vterm) && isSysPred(gterm))){
    if(isSysPred(vterm) || isSysPred(gterm)) {
      return false;
    }
    if(!usefulInMatch(gterm)){
      return false;
    }
    if(trig.getHead() != getHead(gterm)){
      return false;
    }

    if(!gterm.getType().isBool()){
      res2= recSynMatch(gterm, vterm, env);
      return res2;
    }

    if(!*d_usePolarity){
      return recSynMatch(gterm, vterm, env);
    }

    const bool gtrue = (trueExpr()==findExpr(gterm));
    if(gtrue ){
      if(trig.isNeg()) {
	return recSynMatch(gterm, vterm, env);
      }
      else{
	return false;
      }
    }
    const bool gfalse = (falseExpr()==findExpr(gterm));
    if(gfalse){
      if (trig.isPos()){
	return recSynMatch(gterm, vterm, env);
      }
      else{
	return false;
      }
    }
    else {
      return false;
    }
  }
  else{
    DebugAssert((2==gterm.arity() && 2==vterm.arity()), "impossible situation in top pred");
    DebugAssert(!((isLE(gterm) || isLT(gterm)) && !isIntx(gterm[0],0)), "canonical form changed");

#ifdef _CVC3_DEBUG_MODE
    if( CVC3::debugger.trace("quant toppred")  ){
      cout << "toppred gterm, vterm" << gterm << "::" << vterm << endl;
      cout << findExpr(gterm) << "::" << trig.isPos() << "|" << trig.isNeg() << endl;
    }
#endif


    Expr gl = getLeft(gterm[1]);
    Expr gr = getRight(gterm[1]);

    if(null_expr == gr || null_expr == gl){
      gl = gterm[0];
      gr = gterm[1];
    }

    Expr vr, vl;
    Expr tvr, tvl;

    tvr=null_expr;
    tvl=null_expr;

    if(isGE(vterm) || isGT(vterm)){
      vr = vterm[0];
      vl = vterm[1];
    }
    else if(isLE(vterm) || isLT(vterm)){
      vr = vterm[1];
      vl = vterm[0];
    }
    else{
      DebugAssert(false, "impossilbe in toppred");
    }

    if(isIntx(vl,0)){
      tvl = getLeft(vr);
      tvr = getRight(vr);
    }
    else if(isIntx(vr,0)) {
      tvl = getLeft(vl);
      tvr = getRight(vl);
    }

    if( (null_expr != tvl) && (null_expr != tvr)){
      vl = tvl;
      vr = tvr;
    }


    const bool gtrue = (trueExpr()==findExpr(gterm));
    const bool gfalse = (falseExpr()==findExpr(gterm));

    TRACE("quant toppred"," vl, gl, vr, gr:", vl.toString()+"::"+gl.toString()+"||", vr.toString()+"::"+gr.toString());

    bool res;

    DebugAssert(!(trig.isNeg() && trig.isPos()), "expr in both pos and neg");

    if(!*d_usePolarity){
      return (recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env));
    }

    if(trig.isNeg()){
      if (( gtrue ) )  {
	res=(recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env));
      }
      else {
	res=(recSynMatch(gl, vr, env) && recSynMatch(gr, vl, env));
      }
    }
    else if(trig.isPos()){
      if (( gfalse )) {
	res=(recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env));
      }
      else {
	res=(recSynMatch(gl, vr, env) && recSynMatch(gr, vl, env));
      }
    }
    else {
      DebugAssert(false, "impossible polarity for trig");
      res = false;
    }

#ifdef _CVC3_DEBUG_MODE
    if( CVC3::debugger.trace("quant toppred")  ){
      cout<<"res| "<< res << " | " << gtrue << " | " << gfalse << endl;
    }
#endif
    return res;
  }
}

bool TheoryQuant::recSynMatch(const Expr& gterm, const Expr& vterm, ExprMap<Expr>& env){
  TRACE("quant match", "gterm:| "+gterm.toString()," vterm:| "+vterm.toString(),"");
  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");

  if (BOUND_VAR == vterm.getKind())  {
    TRACE("quant match", "bound var found;", vterm.toString(),"");
    ExprMap<Expr>::iterator p = env.find(vterm);
    if ( p != env.end()){
      if (simplifyExpr(gterm) != simplifyExpr(p->second)){
	return false;
      }
      else
	return true;
    }
    else {
      env[vterm] = simplifyExpr(gterm);
      return true;
    }
  }
  else if (!vterm.containsBoundVar()){
    if(simplifyExpr(vterm) == simplifyExpr(gterm)) {
      return true;
    }
    else{
      return false;
    }
  }

  else if(false && isSysPred(vterm) && isSysPred(gterm)){

    TRACE("quant syspred"," vterm, gterm ", vterm.toString()+" :|: ", gterm.toString());
    TRACE("quant syspred"," simplified vterm, gterm ", simplifyExpr(vterm).toString()+" :|: ", simplifyExpr(gterm).toString());
    FatalAssert(false, "should not be here in synmatch");
    exit(3);
  }
  else{
      if(canGetHead(vterm)){
	Expr vhead = getHead(vterm);
	TRACE("quant match", "head vterm:", getHead(vterm), "");
	if(vterm.isAtomicFormula()){
	  if (canGetHead(gterm)) {
	    if ( vhead != getHead(gterm) ){
	      return false;
	    }
	    for(int i=vterm.arity()-1; i >= 0; i--){
	      if (false == recSynMatch(gterm[i], vterm[i] , env))
		return false;
	    }
	    return true;
	  }
	  else{
	    return false;
	  }
	}
	if ( (canGetHead(gterm)) && vhead == getHead(gterm)){
	  if(gterm.arity() != vterm.arity()){
	    return false;
	  }
	  for(int i=vterm.arity()-1; i >= 0; i--){
	    if (false == recSynMatch(gterm[i], vterm[i] , env)) {
	      return false;
	    }
	  }
	  return true;
	}

	if(false && !*d_useEqu){
	  return false;
	}

	if( d_same_head_expr.count(vhead) > 0 ) {
	  const Expr& findGterm = simplifyExpr(gterm);
	  //if(isIntx(findGterm,0) || isIntx(findGterm,1)) return false;//special for simplify benchmark
	  TRACE("quant match", "find gterm:", findGterm.toString(),"");
	  CDList<Expr>* gls = d_same_head_expr[vhead];
	  for(size_t i = 0; i<gls->size(); i++){
	    if (simplifyExpr((*gls)[i]) == findGterm){
	      TRACE("quant match", "find matched gterm:", (*gls)[i].toString(),"");
	      DebugAssert((*gls)[i].arity() == vterm.arity(), "gls has different arity");

	      for(int child=vterm.arity()-1; child >= 0 ; child--){
		const Expr& newgterm = (*gls)[i];
		if (false == recSynMatch(newgterm[child], vterm[child] , env)){
		  TRACE("quant match", "match false", (*gls)[i][child].toString(), vterm[child].toString());
		  return false;
		}
	      }
	      TRACE("quant match", "good match, return true:", gterm, vterm.toString());
	      return true;
	    }
	  }//end of for
	  return false;
	}
	else  {
	  return false;//end of if
	}
      }
      else{
 	TRACE("quant match more", "match more", gterm.toString()+" # ", vterm.toString());
 	if( (gterm.getKind() == vterm.getKind()) &&
	    (gterm.arity() == vterm.arity()) &&
	    gterm.arity()>0 ){
 	  for(int child=0; child < vterm.arity() ; child++){
 	    if (false == recSynMatch(gterm[child], vterm[child] , env)){
 	      TRACE("quant match", "match false", gterm[child].toString(), vterm[child].toString());
 	      return false;
 	    }
 	  }
 	  return true;
 	}
	else  return false;
      }
  }
}

*/

/*
void TheoryQuant::goodSynMatch(const Expr& e,
			       const std::vector<Expr> & boundVars,
			       std::vector<std::vector<Expr> >& instBinds,
			       std::vector<Expr>& instGterms,
			       const CDList<Expr>& allterms,
			       size_t tBegin){
  for (size_t i=tBegin; i<allterms.size(); i++)    {
    Expr gterm = allterms[i];
    if (0 == gterm.arity() )
      continue;
    TRACE("quant matching", gterm.toString(), "||", e.toString()) ;
    //    if( usefulInMatch(gterm) && possibleMatch(gterm,e))   {
    if(usefulInMatch(gterm))   {
      ExprMap<Expr> env;
      env.clear();
      bool found = recSynMatch(gterm,e,env);
      if(found){

	TRACE("quant matching found", " good:",gterm.toString()+" to " , e.toString());
	TRACE("quant matching found", " simplified good:",simplifyExpr(gterm).toString()+" to " , simplifyExpr(e).toString());
	std::vector<Expr> inst;

	DebugAssert((boundVars.size() == env.size()),"bound var size != env.size()");

	for(size_t i=0; i<boundVars.size(); i++) {
	  ExprMap<Expr>::iterator p = env.find(boundVars[i]);
	  DebugAssert((p!=env.end()),"bound var cannot be found");
	  inst.push_back(p->second);
	}
	instBinds.push_back(inst);
	instGterms.push_back(gterm);
      }
      else{
	TRACE("quant matching", "bad one",gterm.toString()+" to " , e.toString());
      }
    }
  }
}

*/
/*
void TheoryQuant::goodSynMatchNewTrig(const Trigger& trig,
				      const std::vector<Expr> & boundVars,
				      std::vector<std::vector<Expr> >& instBinds,
				      std::vector<Expr>& instGterms,
				      const CDList<Expr>& allterms,
				      size_t tBegin){
  for (size_t i=tBegin; i<allterms.size(); i++)    {
    Expr gterm (allterms[i]);
    //    TRACE("quant matching", gterm.toString(), "||", trig.getEx().toString()) ;
    if(usefulInMatch(gterm)) {
      ExprMap<Expr> env;
      env.clear();
      bool found = synMatchTopPred(gterm,trig,env);
      if(found){
	//TRACE("quant matching found", " top good:",gterm.toString()+" to " , trig.getEx().toString());
	std::vector<Expr> inst;
	inst.clear();
	DebugAssert((boundVars.size() <= env.size()),"bound var size != env.size()");

	for(size_t i=0; i<boundVars.size(); i++) {
	  ExprMap<Expr>::iterator p = env.find(boundVars[i]);
	  DebugAssert((p!=env.end()),"bound var cannot be found");
	  inst.push_back(p->second);
	}

	instBinds.push_back(inst);
	instGterms.push_back(gterm);
      }
      else{
	//	TRACE("quant matching", "bad one",gterm.toString()+" to ", trig.getEx().toString());
      }
    }
  }
}
*/

/*
bool TheoryQuant::hasGoodSynInstNewTrigOld(Trigger& trig,
					   std::vector<Expr> & boundVars,
					   std::vector<std::vector<Expr> >& instBinds,
					   std::vector<Expr>& instGterms,
					   const CDList<Expr>& allterms,
					   size_t tBegin){

  const std::set<Expr>& bvs = getBoundVars(trig.getEx());

  boundVars.clear();
  for(std::set<Expr>::const_iterator i=bvs.begin(),iend=bvs.end(); i!=iend; ++i)
    boundVars.push_back(*i);

  instBinds.clear();
  goodSynMatchNewTrig(trig, boundVars, instBinds, instGterms, allterms, tBegin);

  if (instBinds.size() > 0)
    return true;
  else
    return false;
}


bool TheoryQuant::hasGoodSynInstNewTrig(Trigger& trig,
					const std::vector<Expr>& boundVars,
					std::vector<std::vector<Expr> >& instBinds,
					std::vector<Expr>& instGterms,
					const CDList<Expr>& allterms,
					size_t tBegin){
//   boundVars=trig.getBVs();
//   const std::set<Expr>& bvs = getBoundVars(trig.getEx());

//   boundVars.clear();
//   for(std::set<Expr>::const_iterator i=bvs.begin(),iend=bvs.end(); i!=iend; ++i)
//     boundVars.push_back(*i);

  instBinds.clear();
  goodSynMatchNewTrig(trig, boundVars, instBinds, instGterms, allterms, tBegin);

  if (instBinds.size() > 0)
    return true;
  else
    return false;
}
*/
int TheoryQuant::loc_gterm(const std::vector<Expr>& border,
			   const Expr& vterm,
			   int pos){
  const std::vector<Expr>& order = d_mtrigs_bvorder[vterm];
  const Expr& var = order[pos];
  for(size_t i=0; i<border.size(); i++){
    if (border[i] == var) return i;
  }

  DebugAssert(false, "internal error in loc_germ");
  return -1;
}

/*
void  TheoryQuant::recSearchCover(const std::vector<Expr>& border,
				  const std::vector<Expr>& mtrigs,
				  int cur_depth,
				  std::vector<std::vector<Expr> >& instSet,
				  std::vector<Expr>& cur_inst
				  ){
  int max_dep = mtrigs.size();

  if(cur_depth >= max_dep) return;

  Expr cur_vterm = mtrigs[cur_depth]; //get the current vterm
  if(d_mtrigs_inst.count(cur_vterm) <=0) return;
  CDList<std::vector<Expr> >* gterm_list = d_mtrigs_inst[cur_vterm]; // get the list of ground term found for cur_vterm
  for(size_t i=0; i< gterm_list->size(); i++){
    const std::vector<Expr>& cur_gterm = (*gterm_list)[i];
    std::vector<Expr> new_inst(border.size()); //get a new inst array

    for(size_t j=0; j< border.size(); j++){
      new_inst[j]=cur_inst[j]; //copy to cur_int to new_inst
    }

    bool has_problem = false;//next, try to put the cur gterm into new_inst
    for(size_t j=0; j< cur_gterm.size(); j++){
      int cur_loc_gterm = loc_gterm(border, cur_vterm, j);

      if( null_expr == new_inst[cur_loc_gterm]){
	new_inst[cur_loc_gterm] = cur_gterm[j];
      }
      else if (new_inst[cur_loc_gterm] != cur_gterm[j]){
	has_problem = true;
	break;
      }

    }

    if (has_problem){
      continue;
    }

    bool finished = true;
    for(size_t j=0; j< border.size() ;j++){
      if(null_expr == new_inst[j]){
	finished = false;
	break;
      }
    }

    if(finished){
      std::vector<Expr> good_inst;
      for(size_t j=0; j<border.size(); j++){
	good_inst.push_back(new_inst[j]);
      }
      instSet.push_back(good_inst);
    }
    else{
      recSearchCover(border,
		     mtrigs,
		     cur_depth+1,
		     instSet,
		     new_inst);
    }
  }//end of for
}
*/
/*
void  TheoryQuant::searchCover(const Expr& thm,
			       const std::vector<Expr>& border,
			       std::vector<std::vector<Expr> >& instSet
			       ){
  std::vector<Expr> dumy(border.size()) ; //use dynamic array here
  for(size_t j=0; j< border.size() ;j++){
    dumy[j]=null_expr;
  }
  const std::vector<Expr>& mtrigs = d_multTriggers[thm];
  recSearchCover(border, mtrigs, 0, instSet, dumy);
}

*/
/*
bool TheoryQuant::hasGoodSynMultiInst(const Expr& thm,
				      std::vector<Expr> & boundVars,
				      std::vector<std::vector<Expr> >& instSet,
				      const CDList<Expr>& allterms,
				      size_t tBegin){

  const std::set<Expr>& bvs = getBoundVars(thm);

  boundVars.clear();
  for(std::set<Expr>::const_iterator i=bvs.begin(),iend=bvs.end(); i!=iend; ++i)
    boundVars.push_back(*i);

  instSet.clear();

  bool new_match = false;
  //assumption: every trig is different
  //this is not true later, fix this asap
  const std::vector<Expr>& mtrigs = d_multTriggers[thm];

  for(std::vector<Expr>::const_iterator i= mtrigs.begin(), iend = mtrigs.end(); i != iend; i++){

    if(d_mtrigs_bvorder[*i].empty()){ //setup an order
      const std::set<Expr>& trig_bvs = getBoundVars(*i);
      for(std::set<Expr>::const_iterator j= trig_bvs.begin(), jend = trig_bvs.end();
	  j != jend;
	  j++){
	d_mtrigs_bvorder[*i].push_back(*j);
      }
    }

    const std::vector<Expr>& trig_bvorder = d_mtrigs_bvorder[*i];
    //    std::set<std::vector<Expr> > trig_insts;
    std::vector<std::vector<Expr> > trig_insts;
    trig_insts.clear();

    std::vector<Expr> gtms;
    goodSynMatch(*i, trig_bvorder, trig_insts, gtms, allterms, tBegin);

    if (trig_insts.size() > 0){
      new_match=true;
      if(d_mtrigs_inst.count(*i) <= 0){
	d_mtrigs_inst[*i] = new(true) CDList<std::vector<Expr> > (theoryCore()->getCM()->getCurrentContext());
      }
      for(std::vector<std::vector<Expr> >::const_iterator j = trig_insts.begin(), jend = trig_insts.end();
	  j != jend;
	  j++){

	d_mtrigs_inst[*i]->push_back(*j);
	for(std::vector<Expr>::const_iterator k = j->begin(), kend = j->end();
	    k != kend;
	    k++){
	}
      }
    }
  } // end of for

  for(std::vector<Expr>::const_iterator i= mtrigs.begin(), iend = mtrigs.end(); i != iend; i++){
    if (d_mtrigs_inst.count(*i) <=0 ) continue;
    for(CDList<std::vector<Expr> >::const_iterator j = d_mtrigs_inst[*i]->begin(),
	  jend = d_mtrigs_inst[*i]->end();
	  j != jend;
	  j++){

      for(std::vector<Expr>::const_iterator k = j->begin(), kend = j->end();
	  k != kend;
	  k++){
      }
    }
  }
  {//code for search a cover
    if(new_match){
      searchCover(thm, boundVars, instSet);
    }
  }

  if(instSet.size() > 0 ) {
    return true;
  }
  else {
    return false;
  }

}

*/
/*

bool inStrCache(std::set<std::string> cache, std::string str){
  return (cache.find(str) != cache.end());
}
*/
/*
bool TheoryQuant::hasGoodSemInst(const Expr& e,
				 std::vector<Expr> & boundVars,
				 std::set<std::vector<Expr> >& instSet,
				 size_t tBegin){
  return false;
}

*/
/*
void genPartInstSetThm(const std::vector<Expr>&  bVarsThm,
		       std::vector<Expr>& bVarsTerm,
		       const std::vector<std::vector<Expr> >& termInst,
		       std::vector<std::vector<Expr> >& instSetThm){
  ExprMap<bool> bVmap;

  for(size_t i=0; i< bVarsThm.size(); ++i)    {
    bVmap[bVarsThm[i]]=true;
  }

  std::vector<Expr> tempBVterm;
  std::vector<int> locTerm;

  for (size_t j=0; j<bVarsTerm.size(); j++){
    if (bVmap.count(bVarsTerm[j]) > 0){
      locTerm.push_back(1);
      tempBVterm.push_back(bVarsTerm[j]);
    }
    else{
      locTerm.push_back(0);
    }
  }

  DebugAssert(locTerm.size() == bVarsTerm.size(), "locTerm.size !- bVarsTerm.size()");

  for(std::vector<std::vector<Expr> >::const_iterator i=termInst.begin(),
	iend=termInst.end();i!=iend; i++)  {
    std::vector<Expr> buf;
    buf.clear();
    for(size_t j=0; j< bVarsTerm.size(); ++j){
      if(locTerm[j])
	buf.push_back((*i)[j]);
    }
    instSetThm.push_back(buf);
  }
  bVarsTerm=tempBVterm;
}
*/

/*
void genInstSetThm(const std::vector<Expr>& bVarsThm,
		   const std::vector<Expr>& bVarsTerm,
		   const std::vector<std::vector<Expr> >& termInst,
		   std::vector<std::vector<Expr> >& instSetThm){

  std::vector<int> bVmap;

  for(size_t i=0; i< bVarsThm.size(); ++i)    {
    bVmap.push_back(-1);
    for (size_t j=0; j<bVarsTerm.size(); j++){
      if (bVarsThm[i] == bVarsTerm[j]){
	DebugAssert(bVmap[i] == -1, "bVmap[1] != -1");
	bVmap[i]=j;
      }
    }
  }

  for(size_t i=0; i< bVarsThm.size(); ++i)
    if( -1 == bVmap[i])  {
      return;
    }

  for(std::vector<std::vector<Expr> >::const_iterator i=termInst.begin(),
	iend=termInst.end();i!=iend; i++)  {
    std::vector<Expr> buf;
    buf.clear();
    for(size_t j=0; j< bVarsThm.size(); ++j){
      buf.push_back((*i)[bVmap[j]]);
    }
    instSetThm.push_back(buf);
  }
}
*/

/*
void TheoryQuant::synInst(const Theorem & univ, const CDList<Expr>& allterms, size_t tBegin ){
  if(d_useFullTrig){
    synFullInst(univ, allterms, tBegin);
  }

  if(d_useMultTrig){
    synMultInst(univ, allterms, tBegin);
  }

  if(d_usePartTrig){
    synPartInst(univ, allterms, tBegin);
  }
}
*/

inline bool TheoryQuant::transFound(const Expr& comb){
  return (d_trans_found.count(comb) > 0);
}

inline void TheoryQuant::setTransFound(const Expr& comb){
  d_trans_found[comb] = true;
}

inline bool TheoryQuant::trans2Found(const Expr& comb){
  return (d_trans2_found.count(comb) > 0);
}

inline void TheoryQuant::setTrans2Found(const Expr& comb){
  d_trans2_found[comb] = true;
}


inline CDList<Expr> & TheoryQuant::backList(const Expr& ex){
  if(d_trans_back.count(ex)>0){
    return *d_trans_back[ex];
  }
  else{
    return null_cdlist;
  }
}

inline CDList<Expr> & TheoryQuant::forwList(const Expr& ex){
  if(d_trans_forw.count(ex)>0){
    return *d_trans_forw[ex];
  }
  else{
    return null_cdlist;
  }
}

inline void  TheoryQuant::pushBackList(const Expr& node, Expr ex){
  if(d_trans_back.count(node)>0){
    d_trans_back[node]->push_back(ex);
  }
  else{
    d_trans_back[node] = new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext());
    d_trans_back[node]->push_back(ex);
  }
}

inline void  TheoryQuant::pushForwList(const Expr& node, Expr ex){
  if(d_trans_forw.count(node)>0){
    d_trans_forw[node]->push_back(ex);
  }
  else{
    d_trans_forw[node] = new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext());
    d_trans_forw[node]->push_back(ex);
  }
}

/*
void TheoryQuant::synFullInst(const Theorem & univ, const CDList<Expr>& allterms, size_t tBegin ){

  const Expr& quantExpr = univ.getExpr();
  //  const std::vector<Expr>& bVarsThm = quantExpr.getVars();
  std::vector<Expr> bVarsThm = quantExpr.getVars();

  TRACE("quant inst", "try full inst with:|", quantExpr.toString() , " ");

  std::vector<std::vector<Expr> > instBindsThm; //set of instantiations for the thm,
  std::vector<std::vector<Expr> > instBindsTerm; //bindings, in the order of bVarsTrig
  std::vector<Expr > instGterms; //instGterms are gterms matched, instBindsTerm and instGterms must have the same length
  std::vector<Expr> bVarsTrig;

  if(*d_useTrigNew){
    std::vector<Trigger>& new_trigs=d_fullTrigs[quantExpr];
    for( size_t i= 0; i<new_trigs.size(); i++)  {
      Trigger& trig = new_trigs[i];
      //      if( 0 != trig.getPri()) continue;
      TRACE("quant inst","try new full trigger:|", trig.getEx().toString(),"");

      instBindsTerm.clear();
      bVarsTrig.clear();
      instBindsThm.clear();
      instGterms.clear();

      {//code for trans2
	if(trig.hasTr2()){
	  //if(hasGoodSynInstNewTrig(trig, bVarsTrig, instBindsTerm, instGterms, allterms, tBegin)) {
	  if(hasGoodSynInstNewTrig(trig, trig.getBVs(), instBindsTerm, instGterms, allterms, tBegin)) {
	    for(size_t j=0; j<instBindsTerm.size(); j++){
	      DebugAssert(2 == instBindsTerm[j].size(), "internal error in trans2");

	      Expr& gterm = instGterms[j];

	      if(simplifyExpr(instBindsTerm[j][0]) != simplifyExpr(instBindsTerm[j][1])){
		Expr comb = Expr(RAW_LIST,instBindsTerm[j][0],instBindsTerm[j][1]);
		if(!trans2Found(comb)){
		  setTrans2Found(comb);

		  TRACE("quant trans","new trans2: ", vectorExpr2string(instBindsTerm[j]), "");

		  Expr comb_rev = Expr(RAW_LIST,instBindsTerm[j][1],instBindsTerm[j][0]);
		  if(trans2Found(comb_rev)){
		    Expr sr(instBindsTerm[j][0]);
		    Expr dt(instBindsTerm[j][1]);

		    vector<Expr> bind;
		    bind.clear();
		    bind.push_back(sr);
		    bind.push_back(dt);

		    enqueueInst(univ, bind, gterm);
		    TRACE("quant inst", "trans pred rule2 ", univ.toString(), " | with bind: "+vectorExpr2string(bind));  		    TRACE("quant trans", "trans2 ", vectorExpr2string(bind), "");
		  }
		}
	      }
	    }
	  }
	  return;
	}
      }

      {//code for trans pred
	if(trig.hasTr()){
	  //	  if(hasGoodSynInstNewTrig(trig, bVarsTrig, instBindsTerm, instGterms, allterms, tBegin)) {
	  if(hasGoodSynInstNewTrig(trig, trig.getBVs(), instBindsTerm, instGterms, allterms, tBegin)) {
	    for(size_t j=0; j<instBindsTerm.size(); j++){
	      DebugAssert(2 == instBindsTerm[j].size(), "internal error in trans");

	      Expr& gterm = instGterms[j];

	      if(simplifyExpr(instBindsTerm[j][0]) != simplifyExpr(instBindsTerm[j][1])){

		Expr comb = Expr(RAW_LIST,instBindsTerm[j][0],instBindsTerm[j][1]);

		if(!transFound(comb)){
		  setTransFound(comb);

		  TRACE("quant trans","new: ", vectorExpr2string(instBindsTerm[j]), "");

		  Expr sr(instBindsTerm[j][0]);
		  Expr dt(instBindsTerm[j][1]);

		  const CDList<Expr>& dtForw = forwList(dt);
		  const CDList<Expr>& srBack = backList(sr);

		  for(size_t k=0; k<dtForw.size(); k++){
		    vector<Expr> bind;
		    bind.clear();
		    bind.push_back(sr);
		    bind.push_back(dt);
		    bind.push_back(dtForw[k]);

		    enqueueInst(univ, bind, gterm);

		    TRACE("quant inst", "trans pred rule", univ.toString(), " | with bind: "+vectorExpr2string(bind));
		    TRACE("quant trans", "trans res forw: ", vectorExpr2string(bind), "");
		  }

		  for(size_t k=0; k<srBack.size(); k++){
		    vector<Expr> bind;
		    bind.clear();
		    bind.push_back(srBack[k]);
		    bind.push_back(sr);
		    bind.push_back(dt);

		    enqueueInst(univ, bind, gterm);
		    TRACE("quant inst", "trans pred rule ", univ.toString(), " | with bind: "+vectorExpr2string(bind));
  		    TRACE("quant trans", "trans res back: ", vectorExpr2string(bind), "");
		  }

		  pushForwList(sr,dt);
		  pushBackList(dt,sr);
		}
	      }
	    }
	  }
	  return;
	}
      }

      bool univsHasMoreBVs ;

      univsHasMoreBVs = (d_hasMoreBVs.count(quantExpr) > 0);

      //      if ( !d_allout || !trig.isSimp() || univsHasMoreBVs || *d_useLazyInst){
      //      if ( !d_allout || !trig.isSimp() || univsHasMoreBVs || true){
      if  ( !d_allout || !trig.isSuperSimp() || univsHasMoreBVs ){
      //      if ( !d_allout || !trig.isSimp() || univsHasMoreBVs ){
      */
	/*
	if(hasGoodSynInstNewTrigOld(trig, bVarsTrig, instBindsTerm, instGterms, allterms, tBegin)) {
	  genInstSetThm(bVarsThm, bVarsTrig, instBindsTerm, instBindsThm);
	  for (size_t j = 0; j<instBindsTerm.size(); j++){
 	    const Expr& gterm = instGterms[j];
 	    const std::vector<Expr>& binds = instBindsThm[j];
 	    enqueueInst(univ, trig, binds, gterm);
 	    TRACE("quant inst", "insert full inst", univ.toString(), " | with bind: "+vectorExpr2string(binds));
 	  }
 	}
	*/
/*
	bVarsTrig=trig.getBVs();//vVarsTrig is used later, do not forget this.
 	if(hasGoodSynInstNewTrig(trig, bVarsThm, instBindsTerm, instGterms, allterms, tBegin)) {
  	  for (size_t j = 0; j<instBindsTerm.size(); j++){
  	    const Expr& gterm = instGterms[j];
  	    const std::vector<Expr>& binds = instBindsTerm[j];

  	    enqueueInst(univ, trig, binds, gterm);

  	    TRACE("quant inst", "insert full inst", univ.toString(), " | with bind: "+vectorExpr2string(binds));
  	  }
  	}

      }

      //      if(!d_allout || *d_useLazyInst){
      if(!d_allout){
	if(trig.hasRW() ){

	  if(1 == bVarsTrig.size()){
	    std::vector<Expr> tp = d_arrayIndic[trig.getHead()];
	    for(size_t i=0; i<tp.size(); i++){
	      std::vector<Expr> tp = d_arrayIndic[trig.getHead()];

	      Expr index = tp[i];
	      std::vector<Expr> temp;
	      temp.clear();
	      temp.push_back(index);

	      enqueueInst(univ, temp, index);
	      TRACE("quant inst", "read write rule", univ.toString(), " | with bind: "+vectorExpr2string(temp));
	    }
	  }
	  else{
	  }
	}
      }
    }//end for each trigger
  }
}
*/

void TheoryQuant::arrayHeuristic(const Trigger& trig, size_t univ_id){
  return;
  std::vector<Expr> tp = d_arrayIndic[trig.head];
  for(size_t i=0; i<tp.size(); i++){
    const Expr& index = tp[i];
    std::vector<Expr> temp;
    temp.push_back(index);
    enqueueInst(univ_id, temp, index);
    //	  TRACE("quant inst", "read write rule", univ.toString(), " | with bind: "+vectorExpr2string(temp));
  }
}

void inline TheoryQuant::iterFWList(const Expr& sr, const Expr& dt, size_t univ_id, const Expr& gterm){
  const CDList<Expr>& dtForw = forwList(dt);
  for(size_t k=0; k<dtForw.size(); k++){
    vector<Expr> tri_bind;
    tri_bind.push_back(sr);
    tri_bind.push_back(dt);
    tri_bind.push_back(dtForw[k]);
    enqueueInst(univ_id, tri_bind, gterm);
  }
}

void inline TheoryQuant::iterBKList(const Expr& sr, const Expr& dt, size_t univ_id, const Expr& gterm){
  const CDList<Expr>& srBack = backList(sr);
  for(size_t k=0; k<srBack.size(); k++){
    vector<Expr> tri_bind;
    tri_bind.push_back(srBack[k]);
    tri_bind.push_back(sr);
    tri_bind.push_back(dt);
    enqueueInst(univ_id, tri_bind, gterm);
  }
}



Expr TheoryQuant::simpRAWList(const Expr& org){
  vector<Expr> result;
  if(null_expr == org) return null_expr;
  for(int i =0 ; i < org.arity(); i++){
    result.push_back(simplifyExpr(org[i]));
  }
  return Expr(RAW_LIST,result);
}


void TheoryQuant::synNewInst(size_t univ_id, const vector<Expr>& bind, const Expr& gterm, const Trigger& trig ){
  if(trig.isMulti){
    const multTrigsInfo& mtriginfo = d_all_multTrigsInfo[trig.multiId];

    vector<Expr> actual_bind;
    for(size_t i=0, iend=bind.size(); i<iend; i++){
      if(null_expr != bind[i]){
	actual_bind.push_back(bind[i]);
      }
    }

    Expr actual_bind_expr = Expr(RAW_LIST, actual_bind);

    size_t index = trig.multiIndex;

    // first,  test if we have see this binding before
    CDMap<Expr,bool> * oldBindMap = mtriginfo.var_binds_found[index];
    CDMap<Expr,bool>::iterator cur_iter = oldBindMap->find(actual_bind_expr);

    if (oldBindMap->end() != cur_iter){
      return;
    }
    else{
      (*oldBindMap)[actual_bind_expr] = true;
    }

    //for now, we only have one set of commom positions, so it must be 0
    //this is not true later.
    const vector<size_t>& comm_pos = mtriginfo.common_pos[0];
    size_t comm_pos_size = comm_pos.size();

    Expr comm_expr;
    vector<Expr> comm_expr_vec;
    for(size_t i = 0; i < comm_pos_size; i++){
      comm_expr_vec.push_back(bind[comm_pos[i]]);
    }

    if(0 == comm_pos_size){
      comm_expr = null_expr;
    }
    else{
      comm_expr = Expr(RAW_LIST, comm_expr_vec);
    }

    Expr uncomm_expr;
    vector<Expr> uncomm_expr_vec;

    const vector<size_t>& uncomm_pos = mtriginfo.var_pos[index];
    size_t uncomm_pos_size = uncomm_pos.size();
    for(size_t i = 0; i< uncomm_pos_size; i++){
      uncomm_expr_vec.push_back(bind[uncomm_pos[i]]);
    }
    if(0 == uncomm_pos_size){
      uncomm_expr = null_expr;
    }
    else{
      uncomm_expr = Expr(RAW_LIST, uncomm_expr_vec);
    }

    CDList<Expr>* add_into_list ;
    CDList<Expr>* iter_list;
    ExprMap<CDList<Expr>* >::iterator add_into_iter;
    ExprMap<CDList<Expr>* >::iterator iter_iter;

    size_t other_index = 0;
    if(0 == index){
      other_index =1;
    }
    else if (1 == index){
      other_index = 0;
    }
    else{
      FatalAssert(false, "Sorry, only two vterms in a multi-trigger.");
    }

    add_into_iter = mtriginfo.uncomm_list[index]->find(comm_expr);

    if(mtriginfo.uncomm_list[index]->end() == add_into_iter){
      add_into_list = new (true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext());
      (*mtriginfo.uncomm_list[index])[comm_expr] = add_into_list;
    }
    else{
      add_into_list = add_into_iter->second;
    }

    add_into_list->push_back(uncomm_expr);


    Expr simpCommExpr = simpRAWList(comm_expr);
//     if(simpCommExpr != comm_expr) {
//       cout<<"common and simplified comm expr" << comm_expr << " I " << simpCommExpr << endl;
//     }

    { //
      ExprMap<CDList<Expr>* >* otherMap = mtriginfo.uncomm_list[other_index];

      //      iter_iter = mtriginfo.uncomm_list[other_index]->find(comm_expr);
      ExprMap<CDList<Expr>* >::iterator otherMapBegin = otherMap->begin(), otherMapEnd = otherMap->end();
      for(ExprMap<CDList<Expr>* >::iterator otherMapIter = otherMapBegin; otherMapIter != otherMapEnd; otherMapIter++){

	Expr otherCommonExpr = simpRAWList(otherMapIter->first);
	if(simpCommExpr != otherCommonExpr) continue;
	//	iter_iter = otherMap->find(comm_expr);
	//	if(mtriginfo.uncomm_list[other_index]->end() == iter_iter){
	//	  return;
	//	}
	//	else{
	//	  iter_list = iter_iter->second;
	//	}

	if(comm_expr != otherMapIter->first) {
	}

	iter_list = otherMapIter->second;
	const vector<size_t>& uncomm_iter_pos = mtriginfo.var_pos[other_index];
	size_t uncomm_iter_pos_size = uncomm_iter_pos.size();

	for(size_t i =0, iend = iter_list->size(); i<iend; i++){
	  const Expr& cur_iter_expr = (*iter_list)[i];
	  vector<Expr> new_bind(bind);
	  for(size_t j=0; j<uncomm_iter_pos_size; j++){
	    new_bind[uncomm_iter_pos[j]] = cur_iter_expr[j];
	  }
	  enqueueInst(univ_id, new_bind, gterm);
	}
      }
    }
    return;
  }

  {//code for trans2
    if(trig.hasT2){
      vector<Expr> actual_bind;
      for(size_t i=0; i<bind.size(); i++){
	if(bind[i] != null_expr){
	  actual_bind.push_back(bind[i]);
	}
      }
      if(actual_bind.size() != 2){
	//	cout<<"2 != bind.size()" <<endl;
      }

      Expr acb1 = simplifyExpr(actual_bind[0]);
      Expr acb2 = simplifyExpr(actual_bind[1]);
      actual_bind[0]=acb1;
      actual_bind[1]=acb2;
      if(acb1 != acb2){
	Expr comb = Expr(RAW_LIST,acb1, acb2);
	if(!trans2Found(comb)){
	  setTrans2Found(comb);
	  Expr comb_rev = Expr(RAW_LIST,acb2, acb1);
	  if(trans2Found(comb_rev)){
	    enqueueInst(univ_id, actual_bind, gterm);
	  }
	}
      }
    return;
    }
  }

  {//code for trans pred
    if(trig.hasTrans){
      vector<Expr> actual_bind;
      for(size_t i=0; i<bind.size(); i++){
	if(bind[i] != null_expr){
	  actual_bind.push_back(simplifyExpr(bind[i]));
	}
      }
      if(simplifyExpr(actual_bind[0]) != simplifyExpr(actual_bind[1])){
	Expr comb = Expr(RAW_LIST,actual_bind[0], actual_bind[1]);

	if(!transFound(comb)){
	  setTransFound(comb);

	  Expr sr(actual_bind[0]);
	  Expr dt(actual_bind[1]);

	  iterFWList(sr, dt, univ_id, gterm);
	  if(*d_useNewEqu){
	    Expr cur_next = dt.getEqNext().getRHS();
	    while (cur_next != dt) {
	      iterFWList(sr, cur_next, univ_id, gterm);
	      cur_next = cur_next.getEqNext().getRHS();
	    }
	  }

	  iterBKList(sr, dt, univ_id, gterm);
	  if(*d_useNewEqu){
	    Expr cur_next = sr.getEqNext().getRHS();
	    while (cur_next != sr) {
	      iterBKList(cur_next, dt, univ_id, gterm);
	      cur_next = cur_next.getEqNext().getRHS();
	    }
	  }
	  pushForwList(sr,dt);
	  pushBackList(dt,sr);
	}
      }
      return;
    }
  } //end of code for trans

  //  cout<<"before enqueueisnt"<<endl;
  enqueueInst(univ_id, bind, gterm);
  //      if(!d_allout || *d_useLazyInst){

}


/*

void TheoryQuant::synNewInst(size_t univ_id, const vector<Expr>& bind, const Expr& gterm, const Trigger& trig ){
  //  cout<<"synnewinst "<<univ_id<<endl;
  {//code for trans2
    if(trig.hasT2){
      vector<Expr> actual_bind;
      for(size_t i=0; i<bind.size(); i++){
	if(bind[i] != null_expr){
	  actual_bind.push_back(bind[i]);
	}
      }
      if(actual_bind.size() != 2){
	cout<<"2 != bind.size()" <<endl;
      }
      if(simplifyExpr(actual_bind[0]) != simplifyExpr(actual_bind[1])){
	Expr comb = Expr(RAW_LIST,actual_bind[0], actual_bind[1]);
	if(!trans2Found(comb)){
	  setTrans2Found(comb);
	  Expr comb_rev = Expr(RAW_LIST,actual_bind[1], actual_bind[0]);
	  if(trans2Found(comb_rev)){
	    enqueueInst(univ_id, actual_bind, gterm);
	  }
	}
      }
    return;
    }
  }

  {//code for trans pred
    if(trig.hasTrans){
      vector<Expr> actual_bind;
      for(size_t i=0; i<bind.size(); i++){
	if(bind[i] != null_expr){
	  actual_bind.push_back(bind[i]);
	}
      }
      if(simplifyExpr(actual_bind[0]) != simplifyExpr(actual_bind[1])){
	Expr comb = Expr(RAW_LIST,actual_bind[0], actual_bind[1]);

	if(!transFound(comb)){
	  setTransFound(comb);

	  Expr sr(actual_bind[0]);
	  Expr dt(actual_bind[1]);

	  const CDList<Expr>& dtForw = forwList(dt);
	  const CDList<Expr>& srBack = backList(sr);

	  for(size_t k=0; k<dtForw.size(); k++){
	    vector<Expr> tri_bind;
	    tri_bind.push_back(sr);
	    tri_bind.push_back(dt);
	    tri_bind.push_back(dtForw[k]);

	    enqueueInst(univ_id, tri_bind, gterm);
	  }

	  for(size_t k=0; k<srBack.size(); k++){
	    vector<Expr> tri_bind;
	    tri_bind.push_back(srBack[k]);
	    tri_bind.push_back(sr);
	    tri_bind.push_back(dt);

	    enqueueInst(univ_id, tri_bind, gterm);
	    //	    TRACE("quant inst", "trans pred rule ", univ.toString(), " | with bind: "+vectorExpr2string(bind));
	    //	    TRACE("quant trans", "trans res back: ", vectorExpr2string(bind), "");
	  }

	  pushForwList(sr,dt);
	  pushBackList(dt,sr);
	}
      }
      return;
    }
  }
  //  cout<<"before enqueueisnt"<<endl;
  enqueueInst(univ_id, bind, gterm);

  //      if(!d_allout || *d_useLazyInst){
  if(!d_allout){
    if(trig.hasRWOp ){

      if(1 == trig.bvs.size()){
	std::vector<Expr> tp = d_arrayIndic[trig.head];
	for(size_t i=0; i<tp.size(); i++){
	  std::vector<Expr> tp = d_arrayIndic[trig.head];

	  Expr index = tp[i];
	  std::vector<Expr> temp;
	  temp.clear();
	  temp.push_back(index);

	  enqueueInst(univ_id, temp, index);
	  //	  TRACE("quant inst", "read write rule", univ.toString(), " | with bind: "+vectorExpr2string(temp));
	}
      }
      else{
      }
    }
  }
}
*/

/*
void TheoryQuant::synMultInst(const Theorem & univ, const CDList<Expr>& allterms, size_t tBegin ){

  const Expr& quantExpr = univ.getExpr();

  if(d_multTriggers[quantExpr].size() <= 0) return ;

  TRACE("quant inst", "try muli with:|", quantExpr.toString() , " ");
  const std::vector<Expr>& bVarsThm = quantExpr.getVars();

  std::vector<std::vector<Expr> > instSetThm; //set of instantiations for the thm
  std::vector<std::vector<Expr> > termInst; //terminst are bindings, in the order of bVarsTrig
  std::vector<Expr> bVarsTrig;


  if(hasGoodSynMultiInst(quantExpr, bVarsTrig, termInst, allterms, tBegin)) {
    genInstSetThm(bVarsThm, bVarsTrig, termInst, instSetThm);
  }
  {
    for(std::vector<std::vector<Expr> >::iterator i=instSetThm.begin(), iend=instSetThm.end(); i!=iend; ++i) {
      enqueueInst(univ, *i, null_expr);//fix the null_expr here asap
      TRACE("quant inst", "insert mult inst", univ.toString(), " | with bind: "+vectorExpr2string(*i));
    }
  }

}
*/
/*
void TheoryQuant::synPartInst(const Theorem & univ, const CDList<Expr>& allterms,  size_t tBegin ){

  const Expr& quantExpr = univ.getExpr();
  TRACE("quant inst", "try part with ", quantExpr.toString() , " ");

  const std::vector<Trigger>& triggers = d_partTrigs[quantExpr];

  std::vector<std::vector<Expr> > instSetThm; //set of instantiations for the thm
  std::vector<std::vector<Expr> > termInst; //terminst are bindings, in the order of bVarsTrig
  std::vector<Expr> bVarsTrig;
  std::vector<Expr> instGterms;

  for( std::vector<Trigger>::const_iterator i= triggers.begin(), iend=triggers.end();i!=iend;++i)  {

    Trigger trig = *i;
    TRACE("quant inst","handle part trigger", trig.getEx().toString(),"");
    termInst.clear();
    bVarsTrig.clear();
    instSetThm.clear();
    //    if(hasGoodSynInstNewTrig(trig, bVarsTrig, termInst, instGterms,allterms, tBegin)) {
    if(hasGoodSynInstNewTrig(trig, trig.getBVs(), termInst, instGterms,allterms, tBegin)) {
      TRACE("quant syninst", "has good ", termInst.size(),"");
      TRACE("quant syninst", "after good ",instSetThm.size(), "");

      Theorem newUniv = d_rules->adjustVarUniv(univ, trig.getBVs());

      TRACE("quant syninst", " new univ:" ,newUniv.toString(),"");
      {
	for(size_t i = 0; i< termInst.size(); i++){
	  const std::vector<Expr>& binds = termInst[i];
	  const Expr& gterm = instGterms[i];
	  enqueueInst(newUniv, binds, gterm);
	  TRACE("quant yeting inst", "instantiating =========", "" , "");
	  TRACE("quant yeting inst", "instantiating", newUniv.getExpr().toString(), " | with bind: "+vectorExpr2string(binds));
	  TRACE("quant yeting inst", "instantiating org ", univ.getExpr().toString(), " | with gterm "+gterm.toString());
	}
      }
    }
  }
}

*/
/*
void TheoryQuant::semInst(const Theorem & univ, size_t tBegin){
}
*/


void TheoryQuant::checkSat(bool fullEffort){

  if(*d_translate) return;
  if(d_rawUnivs.size() <=0 ) return;
  if (d_maxILReached) {
    //    cout<<"return bc max il "<<endl;
    return;
  }
  else{
  }

  DebugAssert(d_univsQueue.size() == 0, "something left in d_univsQueue");
  DebugAssert(d_simplifiedThmQueue.size() == 0, "something left in d_univsQueue");

  if( false ) {
  //  if( false || true) {

    for(size_t eqs_index = d_lastEqsUpdatePos; eqs_index < d_eqsUpdate.size();  eqs_index++){

      Theorem eqThm = d_eqsUpdate[eqs_index];
      //      const Expr& leftTerm = eqThm.getLHS();
      const Expr& rightTerm = eqThm.getRHS();

      std::vector<multTrigsInfo> d_all_multTrigsInfo;
      //      cout<< " size " << d_all_multTrigsInfo.size() << endl;
      int numUsefulMultTriger = 0;
      for(size_t i = 0; i < d_all_multTrigsInfo.size(); i++){
	multTrigsInfo& curMultiTrigger =  d_all_multTrigsInfo[i];
	if(curMultiTrigger.uncomm_list.size() != 2 ){
	  FatalAssert(false, "error in ");
	}
	ExprMap<CDList<Expr>* >* uncommonMapOne = curMultiTrigger.uncomm_list[0];
	ExprMap<CDList<Expr>* >* uncommonMapTwo = curMultiTrigger.uncomm_list[1];

	if(uncommonMapOne->size() != 0 || uncommonMapTwo->size() != 0 ){
	  numUsefulMultTriger++;
	}

	//	continue;

	if(uncommonMapOne->size() == 0 ) {
	  continue;
	}

	//why uncommonMapOne is empty but uncommonMapTwo is not?, let me figure this out.


	ExprMap<CDList<Expr>* >::iterator iterOneBegin(uncommonMapOne->begin()), iterOneEnd(uncommonMapOne->end());

	//cout<<"left and right " << leftTerm << " $ " << rightTerm <<endl;
	//	cout<<"------------ left and right ---------" << leftTerm << " $ " << rightTerm <<endl;

	vector<pair<Expr, CDList<Expr>* > > oneFoundTerms;
	for(ExprMap<CDList<Expr>* >::iterator iterOne=iterOneBegin; iterOne != iterOneEnd; iterOne++){

	  if(simplifyExpr((iterOne->first)[0]) == simplifyExpr(rightTerm)){ //for test only for trans
	    //	    cout<<"found one " << iterOne->first << endl;
	    //	    oneFoundTerms.push_back(iterOne->second);
	    oneFoundTerms.push_back(*iterOne);
	  }
	}

	ExprMap<CDList<Expr>* >::iterator iterTwoBegin(uncommonMapTwo->begin()), iterTwoEnd(uncommonMapTwo->end());
	//	vector<CDList<Expr>* > twoFoundTerms;
	vector<pair<Expr, CDList<Expr>* > >twoFoundTerms;
	for(ExprMap<CDList<Expr>* >::iterator iterTwo = iterTwoBegin; iterTwo != iterTwoEnd; iterTwo++){
	  if(simplifyExpr((iterTwo->first)[0]) == simplifyExpr(rightTerm)){
	    //	    cout<<"found two " << iterTwo->first << endl;
	    //	    twoFoundTerms.push_back(iterTwo->second);
	    twoFoundTerms.push_back(*iterTwo);
	  }
	}
	{
	  for(size_t i= 0 ; i< oneFoundTerms.size(); i++){
	    for(size_t j= 0 ; j< twoFoundTerms.size(); j++){
	      pair<Expr, CDList<Expr>* > pairOne = oneFoundTerms[i];
	      pair<Expr, CDList<Expr>* > pairTwo = twoFoundTerms[j];
	      if(pairOne.first == pairTwo.first) continue;
	      //	      cout<<"pairone.first " << pairOne.first << endl;
	      //	      cout<<"pairTwo.first " << pairTwo.first << endl;
	      CDList<Expr>* oneExprList = pairOne.second;
	      CDList<Expr>* twoExprList = pairTwo.second;
              //	      cout<<"one size" << oneExprList->size() << endl;
	      for(size_t oneIter = 0; oneIter < oneExprList->size(); oneIter++){
		//		cout<<"two size" << twoExprList->size() << endl;
		for(size_t twoIter = 0; twoIter < twoExprList->size(); twoIter++){
		  Expr gterm1 = (*oneExprList)[oneIter][0];
		  Expr gterm2 = (*twoExprList)[twoIter][0];
		  //		  cout<<"one and two " << oneIter << " # " << twoIter << endl;
		  //		  cout<<"one and two " << gterm1 << " # " << gterm2 << endl;
		  vector<Expr> bind ;
		  bind.push_back(gterm1);
		  bind.push_back(rightTerm);
		  bind.push_back(gterm2);
		  size_t univID = curMultiTrigger.univ_id;

		  if(d_univs[univID] != curMultiTrigger.univThm) {
		    //		    cout << "errror in debuging:" << endl;
                    //		    cout << d_univs[univID] << endl;
                    //		    cout << curMultiTrigger.univThm << endl;
		    exit(3);
		  }

		  enqueueInst(curMultiTrigger.univ_id, bind, rightTerm);
		  //		  cout << "enqueued 1" <<  vectorExpr2string(bind) <<endl;

 		  bind.clear();
 		  bind.push_back(gterm2);
 		  bind.push_back(rightTerm);
 		  bind.push_back(gterm1);
 		  enqueueInst(curMultiTrigger.univ_id, bind, rightTerm);
		  //		  cout << "enqueued 3" <<  vectorExpr2string(bind) <<endl;

		}
	      }
	    }
	  }
	}//end of add founded new matchings
      }
      //      cout << "useful multriggers " << numUsefulMultTriger << endl;
    }
  }

  sendInstNew();
  /*
  {//to test update eqs list
    //    cout<<"# equs in checksat "<<endl;

    cout<<"---------in checksat ----------------" << endl;
    for(size_t eqs_index = d_lastEqsUpdatePos; eqs_index < d_eqsUpdate.size();  eqs_index++){

      Theorem t = d_eqsUpdate[eqs_index];
      const Expr& leftTerm = t.getLHS();
      NotifyList* leftUpList = leftTerm.getNotify();
      cout<<"left term is " << leftTerm << " || " << simplifyExpr(leftTerm) << endl;

      if(NULL == leftUpList) continue;


      cout<<"the left notify list" <<endl;
      NotifyList& l = *leftUpList;
      for(size_t i=0,iend=l.size(); i<iend; ++i) {
	cout << "[" << l.getTheory(i)->getName() << ", " << l.getExpr(i) << "] " << l.getExpr(i).getSig().isNull() << endl;
      }

      const Expr& rightTerm = t.getRHS();
      cout<<"right term is " << rightTerm << endl;
      NotifyList* rightUpList = rightTerm.getNotify();
      if(NULL == rightUpList) continue;

      cout<<"the right notify list" << endl;

      NotifyList& ll = *rightUpList;
      for(size_t i=0,iend=ll.size(); i<iend; ++i) {
	cout << "[" << ll.getTheory(i)->getName() << ", " << ll.getExpr(i) << "] " << ll.getExpr(i).getSig().isNull() << endl;
      }


      cout<<"------------" << leftTerm << " # " << rightTerm <<endl;

    }
  }
  */


#ifdef _CVC3_DEBUG_MODE
  if(fullEffort){
    if( CVC3::debugger.trace("quant assertfact")  ){
      cout<<"===========all cached univs =========="<<endl;
      //      for (ExprMap<Theorem>::iterator i=d_simpUnivs.begin(), iend=d_simpUnivs.end(); i!=iend;  i++){
      //	cout<<"------------------------------------"<<endl;
      //	cout<<(i->first).toString()<<endl;
      //	cout<<"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"<<endl;
      //	cout<<(i->second).getExpr().toString()<<endl;
      //}
    }
    if( CVC3::debugger.trace("quant samehead")  ){
      cout<<"===========all cached  =========="<<endl;
      for (ExprMap< CDList<Expr>*>::iterator i=d_same_head_expr.begin(), iend=d_same_head_expr.end(); i!=iend;  i++){
	cout<<"------------------------------------"<<endl;
	cout<<(i->first)<<endl;
	cout<<"_______________________"<<endl;
	CDList<Expr> * terms= i->second;
	for(size_t i =0; i<terms->size(); i++){
	  cout<<(*terms)[i]<<endl;
	}
      }
    }
  }
#endif

#ifdef _CVC3_DEBUG_MODE
  if( CVC3::debugger.trace("quant checksat")  ){
    const CDList<Expr>& allpreds = theoryCore()->getPredicates();
    cout<<"=========== cur pred & terms =========="<<endl;

    for (size_t i=d_lastPredsPos; i<allpreds.size(); i++){
    //    for (size_t i=0; i<allpreds.size(); i++){
      cout<<"i="<<allpreds[i].getIndex()<<" :"<<findExpr(allpreds[i])<<"|"<<allpreds[i]<<endl;
    }

    const CDList<Expr>&  allterms = theoryCore()->getTerms();

    for (size_t i=d_lastTermsPos; i<allterms.size(); i++){
      cout<<"i="<<allterms[i].getIndex()<<" :"<<findExpr(allterms[i])<<"|"<<allterms[i]<<endl;
    }
    cout<<"=========== cur quant =========="<<endl;
    for (size_t i=0; i<d_univs.size(); i++){
      cout<<"i="<<d_univs[i].getExpr().getIndex()<<" :"<<findExpr(d_univs[i].getExpr())<<"|"<<d_univs[i]<<endl;
    }
  }


  if( CVC3::debugger.trace("quant checksat equ") ){
    const CDList<Expr>& allpreds = theoryCore()->getPredicates();
    cout<<"=========== cur pred equ =========="<<endl;

    for (size_t i=d_lastPredsPos; i<allpreds.size(); i++){
      if(allpreds[i].isEq()){
	cout<<"i="<<allpreds[i].getIndex()<<" :"<<findExpr(allpreds[i])<<"|"<<allpreds[i]<<endl;
      }
    }
    cout<<"=========== cur pred equ end  =========="<<endl;
  }

#endif

  if((*d_useLazyInst && !fullEffort) ) return;

  if(false) {//for the same head list
   const CDList<Expr>&  allterms = theoryCore()->getTerms();
   for(size_t i=d_lastTermsPos; i<allterms.size(); i++){
     Expr t = allterms[i];
     if(canGetHead(t)){
       if(d_same_head_expr.count(getHead(t)) >0){
	 d_same_head_expr[getHead(t)]->push_back(t);
       }
       else{
	 d_same_head_expr[getHead(t)]=
	   new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
	 d_same_head_expr[getHead(t)]->push_back(t);
       }
     }
   }

   const CDList<Expr>&  allpreds = theoryCore()->getPredicates();
   for(size_t i=d_lastPredsPos; i<allpreds.size(); i++){
     Expr t = allpreds[i];
     if(canGetHead(t)){
       if(d_same_head_expr.count(getHead(t)) >0){
	 d_same_head_expr[getHead(t)]->push_back(t);
       }
       else{
	 d_same_head_expr[getHead(t)]=
	   new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
	 d_same_head_expr[getHead(t)]->push_back(t);
       }
     }
   }
  }

  if(false){
    for(size_t eqs_index = d_lastEqsUpdatePos; eqs_index < d_eqsUpdate.size();  eqs_index++){

      const Expr lTerm = d_eqsUpdate[eqs_index].getLHS();
      const Expr rTerm = d_eqsUpdate[eqs_index].getRHS();

      d_eqs.push_back(lTerm);
      d_eqs.push_back(rTerm);
    }
  }

  if(false) {//for the equalities list
    const CDList<Expr>&  allpreds = theoryCore()->getPredicates();
    for(size_t i=d_lastPredsPos; i<allpreds.size(); i++){
      const Expr& t = allpreds[i];
      if(t.isEq()){
	//	cout<<"EQ: "<<t<<endl;
	const Expr lterm = t[0];
	const Expr rterm = t[1];
	d_eqs.push_back(lterm);
	d_eqs.push_back(rterm);

	/*
	ExprMap<CDList<Expr>* >::iterator iter = d_eq_list.find(lterm);
	if(d_eq_list.end() == iter){
	  d_eq_list[lterm] = new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
	  d_eq_list[lterm]->push_back(rterm);
	}
	else{
	  iter->second->push_back(rterm);
	}

	//	cout<<"LTERM: " <<rterm<<endl;
	iter = d_eq_list.find(rterm);
	if(d_eq_list.end() == iter){
	  d_eq_list[rterm] = new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
	  d_eq_list[rterm]->push_back(lterm);
	}
	else{
	  iter->second->push_back(lterm);
	}
	//	cout<<"RTERM: " <<lterm<<endl;
	*/
      }
    }
  }


  {//for rw heuristic
   const CDList<Expr>&  allterms = theoryCore()->getTerms();
   for(size_t i=d_lastTermsPos; i<allterms.size(); i++){
     const Expr& cur=allterms[i];
     if(READ == cur.getKind() || WRITE == cur.getKind()){
       arrayIndexName(cur);
     }
   }
  }

  d_instThisRound = 0;
  //  d_useMultTrig=*d_useMult;
  //  d_usePartTrig=*d_usePart;
  d_useFullTrig=true;

  if(fullEffort) {
    d_inEnd=true;
  }
  else{
    d_inEnd=false;
  }


  ExprMap<ExprMap<vector<dynTrig>* >* > new_trigs;
  if(fullEffort || theoryCore()->getCM()->scopeLevel() <= 5 || true){
    for(size_t i=d_univs.size(); i<d_rawUnivs.size(); i++){
      setupTriggers(new_trigs, d_rawUnivs[i], i);
    }
  }
  try {
    if (!(*d_useNew)){
      naiveCheckSat(fullEffort);
    }
    else if (*d_useSemMatch){
      semCheckSat(fullEffort);
    }
    else {
      synCheckSat(new_trigs, fullEffort);
    }
  }

  catch (int x){

     while(!d_simplifiedThmQueue.empty()){
       d_simplifiedThmQueue.pop();
       d_abInstCount++;
     }
     while(!d_gUnivQueue.empty()){
       d_gUnivQueue.pop();
     }
     while(!d_gBindQueue.empty()){
       d_gBindQueue.pop();
     }



    d_tempBinds.clear();
    saveContext();
    delNewTrigs(new_trigs);
    return;
  }

  sendInstNew();

  saveContext();

  try{
    if((*d_useNaiveInst) && (*d_useNew) && (0 == d_instThisRound) && fullEffort && theoryCore()->getTerms().size() < (size_t)(*d_maxNaiveCall )) {
      //      cout<<"naive called"<<endl;
      if (0== theoryCore()->getTerms().size()){
	static int counter =0;

	std::set<Expr> types;
	for(size_t i = 0; i<d_univs.size(); i++){
	  const Expr& cur_quant = d_univs[i].getExpr();
	  const std::vector<Expr> cur_vars = cur_quant.getVars();
	  for(size_t j =0; j<cur_vars.size(); j++){
	    types.insert(cur_vars[j].getType().getExpr());
	  }
	}

	std::string base("_naiveInst");
	for(std::set<Expr>::iterator i=types.begin(), iend = types.end(); i != iend; i++){
	  counter++;
	  std::stringstream tempout;
	  tempout << counter;
	  std::string out_str = base + tempout.str();
	  Expr newExpr = theoryCore()->getEM()->newVarExpr(out_str);

	  newExpr.setType(Type(*i));

	  Proof pf;

	  Expr newExpr2 = theoryCore()->getEM()->newVarExpr(out_str+"extra");
	  newExpr2.setType(Type(*i));

	  Expr newConstThm;

	  if(Type(*i) == theoryCore()->getEM()->newRatExpr(0).getType()){
	    //somehow theory_arith will complain if we use expr2 to form the eq here
	    newConstThm = newExpr.eqExpr(theoryCore()->getEM()->newRatExpr(0));
	  }
	  else{
	    newConstThm = newExpr.eqExpr(newExpr2);
	  }
	  Theorem newThm  = d_rules->addNewConst(newConstThm);

	  if(*d_useGFact){
	    //	    addGlobalLemma(newThm, -1);
	    enqueueFact(newThm);
	  }
	  else{
	    enqueueFact(newThm);
	  }
	  //	  enqueueSE(newThm);
	  //
	  d_tempBinds.clear();
	  return;
	}

      }
    naiveCheckSat(fullEffort);
    }
  }//end of try

  catch (int x){

     while(!d_simplifiedThmQueue.empty()){
       d_simplifiedThmQueue.pop();
       d_abInstCount++;
      }
     while(!d_gUnivQueue.empty()){
       d_gUnivQueue.pop();
     }
     while(!d_gBindQueue.empty()){
       d_gBindQueue.pop();
     }


    d_tempBinds.clear();
    saveContext();
    delNewTrigs(new_trigs);
    return;
  }

  if(fullEffort) {
    sendInstNew();
  }

  combineOldNewTrigs(new_trigs);
  delNewTrigs(new_trigs);
}

void TheoryQuant::saveContext(){
  d_lastArrayPos.set(d_arrayTrigs.size());
  d_univsSavedPos.set(d_univs.size());
  d_rawUnivsSavedPos.set(d_rawUnivs.size());
  d_lastTermsPos.set(theoryCore()->getTerms().size());
  d_lastPredsPos.set(theoryCore()->getPredicates().size());
  d_lastUsefulGtermsPos.set(d_usefulGterms.size());
  d_lastEqsUpdatePos.set(d_eqsUpdate.size());
}

void TheoryQuant::synCheckSat(ExprMap<ExprMap<vector<dynTrig>* >* >&  new_trigs, bool fullEffort){

  d_allout=false;

  if(fullEffort)   {
    setIncomplete("Quantifier instantiation");
  }

  size_t uSize = d_univs.size() ;
  const CDList<Expr>& allterms = theoryCore()->getTerms();
  const CDList<Expr>& allpreds = theoryCore()->getPredicates();
  size_t tSize = allterms.size();
  size_t pSize = allpreds.size();

  TRACE("quant",uSize, " uSize and univsSavedPOS ", d_univsSavedPos);
  TRACE("quant",tSize, " tSize and termsLastPos ", d_lastTermsPos);
  TRACE("quant",pSize, " pSize and predsLastPos ", d_lastPredsPos);
  TRACE("quant", fullEffort, " fulleffort:scope ",theoryCore()->getCM()->scopeLevel() );

  for(size_t i=d_lastTermsPos; i<tSize; i++){
    const Expr& cur(allterms[i]);
    //    if(usefulInMatch(cur) && cur.hasFind()){
    if(usefulInMatch(cur)){
      if(*d_useExprScore){
	int score = getExprScore(cur);
	if(score <= d_curMaxExprScore && 0 <= score ){
	  d_usefulGterms.push_back(cur);
	  add_parent(cur);
	}
      }
      else{
	d_usefulGterms.push_back(cur);
	add_parent(cur);
      }
    }
    else{
    }
  }

  for(size_t i=d_lastPredsPos; i<pSize; i++){
    const Expr& cur=allpreds[i];
    //    if( usefulInMatch(cur) && cur.hasFind()){
    if( usefulInMatch(cur)){
      if(*d_useExprScore ){
	int score = getExprScore(cur);
	if(score <= d_curMaxExprScore && 0 <= score){
	  d_usefulGterms.push_back(cur);
	  add_parent(cur);
	}
      }
      else{
	d_usefulGterms.push_back(cur);
	add_parent(cur);
      }
    }
    else{
    }
  }


  //  if(d_useFullTrig && d_inEnd && *d_useInstEnd ){
  if(d_useFullTrig && d_inEnd ){

    if(*d_useExprScore){

      matchListOld(d_usefulGterms, d_lastUsefulGtermsPos, d_usefulGterms.size() ); //new terms to old list
      matchListNew(new_trigs, d_usefulGterms, 0, d_usefulGterms.size()); //new and old terms to new list

      if(sendInstNew() > 0){
	TRACE("inend", "debug 1", "" ,"" );
	return;
      }

      d_allout = true; //let me look at these d_allout later yeting
      {
	CDList<Expr>* changed_terms = new (false) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
	collectChangedTerms(*changed_terms);

	matchListOld(*changed_terms, 0, changed_terms->size());
	matchListNew(new_trigs, *changed_terms, 0 , changed_terms->size());
	delete changed_terms;
      }
      d_allout = false;
      int n;
      if( ( n = sendInstNew()) > 0){
	TRACE("inend",  "debug 2", " # ",n );
	return;
      }

      bool hasMoreGterms(false);

      do {

      hasMoreGterms=false;

      int numNewTerm=0;
      int oldNum=d_usefulGterms.size();

      for(size_t i=0; i<tSize; i++){
	const Expr& cur(allterms[i]);
	//if(!(usefulInMatch(cur)) || !cur.hasFind()) continue;
	if(!(usefulInMatch(cur)) ) continue;
	int score = getExprScore(cur);
	if( score > d_curMaxExprScore){
	  if((d_curMaxExprScore + 1) == score){
	    //	  if((d_curMaxExprScore + 1) <= score){
	    d_usefulGterms.push_back(cur);
	    add_parent(cur);
	    numNewTerm++;
	  }
	  else{
	    hasMoreGterms = true;
	    TRACE("inend", "is this good? ", cur.toString()+" #-# " , score);
	    //	    cout<<"should not be here"<<endl;
	    if(*d_useGFact && false ){
	      d_usefulGterms.push_back(cur);
	      add_parent(cur);
	      numNewTerm++;
	    }
	    //	    cout<<"extra term e:"<<score<<" # "<<d_curMaxExprScore << " # "<< cur<<endl;
	    //	    cout<<"extra id:"<<cur.getIndex()<<endl;
	    //	    exit(3);
	  }
	}
      }


      for(size_t i=0; i<pSize; i++){
	const Expr& cur(allpreds[i]);
	//	if(!(usefulInMatch(cur)) ||  !cur.hasFind()) continue;
	if(!(usefulInMatch(cur)) ) continue;
	int score = getExprScore(cur);
	if( score > d_curMaxExprScore){
	  if((d_curMaxExprScore + 1) == score){
	    //  if((d_curMaxExprScore + 1) <= score){
	    d_usefulGterms.push_back(cur);
	    add_parent(cur);
	    numNewTerm++;
	  }
	  else{
	    hasMoreGterms = true;
	    TRACE("inend", "is this good? ", cur.toString()+" #-# " , score);
	    //	    cout<<"should not be here"<<endl;
	    if(*d_useGFact && false ){
	      d_usefulGterms.push_back(cur);
	      add_parent(cur);
	      numNewTerm++;
	    }
	    //	    cout<<"extra pred e:"<<score<<" # "<<d_curMaxExprScore << " # "<< cur<<endl;
	    //	    cout<<"extra id:"<<cur.getIndex()<<endl;
	    //	    exit(3);
	  }
	}
      }

      /*
      IF_DEBUG({
	bool hasStrange(false);
	for(size_t i=0; i<pSize-1; i++){
	  if(getExprScore(allpreds[i]) > getExprScore(allpreds[i+1]) ){
	    cout<<"strange pred"<<allpreds[i]<<endl;
	    hasStrange=true;
	  }
	}
	for(size_t i=0; i<tSize-1; i++){
	  if(getExprScore(allterms[i]) > getExprScore(allterms[i+1])){
	    cout<<"strange term"<<allterms[i]<<endl;
	    hasStrange=true;
	  }
	}
	if(hasStrange){
	  cout<<"strange here"<<endl;
	  for(size_t i=0; i<pSize; i++){
	    if (usefulInMatch(allpreds[i]) ) cout<<getExprScore(allpreds[i]) << " t# " <<allpreds[i]<<endl;
	  }
	  for(size_t i=0; i<tSize; i++){
	    if (usefulInMatch(allterms[i]) )  cout<<getExprScore(allterms[i]) << " p# " <<allterms[i]<<endl;
	  }
	  cout<<"strange end"<<endl;
	}
      }
	       )
      */
//       if(d_curMaxExprScore < 15 || true){
// 	d_curMaxExprScore = d_curMaxExprScore+1;
//       }

      if(d_curMaxExprScore >= 0 && d_curMaxExprScore <= *d_maxIL ){
	d_curMaxExprScore =  d_curMaxExprScore+1;;
      }
      else {
	d_curMaxExprScore =  d_curMaxExprScore+1;
	//	d_curMaxExprScore =  d_curMaxExprScore+0; //this is for debugging Yeting
	d_maxILReached = true;
	//cout<<"il reached: " << endl;
      }

      //      cout << " max il " << *d_maxIL << endl;
      //      cout <<d_curMaxExprScore << endl;

      if(numNewTerm >0 ){
	matchListOld(d_usefulGterms, oldNum, d_usefulGterms.size() );
	matchListNew(new_trigs, d_usefulGterms, oldNum, d_usefulGterms.size());

	if(sendInstNew() > 0){
	  TRACE("inend",  "debug 3 1", "" , "" );
	  return;
	}
      }

      if(hasMoreGterms){
        ;
	//	cout<<"has more " << endl;
	//	cout<<d_curMaxExprScore<<endl;
	//	cout<<"oldNum" << oldNum << endl;
      }
      //      } while(hasMoreGterms && d_curMaxExprScore <= 10 );
      } while(hasMoreGterms && d_curMaxExprScore <= *d_maxIL);

      d_allout = true;
      matchListOld(d_usefulGterms, 0, d_usefulGterms.size() );
      matchListNew(new_trigs, d_usefulGterms, 0, d_usefulGterms.size());
      if(sendInstNew() > 0){
	TRACE("inend",  "debug 3 2", "" , "" );
	return;
      }
      d_allout = false;

      //      for(size_t array_index = 0; array_index < d_arrayTrigs.size(); array_index++){
      //	arrayHeuristic(d_arrayTrigs[array_index].trig, d_arrayTrigs[array_index].univ_id);
      //      }


      return ;
    }

    TRACE("inend", "debug 3 0", "", "");
    TRACE("quant","this round; ",d_callThisRound,"");

    return;
  }


  if ((uSize == d_univsSavedPos) &&
      (tSize == d_lastTermsPos) &&
      (pSize == d_lastPredsPos) ) return;

  //  cout<<"match old"<<endl;
  matchListOld(d_usefulGterms, d_lastUsefulGtermsPos,d_usefulGterms.size() ); //new terms to old list
  //  cout<<"match new"<<endl;
  matchListNew(new_trigs, d_usefulGterms, 0, d_usefulGterms.size() ); //new and old terms to new list

  for(size_t array_index = d_lastArrayPos; array_index < d_arrayTrigs.size(); array_index++){
    arrayHeuristic(d_arrayTrigs[array_index].trig, d_arrayTrigs[array_index].univ_id);
  }

  TRACE("quant","this round; ",d_callThisRound,"");

  return;
}


void TheoryQuant::semCheckSat(bool fullEffort){
}

//the following is old code and I did not modify much, Yeting
void TheoryQuant::naiveCheckSat(bool fullEffort){
  d_univsSavedPos.set(0);
  TRACE("quant", "checkSat ", fullEffort, "{");
  IF_DEBUG(int instCount = d_instCount;)
  size_t uSize = d_univs.size(), stSize = d_savedTerms.size();
  if(true || (fullEffort && uSize > 0)) {
    // First of all, this algorithm is incomplete
    setIncomplete("Quantifier instantiation");

    if(d_instCount>=*d_maxQuantInst)
      return;
    //first attempt to instantiate with the saved terms
    //only do this if there are new saved terms or new theroems and
    // at least some saved terms
    bool savedOnly = ((uSize > d_univsSavedPos.get()  && stSize > 0) ||
		      (stSize > d_savedTermsPos.get()));
    int origCount = d_instCount;
    if(savedOnly)
      {
	TRACE("quant", "checkSat [saved insts]: univs size = ", uSize , " ");
	for(size_t i=0, pos = d_univsSavedPos.get(); i<uSize; i++) {
	  if(d_instCount>= *d_maxQuantInst)
	    break;
	  else
	    instantiate(d_univs[i], i>=pos, true,  d_savedTermsPos.get());
	}
	d_univsSavedPos.set(d_univs.size());
	d_savedTermsPos.set(stSize);
      }
    if(!savedOnly || d_instCount == origCount)
      { //instantiate with context dependent assertions terms
	TRACE("quant", "checkSat [context insts]: univs size = ", uSize , " ");
	const CDList<Expr>& assertions = theoryCore()->getTerms();
	int origSize = d_contextTerms.size();
	//	for(size_t i=0; i<uSize; i++)
	//	  assertions.push_back(d_univs[i].getExpr());
	//build the map of all terms grouped into vectors by types
	TRACE("quant", "checkSat terms size = ", assertions.size() , " ");
	mapTermsByType(assertions);
	for(size_t i=0, pos = d_univsContextPos.get(); i<uSize; i++) {
	  if(d_instCount>= *d_maxQuantInst)
	    break;
	  else
	    instantiate(d_univs[i], i>=pos, false, origSize);
	}
	d_univsContextPos.set(d_univs.size());
      }
    TRACE("quant terse", "checkSat total insts: ",
	  d_instCount, ", new "+int2string(d_instCount - instCount));
  }
  TRACE("quant", "checkSat total insts: ", d_instCount, " ");
  TRACE("quant", "checkSat new insts: ", d_instCount - instCount, " ");
  TRACE("quant", "checkSat effort:",  fullEffort, " }");

}


/*! \brief Queues up all possible instantiations of bound
 * variables.
 *
 * The savedMap boolean indicates whether to use savedMap or
 * d_contextMap the all boolean indicates weather to use all
 * instantiation or only new ones and newIndex is the index where
 * new instantiations begin.
 */
void TheoryQuant::instantiate(Theorem univ, bool all, bool savedMap,
			      size_t newIndex)
{

  if(!all && ((savedMap &&  newIndex == d_savedTerms.size())
  	      ||(!savedMap && newIndex == d_contextTerms.size())))
    return;

  TRACE("quant", "instanitate", all , "{");
  std::vector<Expr> varReplacements;
  recInstantiate(univ, all, savedMap, newIndex, varReplacements);
  TRACE("quant", "instanitate", "", "}");

}

 //! does most of the work of the instantiate function.
void TheoryQuant::recInstantiate(Theorem& univ, bool all, bool savedMap,
				 size_t newIndex,
				 std::vector<Expr>& varReplacements)
{
  Expr quantExpr = univ.getExpr();
  const vector<Expr>& boundVars = quantExpr.getVars();

  size_t curPos = varReplacements.size();
  TRACE("quant", "recInstantiate: ", boundVars.size() - curPos, "");
  //base case: a full vector of instantiations exists
  if(curPos == boundVars.size()) {
    if(!all)
      return;
    Theorem t = d_rules->universalInst(univ, varReplacements);
    d_insts[t.getExpr()] = varReplacements;
    TRACE("quant", "recInstantiate => " , t.toString(), "");
    if(d_instCount< *d_maxQuantInst) {
      d_instCount=d_instCount+1;
      enqueueInst(univ, varReplacements, null_expr);
      //            enqueueInst(univ, t);
	    // enqueueFact(t);
    }
    return;
  }
  //recursively add all possible instantiations in the next
  //available space of the vector
  else {
    Type t = getBaseType(boundVars[curPos]);
    int iendC=0, iendS=0, iend;
    std::vector<size_t>* typeVec = NULL; // = d_savedMap[t];
    CDList<size_t>* typeList = NULL; // = *d_contextMap[t];
    if(d_savedMap.count(t) > 0) {
      typeVec = &(d_savedMap[t]);
      iendS = typeVec->size();
      TRACE("quant", "adding from savedMap: ", iendS, "");
    }
    if(!savedMap) {
      if(d_contextMap.count(t) > 0) {
	typeList = d_contextMap[t];
	iendC = typeList->size();
	TRACE("quant", "adding from contextMap:", iendC , "");
      }
    }
    iend = iendC + iendS;
    for(int i =0; i<iend; i++) {
      TRACE("quant", "I must have gotten here!", "", "");
      size_t index;
      if(i<iendS){
	index = (*typeVec)[i];
	varReplacements.push_back(d_savedTerms[index]);
      }
      else {
	index = (*typeList)[i-iendS];
	varReplacements.push_back(d_contextTerms[index]);
      }
      if((index <  newIndex) || (!savedMap && i<iendS))
	recInstantiate(univ, all, savedMap, newIndex,  varReplacements);
      else
	recInstantiate(univ, true, savedMap, newIndex,  varReplacements);
      varReplacements.pop_back();
    }


  }
}

/*! \brief categorizes all the terms contained in a vector of  expressions by
 * type.
 *
 * Updates d_contextTerms, d_contextMap, d_contextCache accordingly.
 */
void TheoryQuant::mapTermsByType(const CDList<Expr>& terms)
{
  Expr trExpr=trueExpr(), flsExpr = falseExpr();
  Type boolT = boolType();
  if(d_contextMap.count(boolT) == 0)
    {
      d_contextMap[boolT] =
        new(true) CDList<size_t>(theoryCore()->getCM()->getCurrentContext());
      size_t pos = d_contextTerms.size();
      d_contextTerms.push_back(trExpr);
      d_contextTerms.push_back(flsExpr);
      (*d_contextMap[boolT]).push_back(pos);
      (*d_contextMap[boolT]).push_back(pos+1);
    }
  for(size_t i=0; i<terms.size(); i++)
    recursiveMap(terms[i]);
  // Add all our saved universals to the pool
  for(size_t i=0; i<d_univs.size(); i++)
    recursiveMap(d_univs[i].getExpr());
}

/*! \brief categorizes all the terms contained in an expressions by
 * type.
 *
 * Updates d_contextTerms, d_contextMap, d_contextCache accordingly.
 * returns true if the expression does not contain bound variables, false
 * otherwise.
 */
bool TheoryQuant::recursiveMap(const Expr& e)
{
  if(d_contextCache.count(e)>0) {
    return(d_contextCache[e]);
  }
  if(e.arity()>0)  {
    for(Expr::iterator it = e.begin(), iend = e.end(); it!=iend; ++it)
      //maps the children and returns a bool
      if(recursiveMap(*it) == false) {
	d_contextCache[e] = false;
      }
  }
  else if(e.getKind() == EXISTS || e.getKind() == FORALL){
    //maps the body
    if(recursiveMap(e.getBody())==false) {
      d_contextCache[e]=false;
    }
  }
  //found a bound variable in the children
  if(d_contextCache.count(e)>0) {
    return false;
  }

  if(d_savedCache.count(e) > 0) {
    return true;
  }

  Type type = getBaseType(e);

  if(!type.isBool() && !(e.getKind()==BOUND_VAR)){
     TRACE("quant", "recursiveMap: found ",
	   e.toString() + " of type " + type.toString(), "");
    int pos = d_contextTerms.size();
    d_contextTerms.push_back(e);
    if(d_contextMap.count(type)==0)
      d_contextMap[type] =
        new(true) CDList<size_t>(theoryCore()->getCM()->getCurrentContext());
    (*d_contextMap[type]).push_back(pos);
  }

  if(e.getKind() == BOUND_VAR) {
    d_contextCache[e] = false;
    return false;
  }
  else {
    d_contextCache[e] = true;
    return true;
  }
  //need  to implement:
  //insert all instantiations if type is finite and reasonable
  //also need to implement instantiations of subtypes
}

/*!\brief Used to notify the quantifier algorithm of possible
 * instantiations that were used in proving a context inconsistent.
 */
void TheoryQuant::notifyInconsistent(const Theorem& thm){
#ifdef _CVC3_DEBUG_MODE

  if( CVC3::debugger.trace("quant inscon")  ){

    cout<<"the one caused incsonsistency"<<endl;
    cout<<thm.getAssumptionsRef().toString()<<endl;
    std::vector<Expr> assump;
    thm.getLeafAssumptions(assump);

    cout<<"===========leaf assumptions; =========="<<endl;
    for(std::vector<Expr>::iterator i=assump.begin(), iend=assump.end(); i!=iend; i++){
      cout<<">>"<<i->toString()<<endl;
    }
  }
#endif

  if(d_univs.size() == 0)
    return;
  DebugAssert(thm.getExpr().isFalse(), "notifyInconsistent called with"
	" theorem: " + thm.toString() + " which is not a derivation of false");
  TRACE("quant", "notifyInconsistent: { " , thm.toString(), "}");
  //  thm.clearAllFlags();
  //  findInstAssumptions(thm);
  TRACE("quant terse", "notifyInconsistent: savedTerms size = ",
	d_savedTerms.size(), "");
  TRACE("quant terse", "last term: ",
	d_savedTerms.size()? d_savedTerms.back() : Expr(), "");
}
/*! \brief A recursive function used to find instantiated universals
 * in the hierarchy of assumptions.
 */
void TheoryQuant::findInstAssumptions(const Theorem& thm)
{
  if(thm.isNull() || thm.isRefl() || thm.isFlagged())
    return;
  thm.setFlag();
  const Expr& e = thm.getExpr();
  if(d_insts.count(e) > 0) {
    vector<Expr>& insts = d_insts[e];
    int pos;
    for(vector<Expr>::iterator it = insts.begin(), iend = insts.end(); it!=iend
	  ; ++it)
      {
	if(d_savedCache.count(*it) ==  0) {
	  TRACE("quant", "notifyInconsistent: found:", (*it).toString(), "");
	  d_savedCache[*it] = true;
	  pos = d_savedTerms.size();
	  d_savedTerms.push_back(*it);
	  d_savedMap[getBaseType(*it)].push_back(pos);
	}
      }
  }
  if(thm.isAssump())
    return;
  const Assumptions& a = thm.getAssumptionsRef();
  for(Assumptions::iterator it =a.begin(), iend = a.end(); it!=iend; ++it){
    findInstAssumptions(*it);
  }
}

//! computes the type of a quantified term. Always a  boolean.
void TheoryQuant::computeType(const Expr& e)
{
  switch (e.getKind()) {
  case FORALL:
  case EXISTS: {
    if(!e.getBody().getType().isBool())
      throw TypecheckException("Type mismatch for expression:\n\n   "
			      + e.getBody().toString()
			      + "\n\nhas the following type:\n\n  "
			      + e.getBody().getType().toString()
			      + "\n\nbut the expected type is Boolean:\n\n  ");
    else

      e.setType(e.getBody().getType());
    break;
  }
  default:
    DebugAssert(false,"Unexpected kind in Quantifier Theory: "
		+ e.toString());
    break;
  }
}

/*!
 * TCC(forall x.phi(x)) = (forall x. TCC(phi(x)))
 *                         OR (exists x. TCC(phi(x)) & !phi(x))
 * TCC(exists x.phi(x)) = (forall x. TCC(phi(x)))
 *                         OR (exists x. TCC(phi(x)) & phi(x))
 */


Expr TheoryQuant::computeTCC(const Expr& e) {
  DebugAssert(e.isQuantifier(), "Unexpected expression in Quantifier Theory: "
	      + e.toString());

  bool forall(e.getKind() == FORALL);
  const Expr& phi = e.getBody();
  Expr tcc_phi = getTCC(phi);
  Expr forall_tcc = getEM()->newClosureExpr(FORALL, e.getVars(), tcc_phi);
  Expr exists_tcc = getEM()->newClosureExpr(EXISTS, e.getVars(),
                                            tcc_phi && (forall? !phi : phi));
  return (forall_tcc || exists_tcc);
}


ExprStream&
TheoryQuant::print(ExprStream& os, const Expr& e) {
  switch(os.lang()) {
  case SIMPLIFY_LANG:
    {
      switch(e.getKind()){
      case FORALL:
      case EXISTS: {
	if(!e.isQuantifier()) {
	  e.print(os);
	  break;
	}
	os << "(" << ((e.getKind() == FORALL)? "FORALL" : "EXISTS");
	const vector<Expr>& vars = e.getVars();
	bool first(true);
	os << "(" ;
	for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
	    i!=iend; ++i) {
	  if(first) first = false;
	  else os << " " ;
	  os << *i;
	  // The quantifier may be in a raw parsed form, in which case
	  // the type is not assigned yet
	  //if(i->isVar())  // simplify do not need type
	  //  os << ":" << space << pushdag << (*i).getType() << popdag;
	}
	os << ") "  << e.getBody() <<  ")";
      }
	break;
      default:
	e.print(os);
	break;
      }
      break;
    }
  case TPTP_LANG:
    {
      switch(e.getKind()){
      case FORALL:
      case EXISTS: {
	if(!e.isQuantifier()) {
	  e.print(os);
	  break;
	}
	os << ((e.getKind() == FORALL)? " ! " : " ? ");
	const vector<Expr>& vars = e.getVars();
	bool first(true);
	os << "[" ;
	for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
	    i!=iend; ++i) {
	  if(first) first = false;
	  else os << "," ;
	  os << *i  ;
	  if(i->isVar())  os <<  ": "<< (*i).getType() ;
	}
	os << "] : ("  << e.getBody() <<")";
      }
	break;
      default:
	e.print(os);
	break;
      }
      break;
    }


  case PRESENTATION_LANG: {
    switch(e.getKind()){
    case FORALL:
    case EXISTS: {
      if(!e.isQuantifier()) {
	e.print(os);
	break;
      }
      os << "(" << push << ((e.getKind() == FORALL)? "FORALL" : "EXISTS")
	 << space << push;
      const vector<Expr>& vars = e.getVars();
      bool first(true);
      os << "(" << push;
      for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
	  i!=iend; ++i) {
	if(first) first = false;
	else os << push << "," << pop << space;
	os << *i;
	// The quantifier may be in a raw parsed form, in which case
	// the type is not assigned yet
	// the following lines are changed for a neat output / by yeting
	if(*d_translate || true){
	  if(i->isVar())
	    os << ":" << space << pushdag << (*i).getType() << popdag;
	}
      }
      os << push << ") " << pushdag << push;

      // print manual triggers
      const vector<vector<Expr> >& triggers = e.getTriggers();
      for (vector<vector<Expr> >::const_iterator i=triggers.begin(), iend=triggers.end(); i != iend; ++i) {
	//        const vector<Expr>& terms = (*i).getKids();
        const vector<Expr>& terms = (*i);
        if (terms.size() > 0) {
          os << push << ": PATTERN (" << pushdag << push;
          vector<Expr>::const_iterator j=terms.begin(), jend=terms.end();
          os << nodag << pushdag << *j << popdag; ++j;
          for(;j!=jend; ++j) {
            os << push << ", " << pop << space << pushdag << *j << popdag;
          }
          os << ") " << push;
        }
      }

      os << ": " << pushdag << e.getBody() << push << ")";
    }
      break;
    default:
      e.print(os);
      break;
    }
    break;
  }
  case SMTLIB_LANG: {
    d_theoryUsed = true;
    switch(e.getKind()){
      case FORALL:
      case EXISTS: {
        if(!e.isQuantifier()) {
          e.print(os);
          break;
        }
        os << "(" << push << ((e.getKind() == FORALL)? "forall" : "exists")
           << space;
        const vector<Expr>& vars = e.getVars();
        bool first(true);
        //      os << "(" << push;
        for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
            i!=iend; ++i) {
          if(first) first = false;
          else os << space;
          os << "(" << push << *i;
          // The quantifier may be in a raw parsed form, in which case
          // the type is not assigned yet
          if(i->isVar())
            os << space << pushdag << (*i).getType() << popdag;
          os << push << ")" << pop << pop;
        }

        os << space << pushdag
           << e.getBody() << push;

        // print manual triggers
        const vector<vector<Expr> >& triggers = e.getTriggers();
        for (vector<vector<Expr> >::const_iterator i=triggers.begin(), iend=triggers.end(); i != iend; ++i) {
	  //          const vector<Expr>& terms = (*i).getKids();
          const vector<Expr>& terms = (*i);
          /* TODO: How does SMT-LIB v2 handle patterns? */
          if (terms.size() > 0) {
            os << push << space << ":pat {" << space << pushdag << push;
            vector<Expr>::const_iterator j=terms.begin(), jend=terms.end();
            os << nodag << pushdag << *j << popdag; ++j;
            for(;j!=jend; ++j) {
              os << space << pushdag << *j << popdag;
            }
            os << space << "}" << space << push;
          }
        }
        os << push << ")";
        break;
      }
      default:
        throw SmtlibException("TheoryQuant::print: SMTLIB_LANG: Unexpected expression: "
                              +getEM()->getKindName(e.getKind()));
        break;
    }
    break;
  } // End of SMTLIB_LANG
  case SMTLIB_V2_LANG: {
    d_theoryUsed = true;
    switch(e.getKind()){
      case FORALL:
      case EXISTS: {
        if(!e.isQuantifier()) {
          e.print(os);
          break;
        }
        os << "(" << push << ((e.getKind() == FORALL)? "forall" : "exists")
           << space;
        const vector<Expr>& vars = e.getVars();
        bool first(true);
        os << "(" << push;
        for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
            i!=iend; ++i) {
          if(first) first = false;
          else os << space;
          os << "(" << push << *i;
          // The quantifier may be in a raw parsed form, in which case
          // the type is not assigned yet
          if(i->isVar())
            os << space << pushdag << (*i).getType() << popdag;
          os << push << ")" << pop << pop;
        }
        os << ")" << pop;

        const vector<vector<Expr> >& triggers = e.getTriggers();
        if( !triggers.empty() ) {
          os << space << push << "(!";
        }
        os << space << pushdag << e.getBody();

        // print manual triggers
        for (vector<vector<Expr> >::const_iterator i=triggers.begin(), iend=triggers.end(); i != iend; ++i) {
          //          const vector<Expr>& terms = (*i).getKids();
          const vector<Expr>& terms = (*i);
          if (terms.size() > 0) {
            os << push << space << ":pattern" << space << push << "(" ;
            vector<Expr>::const_iterator j=terms.begin(), jend=terms.end();
            os << nodag << pushdag << *j << popdag; ++j;
            for(;j!=jend; ++j) {
              os << space << pushdag << *j << popdag;
            }
            os << ")" << pop << space ;
          }
        }
        if( !triggers.empty() ) {
          os << ")" << pop;
        }
        os << ")" << pop;
        break;
      }
      default:
        throw SmtlibException("TheoryQuant::print: SMTLIB_LANG: Unexpected expression: "
                              +getEM()->getKindName(e.getKind()));
        break;
    }
    break;
  } // End of SMTLIB_LANG

  case LISP_LANG: {
    switch(e.getKind()){
    case FORALL:
    case EXISTS: {
      if(!e.isQuantifier()) {
	e.print(os);
	break;
      }
      os << "(" << push << ((e.getKind() == FORALL)? "FORALL" : "EXISTS")
	 << space;
      const vector<Expr>& vars = e.getVars();
      bool first(true);
      os << "(" << push;
      for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
	  i!=iend; ++i) {
	if(first) first = false;
	else os << space;
	os << "(" << push << *i;
	// The quantifier may be in a raw parsed form, in which case
	// the type is not assigned yet
	if(i->isVar())
	  os << space << pushdag << (*i).getType() << popdag;
	os << push << ")" << pop << pop;
      }
      os << push << ")" << pop << pop << pushdag
	 << e.getBody() << push << ")";
    }
      break;
    default:
      e.print(os);
      break;
    }
    break;
  }
  default:
    e.print(os);
    break;
  }
  return os;
}

///////////////////////////////////////////////////////////////////////////////
//parseExprOp:
//translating special Exprs to regular EXPR??
///////////////////////////////////////////////////////////////////////////////
Expr
TheoryQuant::parseExprOp(const Expr& e) {
  TRACE("parser", "TheoryQuant::parseExprOp(", e, ")");
  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  if(RAW_LIST != e.getKind()) return e;

  DebugAssert(e.arity() > 0,
	      "TheoryQuant::parseExprOp:\n e = "+e.toString());

  const Expr& c1 = e[0][0];
  const string& opName(c1.getString());
  int kind = getEM()->getKind(opName);
  switch(kind) {
  case FORALL:
  case EXISTS: { // (OP ((v1 ... vn tp1) ...) body)
    if(!( (e.arity() == 3  || 4 == e.arity())  &&
	  e[1].getKind() == RAW_LIST &&
	  e[1].arity() > 0))
      throw ParserException("Bad "+opName+" expression: "+e.toString());


    // Iterate through the groups of bound variables
    vector<pair<string,Type> > vars; // temporary stack of bound variables
    for(Expr::iterator i=e[1].begin(), iend=e[1].end(); i!=iend; ++i) {
      if(i->getKind() != RAW_LIST || i->arity() < 2)
	throw ParserException("Bad variable declaration block in "+opName
			    +" expression: "+i->toString()
			    +"\n e = "+e.toString());
      // Iterate through individual bound vars in the group.  The
      // last element is the type, which we have to rebuild and
      // parse, since it is used in the creation of bound variables.
      Type tp(parseExpr((*i)[i->arity()-1]));
      if (tp == boolType()) {
        throw ParserException("A quantified variable may not be of type BOOLEAN");
      }
      for(int j=0, jend=i->arity()-1; j<jend; ++j) {
	if((*i)[j].getKind() != ID)
	  throw ParserException("Bad variable declaration in "+opName+""
			      " expression: "+(*i)[j].toString()+
			      "\n e = "+e.toString());
	vars.push_back(pair<string,Type>((*i)[j][0].getString(), tp));
      }
    }
    // Create all the bound vars and save them in a vector
    vector<Expr> boundVars;
    for(vector<pair<string,Type> >::iterator i=vars.begin(), iend=vars.end();
	i!=iend; ++i)
      boundVars.push_back(addBoundVar(i->first, i->second));
    // Rebuild the body
    Expr body(parseExpr(e[2]));
    // Build the resulting Expr as (OP (vars) body)

    std::vector<std::vector<Expr> > patterns;
    if(e.arity() == 4){
      DebugAssert ((RAW_LIST == e[3].getKind()),"Unknown type for patterns"+e[3].toString());
      for(int i = 0; i < e[3].arity(); i++){
	const Expr& cur_trig(e[3][i]);
	DebugAssert ((RAW_LIST == cur_trig.getKind()),"Unknown type for cur_trig"+cur_trig.toString());
	//	cout<<"cur trig"<<cur_trig<<endl;
	std::vector<Expr> cur_pattern;
	for(int j =0; j < cur_trig.arity(); j++){
	  try {
	    cur_pattern.push_back(parseExpr(cur_trig[j]));
	  }
	  catch (Exception e){
	    //	    cout <<e << endl;
	    //	    cout <<"exception in pattern" << flush << endl;
	    cur_pattern.clear();
	  }
	}
	if (cur_pattern.size() > 0 ){
	  //	  Expr cur_parsed_trig(RAW_LIST, cur_pattern, getEM());
	  patterns.push_back(cur_pattern);
	}
      }
    }


    Expr res;
    if(3 == e.arity()) {
      res = getEM()->newClosureExpr((kind == FORALL) ? FORALL : EXISTS,boundVars, body);
    }
    else{// 4 == e.arity()
      res = getEM()->newClosureExpr((kind == FORALL) ? FORALL : EXISTS,boundVars, body, patterns );
      //      cout<<"patterns vector"<<vectorExpr2string(patterns)<<endl;;
      //      cout<<"patterns thm"<<res<<endl;;
    }
    return res;
    break;
  }
  default:
    DebugAssert(false,
		"TheoryQuant::parseExprOp: invalid command or expression: " + e.toString());
    break;
  }
  return e;
}

