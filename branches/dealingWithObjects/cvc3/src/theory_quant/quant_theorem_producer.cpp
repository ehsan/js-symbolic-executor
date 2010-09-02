/*****************************************************************************/
/*!
* \file quant_theorem_producer.cpp
 *
 * Author: Daniel Wichs, Yeting Ge
 *
 * Created: Jul 07 22:22:38 GMT 2003
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
 * CLASS: QuantProofRules
 *
 *
 * Description: TRUSTED implementation of arithmetic proof rules.
 *
 */
/*****************************************************************************/

// This code is trusted
#define _CVC3_TRUSTED_


#include "quant_theorem_producer.h"
#include "theory_quant.h"
#include "theory_core.h"


using namespace std;
using namespace CVC3;


QuantProofRules* TheoryQuant::createProofRules() {
  return new QuantTheoremProducer(theoryCore()->getTM(), this);
}


#define CLASS_NAME "CVC3::QuantTheoremProducer"


//! ==> NOT FORALL (vars): e  IFF EXISTS (vars) NOT e
Theorem
QuantTheoremProducer::rewriteNotForall(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot() && e[0].isForall(),
		"rewriteNotForall: expr must be NOT FORALL:\n"
		+e.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_not_forall", e);
  return newRWTheorem(e, e.getEM()->newClosureExpr(EXISTS, e[0].getVars(),
                                                   !e[0].getBody()),
                      Assumptions::emptyAssump(), pf);
}

Theorem
QuantTheoremProducer::addNewConst(const Expr& e) {
  Proof pf;
  if(withProof())
    pf = newPf("add_new_const", e);
  return newTheorem(e, Assumptions::emptyAssump(), pf);
}

///do not use this rule, this is for debug only
Theorem
QuantTheoremProducer::newRWThm(const Expr& e, const Expr& newE) {
  Proof pf;
  if(withProof())
    pf = newPf("from cache", e);
  return newRWTheorem(e, newE,Assumptions::emptyAssump(), pf);
}


Theorem
QuantTheoremProducer::normalizeQuant(const Expr& quant) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(quant.isForall()||quant.isExists(),
		"normalizeQuant: expr must be FORALL or EXISTS\n"
		+quant.toString());
  }


  std::map<Expr,int>::iterator typeIter;
  std::string base("_BD");
  int counter(0);

  vector<Expr> newVars;
  const std::vector<Expr>& cur_vars = quant.getVars();
  for(size_t j =0; j<cur_vars.size(); j++){
    Type t = cur_vars[j].getType();
    int typeIndex ;

    typeIter = d_typeFound.find(t.getExpr());

    if(d_typeFound.end() ==  typeIter){
      typeIndex = d_typeFound.size();
      d_typeFound[t.getExpr()] = typeIndex;
    }
    else{
      typeIndex = typeIter->second;
    }

    counter++;
    std::stringstream stringType;
    stringType << counter << "TY" << typeIndex ;
    std::string out_str = base + stringType.str();
    Expr newExpr = d_theoryQuant->getEM()->newBoundVarExpr(out_str, int2string(counter));
    newExpr.setType(t);
    newVars.push_back(newExpr);
  }

  vector<vector<Expr> > trigs = quant.getTriggers();
  for(size_t i = 0 ; i < trigs.size(); i++){
    for(size_t j = 0 ; j < trigs[i].size(); j++){
      trigs[i][j] = trigs[i][j].substExpr(cur_vars,newVars);
    }
  }

  Expr normBody = quant.getBody().substExpr(cur_vars,newVars);
  Expr normQuant = d_theoryQuant->getEM()->newClosureExpr(quant.isForall()?FORALL:EXISTS, newVars, normBody, trigs);

  Proof pf;
  if(withProof())
    pf = newPf("normalizeQuant", quant, normQuant);

  return newRWTheorem(quant, normQuant, Assumptions::emptyAssump(), pf);

}


//! ==> NOT EXISTS (vars): e  IFF FORALL (vars) NOT e
Theorem QuantTheoremProducer::rewriteNotExists(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot() && e[0].isExists(),
		"rewriteNotExists: expr must be NOT FORALL:\n"
		+e.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_not_exists", e);
  return newRWTheorem(e, e.getEM()->newClosureExpr(FORALL, e[0].getVars(),
                                                   !e[0].getBody()),
                      Assumptions::emptyAssump(), pf);
}


Theorem QuantTheoremProducer::universalInst(const Theorem& t1, const  vector<Expr>& terms, int quantLevel, Expr gterm){
  Expr e = t1.getExpr();
  const vector<Expr>& boundVars = e.getVars();

     for(unsigned int i=0; i<terms.size(); i++){
       if (d_theoryQuant->getBaseType(boundVars[i]) !=
 	  d_theoryQuant->getBaseType(terms[i])){
 	Proof pf;
 	return newRWTheorem(terms[i],terms[i], 
 			    Assumptions::emptyAssump(), pf);
       }
 //this is the same as return a TRUE theorem, which will be ignored immeridatele.  So, this is just return doing nothing. 
     }


  if(CHECK_PROOFS) {
    CHECK_SOUND(boundVars.size() == terms.size(),
		"Universal instantiation: size of terms array does "
		"not match quanitfied variables array size");
    CHECK_SOUND(e.isForall(),
		"universal instantiation: expr must be FORALL:\n"
		+e.toString());

    for(unsigned int i=0; i<terms.size(); i++)
      CHECK_SOUND(d_theoryQuant->getBaseType(boundVars[i]) ==
		  d_theoryQuant->getBaseType(terms[i]),
		  "Universal instantiation: type mismatch");
  }

  //build up a conjunction of type predicates for expression
  Expr tr = e.getEM()->trueExpr();
  Expr typePred = tr;
  //  unsigned qlevel, qlevelMax = 0;
  for(unsigned int i=0; i<terms.size(); i++) {
    Expr p = d_theoryQuant->getTypePred(boundVars[i].getType(),terms[i]);
    if(p!=tr) {
      if(typePred==tr)
	typePred = p;
      else
	typePred = typePred.andExpr(p);
    }
    //    qlevel = d_theoryQuant->theoryCore()->getQuantLevelForTerm(terms[i]);
    //    if (qlevel > qlevelMax) qlevel = qlevelMax;
  }


  //  Expr inst = e.getBody().substExprQuant(e.getVars(), terms);
  Expr inst = e.getBody().substExpr(e.getVars(), terms);

  //  Expr inst = e.getBody().substExpr(e.getVars(), terms);


  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> es;
    pfs.push_back(t1.getProof());
    es.push_back(e);
    es.push_back(Expr(RAW_LIST,terms));
    //    es.insert(es.end(), terms.begin(), terms.end());
    es.push_back(inst);
    if (gterm.isNull()) {
      es.push_back( d_theoryQuant->getEM()->newRatExpr(0));
    }
    else {es.push_back(gterm);
    }
    pf= newPf("universal_elimination1", es, pfs);
  }


  //   Expr inst = e.getBody().substExpr(e.getVars(), terms);


   Expr imp;
   if(typePred == tr ) //just for a easy life, yeting, change this assp
     imp = inst;
   else
     imp = typePred.impExpr(inst);
   Theorem ret = newTheorem(imp, t1.getAssumptionsRef(), pf);

   int thmLevel = t1.getQuantLevel();
   if(quantLevel  >= thmLevel) {
      ret.setQuantLevel(quantLevel+1);
    }
    else{
      ret.setQuantLevel(thmLevel+1);
    }

   //   ret.setQuantLevel(quantLevel+1);
   return ret;
}


//! Instantiate a  universally quantified formula
/*! From T|-FORALL(var): e generate T|-psi => e' where e' is obtained
 * from e by instantiating bound variables with terms in
 * vector<Expr>& terms.  The vector of terms should be the same
 * size as the vector of bound variables in e. Also elements in
 * each position i need to have matching base types. psi is the conjunction of
 * subtype predicates for the bound variables of the quanitfied expression.
 * \param t1 the quantifier (a Theorem)
 * \param terms the terms to instantiate.
 * \param quantLevel the quantification level for the formula
 */
Theorem QuantTheoremProducer::universalInst(const Theorem& t1, const  vector<Expr>& terms, int quantLevel){

  Expr e = t1.getExpr();
  const vector<Expr>& boundVars = e.getVars();
  if(CHECK_PROOFS) {
    CHECK_SOUND(boundVars.size() == terms.size(),
		"Universal instantiation: size of terms array does "
		"not match quanitfied variables array size");
    CHECK_SOUND(e.isForall(),
		"universal instantiation: expr must be FORALL:\n"
		+e.toString());
     for(unsigned int i=0; i<terms.size(); i++)
       CHECK_SOUND(d_theoryQuant->getBaseType(boundVars[i]) ==
                   d_theoryQuant->getBaseType(terms[i]),
 	      "Universal instantiation: type mismatch");
  }

  //build up a conjunction of type predicates for expression
  Expr tr = e.getEM()->trueExpr();
  Expr typePred = tr;
  //  unsigned qlevel, qlevelMax = 0;
  for(unsigned int i=0; i<terms.size(); i++) {
    Expr p = d_theoryQuant->getTypePred(boundVars[i].getType(),terms[i]);
    if(p!=tr) {
      if(typePred==tr)
	typePred = p;
      else
	typePred = typePred.andExpr(p);
    }
    //    qlevel = d_theoryQuant->theoryCore()->getQuantLevelForTerm(terms[i]);
    //    if (qlevel > qlevelMax) qlevel = qlevelMax;
  }

  //Expr inst = e.getBody().substExprQuant(e.getVars(), terms);
  Expr inst = e.getBody().substExpr(e.getVars(), terms);


  //  Expr inst = e.getBody().substExpr(e.getVars(), terms);


  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> es;
    pfs.push_back(t1.getProof());
    es.push_back(e);
    es.push_back(Expr(RAW_LIST,terms));
    //    es.insert(es.end(), terms.begin(), terms.end());
    es.push_back(inst);
    pf= newPf("universal_elimination2", es, pfs);
  }

  //   Expr inst = e.getBody().substExpr(e.getVars(), terms);


   Expr imp;
   if(typePred == tr) //just for a easy life, yeting, change this assp
     imp = inst;
   else
     imp = typePred.impExpr(inst);
   Theorem ret = newTheorem(imp, t1.getAssumptionsRef(), pf);

   int thmLevel = t1.getQuantLevel();
   if(quantLevel >= thmLevel) {
      ret.setQuantLevel(quantLevel+1);
    }
    else{
      ret.setQuantLevel(thmLevel+1);
    }

   //   ret.setQuantLevel(quantLevel+1);
   return ret;
}

Theorem QuantTheoremProducer::universalInst(const Theorem& t1, const  vector<Expr>& terms){

  Expr e = t1.getExpr();
  const vector<Expr>& boundVars = e.getVars();
  if(CHECK_PROOFS) {
    CHECK_SOUND(boundVars.size() == terms.size(),
		"Universal instantiation: size of terms array does "
		"not match quanitfied variables array size");
    CHECK_SOUND(e.isForall(),
		"universal instantiation: expr must be FORALL:\n"
		+e.toString());
    for(unsigned int i=0; i<terms.size(); i++)
      CHECK_SOUND(d_theoryQuant->getBaseType(boundVars[i]) ==
                  d_theoryQuant->getBaseType(terms[i]),
	      "Universal instantiation: type mismatch");
  }

  //build up a conjunction of type predicates for expression
  Expr tr = e.getEM()->trueExpr();
  Expr typePred = tr;
  unsigned qlevel=0, qlevelMax = 0;
  for(unsigned int i=0; i<terms.size(); i++) {
    Expr p = d_theoryQuant->getTypePred(boundVars[i].getType(),terms[i]);
    if(p!=tr) {
      if(typePred==tr)
	typePred = p;
      else
	typePred = typePred.andExpr(p);
    }
    qlevel = d_theoryQuant->theoryCore()->getQuantLevelForTerm(terms[i]);
    if (qlevel > qlevelMax) qlevel = qlevelMax;
  }

  Expr inst = e.getBody().substExpr(e.getVars(), terms);
  //  Expr inst = e.getBody().substExprQuant(e.getVars(), terms);


  //  Expr inst = e.getBody().substExpr(e.getVars(), terms);

  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> es;
    pfs.push_back(t1.getProof());
    es.push_back(e);
    es.push_back(Expr(RAW_LIST,terms));
    //    es.insert(es.end(), terms.begin(), terms.end());
    es.push_back(inst);
    pf= newPf("universal_elimination3", es, pfs);
  }

  //   Expr inst = e.getBody().substExpr(e.getVars(), terms);

   Expr imp;
   if( typePred == tr ) //just for easy life, yeting, change this asap
     imp = inst;
   else
     imp = typePred.impExpr(inst);
   Theorem ret = newTheorem(imp, t1.getAssumptionsRef(), pf);


   unsigned thmLevel = t1.getQuantLevel();
   if(qlevel >= thmLevel) {
      ret.setQuantLevel(qlevel+1);
    }
    else{
      //      ret.setQuantLevel(thmLevel+1);
      ret.setQuantLevel(thmLevel+1);
    }


   //   ret.setQuantLevel(qlevel+1);
   return ret;
}


Theorem QuantTheoremProducer::partialUniversalInst(const Theorem& t1, const vector<Expr>& terms, int quantLevel){
  cout<<"error in partial inst" << endl;
  Expr e = t1.getExpr();
  const vector<Expr>& boundVars = e.getVars();
  if(CHECK_PROOFS) {
    CHECK_SOUND(boundVars.size() >= terms.size(),
		"Universal instantiation: size of terms array does "
		"not match quanitfied variables array size");
    CHECK_SOUND(e.isForall(),
		"universal instantiation: expr must be FORALL:\n"
		+e.toString());
    for(unsigned int i=0; i<terms.size(); i++){
      CHECK_SOUND(d_theoryQuant->getBaseType(boundVars[i]) ==
                  d_theoryQuant->getBaseType(terms[i]),
	      "partial Universal instantiation: type mismatch");
    }
  }

  //build up a conjunction of type predicates for expression
  Expr tr = e.getEM()->trueExpr();
  Expr typePred = tr;
  for(unsigned int i=0; i<terms.size(); i++) {
    Expr p = d_theoryQuant->getTypePred(boundVars[i].getType(),terms[i]);
    if(p!=tr) {
      if(typePred==tr)
	typePred = p;
      else
	typePred = typePred.andExpr(p);
    }
  }
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> es;
    pfs.push_back(t1.getProof());
    es.push_back(e);
    es.insert(es.end(), terms.begin(), terms.end());
    pf= newPf("partial_universal_instantiation", es, pfs);
  }


  if(terms.size() == boundVars.size()){
    Expr inst = e.getBody().substExpr(e.getVars(), terms);
    Expr imp;
    if(typePred == tr)
      imp = inst;
    else
      imp = typePred.impExpr(inst);
    return(newTheorem(imp, t1.getAssumptionsRef(), pf));
  }
  else{
    vector<Expr> newBoundVars;
    for(size_t i=0; i<terms.size(); i++) {
      newBoundVars.push_back(boundVars[i]);
    }

    vector<Expr>leftBoundVars;
    for(size_t i=terms.size(); i<boundVars.size(); i++) {
      leftBoundVars.push_back(boundVars[i]);
    }

    Expr tempinst = e.getBody().substExpr(newBoundVars, terms);
    Expr inst = d_theoryQuant->getEM()->newClosureExpr(FORALL, leftBoundVars, tempinst);

    Expr imp;
    if(typePred == tr)
      imp = inst;
    else
      imp = typePred.impExpr(inst);

    Theorem res = (newTheorem(imp, t1.getAssumptionsRef(), pf));
    int thmLevel = t1.getQuantLevel();
    if(quantLevel >= thmLevel) {
      res.setQuantLevel(quantLevel+1);
    }
    else{
      //k      ret.setQuantLevel(thmLevel+1);
      res.setQuantLevel(thmLevel);
    }
    return res;

  }
}

//! find all bound variables in e and maps them to true in boundVars
void QuantTheoremProducer::recFindBoundVars(const Expr& e,
		           ExprMap<bool> & boundVars, ExprMap<bool> &visited)
{
  if(visited.count(e)>0)
    return;
  else
    visited[e] = true;
  if(e.getKind() == BOUND_VAR)
    boundVars[e] = true;
  if(e.getKind() == EXISTS || e.getKind() == FORALL)
    recFindBoundVars(e.getBody(), boundVars, visited);
  for(Expr::iterator it = e.begin(); it!=e.end(); ++it)
    recFindBoundVars(*it, boundVars, visited);

}

//!adjust the order of bound vars, newBvs begin first
Theorem QuantTheoremProducer::adjustVarUniv(const Theorem& t1, const std::vector<Expr>& newBvs){
  const Expr e=t1.getExpr();
  const Expr body = e.getBody();
  if(CHECK_PROOFS) {
      CHECK_SOUND(e.isForall(),
		"adjustVarUniv: "
		+e.toString());
  }

  const vector<Expr>& origVars = e.getVars();


  ExprMap<bool> oldmap;
  for(vector<Expr>::const_iterator it = origVars.begin(),
	iend=origVars.end(); it!=iend; ++it)    {
    oldmap[*it]=true;
  }

  vector<Expr> quantVars;
  for(vector<Expr>::const_iterator it = newBvs.begin(),
	iend=newBvs.end(); it!=iend; ++it)    {
    if(oldmap.count(*it) > 0)
      quantVars.push_back(*it);
  }

  if(quantVars.size() == origVars.size())
    return t1;

  ExprMap<bool> newmap;
  for(vector<Expr>::const_iterator it = newBvs.begin(),
	iend=newBvs.end(); it!=iend; ++it)    {
    newmap[*it]=true;
  }

  for(vector<Expr>::const_iterator it = origVars.begin(),
	iend=origVars.end(); it!=iend; ++it)    {
    if(newmap.count(*it)<=0){
      quantVars.push_back(*it);
    };
  }

  Proof pf;
  if(withProof()) {
    vector<Expr> es;
    vector<Proof> pfs;
    es.push_back(e);
    es.insert(es.end(), quantVars.begin(), quantVars.end());
    pfs.push_back(t1.getProof());
    pf= newPf("adjustVarUniv", es, pfs);
  }

  Expr newQuantExpr;
  newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(FORALL, quantVars, body);

  return(newTheorem(newQuantExpr, t1.getAssumptionsRef(), pf));
}

//!pack (forall (x) forall (y)) into (forall (x y))
Theorem QuantTheoremProducer::packVar(const Theorem& t1){
  Expr out_forall =t1.getExpr();

  if(CHECK_PROOFS) {
      CHECK_SOUND(out_forall.isForall(),
		"packVar: "
		+out_forall.toString());
  }

  vector<Expr> bVars = out_forall.getVars();

  if(!out_forall.getBody().isForall()){
    return t1;
  }

  Expr cur_body = out_forall.getBody();

  while(cur_body.isForall()){
    vector<Expr> bVarsLeft = cur_body.getVars();
    for(vector<Expr>::iterator i=bVarsLeft.begin(), iend=bVarsLeft.end(); i!=iend; i++){
      bVars.push_back(*i);
    }
    cur_body=cur_body.getBody();
  }

  Proof pf;
  if(withProof()) {
    vector<Expr> es;
    vector<Proof> pfs;
    es.push_back(out_forall);
    es.insert(es.end(), bVars.begin(), bVars.end());
    pfs.push_back(t1.getProof());
    pf= newPf("packVar", es, pfs);
  }

  Expr newQuantExpr;
  newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(FORALL, bVars, cur_body);

  return (newTheorem(newQuantExpr, t1.getAssumptionsRef(), pf));
  //  return (newRWTheorem(t1,newQuantExpr, t1.getAssumptionsRef(), pf));
}

//! convert (forall (x) ... forall (y)) into (forall (x y)...)
//! convert (exists (x) ... exists (y)) into (exists (x y)...)
Theorem QuantTheoremProducer::pullVarOut(const Theorem& t1){
  const Expr thm_expr=t1.getExpr();
  
  if(CHECK_PROOFS) {
    CHECK_SOUND(thm_expr.isForall() || thm_expr.isExists(),
		"pullVarOut: "
		+thm_expr.toString());
  }

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
      
      Proof pf;
      if(withProof()) {
	vector<Expr> es;
	vector<Proof> pfs;
	es.push_back(thm_expr);
	es.insert(es.end(), bVarsIn.begin(), bVarsIn.end());
	pfs.push_back(t1.getProof());
	pf= newPf("pullVarOut", es, pfs);
      }
      
      Expr newbody;
      
      newbody=(outBody[0][0].notExpr()).orExpr(innerBody.notExpr());
      
      Expr newQuantExpr;
      newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(FORALL, bVarsOut, newbody);
      
      return(newTheorem(newQuantExpr, t1.getAssumptionsRef(), pf));
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
      
      Proof pf;
      if(withProof()) {
	vector<Expr> es;
	vector<Proof> pfs;
	es.push_back(thm_expr);
	es.insert(es.end(), bVarsIn.begin(), bVarsIn.end());
	pfs.push_back(t1.getProof());
	pf= newPf("pullVarOut", es, pfs);
      }
      
      Expr newbody;
      if(outBody.isAnd()){
	newbody=outBody[0].andExpr(innerBody);
      }
      else if(outBody.isImpl()){
	newbody=outBody[0].impExpr(innerBody);
      }
      
      Expr newQuantExpr;
      newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(FORALL, bVarsOut, newbody);
      
      return(newTheorem(newQuantExpr, t1.getAssumptionsRef(), pf));
    }
    return t1; // case cannot be handled now. 
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
      
      Proof pf;
      if(withProof()) {
	vector<Expr> es;
	vector<Proof> pfs;
	es.push_back(thm_expr);
	es.insert(es.end(), bVarsIn.begin(), bVarsIn.end());
	pfs.push_back(t1.getProof());
	pf= newPf("pullVarOut", es, pfs);
      }
      
      Expr newbody;
      if(outBody.isAnd()){
	newbody=outBody[0].andExpr(innerBody);
      }
      else if(outBody.isImpl()){
	newbody=outBody[0].impExpr(innerBody);
      }
      
      Expr newQuantExpr;
      newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(EXISTS, bVarsOut, newbody);
      
      return(newTheorem(newQuantExpr, t1.getAssumptionsRef(), pf));
    }
  }
  return t1; 
}



/*! @brief From T|- QUANTIFIER (vars): e we get T|-QUANTIFIER(vars') e
 * where vars' is obtained from vars by removing all bound variables
 *  not used in e. If vars' is empty the produced theorem is just T|-e
 */
Theorem QuantTheoremProducer::boundVarElim(const Theorem& t1)
{
  const Expr e=t1.getExpr();
  const Expr body = e.getBody();
  if(CHECK_PROOFS) {
      CHECK_SOUND(e.isForall() || e.isExists(),
		"bound var elimination: "
		+e.toString());
  }
  ExprMap<bool> boundVars; //a mapping of bound variables in the body to true
  ExprMap<bool> visited; //to make sure expressions aren't traversed
			  //multiple times
  recFindBoundVars(body, boundVars, visited);
  vector<Expr> quantVars;
  const vector<Expr>& origVars = e.getVars();
  for(vector<Expr>::const_iterator it = origVars.begin(),
	iend=origVars.end(); it!=iend; ++it)
    {
    if(boundVars.count(*it) > 0)
      quantVars.push_back(*it);
    }

  // If all variables are used, just return the original theorem
  if(quantVars.size() == origVars.size())
    return t1;

  Proof pf;
  if(withProof()) {
    vector<Expr> es;
    vector<Proof> pfs;
    es.push_back(e);
    es.insert(es.end(), quantVars.begin(), quantVars.end());
    pfs.push_back(t1.getProof());
    pf= newPf("bound_variable_elimination", es, pfs);
  }
  if(quantVars.size() == 0)
    return(newTheorem(e.getBody(), t1.getAssumptionsRef(), pf));

  Expr newQuantExpr;
  if(e.isForall())
    newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(FORALL, quantVars, body);
  else
    newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(EXISTS, quantVars, body);

  return(newTheorem(newQuantExpr, t1.getAssumptionsRef(), pf));
}
