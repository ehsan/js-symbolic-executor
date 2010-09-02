/*****************************************************************************/
/*!
 * \file theory_records.cpp
 * 
 * Author: Daniel Wichs
 * 
 * Created: 7/21/03
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
#include "theory_records.h"
#include "typecheck_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
#include "records_proof_rules.h"
#include "theory_core.h"


using namespace std;
using namespace CVC3;

/*!
 * When a record/tuple (dis)equality is expanded into the
 * (dis)equalities of fields, we have to perform rewrites on the
 * resulting record terms before the simplifier kicks in.  
 *
 * Otherwise, if we have r1.f = r2.f, but r1=r2 was asserted before,
 * for some complex record expressions r1 and r2, then the simplifier
 * will substitute r2 for r1, and we get r2.f=r2.f at the end, which
 * is not a useful fact to have.
 *
 * However, r1.f and/or r2.f may rewrite to something interesting, and
 * the equality may yield new important facts.
 */
Theorem 
TheoryRecords::rewriteAux(const Expr& e) {
  Theorem res;
  switch(e.getKind()) {
  case EQ:
  case IFF:
  case AND:
  case OR: {
    vector<unsigned> changed;
    vector<Theorem> thms;
    for(int i=0, iend=e.arity(); i<iend; ++i) {
      Theorem t(rewriteAux(e[i]));
      if(t.getLHS() != t.getRHS()) {
	changed.push_back(i);
	thms.push_back(t);
      }
    }
    if(thms.size() > 0) {
      res = substitutivityRule(e, changed, thms);
      // Need to guarantee that new expressions are fully simplified
      if(res.getRHS().hasFind())
	res = transitivityRule(res, res.getRHS().getFind());
    } else
      res = reflexivityRule(e);
    break;
  }
  case NOT: {
    vector<Theorem> thms;
    thms.push_back(rewriteAux(e[0]));
    if(thms[0].getLHS() != thms[0].getRHS()) {
      res = substitutivityRule(NOT, thms);
      // Need to guarantee that new expressions are fully simplified
      if(res.getRHS().hasFind())
	res = transitivityRule(res, res.getRHS().getFind());
    } else
      res = reflexivityRule(e);
    break;
  }
  default:
    res = rewrite(e);
    break;
  }
  return res;
}


Theorem 
TheoryRecords::rewriteAux(const Theorem& thm) {
  return iffMP(thm, rewriteAux(thm.getExpr()));
}


TheoryRecords::TheoryRecords(TheoryCore* core)
  : Theory(core, "Records")
{

  getEM()->newKind(RECORD_TYPE, "_RECORD_TYPE", true);
  getEM()->newKind(TUPLE_TYPE, "_TUPLE_TYPE", true);

  getEM()->newKind(RECORD, "_RECORD");
  getEM()->newKind(RECORD_SELECT, "_RECORD_SELECT");
  getEM()->newKind(RECORD_UPDATE, "_RECORD_UPDATE");
  getEM()->newKind(TUPLE, "_TUPLE");
  getEM()->newKind(TUPLE_SELECT, "_TUPLE_SELECT");
  getEM()->newKind(TUPLE_UPDATE, "_TUPLE_UPDATE");

  d_rules = createProofRules();
  vector<int> kinds;

  kinds.push_back(RECORD);
  kinds.push_back(RECORD_SELECT);
  kinds.push_back(RECORD_UPDATE);
  kinds.push_back(RECORD_TYPE);
  kinds.push_back(TUPLE_TYPE);
  kinds.push_back(TUPLE);
  kinds.push_back(TUPLE_SELECT);
  kinds.push_back(TUPLE_UPDATE);

  registerTheory(this, kinds);
}

TheoryRecords::~TheoryRecords() {
  delete d_rules;
}

void TheoryRecords::assertFact(const Theorem& e)
{
  //  TRACE("records", "assertFact => ", e.toString(), "");
  const Expr& expr = e.getExpr();
  Theorem expanded;
  switch(expr.getKind()) {
  case IFF:
  case EQ: {
    int lhsKind = getBaseType(expr[0]).getExpr().getOpKind();
    if(lhsKind == RECORD_TYPE || lhsKind== TUPLE_TYPE)
      {
	expanded = rewriteAux(d_rules->expandEq(e));
	TRACE("records", "assertFact: enqueuing: ", expanded.toString(), "");
	enqueueFact(expanded);
      }
    return;
  }
  case NOT:
    DebugAssert(expr[0].getKind() == EQ || expr[0].getKind() == IFF,
                "expecting a disequality or boolean field extraction: "
                +expr.toString());
    break;
  default:
    DebugAssert(false, "TheoryRecords::assertFact expected an equation"
		" or negation of equation expression. Instead it got"
		+ e.toString());
    
  }
      
}


Theorem TheoryRecords::rewrite(const Expr& e) {
  Theorem rw;
  TRACE("records", "rewrite(", e, ") {");
  bool needRecursion=false;
  switch(e.getOpKind()) {
  case TUPLE_SELECT:
  case RECORD_SELECT: {
    switch(e[0].getOpKind()){
    case RECORD:{
      rw = d_rules->rewriteLitSelect(e);
      break;
    }
    case TUPLE: {
      rw =   d_rules->rewriteLitSelect(e);
      break;
    }
    case RECORD_UPDATE: {
      rw = d_rules->rewriteUpdateSelect(e);
      needRecursion=true;
      break;
    }
    case TUPLE_UPDATE: {
      rw = d_rules->rewriteUpdateSelect(e);
      needRecursion=true;
      break;
    }
    default:{
      rw =  reflexivityRule(e);
      break;
    }
    }
    break;
  } 
  case RECORD_UPDATE: {
    DebugAssert(e.arity() == 2, 
		"TheoryRecords::rewrite(RECORD_UPDATE): e="+e.toString());
    if(e[0].getOpKind() == RECORD)
      rw= d_rules->rewriteLitUpdate(e);
    else
      rw =  reflexivityRule(e);
    break;
  }
  case TUPLE_UPDATE: {
    if(e[0].getOpKind() == TUPLE)
      rw = d_rules->rewriteLitUpdate(e);
    else
      rw =  reflexivityRule(e);
    break;
  }
  case RECORD:
  case TUPLE:
    rw = rewriteCC(e); // Congruence closure rewrites
    break;
  default: {
    rw = reflexivityRule(e);
    break;
  }   
  }
  Theorem res;
  if(needRecursion==true) res = transitivityRule(rw, rewrite(rw.getRHS()));
  else
    res = rw;
  TRACE("records", "rewrite => ", res.getRHS(), " }");
  return res;
}


Expr TheoryRecords::computeTCC(const Expr& e)
{
  TRACE("records", "computeTCC( ", e, ")   {");
  Expr tcc(Theory::computeTCC(e));
  switch (e.getOpKind()) {
  case RECORD:
  case RECORD_SELECT:
  case TUPLE:
  case TUPLE_SELECT:
    break;
  case RECORD_UPDATE: {
    Expr tExpr = e.getType().getExpr();
    const std::string field(getField(e));
    int index = getFieldIndex(tExpr, field);
    Expr pred = getTypePred(e.getType()[index], e[1]);
    tcc = rewriteAnd(tcc.andExpr(pred)).getRHS();
    break;
  }
  case TUPLE_UPDATE: {
    Expr tExpr = e.getType().getExpr();
    int index = getIndex(e);
    Expr pred = getTypePred(e.getType()[index], e[1]);
    tcc = rewriteAnd(tcc.andExpr(pred)).getRHS();
    break;
  }
  default: {
    DebugAssert (false, "Theory records cannot calculate this tcc");
  }
  }
  TRACE("records", "computeTCC => ", tcc, "}");
  return tcc;
}

void TheoryRecords::computeModelTerm(const Expr& e, std::vector<Expr>& v) {
  Type t = e.getType();
  Expr tExpr  = t.getExpr();
  if(tExpr.getOpKind() == RECORD_TYPE) {
    const vector<Expr>& fields = getFields(tExpr);
    for(unsigned int i = 0; i < fields.size() ; i++) {
      Expr term(recordSelect(e, fields[i].getString()));
      term = rewrite(term).getRHS();
      v.push_back(term);
    }
  }
  else if(tExpr.getOpKind() == TUPLE_TYPE) {
    for(int i=0; i<tExpr.arity(); i++) {
      Expr term(tupleSelect(e, i));
      term = rewrite(term).getRHS();
      v.push_back(term);
    }
  }
}

void TheoryRecords::computeModel(const Expr& e, std::vector<Expr>& v) {
  Type t = getBaseType(e);
  Expr tExpr  = t.getExpr();
  vector<Theorem> thms;
  vector<unsigned> changed;
  Theorem asst;
  if(tExpr.getOpKind() == RECORD_TYPE)
    asst = d_rules->expandRecord(e);
  else if(tExpr.getOpKind() == TUPLE_TYPE)
    asst = d_rules->expandTuple(e);
  else {
    DebugAssert(false, "TheoryRecords::computeModel("+e.toString()+")");
    return;
  }

  const Expr& lit = asst.getRHS();
  int size(lit.arity());
  for(int i = 0; i < size ; i++) {
    Theorem thm(getModelValue(lit[i]));
    if(thm.getLHS() != thm.getRHS()) {
      thms.push_back(thm);
      changed.push_back(i);
    }
  }
  if(changed.size()>0)
    asst = transitivityRule(asst, substitutivityRule(lit, changed, thms));
  assignValue(asst);
  v.push_back(e);
}


Expr TheoryRecords::computeTypePred(const Type& t, const Expr& e)
{
  TRACE("typePred", "ComputeTypePred[Records]", e, "");
  Expr tExpr = t.getExpr();
  switch(tExpr.getOpKind()) {
  case RECORD_TYPE: {
    const vector<Expr>& fields = getFields(tExpr);
    vector<Expr> fieldPreds;
    for(unsigned int i = 0; i<fields.size(); i++) {
      Expr sel(recordSelect(e, fields[i].getString()));
      fieldPreds.push_back(getTypePred(tExpr[i], sel));
    }
      Expr pred = andExpr(fieldPreds);
      TRACE("typePred", "Computed predicate ", pred, "");
      return pred;
  }
  case TUPLE_TYPE: {
    std::vector<Expr> fieldPreds;
    for(int i = 0; i<tExpr.arity(); i++) {
      fieldPreds.push_back(getTypePred(tExpr[i], tupleSelect(e, i)));
    }
    Expr pred = andExpr(fieldPreds);
    TRACE("typePred", "Computed predicate ", pred, "");
    return pred;    
  }
  default:
   DebugAssert(false, "computeTypePred[TheoryRecords] called with wrong type");
   return Expr();
  }
}


void TheoryRecords::checkType(const Expr& e)
{
  switch (e.getOpKind()) {
    case RECORD_TYPE: {
      Expr::iterator i = e.begin(), iend = e.end();
      for (; i != iend; ) {
        Type t(*i);
        ++i;
        if (t.isBool()) throw Exception
            ("Records cannot contain BOOLEANs: "
             +e.toString());
        if (t.isFunction()) throw Exception
            ("Records cannot contain functions");
      }
      break;
    }
    case TUPLE_TYPE: {
      Expr::iterator i = e.begin(), iend = e.end();
      for (; i != iend; ) {
        Type t(*i);
        ++i;
        if (t.isBool()) throw Exception
            ("Tuples cannot contain BOOLEANs: "
             +e.toString());
        if (t.isFunction()) throw Exception
            ("Tuples cannot contain functions");
      }
      break;
    }
    default:
      DebugAssert(false, "Unexpected kind in TheoryRecords::checkType"
                  +getEM()->getKindName(e.getOpKind()));
  }
}


//TODO: implement finiteTypeInfo
Cardinality TheoryRecords::finiteTypeInfo(Expr& e, Unsigned& n,
                                          bool enumerate, bool computeSize)
{
  return CARD_UNKNOWN;
}


void TheoryRecords::computeType(const Expr& e)
{
  switch (e.getOpKind()) {
  case RECORD:{
    DebugAssert(e.arity() > 0, "wrong arity of RECORD" + e.toString());
    vector<Expr> fieldTypes;
    const vector<Expr>& fields = getFields(e);
    string previous;
    DebugAssert((unsigned int)e.arity() == fields.size(),
		"size of fields does not match size of values");
    for(int i = 0; i<e.arity(); ++i) {
      DebugAssert(fields[i].getString() != previous, 
		  "a record cannot not contain repeated fields"
		  + e.toString());
      fieldTypes.push_back(e[i].getType().getExpr());
      previous=fields[i].getString();
    }
    e.setType(Type(recordType(fields, fieldTypes)));
    return;
  }
  case RECORD_SELECT: {
    DebugAssert(e.arity() == 1, "wrong arity of RECORD_SELECT" + e.toString());
    Expr t = e[0].getType().getExpr();
    const string& field = getField(e);
    DebugAssert(t.getOpKind() == RECORD_TYPE, "incorrect RECORD_SELECT expression"
		"first child not a RECORD_TYPE" + e.toString());
    int index = getFieldIndex(t, field);
    if(index==-1)
      throw TypecheckException("record selection does not match any field "
			       "in record" + e.toString());
    e.setType(Type(t[index]));
    return;
  }
  case RECORD_UPDATE: {
    DebugAssert(e.arity() == 2, "wrong arity of RECORD_UPDATE" + e.toString());
    Expr t = e[0].getType().getExpr();
    const string& field = getField(e);
    DebugAssert(t.getOpKind() == RECORD_TYPE, "incorrect RECORD_SELECT expression"
		"first child not a RECORD_TYPE" + e.toString());
    int index = getFieldIndex(t, field);
    if(index==-1)
      throw TypecheckException
	("record update field \""+field
	 +"\" does not match any in record type:\n"
	 +t.toString()+"\n\nThe complete expression is:\n\n"
	 + e.toString());
    if(getBaseType(Type(t[index])) != getBaseType(e[1]))
      throw TypecheckException("Type checking error: \n"+ e.toString());
    e.setType(e[0].getType());
    return;
  }
  case TUPLE: {
    DebugAssert(e.arity() > 0, "wrong arity of TUPLE"+ e.toString());
    std::vector<Expr> types;
    for(Expr::iterator it = e.begin(), end=e.end(); it!=end; ++it)
      {
	types.push_back((*it).getType().getExpr());
      }
    e.setType(Type(Expr(TUPLE_TYPE, types, getEM())));
    return;
  }
  case TUPLE_SELECT: {
    DebugAssert(e.arity() == 1, "wrong arity of TUPLE_SELECT" + e.toString());
    Expr t = e[0].getType().getExpr();
    int index = getIndex(e);
    DebugAssert(t.getOpKind() == TUPLE_TYPE,
		"incorrect TUPLE_SELECT expression: "
		"first child is not a TUPLE_TYPE:\n\n" + e.toString());
    if(index >= t.arity())
      throw TypecheckException("tuple index exceeds number of fields: \n"
			       + e.toString());
    e.setType(Type(t[index]));
    return;
  }
  case TUPLE_UPDATE: {
    DebugAssert(e.arity() == 2, "wrong arity of TUPLE_UPDATE" + e.toString());
    Expr t = e[0].getType().getExpr();
    int index = getIndex(e);
    DebugAssert(t.getOpKind() == TUPLE_TYPE, "incorrect TUPLE_SELECT expression: "
		"first child not a TUPLE_TYPE:\n\n" + e.toString());
    if(index >= t.arity())
      throw TypecheckException("tuple index exceeds number of fields: \n"
			       + e.toString());
    if(getBaseType(Type(t[index])) != getBaseType(e[1]))
      throw TypecheckException("tuple update type mismatch: \n"+ e.toString());
    e.setType(e[0].getType());
    return;
  }
  default:
    DebugAssert(false,"Unexpected type: "+e.toString());
    break;
  }
}


Type
TheoryRecords::computeBaseType(const Type& t) {
  const Expr& e = t.getExpr();
  Type res;
  switch(e.getOpKind()) {
  case TUPLE_TYPE:
  case RECORD_TYPE: {
    DebugAssert(e.arity() > 0, "Expected non-empty type");
    vector<Expr> kids;
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
      kids.push_back(getBaseType(Type(*i)).getExpr());
    }
    res = Type(Expr(e.getOp(), kids));
    break;
  }
  default:
    DebugAssert(false,
		"TheoryRecords::computeBaseType("+t.toString()+")");
    res = t;
  }
  return res;
}


void
TheoryRecords::setup(const Expr& e) {
  // Only set up terms
  if (e.isTerm()) {
    switch(e.getOpKind()) {
    case RECORD:
    case TUPLE: // Setup for congruence closure
      setupCC(e);
      break;
    default: { // Everything else
      for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
	i->addToNotify(this, e);
      // Check if we have a tuple of record type, and set up those for CC
      Type tp(getBaseType(e));
      Theorem thm;
      if(isRecordType(tp)) // Expand e into its literal, and it setup for CC
	thm = d_rules->expandRecord(e);
      else if(isTupleType(tp))
	thm = d_rules->expandTuple(e);
      if(!thm.isNull()) {
	Expr lit(thm.getRHS());
	TRACE("records", "setup: lit = ", lit, "");
	// Simplify the kids
	vector<Theorem> thms;
	vector<unsigned> changed;
	for(int i=0,iend=lit.arity(); i<iend; ++i) {
	  TRACE("records", "setup: rewriting lit["+int2string(i)+"] = ",
		lit[i], "");
	  Theorem t = rewrite(lit[i]);
	  t = transitivityRule(t, find(t.getRHS()));
	  if(lit[i] != t.getRHS()) {
	    thms.push_back(t);
	    changed.push_back(i);
	  }
	}
	if(changed.size()>0) {
	  thm = transitivityRule(thm, substitutivityRule(lit, changed, thms));
	  lit = thm.getRHS();
	}
	// Check if lit has already been setup
	if(lit.hasFind()) {
	  enqueueFact(transitivityRule(thm, find(lit)));
	} else {
	  theoryCore()->setupTerm(lit, this, thm);
	  assertEqualities(symmetryRule(thm));
	}
      }
    }
    }
  }
}
 

void
TheoryRecords::update(const Theorem& e, const Expr& d) {
  if (inconsistent()) return;
  DebugAssert(d.hasFind(), "Expected d to have find");

  switch(d.getOpKind()) {
  case RECORD:
  case TUPLE:
    // Record and tuple literals are handled by congruence closure updates
    updateCC(e, d);
    break;
  default: // Everything else
    // If d is not its own representative, don't do anything; the
    // representative will be sent to us eventually.
    if (find(d).getRHS() == d) {
      // Substitute e[1] for e[0] in d and assert the result equal to d
      Theorem thm = updateHelper(d);
      thm = transitivityRule(thm, rewrite(thm.getRHS()));
      assertEqualities(transitivityRule(thm, find(thm.getRHS())));
    }
  }
}


ExprStream& TheoryRecords::print(ExprStream& os, const Expr& e)
{
   switch(os.lang()) {
   case PRESENTATION_LANG: {
     switch(e.getOpKind()){
     case TUPLE:{
       int i=0, iend=e.arity();
       os << "(" << push;
       if(i!=iend) os << e[i];
       ++i;
       for(; i!=iend; ++i) os << push << "," << pop << space << e[i];
       os << push << ")";
       break;
     }
     case TUPLE_TYPE: {
       int i=0, iend=e.arity();
       os << "[" << push;
       if(i!=iend) os << e[i];
       ++i;
       for(; i!=iend; ++i) os << push << "," << pop << space << e[i];
       os << push << "]";
       break;
     }
     case RECORD: {
       size_t i=0, iend=e.arity();
       if(!isRecord(e)) {
	 e.printAST(os);
	 break;
       }
       const vector<Expr>& fields = getFields(e);
       if(iend != fields.size()) {
	 e.printAST(os); 
	 break;
       }
       os << "(# " << push;
       if(i!=iend) {
	 os <<  fields[i].getString() << space 
	    << ":="<< space << push << e[i] << pop;
	 ++i;
       }
       for(; i!=iend; ++i)
	 os << push << "," << pop << space <<  fields[i].getString()
	    << space 
	    << ":="<< space << push << e[i] << pop;
       os << push << space << "#)";
       break;
     }
     case RECORD_TYPE: {
       size_t i=0, iend=e.arity();
       if(!isRecordType(e)) {
	 e.printAST(os);
	 break;
       }
       const vector<Expr>& fields = getFields(e);
       if(iend != fields.size()) {
	 e.printAST(os); 
	 break;
       }
       os << "[# " << push;
       if(i!=iend) {
	 os <<  fields[i].getString() << ":"<< space << push << e[i] << pop;
	 ++i;
       }
       for(; i!=iend; ++i)
	 os << push << "," << pop << space <<  fields[i].getString()
	    << ":"<< space << push << e[i] << pop;
       os << push << space << "#]";
       break;
     }
     case RECORD_SELECT:
       if(isRecordAccess(e) && e.arity() == 1)
	 os << "(" << push <<  e[0] << push << ")" << "." << push 
	    << getField(e);
       else
	 e.printAST(os);
       break;
     case TUPLE_SELECT:
       if(isTupleAccess(e) && e.arity() == 1)
	 os << "(" << push << e[0]  << push << ")" <<   "." << push 
	    << getIndex(e);
       else
	 e.printAST(os);
       break;
     case RECORD_UPDATE:
       if(isRecordAccess(e) && e.arity() == 2)
	 os << "(" << push <<  e[0] << space << "WITH ."
	    << push << getField(e)
	    << space << ":=" << space << push << e[1] << push << ")";
       else
	 e.printAST(os);
       break;
     case TUPLE_UPDATE:
       if(isTupleAccess(e) && e.arity() == 2)
	 os << "(" << push <<  e[0] << space << "WITH ."
	    << push << getIndex(e) 
	    << space << ":=" << space << push << e[1] << push << ")";
       else
	 e.printAST(os);
       break;
     default:
       e.printAST(os);
       break;
     }
     break;
   }
   case SMTLIB_LANG:
   case SMTLIB_V2_LANG: {
     d_theoryUsed = true;
     throw SmtlibException("TheoryRecords::print: SMTLIB not supported");
     switch(e.getOpKind()){
     case TUPLE:{
       int i=0, iend=e.arity();
       os << "(" << push << "TUPLE";
       for(; i<iend; ++i) os << space << e[i];
       os << push << ")";
       break;
     }
     case TUPLE_TYPE: { // FIXME: change to TUPLE_TYPE
       int i=0, iend=e.arity();
       os << "(" << push << "TUPLE_TYPE";
       for(; i!=iend; ++i) os << space << e[i];
       os << push << ")";
       break;
     }
     case RECORD: {
       size_t i=0, iend=e.arity();
       if(!isRecord(e)) {
	 e.printAST(os);
	 break;
       }
       const vector<Expr>& fields = getFields(e);
       if(iend != fields.size()) {
	 e.printAST(os); 
	 break;
       }
       os << "(" << push << "RECORD";
       for(; i!=iend; ++i)
	 os <<  space << "(" << push << fields[i].getString() << space 
	    << e[i] << push << ")" << pop << pop;
       os << push << ")";
       break;
     }
     case RECORD_TYPE: {
       size_t i=0, iend=e.arity();
       if(!isRecord(e)) {
	 e.printAST(os);
	 break;
       }
       const vector<Expr>& fields = getFields(e);
       if(iend != fields.size()) {
	 e.printAST(os); 
	 break;
       }
       os << "(" << push << "RECORD_TYPE";
       for(; i!=iend; ++i)
	 os << space << "(" << push <<  fields[i].getString()
	    << space << e[i] << push << ")" << pop << pop;
       os << push << space << ")";
       break;
     }
     case RECORD_SELECT:
       if(isRecordAccess(e))
	 os << "(" << push << "RECORD_SELECT" << space 
	    << e[0] << space << getField(e) << push << ")";
       else
	 e.printAST(os);
       break;
     case TUPLE_SELECT:
       if(isTupleAccess(e))
	 os << "(" << push << "TUPLE_SELECT" << space
	    << e[0] << space << getIndex(e) << push << ")";
       else
	 e.printAST(os);
       break;
     case RECORD_UPDATE:
       if(isRecordAccess(e) && e.arity() == 2)
	 os << "(" << push << "RECORD_UPDATE" << space
	    << e[0] << space << getField(e) 
	    << space << e[1] << push << ")";
       else
	 e.printAST(os);
       break;
     case TUPLE_UPDATE:
       if(isTupleAccess(e))
	 os << "(" << push << "TUPLE_UPDATE" << space << e[0]
	    << space << getIndex(e) 
	    << space << e[1] << push << ")";
       else
	 e.printAST(os);
       break;
     default:
       e.printAST(os);
       break;
     }
     break;
   }
   case LISP_LANG: {
     switch(e.getOpKind()){
     case TUPLE:{
       int i=0, iend=e.arity();
       os << "(" << push << "TUPLE";
       for(; i<iend; ++i) os << space << e[i];
       os << push << ")";
       break;
     }
     case TUPLE_TYPE: { // FIXME: change to TUPLE_TYPE
       int i=0, iend=e.arity();
       os << "(" << push << "TUPLE_TYPE";
       for(; i!=iend; ++i) os << space << e[i];
       os << push << ")";
       break;
     }
     case RECORD: {
       size_t i=0, iend=e.arity();
       if(!isRecord(e)) {
	 e.printAST(os);
	 break;
       }
       const vector<Expr>& fields = getFields(e);
       if(iend != fields.size()) {
	 e.printAST(os); 
	 break;
       }
       os << "(" << push << "RECORD";
       for(; i!=iend; ++i)
	 os <<  space << "(" << push << fields[i].getString() << space 
	    << e[i] << push << ")" << pop << pop;
       os << push << ")";
       break;
     }
     case RECORD_TYPE: {
       size_t i=0, iend=e.arity();
       if(!isRecord(e)) {
	 e.printAST(os);
	 break;
       }
       const vector<Expr>& fields = getFields(e);
       if(iend != fields.size()) {
	 e.printAST(os); 
	 break;
       }
       os << "(" << push << "RECORD_TYPE";
       for(; i!=iend; ++i)
	 os << space << "(" << push <<  fields[i].getString()
	    << space << e[i] << push << ")" << pop << pop;
       os << push << space << ")";
       break;
     }
     case RECORD_SELECT:
       if(isRecordAccess(e))
	 os << "(" << push << "RECORD_SELECT" << space 
	    << e[0] << space << getField(e) << push << ")";
       else
	 e.printAST(os);
       break;
     case TUPLE_SELECT:
       if(isTupleAccess(e))
	 os << "(" << push << "TUPLE_SELECT" << space
	    << e[0] << space << getIndex(e) << push << ")";
       else
	 e.printAST(os);
       break;
     case RECORD_UPDATE:
       if(isRecordAccess(e) && e.arity() == 2)
	 os << "(" << push << "RECORD_UPDATE" << space
	    << e[0] << space << getField(e)
	    << space << e[1] << push << ")";
       else
	 e.printAST(os);
       break;
     case TUPLE_UPDATE:
       if(isTupleAccess(e))
	 os << "(" << push << "TUPLE_UPDATE" << space << e[0]
	    << space << getIndex(e)
	    << space << e[1] << push << ")";
       else
	 e.printAST(os);
       break;
     default:
       e.printAST(os);
       break;
     }
     break;
   }
   default:
     e.printAST(os);
     break;
   }
   return os;
}

///////////////////////////////////////////////////////////////////////////////
//parseExprOp:
//translating special Exprs to regular EXPR??
///////////////////////////////////////////////////////////////////////////////
Expr
TheoryRecords::parseExprOp(const Expr& e) {
  TRACE("parser", "TheoryRecords::parseExprOp(", e, ")");
  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  if(RAW_LIST != e.getKind()) return e;

  DebugAssert(e.arity() > 0,
	      "TheoryRecords::parseExprOp:\n e = "+e.toString());
  
  const Expr& c1 = e[0][0];
  const string& kindStr = c1.getString();
  int kind = e.getEM()->getKind(kindStr);
  switch(kind) {
  case RECORD_TYPE: // (RECORD_TYPE (f1 e1) (f2 e2) ...)
  case RECORD: {    // (RECORD      (f1 e1) (f2 e2) ...)
    if(e.arity() < 2)
      throw ParserException("Empty "+kindStr+": "+e.toString());
    vector<Expr> fields;
    vector<Expr> kids; 
    Expr::iterator i = e.begin(), iend=e.end();
    ++i;
    for(; i!=iend; ++i) {
      if(i->arity() != 2 || (*i)[0].getKind() != ID)
	throw ParserException("Bad field declaration in "+kindStr+": "
			      +i->toString()+"\n in "+e.toString());
      fields.push_back((*i)[0][0]);
      kids.push_back(parseExpr((*i)[1]));
    }
    return (kind==RECORD)? recordExpr(fields, kids)
      : recordType(fields, kids).getExpr();
  }
  case RECORD_SELECT: { // (RECORD_SELECT e field)
    if(e.arity() != 3 || e[2].getKind() != ID)
      throw ParserException("Field must be an ID in RECORD_SELECT: "
			    +e.toString());
    return recordSelect(parseExpr(e[1]), e[2][0].getString());
  }
  case RECORD_UPDATE: { // (RECORD_UPDATE e1 field e2)
    if(e.arity() != 4 || e[2].getKind() != ID)
      throw ParserException("Field must be an ID in RECORD_UPDATE: "
			    +e.toString());
    return recordUpdate(parseExpr(e[1]), e[2][0].getString(), parseExpr(e[3]));
  }
  case TUPLE_SELECT:  { // (TUPLE_SELECT e index)
    if(e.arity() != 3 || !e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("Index must be an integer in TUPLE_SELECT: "
			    +e.toString());
    return tupleSelect(parseExpr(e[1]), e[2].getRational().getInt());
  }
  case TUPLE_UPDATE:  { // (TUPLE_UPDATE e1 index e2)
    if(e.arity() != 4 || !e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("Index must be an integer in TUPLE_UPDATE: "
			    +e.toString());
    return tupleUpdate(parseExpr(e[1]), e[2].getRational().getInt(),
		       parseExpr(e[3]));
  }
  case TUPLE_TYPE:
  case TUPLE: {
    if(e.arity() < 2)
      throw ParserException("Empty "+kindStr+": "+e.toString());
    vector<Expr> k;
    Expr::iterator i = e.begin(), iend=e.end();
    // Skip first element of the vector of kids in 'e'.
    // The first element is the operator.
    ++i; 
    // Parse the kids of e and push them into the vector 'k'
    for(; i!=iend; ++i) 
      k.push_back(parseExpr(*i));
    return (kind==TUPLE)? tupleExpr(k) : tupleType(k).getExpr();
  }
  default:
    DebugAssert(false,
		"TheoryRecords::parseExprOp: invalid command or expression: " + e.toString());
    break;
  }
  return e;
}


//! Create a record literal
Expr
TheoryRecords::recordExpr(const std::vector<std::string>& fields,
			  const std::vector<Expr>& kids) {
  vector<Expr> fieldExprs;
  vector<string>::const_iterator i = fields.begin(), iend = fields.end();
  for (; i != iend; ++i) fieldExprs.push_back(getEM()->newStringExpr(*i));
  return recordExpr(fieldExprs, kids);
}

Expr
TheoryRecords::recordExpr(const std::vector<Expr>& fields,
			  const std::vector<Expr>& kids) {
  return Expr(Expr(RECORD, fields).mkOp(), kids);
}

//! Create a record type
Type
TheoryRecords::recordType(const std::vector<std::string>& fields,
			  const std::vector<Type>& types) {
  vector<Expr> kids;
  for(vector<Type>::const_iterator i=types.begin(), iend=types.end();
      i!=iend; ++i)
    kids.push_back(i->getExpr());
  return recordType(fields, kids);
}

//! Create a record type
Type
TheoryRecords::recordType(const std::vector<std::string>& fields,
			  const std::vector<Expr>& types) {
  vector<Expr> fieldExprs;
  vector<string>::const_iterator i = fields.begin(), iend = fields.end();
  for (; i != iend; ++i) fieldExprs.push_back(getEM()->newStringExpr(*i));
  return recordType(fieldExprs, types);
}

Type
TheoryRecords::recordType(const std::vector<Expr>& fields,
			  const std::vector<Expr>& types) {
  return Type(Expr(Expr(RECORD_TYPE, fields).mkOp(), types));
}

//! Create a record field selector expression
Expr
TheoryRecords::recordSelect(const Expr& r, const std::string& field) {
  return Expr(getEM()->newSymbolExpr(field, RECORD_SELECT).mkOp(), r);
}

//! Create a record field update expression
Expr
TheoryRecords::recordUpdate(const Expr& r, const std::string& field,
			    const Expr& val) {
  return Expr(getEM()->newSymbolExpr(field, RECORD_UPDATE).mkOp(), r, val);
}

//! Get the list of fields from a record literal
const vector<Expr>&
TheoryRecords::getFields(const Expr& r) {
  DebugAssert(r.isApply() &&
              (r.getOpKind() == RECORD || r.getOpKind() == RECORD_TYPE),
	      "TheoryRecords::getFields: Not a record literal: "
	      +r.toString(AST_LANG));
  return r.getOpExpr().getKids();
}

// Get the i-th field name from the record literal
const string&
TheoryRecords::getField(const Expr& r, int i) {
  DebugAssert(r.isApply() && 
              (r.getOpKind() == RECORD || r.getOpKind() == RECORD_TYPE),
	      "TheoryRecords::getField: Not a record literal: "
	      +r.toString());
  return r.getOpExpr()[i].getString();
}

// Get field index from the record literal
int
TheoryRecords::getFieldIndex(const Expr& e, const string& field) {
  const vector<Expr>& fields = getFields(e);
  for(size_t i=0, iend=fields.size(); i<iend; ++i) {
    if(fields[i].getString() == field) return i;
  }
  DebugAssert(false, "TheoryRecords::getFieldIndex(e="+e.toString()
	      +", field="+field+"): field is not found");
  return -1;
}

//! Get the field name from the record select and update expressions
const std::string&
TheoryRecords::getField(const Expr& r) {
  DebugAssert(r.isApply() && (r.getOpKind() == RECORD_SELECT ||
                              r.getOpKind() == RECORD_UPDATE),
	      "TheoryRecords::getField: Not a record literal: ");
  return r.getOpExpr().getName();
}

//! Create a tuple literal
Expr
TheoryRecords::tupleExpr(const std::vector<Expr>& kids) {
  return Expr(TUPLE, kids, getEM());
}

//! Create a tuple type
Type
TheoryRecords::tupleType(const std::vector<Type>& types) {
  vector<Expr> kids;
  for(vector<Type>::const_iterator i=types.begin(), iend=types.end();
      i!=iend; ++i)
    kids.push_back(i->getExpr());
  return Type(Expr(TUPLE_TYPE, kids, getEM()));
}

//! Create a tuple type
Type
TheoryRecords::tupleType(const std::vector<Expr>& types) {
  return Expr(TUPLE_TYPE, types, getEM());
}

//! Create a tuple index selector expression
Expr
TheoryRecords::tupleSelect(const Expr& tup, int i) {
  return Expr(Expr(TUPLE_SELECT, getEM()->newRatExpr(i)).mkOp(), tup);
}

//! Create a tuple index update expression
Expr
TheoryRecords::tupleUpdate(const Expr& tup, int i, const Expr& val) {
  return Expr(Expr(TUPLE_UPDATE, getEM()->newRatExpr(i)).mkOp(), tup, val);
}

//! Get the index from the tuple select and update expressions
int
TheoryRecords::getIndex(const Expr& r) {
  DebugAssert(r.isApply() && (r.getOpKind() == TUPLE_SELECT ||
                              r.getOpKind() == TUPLE_UPDATE),
	      "TheoryRecords::getField: Not a record literal: ");
  return r.getOpExpr()[0].getRational().getInt();
}
