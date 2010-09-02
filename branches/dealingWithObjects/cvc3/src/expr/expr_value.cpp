/*****************************************************************************/
/*!
 * \file expr_value.cpp
 * 
 * Author: Sergey Berezin
 * 
 * Created: Fri Feb  7 22:29:04 2003
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

#include "expr_value.h"
#include "notifylist.h"

using namespace std;

namespace CVC3 {

////////////////////////////////////////////////////////////////////////
// Class ExprValue static members
////////////////////////////////////////////////////////////////////////

std::hash<char*> ExprValue::s_charHash;
std::hash<long int> ExprValue::s_intHash;

////////////////////////////////////////////////////////////////////////
// Class ExprValue methods
////////////////////////////////////////////////////////////////////////


// Destructor
ExprValue::~ExprValue() {
  // Be careful deleting the attributes: first set them to NULL, then
  // delete, to avoid circular destructor calls
  if (d_find) {
    CDO<Theorem>* find = d_find;
    d_find = NULL;
    delete find;
    free(find);
  }
  if (d_eqNext) {
    CDO<Theorem>* eqNext = d_eqNext;
    d_eqNext = NULL;
    delete eqNext;
    free(eqNext);
  }
  if(d_notifyList != NULL) {
    NotifyList* nl = d_notifyList;
    d_notifyList = NULL;
    delete nl;
  }
  // Set all smart pointers to Null
  d_type = Type();
  d_simpCache=Theorem();
  //  d_simpFrom=Expr();
}

// Equality between any two ExprValue objects (including subclasses)
bool ExprValue::operator==(const ExprValue& ev2) const {
  DebugAssert(getMMIndex() == EXPR_VALUE,
	      "ExprValue::operator==() called from a subclass");
  if(getMMIndex() != ev2.getMMIndex())
    return false;

  return (d_kind == ev2.d_kind);
}


ExprValue* ExprValue::copy(ExprManager* em, ExprIndex idx) const {
  DebugAssert(getMMIndex() == EXPR_VALUE,
	      "ExprValue::copy() called from a subclass");
  return new(em->getMM(EXPR_VALUE)) ExprValue(em, d_kind, idx);
}


bool ExprNodeTmp::operator==(const ExprValue& ev2) const {
  return getMMIndex() == ev2.getMMIndex() &&
    d_kind == ev2.getKind() &&
    getKids() == ev2.getKids();
}

ExprValue* ExprNodeTmp::copy(ExprManager* em, ExprIndex idx) const {
  if (d_em != em) {
    vector<Expr> children;
    vector<Expr>::const_iterator
      i = d_children.begin(), iend = d_children.end();
    for (; i != iend; ++i)
      children.push_back(rebuild(*i, em));
    return new(em->getMM(getMMIndex())) ExprNode(em, d_kind, children, idx);
  }
  return new(em->getMM(getMMIndex())) ExprNode(em, d_kind, d_children, idx);
}


ExprNode::~ExprNode()
{
  // Be careful deleting the attributes: first set them to NULL, then
  // delete, to avoid circular destructor calls
  if (d_sig) {
    CDO<Theorem>* sig = d_sig;
    d_sig = NULL;
    delete sig;
    free(sig);
  }
  if (d_rep) {
    CDO<Theorem>* rep = d_rep;
    d_rep = NULL;
    delete rep;
    free(rep);
  }
}


bool ExprNode::operator==(const ExprValue& ev2) const {
  if(getMMIndex() != ev2.getMMIndex())
    return false;

  return (d_kind == ev2.getKind())
    && (getKids() == ev2.getKids());
}

ExprValue* ExprNode::copy(ExprManager* em, ExprIndex idx) const {
  if (d_em != em) {
    vector<Expr> children;
    vector<Expr>::const_iterator
      i = d_children.begin(), iend = d_children.end();
    for (; i != iend; ++i)
      children.push_back(rebuild(*i, em));
    return new(em->getMM(getMMIndex())) ExprNode(em, d_kind, children, idx);
  }
  return new(em->getMM(getMMIndex())) ExprNode(em, d_kind, d_children, idx);
}


bool ExprString::operator==(const ExprValue& ev2) const {
  if(getMMIndex() != ev2.getMMIndex())
    return false;

  return (getString() == ev2.getString());
}

ExprValue* ExprString::copy(ExprManager* em, ExprIndex idx) const {
  return new(em->getMM(getMMIndex())) ExprString(em, d_str, idx);
}


bool ExprSkolem::operator==(const ExprValue& ev2) const {
  if(getMMIndex() != ev2.getMMIndex())
    return false;

  return (getBoundIndex() == ev2.getBoundIndex()
	  && getExistential() == ev2.getExistential());
}

ExprValue* ExprSkolem::copy(ExprManager* em, ExprIndex idx) const {
  if (d_em != em) {
    return new(em->getMM(getMMIndex()))
      ExprSkolem(em, getBoundIndex(), rebuild(getExistential(), em), idx);
  }
  return new(em->getMM(getMMIndex()))
    ExprSkolem(em, getBoundIndex(), getExistential(), idx);
}


bool ExprRational::operator==(const ExprValue& ev2) const {
  if(getMMIndex() != ev2.getMMIndex())
    return false;

  return (getRational() == ev2.getRational());
}

ExprValue* ExprRational::copy(ExprManager* em, ExprIndex idx) const {
  return new(em->getMM(getMMIndex())) ExprRational(em, d_r, idx);
}


bool ExprVar::operator==(const ExprValue& ev2) const {
  if(getMMIndex() != ev2.getMMIndex())
    return false;

  return (getKind() == ev2.getKind() && getName() == ev2.getName());
}

ExprValue* ExprVar::copy(ExprManager* em, ExprIndex idx) const {
  return new(em->getMM(getMMIndex())) ExprVar(em, d_name, idx);
}


bool ExprSymbol::operator==(const ExprValue& ev2) const {
  if(getMMIndex() != ev2.getMMIndex())
    return false;

  return (getKind() == ev2.getKind() && getName() == ev2.getName());
}

ExprValue* ExprSymbol::copy(ExprManager* em, ExprIndex idx) const {
  return new(em->getMM(getMMIndex())) ExprSymbol(em, d_kind, d_name, idx);
}


bool ExprBoundVar::operator==(const ExprValue& ev2) const {
  if(getMMIndex() != ev2.getMMIndex())
    return false;

  return (getKind() == ev2.getKind() && getName() == ev2.getName()
	  && getUid() == ev2.getUid());
}

ExprValue* ExprBoundVar::copy(ExprManager* em, ExprIndex idx) const {
  return new(em->getMM(getMMIndex())) ExprBoundVar(em, d_name, d_uid, idx);
}


bool ExprApply::operator==(const ExprValue& ev2) const {
  if(getMMIndex() != ev2.getMMIndex())
    return false;

  return (getOp() == ev2.getOp())
      && (getKids() == ev2.getKids());
}

ExprValue* ExprApply::copy(ExprManager* em, ExprIndex idx) const {
  if (d_em != em) {
    vector<Expr> children;
    vector<Expr>::const_iterator
      i = d_children.begin(), iend = d_children.end();
    for (; i != iend; ++i)
      children.push_back(rebuild(*i, em));
    return new(em->getMM(getMMIndex()))
      ExprApply(em, Op(rebuild(d_opExpr, em)), children, idx);
  }
  return new(em->getMM(getMMIndex()))
    ExprApply(em, Op(d_opExpr), d_children, idx);
}


bool ExprApplyTmp::operator==(const ExprValue& ev2) const {
  if(getMMIndex() != ev2.getMMIndex())
    return false;

  return (getOp() == ev2.getOp())
      && (getKids() == ev2.getKids());
}

ExprValue* ExprApplyTmp::copy(ExprManager* em, ExprIndex idx) const {
  if (d_em != em) {
    vector<Expr> children;
    vector<Expr>::const_iterator
      i = d_children.begin(), iend = d_children.end();
    for (; i != iend; ++i)
      children.push_back(rebuild(*i, em));
    return new(em->getMM(getMMIndex()))
      ExprApply(em, Op(rebuild(d_opExpr, em)), children, idx);
  }
  return new(em->getMM(getMMIndex()))
    ExprApply(em, Op(d_opExpr), d_children, idx);
}


bool ExprClosure::operator==(const ExprValue& ev2) const {
  if(getMMIndex() != ev2.getMMIndex())
    return false;

  return (getKind() == ev2.getKind())
      && (getBody() == ev2.getBody())
      && (getVars() == ev2.getVars());
}

ExprValue* ExprClosure::copy(ExprManager* em, ExprIndex idx) const {
  if (d_em != em) {
    vector<Expr> vars;
    vector<Expr>::const_iterator i = d_vars.begin(), iend = d_vars.end();
    for (; i != iend; ++i)
      vars.push_back(rebuild(*i, em));

    vector<vector<Expr> > manual_trigs;
    vector<vector<Expr> >::const_iterator j = d_manual_triggers.begin(), jend = d_manual_triggers.end();
    for (; j != jend; ++j) {
      vector<Expr >::const_iterator k = j->begin(), kend = j->end();
      vector<Expr> cur_trig;
      for (; k != kend; ++k){
	cur_trig.push_back(rebuild(*k,em));
      }
      //      manual_trigs.push_back(rebuild(*j, em));
      manual_trigs.push_back(cur_trig);
    }

    return new(em->getMM(getMMIndex()))
      ExprClosure(em, d_kind, vars, rebuild(d_body, em), manual_trigs, idx);
  }
  return new(em->getMM(getMMIndex()))
    ExprClosure(em, d_kind, d_vars, d_body, d_manual_triggers, idx);
}


////////////////////////////////////////////////////////////////////////
// Methods of subclasses of ExprValue
////////////////////////////////////////////////////////////////////////

// Hash function for subclasses with kids.
size_t ExprValue::hash(const int kind, const std::vector<Expr>& kids) {
  size_t res(s_intHash((long int)kind));
  for(std::vector<Expr>::const_iterator i=kids.begin(), iend=kids.end();
      i!=iend; ++i) {
    void* ptr = i->d_expr;
    res = res*PRIME + pointerHash(ptr);
  }
  return res;
}


// Size function for subclasses with kids.
Unsigned ExprValue::sizeWithChildren(const std::vector<Expr>& kids)
{
  Unsigned res = 1;
  for(vector<Expr>::const_iterator i=kids.begin(), iend=kids.end();
      i!=iend; ++i) {
    res += (*i).d_expr->getSize();
  }
  return res;
}


size_t ExprClosure::computeHash() const {
  return d_body.hash()*PRIME + ExprValue::hash(d_kind, d_vars);
}


} // end of namespace CVC3
