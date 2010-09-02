/*****************************************************************************/
/*!
 * \file variable.cpp
 * \brief Implementation of class Variable; see variable.h for detail.
 * 
 * Author: Sergey Berezin
 * 
 * Created: Fri Apr 25 12:30:17 2003
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

#include <sstream>
#include "variable.h"
#include "search_rules.h"
#include "memory_manager_chunks.h"
#include "memory_manager_malloc.h"

using namespace std;

namespace CVC3 {

///////////////////////////////////////////////////////////////////////
// class Variable methods
///////////////////////////////////////////////////////////////////////

// Constructors
Variable::Variable(VariableManager* vm, const Expr& e)
  : d_val(vm->newVariableValue(e))
{
  d_val->d_refcount++;
}

Variable::Variable(const Variable& l): d_val(l.d_val) {
  if(!isNull()) d_val->d_refcount++;
}

  // Destructor
Variable::~Variable() {
  if(!isNull()) {
    if(--(d_val->d_refcount) == 0)
      d_val->d_vm->gc(d_val);
  }
}

  // Assignment
Variable&
Variable::operator=(const Variable& l) {
  if(&l == this) return *this; // Self-assignment
  if(!isNull()) {
    if(--(d_val->d_refcount) == 0) d_val->d_vm->gc(d_val);
  }
  d_val = l.d_val;
  if(!isNull()) d_val->d_refcount++;
  return *this;
}

const Expr&
Variable::getExpr() const {
  static Expr null;
  if(isNull()) return null;
  return d_val->getExpr();
}

const Expr&
Variable::getNegExpr() const {
  static Expr null;
  if(isNull()) return null;
  return d_val->getNegExpr();
}

// IMPORTANT: Value can be -1 (false), 1 (true), or 0 (unresolved)
int
Variable::getValue() const {
  if(isNull()) return 0;
  return d_val->getValue();
}


int
Variable::getScope() const {
  if(isNull()) return 0;
  return d_val->getScope();
}

const Theorem&
Variable::getTheorem() const {
  static Theorem null;
  if(isNull()) return null;
  return d_val->getTheorem();
}

const Clause&
Variable::getAntecedent() const {
  static Clause null;
  if(isNull()) return null;
  return d_val->getAntecedent();
}

int
Variable::getAntecedentIdx() const {
  if(isNull()) return 0;
  return d_val->getAntecedentIdx();
}

const Theorem&
Variable::getAssumpThm() const {
  static Theorem null;
  if(isNull()) return null;
  return d_val->getAssumpThm();
}

// Setting the attributes: it can be either derived from the
// antecedent clause, or by a theorem.  The scope level is set to
// the current scope.
void
Variable::setValue(int val, const Clause& c, int idx) {
  DebugAssert(!isNull(), "Variable::setValue(antecedent): var is NULL");
  d_val->setValue(val, c, idx);
}

// The theorem's expr must be the same as the variable's expr or
// its negation
void
Variable::setValue(const Theorem& thm) {
  DebugAssert(!isNull(), "Variable::setValue(Theorem): var is NULL");
  d_val->setValue(thm, thm.getScope());
}

void
Variable::setValue(const Theorem& thm, int scope) {
  DebugAssert(!isNull(), "Variable::setValue(Theorem,scope): var is NULL");
  d_val->setValue(thm, scope);
}

void
Variable::setAssumpThm(const Theorem& a, int scope) {
  DebugAssert(!isNull(), "Variable::setAssumpThm(): var is NULL");
  d_val->setAssumpThm(a, scope);
}
  
  // Derive the theorem for either the variable or its negation.  If
  // the value is set by a theorem, that theorem is returned;
  // otherwise a unit propagation rule is applied to the antecedent
  // clause, and the theorem is cached for a quick access later.
Theorem
Variable::deriveTheorem() const {
  return deriveThmRec(false);
}


Theorem
Variable::deriveThmRec(bool checkAssump) const {
  DebugAssert(!isNull(), "Variable::deriveTheorem(): called on Null");
  DebugAssert(getValue() != 0, "Variable::deriveTheorem(): value is not set: "
	      + toString());
  if(!getTheorem().isNull()) return getTheorem();
  if(checkAssump && !getAssumpThm().isNull()) return getAssumpThm();
  // Have to derive the theorem
  Clause c(getAntecedent());
  int idx(getAntecedentIdx());
  const vector<Literal>& lits = c.getLiterals();
  // Theorems for the other literals in the antecedent clause
  vector<Theorem> thms;
  int size(lits.size());
  // Derive theorems recursively
  for(int i=0; i<size; ++i)
    if(i!=idx) thms.push_back(lits[i].getVar().deriveThmRec(true));
  Theorem thm;
  if(idx!=-1)
    thm = d_val->d_vm->getRules()->unitProp(thms, c.getTheorem(), idx);
  else
    thm = d_val->d_vm->getRules()->conflictRule(thms, c.getTheorem());
  
  IF_DEBUG(Expr e(thm.getExpr());)
  DebugAssert(e == getExpr()
	      || (e.isNot() && e[0] == getExpr()),
	      "Variable::deriveTheorem: bad theorem derived: expr ="
	      + toString() + ", thm = " + thm.toString());
  // Cache the result
  d_val->setValue(thm, getScope());
  return thm;
}

string
Variable::toString() const {
  ostringstream ss;
  ss << *this;
  return ss.str();
}

// Friend methods
ostream& operator<<(ostream& os, const Variable& l) {
  return os << (*l.d_val);
}

///////////////////////////////////////////////////////////////////////
// class Literal methods
///////////////////////////////////////////////////////////////////////

string
Literal::toString() const {
  ostringstream ss;
  ss << *this;
  return ss.str();
}

ostream& operator<<(ostream& os, const Literal& l) {
  os << "Lit(" << (l.isNegative()? "!" : "")
     << l.getVar();
  // Attributes
  os << ", count=" << l.count() << ", score=" << l.score();
  return os << ")";
}

///////////////////////////////////////////////////////////////////////
// class VariableValue methods
///////////////////////////////////////////////////////////////////////

// Destructor
VariableValue::~VariableValue() {
  if(d_val!=NULL) { delete d_val; free(d_val); d_val = NULL; }
  if(d_scope!=NULL) { delete d_scope; free(d_scope); d_scope = NULL; }
  if(d_thm!=NULL) { delete d_thm; free(d_thm); d_thm = NULL; }
  if(d_ante!=NULL) { delete d_ante; free(d_ante); d_ante = NULL; }
  if(d_anteIdx!=NULL) { delete d_anteIdx; free(d_anteIdx); d_anteIdx = NULL; }
  if(d_assump!=NULL) { delete d_assump; free(d_assump); d_assump = NULL; }
}

  // Setting the attributes: it can be either derived from the
  // antecedent clause, or by a theorem
void
VariableValue::setValue(int val, const Clause& c, int idx) {
  if(d_val==NULL) {
    // Make sure d_val==0 all the way to scope 0
    d_val = new(true) CDO<int>(d_vm->getCM()->getCurrentContext(), 0, 0);
    IF_DEBUG(d_val->setName("CDO[VariableValue::d_val]");)
  }
  if(d_scope==NULL) {
    d_scope = new(true) CDO<int>(d_vm->getCM()->getCurrentContext());
    IF_DEBUG(d_scope->setName("CDO[VariableValue::d_scope]");)
  }
  if(d_ante==NULL) {
    d_ante = new(true) CDO<Clause>(d_vm->getCM()->getCurrentContext());
    IF_DEBUG(d_ante->setName("CDO[VariableValue::d_ante]");)
  }
  if(d_anteIdx==NULL) {
    d_anteIdx = new(true) CDO<int>(d_vm->getCM()->getCurrentContext());
    IF_DEBUG(d_anteIdx->setName("CDO[VariableValue::d_anteIdx]");)
  }

  // Compute the scope from the antecedent clause
  // Assume the clause is valid exactly at the bottom scope
  int scope(c.getScope());
  for(int i=0, iend=c.size(); i!=iend; ++i) {
    if(i!=idx) {
      int s(c[i].getScope());
      if(s > scope) scope = s;
      DebugAssert(c[i].getValue() != 0,
		  "VariableValue::setValue(ante): literal has no value: "
		  "i="+int2string(i)+" in\n clause = "
		  +c.toString());
    }
  }

  d_val->set(val, scope);
  d_scope->set(scope, scope); // d_vm->getCM()->scopeLevel();
  d_ante->set(c, scope);
  d_anteIdx->set(idx, scope);
  // Set the theorem to null, to clean up the old value
  if(!getTheorem().isNull()) d_thm->set(Theorem(), scope);

  IF_DEBUG(Expr l((idx == -1)? getExpr().getEM()->falseExpr()
		  : c[idx].getExpr());)
  DebugAssert((val > 0 && l == getExpr())
	      || (val < 0 && l.isNot() && l[0] == getExpr()),
	      "VariableValue::setValue(val = " + int2string(val)
	      + ", c = " + c.toString() + ", idx = " + int2string(idx)
	      + "):\n expr = " + getExpr().toString()
	      + "\n literal = " + l.toString());
}

// The theorem's expr must be the same as the variable's expr or
// its negation
void
VariableValue::setValue(const Theorem& thm, int scope) {
  if(d_val==NULL) {
    // Make sure d_val==0 all the way to scope 0
    d_val = new(true) CDO<int>(d_vm->getCM()->getCurrentContext(),0,0);
    IF_DEBUG(d_val->setName("CDO[VariableValue::d_val]");)
  }
  if(d_scope==NULL) {
    d_scope = new(true) CDO<int>(d_vm->getCM()->getCurrentContext());
    IF_DEBUG(d_scope->setName("CDO[VariableValue::d_scope]");)
  }
  if(d_thm==NULL) {
    d_thm = new(true) CDO<Theorem>(d_vm->getCM()->getCurrentContext());
    IF_DEBUG(d_thm->setName("CDO[VariableValue::d_thm]");)
  }

  Expr e(thm.getExpr());
  int val(0);
  if(e == d_expr) val = 1;
  else {
    DebugAssert(e.isNot() && e[0] == d_expr,
		"VariableValue::setValue(thm = "
		+ thm.toString() + "): expr = " + d_expr.toString());
    val = -1;
  }
  // Set the values on that scope
  d_val->set(val, scope);
  d_scope->set(scope, scope); // d_vm->getCM()->scopeLevel();
  d_thm->set(thm, scope);
  // Set clause to null, to clean up the old value
  if(!getAntecedent().isNull()) d_ante->set(Clause(), scope);
}

void
VariableValue::setAssumpThm(const Theorem& thm, int scope) {
  if(d_assump==NULL) {
    // Make sure d_val==0 all the way to scope 0
    d_assump = new(true) CDO<Theorem>(d_vm->getCM()->getCurrentContext());
    IF_DEBUG(d_val->setName("CDO[VariableValue::d_val]");)
  }
  d_assump->set(thm, scope);
}

ostream& operator<<(ostream& os, const VariableValue& v) {
  os << "Var(" << v.getExpr() << " = " << v.getValue();
  if(v.getValue() != 0) {
    os << " @ " << v.getScope();
    if(!v.getTheorem().isNull())
      os << "; " << v.getTheorem();
    else if(!v.getAntecedent().isNull()) {
      os << "; #" << v.getAntecedentIdx()
	 << " in " << CompactClause(v.getAntecedent());
    }
  }
  return os << ")";
}

///////////////////////////////////////////////////////////////////////
// class VariableManager methods
///////////////////////////////////////////////////////////////////////

// Creating unique VariableValue
VariableValue*
VariableManager::newVariableValue(const Expr& e) {
  VariableValue vv(this, e);
  VariableValueSet::iterator i(d_varSet.find(&vv)), iend(d_varSet.end());
  if(i != iend) return (*i);
  // No such variable, create and insert one
  VariableValue* p_vv(new(d_mm) VariableValue(this, e));
  d_varSet.insert(p_vv);
  return p_vv;
}

// Constructor
VariableManager::VariableManager(ContextManager* cm, SearchEngineRules* rules,
				 const string& mmFlag)
  : d_cm(cm), d_rules(rules), d_disableGC(false), d_postponeGC(false) {
  if(mmFlag == "chunks")
    d_mm = new MemoryManagerChunks(sizeof(VariableValue));
  else
    d_mm = new MemoryManagerMalloc();

  d_notifyObj = new VariableManagerNotifyObj(this, d_cm->getCurrentContext());
}

// Destructor
VariableManager::~VariableManager() {
  delete d_notifyObj;
  // Delete the remaining variables
  d_disableGC = true;
  vector<VariableValue*> vars;
  for(VariableValueSet::iterator i=d_varSet.begin(), iend=d_varSet.end();
      i!=iend; ++i) {
    vars.push_back(*i);
    // delete(*i);
    // No need to free memory; we'll delete the entire d_mm
    // d_mm->deleteData(*i);
  }
  d_varSet.clear();
  for(vector<VariableValue*>::iterator i=vars.begin(), iend=vars.end();
      i!=iend; ++i) delete *i;
  delete d_mm;
}

// Garbage collect VariableValue pointer
void
VariableManager::gc(VariableValue* v) {
  if(!d_disableGC) {
    d_varSet.erase(v);
    if(d_postponeGC) d_deleted.push_back(v);
    else {
      delete v;
      d_mm->deleteData(v);
    }
  }
}


void
VariableManager::resumeGC() {
  d_postponeGC = false;
  while(d_deleted.size() > 0) {
    VariableValue* v = d_deleted.back();
    d_deleted.pop_back();
    delete v;
    d_mm->deleteData(v);
  }
}

} // end of namespace CVC3
