/*****************************************************************************/
/*!
 * \file clause.cpp
 * \brief Implementation of class Clause
 * 
 * Author: Sergey Berezin
 * 
 * Created: Mon Apr 28 17:20:23 2003
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

#include "clause.h"
#include "theory_core.h"

using namespace std;

namespace CVC3 {

////////////////////////////////////////////////////////////////////////
//  class ClauseValue methods
////////////////////////////////////////////////////////////////////////

// Constructor: takes the main clause theorem which must be a
// disjunction of literals and have no assumptions.
ClauseValue::ClauseValue(TheoryCore* core, VariableManager* vm,
			 const Theorem& clause, int scope)
  : d_refcount(0), d_refcountOwner(0), d_thm(clause), d_scope(scope),
    // This backtrackable member is initialized in the first scope
    // (which is #0)
    d_sat(core->getCM()->getCurrentContext(), false, 0),
    d_deleted(false) {
  // Check the clause
  DebugAssert(clause.getExpr().isOr(), "Clause(): bad clause given: "
	      + clause.toString());
//   DebugAssert(clause.getExpr().arity()>0, "Clause(): empty clause: "
// 	      + clause.toString());
  // Initialize watched literals to the edges with directions
  // pointing outwards
  d_wp[0]=0; d_dir[0]=-1;
  d_wp[1] = clause.getExpr().arity()-1; d_dir[1]=1;
  // Initialize the literals
  Expr c(clause.getExpr());
  d_literals.reserve(c.arity());
  for(Expr::iterator i=c.begin(), iend=c.end(); i!=iend; ++i) {
    int val(i->isNot()? -1 : 1);
    Variable v(vm, (val < 0)? (*i)[0] : (*i));
    Literal l(v, val > 0);
    d_literals.push_back(l);
    // Update the literal's count for splitter heuristics
    l.count()++;
  }
  IF_DEBUG(d_sat.setName("CDO[Clause.d_sat]");)
}

ClauseValue::~ClauseValue() {
  TRACE_MSG("search literals", "~ClauseValue() {");
  FatalAssert(d_refcount == 0, "~ClauseValue: non-zero refcount: "
	       + int2string(d_refcount));
  if(!d_deleted) { // Update the literal counts for splitter heuristics
    for(vector<Literal>::iterator i=d_literals.begin(),
	  iend=d_literals.end(); i!=iend; ++i) {
      i->count()--;
      IF_DEBUG(if(i->count() == 0)
	       TRACE("search literals", "Null count for ", *i, "");)
    }
  }
  TRACE_MSG("search literals", "~ClauseValue() => }");
}
  
////////////////////////////////////////////////////////////////////////
//  class Clause methods
////////////////////////////////////////////////////////////////////////

// Destructor
Clause::~Clause() {
  if(d_clause != NULL) {
    FatalAssert(d_clause->d_refcount > 0,
		"~Clause: non-positive refcount: "
		+ int2string(d_clause->d_refcount));
    if(--(d_clause->d_refcount) == 0) delete d_clause;
  }
}


void
Clause::markDeleted() const {
  TRACE("search literals", "Clause::markDeleted(",
	CompactClause(*this), ") {");
  DebugAssert(!isNull(), "Clause::markDeleted()");
  if(!d_clause->d_deleted) {
    d_clause->d_deleted = true;
    // Update the literal counts for splitter heuristics
    for(vector<Literal>::iterator i=d_clause->d_literals.begin(),
	  iend=d_clause->d_literals.end(); i!=iend; ++i) {
      i->count()--;
      IF_DEBUG(if(i->count() == 0)
	       TRACE("search literals", "Null count for ", *i, "");)
    }
  }
  TRACE_MSG("search literals", "Clause::markDeleted => }");
}


// Assignment operator
Clause& Clause::operator=(const Clause& c) {
  if(&c == this) return *this; // Self-assignment
  if(d_clause != NULL) {
    DebugAssert(d_clause->d_refcount > 0,
		"Clause::operator=: non-positive refcount: "
		+ int2string(d_clause->d_refcount));
    if(--(d_clause->d_refcount) == 0) delete d_clause;
  }
  d_clause = c.d_clause;
  if(d_clause != NULL) d_clause->d_refcount++;
  return *this;
}

// Printing
string Clause::toString() const {
  std::ostringstream ss;
  ss << *this;
  return ss.str();
}

ostream& operator<<(ostream& os, const Clause& c) {
  if(c.isNull()) return os << "Clause[Null]";
  os << "Clause[";
  if(c.deleted()) os << "DELETED ";
  os << c.id();
  IF_DEBUG(if(c.getFile() != "")
	   os << ", " << c.getFile() << ":" << c.getLine();)
  os << "](" << c.getTheorem()
     << ";\n";
  if(c.wp(0) == c.wp(1)) os << "WARNING: wp[0] = wp[1]\n";
  for(unsigned i=0; i<c.size(); ++i) {
    if(c.wp(0) == i)
      os << "wp[0]" << ((c.dir(0) > 0)? "=>" : "<=") << " ";
    else if(c.wp(1) == i)
      os << "wp[1]" << ((c.dir(1) > 0)? "=>" : "<=") << " ";
    else
      os << "        ";
    os << c[i] << ";\n";
  }
  return os << ((c.sat())? "Clause is SAT" : "") << ")";
}
  
  static void printLit(ostream& os, const Literal& l) {
    if(l.isNegative()) os << "!";
    os << l.getVar().getExpr();
    int val(l.getValue());
    if(val != 0) os << "=" << val << "@" << l.getScope();
  }

ostream& operator<<(std::ostream& os, const CompactClause& c) {
  const vector<Literal>& lits = c.d_clause.getLiterals();
  int wp0(c.d_clause.wp(0)), wp1(c.d_clause.wp(1));
  int i=0, iend=c.d_clause.size();
  os << "Clause[";
  if(c.d_clause.deleted()) os << "*DELETED* ";
  if(c.d_clause.owners() > 0) os << "owned(" << c.d_clause.owners() << ") ";
  if(i!=iend) {
    if(i==wp0 || i==wp1) os << "*";
    printLit(os, lits[i]);  ++i; 
  }
  for(; i!=iend; ++i) {
    os << ", ";
    if(i==wp0 || i==wp1) os << "*";
    printLit(os, lits[i]);
  }
  os << "]";
  return os;
}

string CompactClause::toString() const {
  ostringstream ss;
  ss << (*this);
  return ss.str();
}

#ifdef _CVC3_DEBUG_MODE
bool CVC3::Clause::wpCheck() const
{
  if (sat(true))
    return true;
  return (getLiteral(wp(0)).getValue() == 0 && getLiteral(wp(1)).getValue() == 0);
}
#endif

} // end of namespace CVC3
