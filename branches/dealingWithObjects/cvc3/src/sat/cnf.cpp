/*****************************************************************************/
/*!
 *\file cnf.cpp
 *\brief Implementation of classes used for generic CNF formulas
 *
 * Author: Clark Barrett
 *
 * Created: Mon Dec 12 22:16:11 2005
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


#include "cnf.h"


using namespace std;
using namespace CVC3;
using namespace SAT;


unsigned SAT::Clause::getMaxVar() const
{
  unsigned max = 0;
  const_iterator i, iend;
  for (i = begin(), iend = end(); i != iend; ++i) {
    DebugAssert(!(*i).isNull(), "Null literal found in clause");
    if (unsigned((*i).getVar()) > max) max = unsigned((*i).getVar());
  }
  return max;
}


void SAT::Clause::print() const
{
  if (isSatisfied()) cout << "*";
  const_iterator i, iend;
  for (i = begin(), iend = end(); i != iend; ++i) {
    if ((*i).isNull()) cout << "NULL";
    else if ((*i).isFalse()) cout << "F";
    else if ((*i).isTrue()) cout << "T";
    else {
      if (!(*i).isPositive()) cout << "-";
      cout << (*i).getVar();
    }
    cout << " ";
  }
  cout << endl;
}


void CNF_Formula::copy(const CNF_Formula& cnf)
{
  setNumVars(0);
  Clause* c = d_current;
  // Don't use iterators in case cnf == *this
  unsigned i, iend;
  Clause::const_iterator j, jend;
  for (i = 0, iend = cnf.numClauses(); i != iend; ++i) {
    newClause();
    for (j = cnf[i].begin(), jend = cnf[i].end(); j != jend; ++j) {
      addLiteral(*j);
    }
    
    Clause oldClause = cnf[i];
    //    CVC3::Theorem clauseThm = oldClause.getClauseTheorem();
    CVC3::Theorem clauseThm = cnf[i].getClauseTheorem();
    getCurrentClause().setClauseTheorem(clauseThm);//by yeting
    
    if (cnf[i].isUnit()) registerUnit();
    if (&(cnf[i]) == cnf.d_current) c = d_current;
  }
  d_current = c;
}


void CNF_Formula::print() const
{
  const_iterator i, iend;
  for (i = begin(), iend = end(); i != iend; ++i) {
    (*i).print();
  }
}


const CNF_Formula& CNF_Formula::operator+=(const CNF_Formula& cnf)
{
  Clause* c = d_current;
  // Don't use iterators in case cnf == *this
  unsigned i, iend;
  Clause::const_iterator j, jend;
  for (i = 0, iend = cnf.numClauses(); i != iend; ++i) {
    newClause();
    for (j = cnf[i].begin(), jend = cnf[i].end(); j != jend; ++j) {
      addLiteral(*j);
    }

    Clause oldClause = cnf[i];
    CVC3::Theorem clauseThm = oldClause.getClauseTheorem();
    getCurrentClause().setClauseTheorem(clauseThm);//by yeting

    if (cnf[i].isUnit()) registerUnit();
  }
  d_current = c;
  return *this;
}


const CNF_Formula& CNF_Formula::operator+=(const Clause& c)
{
  Clause* cur = d_current;
  newClause();
  Clause::const_iterator j, jend;
  for (j=c.begin(), jend = c.end(); j != jend; ++j) {
    addLiteral(*j);
  }

  Clause oldClause = c;
  CVC3::Theorem clauseThm = oldClause.getClauseTheorem();
  getCurrentClause().setClauseTheorem(clauseThm);//by yeting
    

  if (c.isUnit()) registerUnit();
  d_current = cur; 
  return *this;
}


void CNF_Formula_Impl::newClause()
{
  d_formula.resize(d_formula.size()+1);
  d_current = &(d_formula.back());
}


void CNF_Formula_Impl::registerUnit()
{
  DebugAssert(d_current->size()==1,"Expected unit clause");
  d_current->setUnit();
  Lit l = *(d_current->begin());
  d_lits[l.getID()] = true;
}


void CNF_Formula_Impl::simplify()
{
  deque<Clause>::iterator i, iend;
  Clause::const_iterator j, jend;
  for (i = d_formula.begin(), iend = d_formula.end(); i != iend; ++i) {
    if ((*i).isUnit()) continue;
    for (j=(*i).begin(), jend = (*i).end(); j != jend; ++j) {
      if ((*j).isTrue()) {
        (*i).setSatisfied();
        break;
      }
      hash_map<int, bool>::iterator it = d_lits.find((*j).getID());
      if (it != d_lits.end()) {
        (*i).setSatisfied();
        break;
      }
    }
  }
}


void CNF_Formula_Impl::reset()
{
  d_formula.clear();
  d_lits.clear();
  d_current = NULL;
  d_numVars = 0;
}


void CD_CNF_Formula::newClause()
{
  //TODO: don't call constructor twice
  d_current = &(d_formula.push_back(Clause()));
}


void CD_CNF_Formula::registerUnit()
{
  DebugAssert(d_current->size()==1,"Expected unit clause");
  d_current->setUnit();
}


