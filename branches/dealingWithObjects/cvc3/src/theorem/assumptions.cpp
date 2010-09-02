/*****************************************************************************/
/*!
 *\file assumptions.cpp
 *\brief Implementation of class Assumptions
 *
 * Author: Clark Barrett
 *
 * Created: Thu Jan  5 06:25:52 2006
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


#include <algorithm>
#include "assumptions.h"


using namespace std;
using namespace CVC3;


Assumptions Assumptions::s_empty;


const Theorem& Assumptions::findTheorem(const Expr& e) const {
  static Theorem null;

  //  TRACE_MSG("assumptions", "findTheorem");

  const Theorem& t = find(e);
  if (!t.isNull()) return t;
  // recurse
  const vector<Theorem>::const_iterator aend = d_vector.end();
  for (vector<Theorem>::const_iterator iter2 = d_vector.begin(); 
       iter2 != aend; ++iter2) {
    if (iter2->isRefl() || !iter2->isFlagged()) {
      if (compare(*iter2, e) == 0) return *iter2;
      if (!iter2->isAssump()) {
        const Theorem& t = iter2->getAssumptionsRef().findTheorem(e);
        if (!t.isNull()) return t;
      }
      if (!iter2->isRefl()) iter2->setFlag();
    }
  }
  return null; // not found
}


bool Assumptions::findExpr(const Assumptions& a,
                           const Expr& e, vector<Theorem>& gamma) {
  bool found = false;
  const Assumptions::iterator aend = a.end();
  Assumptions::iterator iter = a.begin();
  for (; iter != aend; ++iter) { 
    if (iter->isRefl()) continue;
    if (iter->isFlagged()) {
      if (iter->getCachedValue()) found = true;
    }
    else {
      if ((iter->getExpr() == e) || 
	  (!iter->isAssump() && 
	   findExpr(iter->getAssumptionsRef(), e, gamma))) {
	found = true;
	iter->setCachedValue(true);
      }
      else iter->setCachedValue(false);

      iter->setFlag();
    } 
  }

  if (found) {
    for (iter = a.begin(); iter != aend; ++iter) {
      if (iter->isRefl()) continue;
      if (!iter->getCachedValue()) gamma.push_back(*iter);
    }
  }

  return found;
}


bool Assumptions::findExprs(const Assumptions& a, const vector<Expr>& es, 
                            vector<Theorem>& gamma) {
  bool found = false;
  const vector<Expr>::const_iterator esbegin = es.begin();
  const vector<Expr>::const_iterator esend = es.end();
  const Assumptions::iterator aend = a.end();
  Assumptions::iterator iter = a.begin();
  for (; iter != aend; ++iter) {
    if (iter->isRefl()) continue;
    else if (iter->isFlagged()) {
      if (iter->getCachedValue()) found = true;
    }
    else {
      // switch to binary search below? (sort es first)
      if ((::find(esbegin, esend, iter->getExpr()) != esend) ||
	  (!iter->isAssump() && 
	   findExprs(iter->getAssumptionsRef(), es, gamma))) {
	found = true;
	iter->setCachedValue(true);
      }
      else iter->setCachedValue(false);

      iter->setFlag();
    }
  }
  if (found) {
    for (iter = a.begin(); iter != aend; ++iter) {     
      if (iter->isRefl()) continue;
      if (!iter->getCachedValue()) gamma.push_back(*iter);
    }
  }
  return found;
}


Assumptions::Assumptions(const vector<Theorem>& v) {
  if (v.empty()) return;
  d_vector.reserve(v.size());

  const vector<Theorem>::const_iterator iend = v.end();
  vector<Theorem>::const_iterator i = v.begin();

  for (;i != iend; ++i) {
    if ((!i->getAssumptionsRef().empty())) {
      d_vector.push_back(*i);
    }
  }

  if (d_vector.size() <= 1) return;
  sort(d_vector.begin(), d_vector.end());
  vector<Theorem>::iterator newend =
    unique(d_vector.begin(), d_vector.end(), Theorem::TheoremEq);

  d_vector.resize(newend - d_vector.begin());
}


Assumptions::Assumptions(const Theorem& t1, const Theorem& t2)
{
    
  if (!t1.getAssumptionsRef().empty()) {
    if (!t2.getAssumptionsRef().empty()) {
      switch(compare(t1, t2)) {
        case -1: // t1 < t2:
          d_vector.push_back(t1);
          d_vector.push_back(t2);
          break;
        case 0: // t1 == t2:
          d_vector.push_back(t1);
          break;
        case 1: // t1 > t2:
          d_vector.push_back(t2);
          d_vector.push_back(t1);
          break;
      }
    } else d_vector.push_back(t1);
  } else if (!t2.getAssumptionsRef().empty()) {
    d_vector.push_back(t2);
  }
  
  /*
  switch(compare(t1, t2)) {
  case -1: // t1 < t2:
    d_vector.push_back(t1);
    d_vector.push_back(t2);
    break;
  case 0: // t1 == t2:
    d_vector.push_back(t1);
    break;
  case 1: // t1 > t2:
    d_vector.push_back(t2);
    d_vector.push_back(t1);
    break;
  }
  */
}


void Assumptions::add(const Theorem& t)
{
  if (t.getAssumptionsRef().empty()) return;
  vector<Theorem>::iterator iter, iend = d_vector.end();
  iter = lower_bound(d_vector.begin(), iend, t);
  if (iter != iend && compare(t, *iter) == 0) return;
  d_vector.insert(iter, t);
}


void Assumptions::add(const std::vector<Theorem>& thms)
{
  if (thms.size() == 0) return;

IF_DEBUG(
  vector<Theorem>::const_iterator iend = thms.end();
  for (vector<Theorem>::const_iterator i = thms.begin(); 
       i != iend; ++i) {
    if (i+1 == iend) break;
    DebugAssert(compare(*i, *(i+1)) == -1, "Expected sorted");
  }
)
  vector<Theorem> v;
  v.reserve(d_vector.size()+thms.size());

  vector<Theorem>::const_iterator i = d_vector.begin();
  vector<Theorem>::const_iterator j = thms.begin();
  const vector<Theorem>::const_iterator v1end = d_vector.end();
  const vector<Theorem>::const_iterator v2end = thms.end();

  // merge
  while (i != v1end && j != v2end) {
    if (j->getAssumptionsRef().empty()) {
      ++j;
      continue;
    }
    switch(compare(*i, *j)) {
      case 0:
        // copy only 1, drop down to next case
        ++j;
      case -1: // <
        v.push_back(*i);
        ++i;
        break;
      default: // >
        v.push_back(*j);
        ++j;
    };
  }
  // Push in the remaining elements
  for(; i != v1end; ++i) v.push_back(*i);
  for(; j != v2end; ++j) {
    if (!j->getAssumptionsRef().empty())
      v.push_back(*j);
  }

  d_vector.swap(v);
}


string Assumptions::toString() const {
  ostringstream ss;
  ss << (*this);
  return ss.str();
}


void Assumptions::print() const
{
  cout << toString() << endl;
}
      

const Theorem& Assumptions::operator[](const Expr& e) const {
  if (!d_vector.empty()) {
    d_vector.front().clearAllFlags();
  }
  return findTheorem(e);
}


const Theorem& Assumptions::find(const Expr& e) const {
  static Theorem null;
  //    binary search
  int lo = 0; 
  int hi = d_vector.size() - 1;
  int loc;
  while (lo <= hi) {
    loc = (lo + hi) / 2;
 
    switch (compare(d_vector[loc], e)) {
      case 0: return d_vector[loc];
      case -1: // t < e
        lo = loc + 1;
        break;
      default: // t > e
        hi = loc - 1;
    };
  }
  return null;
}


////////////////////////////////////////////////////////////////////
// Assumptions friend methods
////////////////////////////////////////////////////////////////////


namespace CVC3 {


Assumptions operator-(const Assumptions& a, const Expr& e) {
  if (a.begin() != a.end()) {
    a.begin()->clearAllFlags();
    vector<Theorem> gamma;
    if (Assumptions::findExpr(a, e, gamma)) return Assumptions(gamma);
  } 
  return a;
}


Assumptions operator-(const Assumptions& a, const vector<Expr>& es) {
  if (!es.empty() && a.begin() != a.end()) {
    a.begin()->clearAllFlags();
    vector<Theorem> gamma;
    if (Assumptions::findExprs(a, es, gamma)) return Assumptions(gamma);
  }
  return a;
}


ostream& operator<<(ostream& os, const Assumptions &assump) {
  vector<Theorem>::const_iterator i = assump.d_vector.begin();
  const vector<Theorem>::const_iterator iend = assump.d_vector.end();
  if(i != iend) { os << i->getExpr(); i++; }
  for(; i != iend; i++) os << ",\n " << i->getExpr();
  return os;
}


} // end of namespace CVC3
