/*****************************************************************************/
/*!
 * \file theorem.cpp
 * 
 * Author: Sergey Berezin
 * 
 * Created: Dec 10 00:37:49 GMT 2002
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
// CLASS: Theorem
//
// AUTHOR: Sergey Berezin, 07/05/02
//
// See theorem.h file for more information.
///////////////////////////////////////////////////////////////////////////////

#include "theorem.h"
#include "theorem_value.h"
#include "command_line_flags.h"

namespace CVC3 {
  using namespace std;

  //! Compare Theorems by their expressions.  Return -1, 0, or 1.
  /*!
   *  This is an arbitrary total ordering on Theorems.  For
   *  simplicity, we define rewrite theorems (e1 = e2 or e1 <=> e2) to
   *  be smaller than other theorems.
   */
  /*
  int compare(const Theorem& t1, const Theorem& t2) {
    return compare(t1.getExpr(), t2.getExpr());
  }
  */
  int compare(const Theorem& t1, const Theorem& t2) {
    if(t1.d_thm == t2.d_thm) return 0;
    if(t1.isNull()) return -1; // Null Theorem is less than other theorems
    if(t2.isNull()) return 1;

    bool rw1(t1.isRewrite()), rw2(t2.isRewrite());

    if(!rw2) return compare(t1, t2.getExpr());
    else if(!rw1) return -compare(t2, t1.getExpr());
    else {
      int res(compare(t1.getLHS(), t2.getLHS()));
      if(res==0) res = compare(t1.getRHS(), t2.getRHS());
      return res;
    }
  }
  /*
  int compare(const Theorem& t1, const Expr& e2) {
    return compare(t1.getExpr(), e2);
  }
  */
  int compare(const Theorem& t1, const Expr& e2) {
    bool rw1(t1.isRewrite()), rw2(e2.isEq() || e2.isIff());
    if(!rw1) {
      const Expr& e1 = t1.getExpr();
      rw1 = (e1.isEq() || e1.isIff());
    }
    if(rw1) {
      if(rw2) {
	int res(compare(t1.getLHS(), e2[0]));
	if(res==0) res = compare(t1.getRHS(), e2[1]);
	return res;
      } else return -1;
    } else {
      if(rw2) return 1;
      else return compare(t1.getExpr(), e2);
    }
  }
  
  int compareByPtr(const Theorem& t1, const Theorem& t2) {
    if(t1.d_thm == t2.d_thm) return 0;
    else if(t1.d_thm < t2.d_thm) return -1;
    else return 1;
  }


  // Assignment operator
  Theorem& Theorem::operator=(const Theorem& th) {
    // Handle self-assignment
    if(this == &th) return *this;
    if(d_thm == th.d_thm) return *this;

    long tmp = th.d_thm;

    // Increase the refcount on th
    if (tmp & 0x1) {
      TheoremValue* tv = (TheoremValue*) (tmp & (~(0x1)));
      DebugAssert(tv->d_refcount > 0,
                  "Theorem::operator=: invariant violated");
      ++(tv->d_refcount);
    }
    else if (tmp != 0) {
      th.exprValue()->incRefcount();
    }

    // Decrease the refcount on this
    if (d_thm & 0x1) {
      TheoremValue* tv = thm();
      DebugAssert(tv->d_refcount > 0,
                  "Theorem::operator=: invariant violated");
      if(--(tv->d_refcount) == 0) {
        MemoryManager* mm = tv->getMM();
        delete tv;
        mm->deleteData(tv);
      }
    }
    else if (d_thm != 0) {
      exprValue()->decRefcount();
    }

    d_thm = tmp;

    return *this;
  }


  // Constructors
  Theorem::Theorem(TheoremManager* tm, const Expr &thm,
		   const Assumptions& assump, const Proof& pf, 
		   bool isAssump, int scope) {
    TheoremValue* tv;
    if (thm.isEq() || thm.isIff()) {
      if (thm[0] == thm[1]) {
        d_expr = thm[0].d_expr;
        d_expr->incRefcount();
        return;
      }
      tv = new(tm->getRWMM()) RWTheoremValue(tm, thm, assump, pf, isAssump, scope);
    }
    else
      tv = new(tm->getMM()) RegTheoremValue(tm, thm, assump, pf, isAssump, scope);
    tv->d_refcount++;
    d_thm = ((intptr_t)tv)|0x1;
    //    TRACE("theorem", "Theorem(e) => ", *this, "");
    DebugAssert(!withProof() || !pf.isNull(),
		"Null proof in theorem:\n"+toString());
  }

  Theorem::Theorem(TheoremManager* tm, const Expr& lhs, const Expr& rhs,
		   const Assumptions& assump, const Proof& pf, bool isAssump,
                   int scope) {
    if (lhs == rhs) {
      d_expr = lhs.d_expr;
      d_expr->incRefcount();
      return;
    }
    TheoremValue* tv = new(tm->getRWMM())
      RWTheoremValue(tm, lhs, rhs, assump, pf, isAssump, scope);
    tv->d_refcount++;
    d_thm = ((long)tv)|0x1;
    DebugAssert(!withProof() || !pf.isNull(),
		"Null proof in theorem:\n"+toString());
  }


  // Copy constructor
  Theorem::Theorem(const Theorem &th) : d_thm(th.d_thm) {
    if (d_thm & 0x1) {
      DebugAssert(thm()->d_refcount > 0,
		  "Theorem(const Theorem&): refcount = "
		  + int2string(thm()->d_refcount));
      thm()->d_refcount++;
      //      TRACE("theorem", "Theorem(Theorem&) => ", *this, "");
    } else if (d_thm != 0) {
      exprValue()->incRefcount();
    }
  }

  Theorem::Theorem(const Expr& e) : d_expr(e.d_expr)
  {
    d_expr->incRefcount();
  }

  // Destructor
  Theorem::~Theorem() {
    if (d_thm & 0x1) {
      TheoremValue* tv = thm();
      //      TRACE("theorem", "~Theorem(", *this, ") {");
      IF_DEBUG(FatalAssert(tv->d_refcount > 0,
                           "~Theorem(): refcount = "
                           + int2string(tv->d_refcount));)
      if((--tv->d_refcount) == 0) {
        //        TRACE_MSG("theorem", "~Theorem(): deleting");
        MemoryManager* mm = tv->getMM();
        delete tv;
        mm->deleteData(tv);
      }
    }
    else if (d_thm != 0) {
      exprValue()->decRefcount();
    }
  }

  void Theorem::printx() const { getExpr().print(); }
  void Theorem::printxnodag() const { getExpr().printnodag(); }
  void Theorem::pprintx() const { getExpr().pprint(); }
  void Theorem::pprintxnodag() const { getExpr().pprintnodag(); }
  void Theorem::print() const { cout << toString() << endl; }

  // Test if we are running in a proof production mode and with assumptions
  bool Theorem::withProof() const {
    if (isRefl()) return exprValue()->d_em->getTM()->withProof();
    return thm()->d_tm->withProof();
  }

  bool Theorem::withAssumptions() const {
    if (isRefl()) return exprValue()->d_em->getTM()->withAssumptions();
    return thm()->d_tm->withAssumptions();
  }
  
  bool Theorem::isRewrite() const {
    DebugAssert(!isNull(), "CVC3::Theorem::isRewrite(): we are Null");
    return isRefl() || thm()->isRewrite();
  }

  // Return the theorem value as an Expr
  Expr Theorem::getExpr() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getExpr(): we are Null");
    if (isRefl()) {
      Expr e(exprValue());
      if (e.isTerm()) return e.eqExpr(e);
      else return e.iffExpr(e);
    }
    else return thm()->getExpr();
  }

  const Expr& Theorem::getLHS() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getLHS: we are Null");
    if (isRefl()) return *((Expr*)(&d_expr));
    else return thm()->getLHS();
  }

  const Expr& Theorem::getRHS() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getRHS: we are Null");
    if (isRefl()) return *((Expr*)(&d_expr));
    else return thm()->getRHS();
  }

// Return the assumptions.
// void Theorem::getAssumptions(Assumptions& a) const
// {
//   a = getAssumptionsRef();
// }


void Theorem::getAssumptionsRec(set<Expr>& assumptions) const
{
  if (isRefl() || isFlagged()) return;
  setFlag();
  if(isAssump()) {
    assumptions.insert(getExpr());
  }
  else {
    const Assumptions& a = getAssumptionsRef();
    for(Assumptions::iterator i=a.begin(), iend=a.end(); i!=iend; ++i)
      (*i).getAssumptionsRec(assumptions);
  }
}


void Theorem::getLeafAssumptions(vector<Expr>& assumptions,
                                 bool negate) const
{
  if (isNull() || isRefl()) return;
  set<Expr> assumpSet;
  clearAllFlags();
  getAssumptionsRec(assumpSet);
  // Order assumptions by their creation time
  for(set<Expr>::iterator i=assumpSet.begin(), iend=assumpSet.end();
      i!=iend; ++i)
    assumptions.push_back(negate ? (*i).negate() : *i);
}


void Theorem::GetSatAssumptionsRec(vector<Theorem>& assumptions) const
{
  DebugAssert(!isRefl() && !isFlagged(), "Invariant violated");
  setFlag();
  Expr e = getExpr();
  if (e.isAbsLiteral()) {
    if (isAssump() ||
        e.isRegisteredAtom() ||
        (e.isNot() && e[0].isRegisteredAtom())) {
      assumptions.push_back(*this);
      return;
    }
  }
  const Assumptions& a = getAssumptionsRef();
  for (Assumptions::iterator i = a.begin(); i != a.end(); i++) {
    if ((*i).isRefl() || (*i).isFlagged()) continue;
    (*i).GetSatAssumptionsRec(assumptions);
  }
}


void Theorem::GetSatAssumptions(vector<Theorem>& assumptions) const {
  DebugAssert(!isRefl() && !isFlagged(), "Invariant violated");
  setFlag();
  const Assumptions& a = getAssumptionsRef();
  for (Assumptions::iterator i = a.begin(); i != a.end(); i++) {
    if ((*i).isRefl() || (*i).isFlagged()) continue;
    (*i).GetSatAssumptionsRec(assumptions);
  }
}


void Theorem::getAssumptionsAndCongRec(set<Expr>& assumptions,
                                       vector<Expr>& congruences) const
{
  if (isRefl() || isFlagged()) return;
  setFlag();
  if(isAssump()) {
    assumptions.insert(getExpr());
  }
  else {
    const Assumptions& a = getAssumptionsRef();
    if (isSubst() && a.size() == 1) {
      vector<Expr> hyp;
      const Theorem& thm = *(a.begin());
      thm.getAssumptionsAndCongRec(assumptions, congruences);
      if (thm.isRewrite() && thm.getLHS().isTerm()
          && thm.getLHS().isAtomic() && thm.getRHS().isAtomic() &&
          !thm.isRefl()) {
        hyp.push_back(!thm.getExpr());
      }
      else return;
      const Expr& e = getExpr();
      if (e.isAtomicFormula()) {
        if (e[0] < e[1]) {
          hyp.push_back(e[1].eqExpr(e[0]));
        }
        else {
          hyp.push_back(e);
        }
        congruences.push_back(Expr(OR, hyp));
      }
      else if (e[0].isAtomicFormula() && !e[0].isEq()) {
        hyp.push_back(!e[0]);
        hyp.push_back(e[1]);
        congruences.push_back(Expr(OR, hyp));
        hyp.pop_back();
        hyp.pop_back();
        hyp.push_back(e[0]);
        hyp.push_back(!e[1]);
        congruences.push_back(Expr(OR, hyp));
      }
    }
    else {
      Assumptions::iterator i=a.begin(), iend=a.end();
      for(; i!=iend; ++i)
        (*i).getAssumptionsAndCongRec(assumptions, congruences);
    }
  }
}


void Theorem::getAssumptionsAndCong(vector<Expr>& assumptions,
                                    vector<Expr>& congruences,
                                    bool negate) const
{
  if (isNull() || isRefl()) return;
  set<Expr> assumpSet;
  clearAllFlags();
  getAssumptionsAndCongRec(assumpSet, congruences);
  // Order assumptions by their creation time
  for(set<Expr>::iterator i=assumpSet.begin(), iend=assumpSet.end();
      i!=iend; ++i)
    assumptions.push_back(negate ? (*i).negate() : *i);
}


const Assumptions& Theorem::getAssumptionsRef() const
{
  DebugAssert(!isNull(), "CVC3::Theorem::getAssumptionsRef: we are Null");
  if (!isRefl()) {
    return thm()->getAssumptionsRef();
  }
  else return Assumptions::emptyAssump();
}


  bool Theorem::isAssump() const {
    DebugAssert(!isNull(), "CVC3::Theorem::isAssump: we are Null");
    return isRefl() ? false : thm()->isAssump();
  }

  // Return the proof of the theorem.  If running without proofs,
  // return the Null proof.
  Proof Theorem::getProof() const {
    static Proof null;
    DebugAssert(!isNull(), "CVC3::Theorem::getProof: we are Null");
    if (isRefl()) {
      return Proof(Expr(PF_APPLY,
                        exprValue()->d_em->newVarExpr("refl"),
                        Expr(exprValue())));
    }
    else if (withProof() == true)
      return thm()->getProof();
    else
      return null;
  }

  bool Theorem::isFlagged() const {
    DebugAssert(!isNull(), "CVC3::Theorem::isFlagged: we are Null");
    if (isRefl()) return exprValue()->d_em->getTM()->isFlagged((long)d_expr);
    else return thm()->isFlagged();
  }

  void Theorem::clearAllFlags() const {
    DebugAssert(!isNull(), "CVC3::Theorem::clearAllFlags: we are Null");
    if (isRefl()) {
      exprValue()->d_em->getTM()->clearAllFlags();
    } else thm()->clearAllFlags();
  }

  void Theorem::setFlag() const {
    DebugAssert(!isNull(), "CVC3::Theorem::setFlag: we are Null");
    if (isRefl()) exprValue()->d_em->getTM()->setFlag((long)d_expr);
    else thm()->setFlag();
  }

  void Theorem::setCachedValue(int value) const {
    DebugAssert(!isNull(), "CVC3::Theorem::setCachedValue: we are Null");
    if (isRefl()) exprValue()->d_em->getTM()->setCachedValue((long)d_expr, value);
    else thm()->setCachedValue(value);
  }
  
  int Theorem::getCachedValue() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getCachedValue: we are Null");
    if (isRefl()) return exprValue()->d_em->getTM()->getCachedValue((long)d_expr);
    return thm()->getCachedValue();
  }
  
  void Theorem::setSubst() const {
    DebugAssert(!isNull() && !isRefl(), "CVC3::Theorem::setSubst: invalid thm");
    thm()->setSubst();
  }

  bool Theorem::isSubst() const {
    DebugAssert(!isNull(), "CVC3::Theorem::isSubst: we are Null");
    if (isRefl()) return false;
    return thm()->isSubst();
  }

  void Theorem::setExpandFlag(bool val) const {
    DebugAssert(!isNull(), "CVC3::Theorem::setExpandFlag: we are Null");
    if (isRefl()) exprValue()->d_em->getTM()->setExpandFlag((long)d_expr, val);
    thm()->setExpandFlag(val);
  }

  bool Theorem::getExpandFlag() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getExpandFlag: we are Null");
    if (isRefl()) return exprValue()->d_em->getTM()->getExpandFlag((long)d_expr);
    return thm()->getExpandFlag();
  }

  void Theorem::setLitFlag(bool val) const {
    DebugAssert(!isNull(), "CVC3::Theorem::setLitFlag: we are Null");
    if (isRefl()) exprValue()->d_em->getTM()->setLitFlag((long)d_expr, val);
    thm()->setLitFlag(val);
  }

  bool Theorem::getLitFlag() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getLitFlag: we are Null");
    if (isRefl()) return exprValue()->d_em->getTM()->getLitFlag((long)d_expr);
    return thm()->getLitFlag();
  }

  bool Theorem::isAbsLiteral() const {
    return getExpr().isAbsLiteral();
  }

  int Theorem::getScope() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getScope: we are Null");
    return isRefl() ? 0 : thm()->getScope();
  }

  unsigned Theorem::getQuantLevel() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getQuantLevel: we are Null");
    TRACE("quant-level", "isRefl? ", isRefl(), "");
    return isRefl() ? 0 : thm()->getQuantLevel();
  }

  unsigned Theorem::getQuantLevelDebug() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getQuantLevel: we are Null");
    TRACE("quant-level", "isRefl? ", isRefl(), "");
    return isRefl() ? 0 : thm()->getQuantLevelDebug();
  }


  void Theorem::setQuantLevel(unsigned level) {
    DebugAssert(!isNull(), "CVC3::Theorem::setQuantLevel: we are Null");
    //    DebugAssert(!isRefl(), "CVC3::Theorem::setQuantLevel: we are Refl");
    if (isRefl()) return;
    thm()->setQuantLevel(level);
  }

  size_t Theorem::hash() const {
    static std::hash<long int> h;
    return h(d_thm);
  }

  void Theorem::recursivePrint(int& i) const {
    const Assumptions::iterator iend = getAssumptionsRef().end();
    Assumptions::iterator it = getAssumptionsRef().begin();
    if (!isAssump()) {
      for (; it != iend; ++it) {
        if (it->isFlagged()) continue;
        it->recursivePrint(i);
        it->setFlag();
      }
    }

    setCachedValue(i++);
    cout << "[" << getCachedValue()
	 << "]@" << getScope() << "\tTheorem: {";

    if (isAssump()) {
      cout << "assump";
    }
    else if (getAssumptionsRef().empty()) {
      cout << "empty";
    }
    else {
      for (it = getAssumptionsRef().begin(); it != iend; ++it) {
        if (it != getAssumptionsRef().begin()) cout << ", ";
	cout << "[" << it->getCachedValue() << "]" ;
      }
    }
    cout << "}" << endl << "\t\t|- " << getExpr();
    if (isSubst()) cout << " [[Subst]]";
    cout << endl;
  }


  // Return the scope level at which this theorem was created
//   int Theorem::getScope() const {
//     DebugAssert(!isNull(), "CVC3::Theorem::getScope: we are Null");
//     return thm()->getScope();
//   }

//   Assumptions Theorem::getUserAssumptions() const {
//     ExprMap<Theorem> em;
//     Assumptions a = getAssumptionsCopy();

//     collectAssumptions(a, em);
    
//     return a;
//   }

//   void collectAssumptions(Assumptions &a, ExprMap<Theorem> em ) const {
//     if (isAssump()) {
//       // cache?
//       return;
//     }
    
//     const Assumptions a2 = thm()->getAssumptions();
//     a.add(a2);
//     Assumptions::iterator a2begin = a2.begin();
//     const Assumptions::iterator a2end = a2.end();


//   }


  // Printing Theorem
  ostream& Theorem::print(ostream& os, const string& name) const {
    if(isNull()) return os << name << "(Null)";
    ExprManager *em = getExpr().getEM();
    if (isRefl()) os << getExpr();
    else if (withAssumptions()) {
      em->incIndent(name.size()+2);
      os << name << "([" << thm() << "#" << thm()->d_refcount << "]@"
	 << getScope() << "\n[";
      if(isAssump()) os << "Assump";
      else {
	if(thm()->d_tm->getFlags()["print-assump"].getBool()
	   && em->isActive())
	  os << getAssumptionsRef();
	else
	  os << "<assumptions>";
      }
      os << "]\n  |--- ";
      em->indent(7);
      if(em->isActive()) os << getExpr();
      else os << "(being destructed)";
      if(withProof())
	os << "\n Proof = " << getProof();
      return os << ")";
    }
    else {
      em->incIndent(name.size()+1);
      os << name << "(";
      if(em->isActive()) os << getExpr();
      else os << "being destructed";
      return os << ")";
    }
    return os;
  }


} // end of namespace CVC3
