/*****************************************************************************/
/*!
 *\file theory_datatype_lazy.cpp
 *
 * Author: Clark Barrett
 *
 * Created: Wed Dec  1 22:32:26 2004
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


#include "theory_datatype_lazy.h"
#include "datatype_proof_rules.h"
#include "typecheck_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
#include "theory_core.h"
#include "theory_uf.h"
#include "command_line_flags.h"


using namespace std;
using namespace CVC3;


///////////////////////////////////////////////////////////////////////////////
// TheoryDatatypeLazy Public Methods                                             //
///////////////////////////////////////////////////////////////////////////////


TheoryDatatypeLazy::TheoryDatatypeLazy(TheoryCore* core)
  : TheoryDatatype(core),
    d_processQueue(core->getCM()->getCurrentContext()),
    d_processQueueKind(core->getCM()->getCurrentContext()),
    d_processIndex(core->getCM()->getCurrentContext(), 0),
    d_typeComplete(core->getCM()->getCurrentContext(), false)
{ }


void TheoryDatatypeLazy::instantiate(const Expr& e, const Unsigned& u)
{
  DebugAssert(e.hasFind() && findExpr(e) == e,
              "datatype: instantiate: Expected find(e)=e");
  if (isConstructor(e) || e.isTranslated()) return;
  DebugAssert(u != 0 && (u & (u-1)) == 0,
              "datatype: instantiate: Expected single label in u");
  DebugAssert(d_datatypes.find(e.getType().getExpr()) != d_datatypes.end(),
              "datatype: instantiate: Unexpected type: "+e.getType().toString()
              +"\n\n for expression: "+e.toString());
  ExprMap<unsigned>& c = d_datatypes[e.getType().getExpr()];
  ExprMap<unsigned>::iterator c_it = c.begin(), c_end = c.end();
  for (; c_it != c_end; ++c_it) {
    if ((u & ((Unsigned)1 << unsigned((*c_it).second))) != 0) break;
  }
  DebugAssert(c_it != c_end,
              "datatype: instantiate: couldn't find constructor");
  Expr cons = (*c_it).first;

  if (!cons.isFinite() && !e.isSelected()) return;

  Type consType = cons.getType();
  if (consType.arity() == 1) {
    d_processQueue.push_back(d_rules->dummyTheorem(d_facts, e.eqExpr(cons)));
    d_processQueueKind.push_back(ENQUEUE);
    return;
  }
  // create vars
  vector<Expr> vars;
  for (int i = 0; i < consType.arity()-1; ++i) {
    vars.push_back(getEM()->newBoundVarExpr(consType[i]));
  }
  Expr e2 = getEM()->newClosureExpr(EXISTS, vars,
                                    e.eqExpr(Expr(cons.mkOp(), vars)));
  d_processQueue.push_back(d_rules->dummyTheorem(d_facts, e2));
  d_processQueueKind.push_back(ENQUEUE);
  e.setTranslated();
}


void TheoryDatatypeLazy::initializeLabels(const Expr& e, const Type& t)
{
  DebugAssert(findExpr(e) == e,
              "datatype: initializeLabels: Expected find(e)=e");
  DebugAssert(d_datatypes.find(t.getExpr()) != d_datatypes.end(),
              "Unknown datatype: "+t.getExpr().toString());
  ExprMap<unsigned>& c = d_datatypes[t.getExpr()];
  DebugAssert(d_labels.find(e) == d_labels.end(),
              "datatype: initializeLabels: expected unlabeled expr");
  if (isConstructor(e)) {
    Expr cons = getConstructor(e);
    DebugAssert(c.find(cons) != c.end(),
                "datatype: initializeLabels: Couldn't find constructor "
                +cons.toString());
    unsigned position = c[cons];
    d_labels.insert(e,
      SmartCDO<Unsigned>(theoryCore()->getCM()->getCurrentContext(),
                            1 << position, 0));
  }
  else {
    DebugAssert(c.size() > 0, "No constructors?");
    Unsigned value = ((Unsigned)1 << unsigned(c.size())) - 1;
    d_labels.insert(e,
      SmartCDO<Unsigned>(theoryCore()->getCM()->getCurrentContext(),
                            value, 0));
    if (value == 1) instantiate(e, 1);
    else if (!d_typeComplete) {
      d_splitters.push_back(e);
    }
  }
}


void TheoryDatatypeLazy::mergeLabels(const Theorem& thm,
                                 const Expr& e1, const Expr& e2)
{
  DebugAssert(e2.hasFind(),
              "datatype: mergeLabels: Expected hasFind(e2)");
  Theorem fthm = find(e2);
  const Expr& f = fthm.getRHS();
  DebugAssert(d_labels.find(e1) != d_labels.end() &&
              d_labels.find(f) != d_labels.end(),
              "mergeLabels: expr is not labeled");
  DebugAssert(e1.getType() == f.getType(), "Expected same type");
  Unsigned u = d_labels[f].get().get();
  Unsigned uNew = u & d_labels[e1].get().get();
  if (u != uNew) {
    if (e2 != f) d_facts.push_back(fthm);
    if (!thm.isNull()) d_facts.push_back(thm);
    d_labels[f].get().set(uNew);
    if (uNew == 0) {
      setInconsistent(d_rules->dummyTheorem(d_facts, falseExpr()));
      return;
    }
  }
  if (uNew != 0 && ((uNew - 1) & uNew) == 0) {
    instantiate(f, uNew);
  }
}


void TheoryDatatypeLazy::mergeLabels(const Theorem& thm, const Expr& e,
                                 unsigned position, bool positive)
{
  DebugAssert(e.hasFind(),
              "datatype: mergeLabels2: Expected hasFind(e)");
  Theorem fthm = find(e);
  const Expr& f = fthm.getRHS();
  DebugAssert(d_labels.find(f) != d_labels.end(),
              "mergeLabels2: expr is not labeled");
  Unsigned u = d_labels[f].get().get();
  Unsigned uNew = (Unsigned)1 << position;
  if (positive) {
    uNew = u & uNew;
    if (u == uNew) return;
  } else if ((u & uNew) != 0) uNew = u - uNew;
  else return;
  if (e != f) d_facts.push_back(fthm);
  d_facts.push_back(thm);
  d_labels[f].get().set(uNew);
  if (uNew == 0)
    setInconsistent(d_rules->dummyTheorem(d_facts, falseExpr()));
  else if (((uNew - 1) & uNew) == 0) {
    instantiate(f, uNew);
  }
}


void TheoryDatatypeLazy::checkSat(bool fullEffort)
{
  bool done = false;
  while (!done && d_splittersIndex < d_splitters.size()) {
    Expr e = d_splitters[d_splittersIndex];
    if (findExpr(e) == e) {
      DebugAssert(d_labels.find(e) != d_labels.end(),
                  "checkSat: expr is not labeled");
      Unsigned u = d_labels[e].get().get();
      if ((u & (u-1)) != 0) {
        done = true;
        DebugAssert(!d_splitterAsserted || !fullEffort,
                    "splitter should have been resolved");
        if (!d_splitterAsserted) {
          DebugAssert
            (d_datatypes.find(e.getType().getExpr()) != d_datatypes.end(),
             "datatype: checkSat: Unexpected type: "+e.getType().toString()
             +"\n\n for expression: "+e.toString());
          ExprMap<unsigned>& c = d_datatypes[e.getType().getExpr()];
          ExprMap<unsigned>::iterator c_it = c.begin(), c_end = c.end();
          for (; c_it != c_end; ++c_it) {
            if ((u & ((Unsigned)1 << unsigned((*c_it).second))) != 0) break;
          }
          DebugAssert(c_it != c_end,
              "datatype: checkSat: couldn't find constructor");
          addSplitter(datatypeTestExpr((*c_it).first.getName(), e));
          d_splitterAsserted = true;
        }
      }
    }
    if (!done) {
      d_splitterAsserted = false;
      d_splittersIndex = d_splittersIndex + 1;
    }
  }
  while (!done && d_processIndex < d_processQueue.size()) {
    d_typeComplete = true;
    Theorem e = d_processQueue[d_processIndex];
    int kind = d_processQueueKind[d_processIndex];
    switch (kind) {
      case MERGE1: {
        break;
      }
      case ENQUEUE:
        done = true;
        enqueueFact(e);
        break;
      case MERGE2: {
        const Expr& lhs = e.getLHS();
        const Expr& rhs = e.getRHS();
        Theorem thm(e);
        if (lhs.isSelected() && !rhs.isSelected()) {
          d_facts.push_back(e);
          rhs.setSelected();
          thm = Theorem();
        }
        mergeLabels(thm, lhs, rhs);
        break;
      }
      default:
        DebugAssert(false, "Unknown case");
    }
    d_processIndex = d_processIndex + 1;
  }
}



void TheoryDatatypeLazy::setup(const Expr& e)
{
  if (e.getType().getExpr().getKind() == DATATYPE &&
      d_labels.find(e) == d_labels.end()) {
    initializeLabels(e, e.getType());
    e.addToNotify(this, Expr());
  }
  if (e.getKind() != APPLY) return;
  if (isConstructor(e) && e.arity() > 0) {
    d_processQueue.push_back(d_rules->noCycle(e));
    d_processQueueKind.push_back(ENQUEUE);
  }
  if (isSelector(e)) {
    e[0].setSelected();
    d_processQueue.push_back(reflexivityRule(e[0]));
    d_processQueueKind.push_back(MERGE2);
  }
  setupCC(e);
}


void TheoryDatatypeLazy::update(const Theorem& e, const Expr& d)
{
  if (d.isNull()) {
    const Expr& lhs = e.getLHS();
    const Expr& rhs = e.getRHS();
    if (isConstructor(lhs) && isConstructor(rhs) &&
        lhs.isApply() && rhs.isApply() &&
        lhs.getOpExpr() == rhs.getOpExpr()) {
      d_processQueue.push_back(d_rules->decompose(e));
      d_processQueueKind.push_back(ENQUEUE);
    }
    else {
      d_processQueue.push_back(e);
      d_processQueueKind.push_back(MERGE2);
    }
  }
  else {
    const Theorem& dEQdsig = d.getSig();
    if (!dEQdsig.isNull()) {
      const Expr& dsig = dEQdsig.getRHS();
      Theorem thm = updateHelper(d);
      const Expr& sigNew = thm.getRHS();
      if (sigNew == dsig) return;
      dsig.setRep(Theorem());
      if (isSelector(sigNew) && canCollapse(sigNew)) {
        d.setSig(Theorem());
        d_processQueue.push_back(transitivityRule(thm, d_rules->rewriteSelCons(d_facts, sigNew)));
        d_processQueueKind.push_back(ENQUEUE);
      }
      else if (isTester(sigNew) && isConstructor(sigNew[0])) {
        d.setSig(Theorem());
        d_processQueue.push_back(transitivityRule(thm, d_rules->rewriteTestCons(sigNew)));
        d_processQueueKind.push_back(ENQUEUE);
      }
      else {
        const Theorem& repEQsigNew = sigNew.getRep();
        if (!repEQsigNew.isNull()) {
          d.setSig(Theorem());
          d_processQueue.push_back(transitivityRule(repEQsigNew, symmetryRule(thm)));
          d_processQueueKind.push_back(ENQUEUE);
        }
        else {
          int k, ar(d.arity());
          for (k = 0; k < ar; ++k) {
            if (sigNew[k] != dsig[k]) {
              sigNew[k].addToNotify(this, d);
            }
          }
          d.setSig(thm);
          sigNew.setRep(thm);
          getEM()->invalidateSimpCache();
        }
      }
    }
  }
}
