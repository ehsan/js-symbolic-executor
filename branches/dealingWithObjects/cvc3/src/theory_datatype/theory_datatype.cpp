/*****************************************************************************/
/*!
 *\file theory_datatype.cpp
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


#include "theory_datatype.h"
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
// TheoryDatatype Public Methods                                             //
///////////////////////////////////////////////////////////////////////////////


TheoryDatatype::TheoryDatatype(TheoryCore* core)
  : Theory(core, "Datatypes"),
    d_labels(core->getCM()->getCurrentContext()),
    d_facts(core->getCM()->getCurrentContext()),
    d_splitters(core->getCM()->getCurrentContext()),
    d_splittersIndex(core->getCM()->getCurrentContext(), 0),
    d_splitterAsserted(core->getCM()->getCurrentContext(), false),
    d_smartSplits(core->getFlags()["dt-smartsplits"].getBool())
{
  d_rules = createProofRules();

  // Register new local kinds with ExprManager
  getEM()->newKind(DATATYPE_DECL, "_DATATYPE_DECL");
  getEM()->newKind(DATATYPE, "_DATATYPE", true);
  getEM()->newKind(CONSTRUCTOR, "_CONSTRUCTOR");
  getEM()->newKind(SELECTOR, "_SELECTOR");
  getEM()->newKind(TESTER, "_TESTER");

  vector<int> kinds;
  kinds.push_back(DATATYPE_DECL);
  kinds.push_back(DATATYPE);
  kinds.push_back(TESTER);
  kinds.push_back(CONSTRUCTOR);
  kinds.push_back(SELECTOR);

  registerTheory(this, kinds);
}


TheoryDatatype::~TheoryDatatype() {
  delete d_rules;
}


void TheoryDatatype::instantiate(const Expr& e, const Unsigned& u)
{
  DebugAssert(!e.hasFind() || findExpr(e) == e,
              "datatype: instantiate: Expected find(e)=e");
  if (isConstructor(e)) return;
  DebugAssert(u != 0 && (u & (u-1)) == 0,
              "datatype: instantiate: Expected single label in u");
  DebugAssert(d_datatypes.find(getBaseType(e).getExpr()) != d_datatypes.end(),
              "datatype: instantiate: Unexpected type: "+getBaseType(e).toString()
              +"\n\n for expression: "+e.toString());
  ExprMap<unsigned>& c = d_datatypes[getBaseType(e).getExpr()];
  ExprMap<unsigned>::iterator c_it = c.begin(), c_end = c.end();
  for (; c_it != c_end; ++c_it) {
    if ((u & (Unsigned(1) << (unsigned)(*c_it).second)) != 0) break;
  }
  DebugAssert(c_it != c_end,
              "datatype: instantiate: couldn't find constructor");
  const Expr& cons = (*c_it).first;

  if (!cons.isFinite() && !e.isSelected()) return;

  Type consType = getBaseType(cons);
  if (consType.arity() == 1) {
    enqueueFact(d_rules->dummyTheorem(d_facts, e.eqExpr(cons)));
    return;
  }
  // create vars
  vector<Expr> vars;
  for (int i = 0; i < consType.arity()-1; ++i) {
    vars.push_back(getEM()->newBoundVarExpr(consType[i]));
  }
  Expr e2 = getEM()->newClosureExpr(EXISTS, vars,
                                    e.eqExpr(Expr(cons.mkOp(), vars)));
  enqueueFact(d_rules->dummyTheorem(d_facts, e2));
}


void TheoryDatatype::initializeLabels(const Expr& e, const Type& t)
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
    d_labels.insert(e,
      SmartCDO<Unsigned>(theoryCore()->getCM()->getCurrentContext(),
                         (Unsigned)1 << c[cons], 0));
  }
  else {
    DebugAssert(c.size() > 0, "No constructors?");
    Unsigned value = ((Unsigned)1 << c.size()) - 1;
    d_labels.insert(e,
      SmartCDO<Unsigned>(theoryCore()->getCM()->getCurrentContext(),
                            value, 0));
    if (value == 1) instantiate(e, 1);
    else {
      if (!d_smartSplits || t.getExpr().isFinite()) d_splitters.push_back(e);
    }
  }
}


void TheoryDatatype::mergeLabels(const Theorem& thm,
                                 const Expr& e1, const Expr& e2)
{
  DebugAssert(e2.hasFind() && findExpr(e2) == e2,
              "datatype: mergeLabels: Expected find(e2)=e2");
  DebugAssert(d_labels.find(e1) != d_labels.end() &&
              d_labels.find(e2) != d_labels.end(),
              "mergeLabels: expr is not labeled");
  DebugAssert(getBaseType(e1) == getBaseType(e2), "Expected same type");
  Unsigned u = d_labels[e2].get().get();
  Unsigned uNew = u & d_labels[e1].get().get();
  if (u != uNew) {
    if (!thm.isNull()) d_facts.push_back(thm);
    d_labels[e2].get().set(uNew);
    if (uNew == 0)
      setInconsistent(d_rules->dummyTheorem(d_facts, falseExpr()));
  }
  if (uNew != 0 && ((uNew - 1) & uNew) == 0) {
    instantiate(e2, uNew);
  }
}


void TheoryDatatype::mergeLabels(const Theorem& thm, const Expr& e,
                                 unsigned position, bool positive)
{
  DebugAssert(e.hasFind() && findExpr(e) == e,
              "datatype: mergeLabels2: Expected find(e)=e");
  DebugAssert(d_labels.find(e) != d_labels.end(),
              "mergeLabels2: expr is not labeled");
  Unsigned u = d_labels[e].get().get();
  Unsigned uNew = (Unsigned)1 << position;
  if (positive) {
    uNew = u & uNew;
    if (u == uNew) return;
  } else if ((u & uNew) != 0) uNew = u - uNew;
  else return;
  d_facts.push_back(thm);
  d_labels[e].get().set(uNew);
  if (uNew == 0)
    setInconsistent(d_rules->dummyTheorem(d_facts, falseExpr()));
  else if (((uNew - 1) & uNew) == 0) {
    instantiate(e, uNew);
  }
}


void TheoryDatatype::addSharedTerm(const Expr& e)
{
  if (getBaseType(e).getExpr().getKind() == DATATYPE &&
      d_labels.find(e) == d_labels.end()) {
    initializeLabels(e, getBaseType(e));
    e.addToNotify(this, Expr());
  }
}


void TheoryDatatype::assertFact(const Theorem& e)
{
  if (!e.isRewrite()) {
    const Expr& expr = e.getExpr();
    if (expr.getOpKind() == TESTER) {
      mergeLabels(e, expr[0],
                  getConsPos(getConsForTester(expr.getOpExpr())),
                  true);
    }
    else if (expr.isNot()) {
      if (expr[0].getOpKind() == TESTER) {
        mergeLabels(e, expr[0][0],
                    getConsPos(getConsForTester(expr[0].getOpExpr())),
                    false);
      }
      else if (expr[0].isEq() &&
               getBaseType(expr[0][0]).getExpr().getKind() == DATATYPE) {
        // Propagate disequality down
        if (d_labels.find(expr[0][0]) == d_labels.end()) {
          initializeLabels(expr[0][0], getBaseType(expr[0][0]));
          expr[0][0].addToNotify(this, Expr());
        }
        if (d_labels.find(expr[0][1]) == d_labels.end()) {
          initializeLabels(expr[0][1], getBaseType(expr[0][1]));
          expr[0][1].addToNotify(this, Expr());
        }
        Unsigned u1 = d_labels[expr[0][0]].get().get();
        Unsigned u2 = d_labels[expr[0][1]].get().get();
        ExprMap<unsigned>& c = d_datatypes[getBaseType(expr[0][0]).getExpr()];
        ExprMap<unsigned>::iterator c_it = c.begin(), c_end = c.end();
        Expr bigConj;
        for (; c_it != c_end; ++c_it) {
          if ((u1 & u2 & ((Unsigned)1 << unsigned((*c_it).second))) != 0) {
            vector<Expr>& selectors = d_constructorMap[(*c_it).first];
            Expr conj;
            for (unsigned i = 0; i < selectors.size(); ++i) {
              Expr e1 = Expr(selectors[i].mkOp(), expr[0][0]);
              Expr e2 = e1.eqExpr(Expr(selectors[i].mkOp(), expr[0][1]));
              if (conj.isNull()) conj = e2;
              else conj = conj.andExpr(e2);
            }
            if (!conj.isNull()) {
              Expr e1 = datatypeTestExpr((*c_it).first.getName(), expr[0][0]);
              Expr e2 = datatypeTestExpr((*c_it).first.getName(), expr[0][1]);
              conj = (e1 && e2).impExpr(!conj);
              if (bigConj.isNull()) bigConj = conj;
              else bigConj = bigConj.andExpr(conj);
            }
          }
        }
        if (!bigConj.isNull()) {
          enqueueFact(d_rules->dummyTheorem(d_facts, bigConj));
        }          
      }
    }
  }
}


void TheoryDatatype::checkSat(bool fullEffort)
{
  bool done = false;
  while (!done && d_splittersIndex < d_splitters.size()) {
    Expr e = d_splitters[d_splittersIndex];
    if ((!d_smartSplits || getBaseType(e).getExpr().isFinite()) &&
        findExpr(e) == e) {
      DebugAssert(d_labels.find(e) != d_labels.end(),
                  "checkSat: expr is not labeled");
      Unsigned u = d_labels[e].get().get();
      if ((u & (u-1)) != 0) {
        done = true;
        DebugAssert(!d_splitterAsserted || !fullEffort,
                    "splitter should have been resolved");
        if (!d_splitterAsserted) {
          DebugAssert
            (d_datatypes.find(getBaseType(e).getExpr()) != d_datatypes.end(),
             "datatype: checkSat: Unexpected type: "+getBaseType(e).toString()
             +"\n\n for expression: "+e.toString());
          ExprMap<unsigned>& c = d_datatypes[getBaseType(e).getExpr()];
          ExprMap<unsigned>::iterator c_it = c.begin(), c_end = c.end();
          vector<Expr> vec;
          for (; c_it != c_end; ++c_it) {
            if ((u & ((Unsigned)1 << unsigned((*c_it).second))) != 0) {
              vec.push_back(datatypeTestExpr((*c_it).first.getName(), e));
            }
          }
          DebugAssert(vec.size() > 1, "datatype: checkSat: expected 2 or more possible constructors");
          enqueueFact(d_rules->dummyTheorem(d_facts, Expr(OR, vec)));
          d_splitterAsserted = true;
        }
      }
    }
    if (d_smartSplits && !done && isSelector(e)) {
      Expr f = findExpr(e[0]);
      DebugAssert(d_labels.find(f) != d_labels.end(),
                  "checkSat: expr is not labeled");
      Unsigned u = d_labels[f].get().get();
      if ((u & (u-1)) != 0) {
        pair<Expr, unsigned> selectorInfo = getSelectorInfo(e.getOpExpr());
        unsigned pos = getConsPos(selectorInfo.first);
        if ((u & ((Unsigned)1 << pos)) != 0) {
          done = true;
          DebugAssert(!d_splitterAsserted || !fullEffort,
                      "splitter should have been resolved");
          if (!d_splitterAsserted) {
            addSplitter(datatypeTestExpr(selectorInfo.first.getName(), f));
            d_splitterAsserted = true;
          }
        }
      }
    }
    if (!done) {
      d_splitterAsserted = false;
      d_splittersIndex = d_splittersIndex + 1;
    }
  }
}


Theorem TheoryDatatype::rewrite(const Expr& e)
{
  // TODO: UF rewrite?
  Theorem thm;
  if (isSelector(e)) {
    if (canCollapse(e)) {
      thm = d_rules->rewriteSelCons(d_facts, e);
      return transitivityRule(thm, simplify(thm.getRHS()));
    }
  }
  else if (isTester(e)) {
    if (isConstructor(e[0])) {
      return d_rules->rewriteTestCons(e);
    }
  }
  return reflexivityRule(e);
}


void TheoryDatatype::setup(const Expr& e)
{
  if (getBaseType(e).getExpr().getKind() == DATATYPE &&
      d_labels.find(e) == d_labels.end()) {
    initializeLabels(e, getBaseType(e));
    e.addToNotify(this, Expr());
  }
  if (e.getKind() != APPLY) return;
  if (isConstructor(e) && e.arity() > 0) {
    enqueueFact(d_rules->noCycle(e));
  }
  if (isSelector(e)) {
    if (d_smartSplits) d_splitters.push_back(e);
    e[0].setSelected();
    mergeLabels(Theorem(), e[0], e[0]);
  }
  setupCC(e);
}


void TheoryDatatype::update(const Theorem& e, const Expr& d)
{
  if (d.isNull()) {
    const Expr& lhs = e.getLHS();
    const Expr& rhs = e.getRHS();
    if (isConstructor(lhs) && isConstructor(rhs) &&
        lhs.isApply() && rhs.isApply() &&
        lhs.getOpExpr() == rhs.getOpExpr()) {
      enqueueFact(d_rules->decompose(e));
    }
    else {
      // Possible for rhs to never have been seen: initialize it here
      DebugAssert(getBaseType(rhs).getExpr().getKind() == DATATYPE,
                  "Expected datatype");
      if (d_labels.find(rhs) == d_labels.end()) {
        initializeLabels(rhs, getBaseType(rhs));
        rhs.addToNotify(this, Expr());
      }
      Theorem thm(e);
      if (lhs.isSelected() && !rhs.isSelected()) {
        d_facts.push_back(e);
        rhs.setSelected();
        thm = Theorem();
      }
      mergeLabels(thm, lhs, rhs);
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
        enqueueFact(transitivityRule(thm, d_rules->rewriteSelCons(d_facts, sigNew)));
      }
      else if (isTester(sigNew) && isConstructor(sigNew[0])) {
        d.setSig(Theorem());
        enqueueFact(transitivityRule(thm, d_rules->rewriteTestCons(sigNew)));
      }
      else {
        const Theorem& repEQsigNew = sigNew.getRep();
        if (!repEQsigNew.isNull()) {
          d.setSig(Theorem());
          enqueueFact(transitivityRule(repEQsigNew, symmetryRule(thm)));
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


Theorem TheoryDatatype::solve(const Theorem& e)
{
  DebugAssert(e.isRewrite() && e.getLHS().isTerm(), "Expected equality");
  const Expr& lhs = e.getLHS();
  if (isConstructor(lhs) && !isConstructor(e.getRHS())) {
    return symmetryRule(e);
  }
  return e;
}


void TheoryDatatype::checkType(const Expr& e)
{
  switch (e.getKind()) {
    case DATATYPE: {
      if (e.arity() != 1 || !e[0].isString())
        throw Exception("Ill-formed datatype"+e.toString());
      if (resolveID(e[0].getString()) != e)
        throw Exception("Unknown datatype"+e.toString());
      break;
    }
    case CONSTRUCTOR:
    case SELECTOR:
    case TESTER:
      throw Exception("Non-type: "+e.toString());
    default:
      FatalAssert(false, "Unexpected kind in TheoryDatatype::checkType"
                  +getEM()->getKindName(e.getKind()));
  }
}


Cardinality TheoryDatatype::finiteTypeInfo(Expr& e, Unsigned& n,
                                           bool enumerate, bool computeSize)
{
  DebugAssert(e.getKind() == DATATYPE,
              "Unexpected kind in TheoryDatatype::finiteTypeInfo");
  if (d_getConstantStack.count(e) != 0) {
    return CARD_INFINITE;
  }
  d_getConstantStack[e] = true;

  Expr typeExpr = e;
  ExprMap<unsigned>& c = d_datatypes[typeExpr];
  ExprMap<unsigned>::iterator c_it = c.begin(), c_end = c.end();
  Cardinality card = CARD_FINITE, cardTmp;
  bool getSize = enumerate || computeSize;
  Unsigned totalSize = 0, thisSize, size;
  vector<Unsigned> sizes;
  int j;

  // Loop through constructors, and check if each one only has a finite number
  // of possibilities
  for (; c_it != c_end; ++c_it) {
    const Expr& cons = (*c_it).first;
    Expr funType = cons.getType().getExpr();
    thisSize = 1;
    for (j = 0; j < funType.arity()-1; ++j) {
      Expr e2 = funType[j];
      cardTmp = theoryOf(e2)->finiteTypeInfo(e2, size, false, getSize);
      if (cardTmp == CARD_INFINITE) {
        card = CARD_INFINITE;
        break;
      }
      else if (cardTmp == CARD_UNKNOWN) {
        card = CARD_UNKNOWN;
        getSize = false;
        // Keep looking to see if we can determine it is infinite
      }
      else if (getSize) {
        thisSize = thisSize * size;
        // Give up if it gets too big
        if (thisSize > 1000000) thisSize = 0;
        if (thisSize == 0) {
          totalSize = 0;
          getSize = false;
        }
      }
    }
    if (card == CARD_INFINITE) break;
    if (getSize) {
      sizes.push_back(thisSize);
      totalSize = totalSize + thisSize;
    }
  }
  
  if (card == CARD_FINITE) {

    if (enumerate) {
      c_it = c.begin();
      unsigned i = 0;
      for (; i < sizes.size(); ++i, ++c_it) {
        if (n < sizes[i]) {
          break;
        }
        else n = n - sizes[i];
      }
      if (i == sizes.size() && n != 0) {
        e = Expr();
      }
      else {
        const Expr& cons = (*c_it).first;
        Expr funType = cons.getType().getExpr();
        if (funType.arity() == 1) {
          e = cons;
        }
        else {
          vector<Expr> kids(funType.arity()-1);
          Unsigned thisSize;
          Unsigned elem;
          for (int j = funType.arity()-2; j >= 0; --j) {
            if (n == 0) {
              elem = 0;
            }
            else {
              thisSize = funType[j].typeSizeFinite();
              elem = n % thisSize;
              n = n - elem;
              n = n / thisSize;
            }
            kids[j] = funType[j].typeEnumerateFinite(elem);
          }
          e = Expr(cons.mkOp(), kids);
        }
      }
    }

    if (computeSize) {
      n = totalSize;
    }

  }
  d_getConstantStack.erase(typeExpr);
  return card;
}


void TheoryDatatype::computeType(const Expr& e)
{
  switch (e.getOpKind()) {
    case CONSTRUCTOR:
    case SELECTOR:
    case TESTER: {
      DebugAssert(e.isApply(), "Expected application");
      Expr op = e.getOp().getExpr();
      Type t = op.lookupType();
      DebugAssert(!t.isNull(), "Expected operator to be well-typed");
      if (t.getExpr().getKind() == DATATYPE) {
        if (e.arity() != 0)
          throw TypecheckException("Expected no children: "+e.toString());
        e.setType(t);
        break;
      }
      else {
        DebugAssert(t.getExpr().getKind() == ARROW, "Expected function type");
        if (e.arity() != t.getExpr().arity()-1)
          throw TypecheckException("Wrong number of children:\n"+e.toString());
        Expr::iterator i = e.begin(), iend = e.end();
        Expr::iterator j = t.getExpr().begin();
        for (; i != iend; ++i, ++j) {
          if (getBaseType(*i) != getBaseType(Type(*j))) {
            throw TypecheckException("Type mismatch for expression:\n\n  "
                                     + (*i).toString()
                                     + "\n\nhas the following type:\n\n  "
                                     + (*i).getType().getExpr().toString()
                                     + "\n\nbut the expected type is:\n\n  "
                                     + (*j).toString()
                                     + "\n\nin datatype function application:\n\n  "
                                     + e.toString());
          }
        }
        e.setType(*j);
      }
      break;
    }
    default:
      DebugAssert(false, "Unexpected kind in datatype::computeType: "
                  +e.toString());
  }
}


void TheoryDatatype::computeModelTerm(const Expr& e, std::vector<Expr>& v) {
}



Expr TheoryDatatype::computeTCC(const Expr& e)
{
  Expr tcc(Theory::computeTCC(e));
  switch (e.getKind()) {
    case CONSTRUCTOR:
      DebugAssert(e.arity() == 0, "Expected leaf constructor");
      return trueExpr();
    case APPLY: {
      DebugAssert(e.isApply(), "Should be application");
      Expr op(e.getOpExpr());
      if (op.getKind() != SELECTOR) return tcc;
      DebugAssert(e.arity() == 1, "Expected single argument");
      const std::pair<Expr,unsigned>& p = getSelectorInfo(op);
      Expr tester = datatypeTestExpr(p.first.getName(), e[0]);
      return tcc.andExpr(tester);
    }
    default:
      DebugAssert(false,"Unexpected type: "+e.toString());
      return trueExpr();
  }
}

///////////////////////////////////////////////////////////////////////////////
// Pretty-printing			                                     //
///////////////////////////////////////////////////////////////////////////////


ExprStream& TheoryDatatype::print(ExprStream& os, const Expr& e) {
  switch (os.lang()) {
    case PRESENTATION_LANG:
      switch (e.getKind()) {
        case DATATYPE_DECL: {
          os << "DATATYPE" << endl;
          bool first(true);
          for (Expr::iterator i = e.begin(), iend = e.end(); i != iend; ++i) {
            if (first) first = false;
            else os << "," << endl;
            os << "  " << push << *i << space << "= " << push;
            DebugAssert(d_datatypes.find(*i) != d_datatypes.end(),
                        "Unknown datatype: "+(*i).toString());
            ExprMap<unsigned>& c = d_datatypes[*i];
            ExprMap<unsigned>::iterator c_it = c.begin(), c_end = c.end();
            bool firstCons(true);
            for (; c_it != c_end; ++c_it) {
              if (!firstCons) {
                os << space << "| ";
              }
              else firstCons = false;
              const Expr& cons = (*c_it).first;
              os << cons;
              vector<Expr>& sels = d_constructorMap[cons];
              bool firstSel(true);
              for (unsigned j = 0; j < sels.size(); ++j) {
                if (firstSel) {
                  firstSel = false;
                  os << "(";
                } else {
                  os << ", ";
                }
                os << sels[j] << space << ": ";
                os << sels[j].getType().getExpr()[1];
              }
              if (!firstSel) {
                os << ")";
              }
            }
            os << pop;
          }
          os << pop << endl;
          os << "END;";
          break;
        }
        case DATATYPE:
          if (e.arity() == 1 && e[0].isString()) {
            os << e[0].getString();
          }
          else e.printAST(os);
          break;
        case APPLY:
          os << e.getOpExpr();
          if(e.arity() > 0) {
            os << "(" << push;
            bool first(true);
            for (Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
              if(first) first = false;
              else os << "," << space;
              os << *i;
            }
            os << push << ")";
          }
          break;
        case CONSTRUCTOR:
        case SELECTOR:
        case TESTER:
          DebugAssert(e.isSymbol(), "Expected symbol");
          os << e.getName();
          break;
        default:
          DebugAssert(false, "TheoryDatatype::print: Unexpected kind: "
                      +getEM()->getKindName(e.getKind()));
      }
      break;
    case SMTLIB_LANG:
      FatalAssert(false, "Not Implemented Yet");
      break;
    case LISP_LANG:
      FatalAssert(false, "Not Implemented Yet");
      break;
    default:
      e.printAST(os);
      break;
  }
  return os;
}

//////////////////////////////////////////////////////////////////////////////
//parseExprOp:
//translating special Exprs to regular EXPR??
///////////////////////////////////////////////////////////////////////////////
Expr TheoryDatatype::parseExprOp(const Expr& e)
{
  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  if(RAW_LIST != e.getKind()) return e;

  DebugAssert(e.arity() > 0,
	      "TheoryDatatype::parseExprOp:\n e = "+e.toString());
  
  DebugAssert(e[0].getKind() == ID,
              "Expected ID kind for first elem in list expr");

  const Expr& c1 = e[0][0];
  int kind = getEM()->getKind(c1.getString());
  switch(kind) {
    case DATATYPE: {
      DebugAssert(e.arity() > 1,
                  "Empty DATATYPE expression\n"
                  " (expected at least one datatype): "+e.toString());

      vector<Expr> names;

      vector<Expr> allConstructorNames;
      vector<Expr> constructorNames;

      vector<Expr> allSelectorNames;
      vector<Expr> selectorNames;
      vector<Expr> selectorNamesKids;

      vector<Expr> allTypes;
      vector<Expr> types;
      vector<Expr> typesKids;

      int i,j,k;
      Expr dt, constructor, selectors, selector;

      // Get names of datatypes
      ExprMap<bool> namesMap;
      for (i = 0; i < e.arity()-1; ++i) {
        dt = e[i+1];
        DebugAssert(dt.getKind() == RAW_LIST && dt.arity() == 2,
                    "Bad formed datatype expression"
                    +dt.toString());
        DebugAssert(dt[0].getKind() == ID,
                    "Expected ID kind for datatype name"
                    +dt.toString());
        names.push_back(dt[0][0]);
        if (namesMap.count(dt[0][0]) != 0) {
          throw ParserException("Datatype name used more than once"+dt[0][0].getString());
        }
        namesMap.insert(dt[0][0], true);
      }

      // Loop through datatypes
      for (i = 0; i < e.arity()-1; ++i) {
        dt = e[i+1];
        DebugAssert(dt[1].getKind() == RAW_LIST && dt[1].arity() > 0,
                    "Expected non-empty list for datatype constructors"
                    +dt.toString());
        dt = dt[1];

        // Loop through constructors for this datatype
        for(j = 0; j < dt.arity(); ++j) {
          constructor = dt[j];
          DebugAssert(constructor.getKind() == RAW_LIST &&
                      (constructor.arity() == 1 || constructor.arity() == 2),
                    "Unexpected constructor"+constructor.toString());
          DebugAssert(constructor[0].getKind() == ID,
                      "Expected ID kind for constructor name"
                      +constructor.toString());
          constructorNames.push_back(constructor[0][0]);

          if (constructor.arity() == 2) {
            selectors = constructor[1];
            DebugAssert(selectors.getKind() == RAW_LIST && selectors.arity() > 0,
                        "Non-empty list expected as second argument of constructor:\n"
                        +constructor.toString());

            // Loop through selectors for this constructor
            for (k = 0; k < selectors.arity(); ++k) {
              selector = selectors[k];
              DebugAssert(selector.getKind() == RAW_LIST && selector.arity() == 2,
                          "Expected list of arity 2 for selector"
                          +selector.toString());
              DebugAssert(selector[0].getKind() == ID,
                          "Expected ID kind for selector name"
                          +selector.toString());
              selectorNamesKids.push_back(selector[0][0]);
              if (selector[1].getKind() == ID && namesMap.count(selector[1][0]) > 0) {
                typesKids.push_back(selector[1][0]);
              }
              else {
                typesKids.push_back(parseExpr(selector[1]));
              }
            }
            selectorNames.push_back(Expr(RAW_LIST, selectorNamesKids));
            selectorNamesKids.clear();
            types.push_back(Expr(RAW_LIST, typesKids));
            typesKids.clear();
          }
          else {
            selectorNames.push_back(Expr(RAW_LIST, selectorNamesKids, getEM()));
            types.push_back(Expr(RAW_LIST, typesKids, getEM()));
          }
        }
        allConstructorNames.push_back(Expr(RAW_LIST, constructorNames));
        constructorNames.clear();
        allSelectorNames.push_back(Expr(RAW_LIST, selectorNames));
        selectorNames.clear();
        allTypes.push_back(Expr(RAW_LIST, types));
        types.clear();
      }

      return Expr(DATATYPE,
                  Expr(RAW_LIST, names),
                  Expr(RAW_LIST, allConstructorNames),
                  Expr(RAW_LIST, allSelectorNames),
                  Expr(RAW_LIST, allTypes));
    }

    default: {
      throw ParserException("Unexpected datatype expression: "+e.toString());
    }
  }
  return e;
}


Expr TheoryDatatype::dataType(const string& name,
                              const vector<string>& constructors,
                              const vector<vector<string> >& selectors,
                              const vector<vector<Expr> >& types)
{
  vector<string> names;
  vector<vector<string> > constructors2;
  vector<vector<vector<string> > > selectors2;
  vector<vector<vector<Expr> > > types2;
  names.push_back(name);
  constructors2.push_back(constructors);
  selectors2.push_back(selectors);
  types2.push_back(types);
  return dataType(names, constructors2, selectors2, types2);
}
 

// Elements of types are either the expr from an existing type or a string
// naming one of the datatypes being defined
Expr TheoryDatatype::dataType(const vector<string>& names,
                              const vector<vector<string> >& allConstructors,
                              const vector<vector<vector<string> > >& allSelectors,
                              const vector<vector<vector<Expr> > >& allTypes)
{
  vector<Expr> returnTypes;

  //  bool wellFounded = false, infinite = false, 
  bool thisWellFounded;

  if (names.size() != allConstructors.size() ||
      allConstructors.size() != allSelectors.size() ||
      allSelectors.size() != allTypes.size()) {
    throw TypecheckException
      ("dataType: vector sizes don't match");
  }

  unsigned i, j, k;
  Expr e;

  // Create reachability predicate for constructor cycle detection
  vector<Type> funTypeArgs;
  funTypeArgs.push_back(Type::anyType(getEM()));
  funTypeArgs.push_back(Type::anyType(getEM()));
  Op op = newFunction("_reach_"+names[0],
                      Type::funType(funTypeArgs, boolType()),
                      true /* compute trans closure */);
  Op reach = getEM()->newSymbolExpr(op.getExpr().getName(),
                                    TRANS_CLOSURE).mkOp();

  for (i = 0; i < names.size(); ++i) {
    e = resolveID(names[i]);
    if (!e.isNull()) {
      throw TypecheckException
        ("Attempt to define datatype "+names[i]+":\n "
         "This variable is already defined.");
    }
    e = Expr(DATATYPE, getEM()->newStringExpr(names[i]));
    installID(names[i], e);
    returnTypes.push_back(e);
    d_reach[e] = reach;
  }

  vector<Expr> selectorVec;

  for (i = 0; i < names.size(); ++i) {

    const vector<string>& constructors = allConstructors[i];
    const vector<vector<string> >& selectors = allSelectors[i];
    const vector<vector<Expr> >& types = allTypes[i];

    if (constructors.size() == 0) {
      throw TypecheckException
        ("datatype: "+names[i]+": must have at least one constructor");
    }
    if (constructors.size() != selectors.size() ||
        selectors.size() != types.size()) {
      throw TypecheckException
        ("dataType: vector sizes at index "+int2string(i)+" don't match");
    }

    ExprMap<unsigned>& constMap = d_datatypes[returnTypes[i]];

    for (j = 0; j < constructors.size(); ++j) {
      Expr c = resolveID(constructors[j]);
      if (!c.isNull()) {
        throw TypecheckException
          ("Attempt to define datatype constructor "+constructors[j]+":\n "
           "This variable is already defined.");
      }
      c = getEM()->newSymbolExpr(constructors[j], CONSTRUCTOR);

      if (selectors[j].size() != types[j].size()) {
        throw TypecheckException
          ("dataType: constructor at index "+int2string(i)+", "+int2string(j)+
           ": number of selectors does not match number of types");
      }
      thisWellFounded = true;
      const vector<string>& sels = selectors[j];
      const vector<Expr>& tps = types[j];

      vector<Type> selTypes;
      Type t;
      Expr s;
      for (k = 0; k < sels.size(); ++k) {
        s = resolveID(sels[k]);
        if (!s.isNull()) {
          throw TypecheckException
            ("Attempt to define datatype selector "+sels[k]+":\n "
             "This variable is already defined.");
        }
        s = getEM()->newSymbolExpr(sels[k], SELECTOR);
        if (tps[k].isString()) {
          t = Type(resolveID(tps[k].getString()));
          if (t.isNull()) {
            throw TypecheckException
              ("Unable to resolve type identifier: "+tps[k].getString());
          }
        } else t = Type(tps[k]);
        if (t.isBool()) {
          throw TypecheckException
            ("Cannot have BOOLEAN inside of datatype");
        }
        else if (t.isFunction()) {
          throw TypecheckException
            ("Cannot have function inside of datatype");
        }
        
        selTypes.push_back(Type(t));
        s.setType(Type(returnTypes[i]).funType(Type(t)));
        if (isDatatype(Type(t)) && !t.getExpr().isWellFounded()) {
          thisWellFounded = false;
        }
        d_selectorMap[s] = pair<Expr,unsigned>(c,k);
        installID(sels[k], s);
        selectorVec.push_back(s);
      }
      if (thisWellFounded) c.setWellFounded();
      if (selTypes.size() == 0) {
        c.setType(Type(returnTypes[i]));
        c.setFinite();
      }
      else c.setType(Type::funType(selTypes, Type(returnTypes[i])));
      installID(constructors[j], c);
      constMap[c] = j;
      d_constructorMap[c] = selectorVec;
      selectorVec.clear();

      string testerString = "is_"+constructors[j];
      e = resolveID(testerString);
      if (!e.isNull()) {
        throw TypecheckException
          ("Attempt to define datatype tester "+testerString+":\n "
           "This variable is already defined.");
      }
      e = getEM()->newSymbolExpr(testerString, TESTER);
      e.setType(Type(returnTypes[i]).funType(boolType()));
      d_testerMap[e] = c;
      installID(testerString, e);
    }
  }

  // Compute fixed point for wellfoundedness check

  bool changed, thisFinite;
  int firstNotWellFounded;
  do {
    changed = false;
    firstNotWellFounded = -1;
    for (i = 0; i < names.size(); ++i) {
      ExprMap<unsigned>& c = d_datatypes[returnTypes[i]];
      ExprMap<unsigned>::iterator c_it = c.begin(), c_end = c.end();
      thisWellFounded = false;
      thisFinite = true;
      for (; c_it != c_end; ++c_it) {
        const Expr& cons = (*c_it).first;
        Expr funType = getBaseType(cons).getExpr();
        int j;
        if (!cons.isFinite()) {
          for (j = 0; j < funType.arity()-1; ++j) {
            if (!isDatatype(funType[j]) || !funType[j].isFinite())
              break;
          }
          if (j == funType.arity()-1) {
            changed = true;
            cons.setFinite();
          }
          else thisFinite = false;
        }
        if (cons.isWellFounded()) {
          thisWellFounded = true;
          continue;
        }
        for (j = 0; j < funType.arity()-1; ++j) {
          if (isDatatype(funType[j]) && !funType[j].isWellFounded())
            break;
        }
        if (j == funType.arity()-1) {
          changed = true;
          cons.setWellFounded();
          thisWellFounded = true;
        }
      }
      if (!thisWellFounded) {
        if (firstNotWellFounded == -1) firstNotWellFounded = i;
      }
      else {
        if (!returnTypes[i].isWellFounded()) {
          changed = true;
          returnTypes[i].setWellFounded();
        }
      }
      if (thisFinite && !returnTypes[i].isFinite()) {
        changed = true;
        returnTypes[i].setFinite();
      }
    }
  } while (changed);

  if (firstNotWellFounded >= 0) {
    // TODO: uninstall all ID's
    throw TypecheckException
      ("Datatype "+names[firstNotWellFounded]+" has no finite terms");
  }

  return Expr(DATATYPE_DECL, returnTypes);
}

Expr TheoryDatatype::datatypeConsExpr(const string& constructor,
                                      const vector<Expr>& args)
{
  Expr e = resolveID(constructor);
  if (e.isNull())
    throw Exception("datatype: unknown constructor: "+constructor);
  if (!(e.isSymbol() && e.getKind() == CONSTRUCTOR))
    throw Exception("datatype: "+constructor+" resolves to: "+e.toString()+
                    "\nwhich is not a constructor");
  if (args.size() == 0) return e;
  return Expr(e.mkOp(), args);
}


Expr TheoryDatatype::datatypeSelExpr(const string& selector, const Expr& arg)
{
  Expr e = resolveID(selector);
  if (e.isNull())
    throw Exception("datatype: unknown selector: "+selector);
  if (!(e.isSymbol() && e.getKind() == SELECTOR))
    throw Exception("datatype: "+selector+" resolves to: "+e.toString()+
                    "\nwhich is not a selector");
  return Expr(e.mkOp(), arg);
}


Expr TheoryDatatype::datatypeTestExpr(const string& constructor, const Expr& arg)
{
  Expr e = resolveID("is_"+constructor);
  if (e.isNull())
    throw Exception("datatype: unknown tester: is_"+constructor);
  if (!(e.isSymbol() && e.getKind() == TESTER))
    throw Exception("datatype: is_"+constructor+" resolves to: "+e.toString()+
                    "\nwhich is not a tester");
  return Expr(e.mkOp(), arg);
}


const pair<Expr,unsigned>& TheoryDatatype::getSelectorInfo(const Expr& e)
{
  DebugAssert(e.getKind() == SELECTOR, "getSelectorInfo called on non-selector: "
              +e.toString());
  DebugAssert(d_selectorMap.find(e) != d_selectorMap.end(),
              "Unknown selector: "+e.toString());
  return d_selectorMap[e];
}


Expr TheoryDatatype::getConsForTester(const Expr& e)
{
  DebugAssert(e.getKind() == TESTER,
              "getConsForTester called on non-tester"
              +e.toString());
  DebugAssert(d_testerMap.find(e) != d_testerMap.end(),
              "Unknown tester: "+e.toString());
  return d_testerMap[e];
}


unsigned TheoryDatatype::getConsPos(const Expr& e)
{
  DebugAssert(e.getKind() == CONSTRUCTOR,
              "getConsPos called on non-constructor");
  Type t = getBaseType(e);
  if (t.isFunction()) t = t[t.arity()-1];
  DebugAssert(isDatatype(t), "Expected datatype");
  DebugAssert(d_datatypes.find(t.getExpr()) != d_datatypes.end(),
              "Could not find datatype: "+t.toString());
  ExprMap<unsigned>& constMap = d_datatypes[t.getExpr()];
  DebugAssert(constMap.find(e) != constMap.end(),
              "Could not find constructor: "+e.toString());
  return constMap[e];
}


Expr TheoryDatatype::getConstant(const Type& t)
{
  // if a cycle is detected, backtrack from this branch
  if (d_getConstantStack.count(t.getExpr()) != 0) {
    return Expr();
  }
  DebugAssert(d_getConstantStack.size() < 1000,
	      "TheoryDatatype::getconstant: too deep recursion depth");
  d_getConstantStack[t.getExpr()] = true;
  if (isDatatype(t)) {
   DebugAssert(d_datatypes.find(t.getExpr()) != d_datatypes.end(),
               "Unknown datatype: "+t.getExpr().toString());
   ExprMap<unsigned>& c = d_datatypes[t.getExpr()];
   ExprMap<unsigned>::iterator i = c.begin(), iend = c.end();
   for (; i != iend; ++i) {
     const Expr& cons = (*i).first;
     if (!getBaseType(cons).isFunction()) {
       d_getConstantStack.erase(t.getExpr());
       return cons;
     }
   }
   for (i = c.begin(), iend = c.end(); i != iend; ++i) {
     const Expr& cons = (*i).first;
     Expr funType = getBaseType(cons).getExpr();
     vector<Expr> args;
     int j = 0;
     for (; j < funType.arity()-1; ++j) {
       Type t_j = Type(funType[j]);
       if (t_j == t || isDatatype(t_j)) break;
       args.push_back(getConstant(t_j));
       DebugAssert(!args.back().isNull(), "Expected non-null");
     }
     if (j == funType.arity()-1) {
       d_getConstantStack.erase(t.getExpr());
       return Expr(cons.mkOp(), args);
     }
   }
   for (i = c.begin(), iend = c.end(); i != iend; ++i) {
     const Expr& cons = (*i).first;
     Expr funType = getBaseType(cons).getExpr();
     vector<Expr> args;
     int j = 0;
     for (; j < funType.arity()-1; ++j) {
       Type t_j = Type(funType[j]);
       if (t_j == t) break;
       args.push_back(getConstant(t_j));
       if (args.back().isNull()) break;
     }
     if (j == funType.arity()-1) {
       d_getConstantStack.erase(t.getExpr());
       return Expr(cons.mkOp(), args);
     }
   }
   FatalAssert(false, "Couldn't find constant for"
               +t.toString());
  }
  DebugAssert(!t.isBool() && !t.isFunction(),
              "Expected non-bool, non-function type");
  //TODO: this name could be an illegal identifier (i.e. could include spaces)
  string name = "datatype_"+t.getExpr().toString();
  Expr e = resolveID(name);
  d_getConstantStack.erase(t.getExpr());
  if (e.isNull()) return newVar(name, t);
  return e;
}


const Op& TheoryDatatype::getReachablePredicate(const Type& t)
{
  DebugAssert(isDatatype(t), "Expected datatype");
  DebugAssert(d_reach.find(t.getExpr()) != d_reach.end(),
              "Couldn't find reachable predicate");
  return d_reach[t.getExpr()];
}


bool TheoryDatatype::canCollapse(const Expr& e)
{
  DebugAssert(isSelector(e), "canCollapse: Selector expression expected");
  DebugAssert(e.arity() == 1, "expected arity 1");
  if (isConstructor(e[0])) return true;
  if (d_labels.find(e[0]) == d_labels.end()) return false;
  DebugAssert(e[0].hasFind() && findExpr(e[0]) == e[0],
              "canCollapse: Expected find(e[0])=e[0]");
  Unsigned u = d_labels[e[0]].get().get();
  Expr cons = getSelectorInfo(e.getOpExpr()).first;
  Unsigned uCons = (Unsigned)1 << unsigned(getConsPos(cons));
  if ((u & uCons) == 0) return true;
  return false;
}
