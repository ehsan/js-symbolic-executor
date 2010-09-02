/*****************************************************************************/
/*!
 * \file theory_uf.cpp
 * 
 * Author: Clark Barrett
 * 
 * Created: Fri Jan 24 02:07:59 2003
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

#include "theory_uf.h"
#include "uf_proof_rules.h"
#include "typecheck_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
#include "command_line_flags.h"
#include "theory_core.h"
#include "translator.h"
// HACK: include theory_records.h to access the TUPLE_TYPE kind
#include "theory_records.h"


using namespace std;
using namespace CVC3;


///////////////////////////////////////////////////////////////////////////////
// TheoryUF Public Methods                                                   //
///////////////////////////////////////////////////////////////////////////////


TheoryUF::TheoryUF(TheoryCore* core)//, bool useAckermann)
  : Theory(core, "Uninterpreted Functions"),
    d_applicationsInModel(core->getFlags()["applications"].getBool()),
    d_funApplications(core->getCM()->getCurrentContext()),
    d_funApplicationsIdx(core->getCM()->getCurrentContext(), 0),
    d_sharedIdx1(core->getCM()->getCurrentContext(), 0),
    d_sharedIdx2(core->getCM()->getCurrentContext(), 0),
    d_sharedTermsMap(core->getCM()->getCurrentContext())
    //    d_useAckermann(useAckermann)
{
  d_rules = createProofRules();

  // Register new local kinds with ExprManager
  getEM()->newKind(TRANS_CLOSURE, "_TRANS_CLOSURE");
  getEM()->newKind(OLD_ARROW, "_OLD_ARROW", true);

  vector<int> kinds;
  //TODO: should this stuff really be in theory_uf?
  kinds.push_back(TYPEDECL);
  kinds.push_back(LAMBDA);
  kinds.push_back(ARROW);
  kinds.push_back(OLD_ARROW);
  kinds.push_back(UFUNC);
  kinds.push_back(TRANS_CLOSURE);

  registerTheory(this, kinds);
}


TheoryUF::~TheoryUF() {
  delete d_rules;
}


//TODO: clean up transitive closure tables
// be sure to free CD objects

void TheoryUF::assertFact(const Theorem& e)
{
  const Expr& expr = e.getExpr();
  switch (expr.getKind()) {
    case NOT:
      break;
    case APPLY:
      if (expr.getOpExpr().computeTransClosure()) {
	enqueueFact(d_rules->relToClosure(e));
      }
      else if (expr.getOpKind() == TRANS_CLOSURE) {
        // const Expr& rel = expr.getFun();
        DebugAssert(expr.isApply(), "Should be apply");
        Expr rel = resolveID(expr.getOpExpr().getName());
        DebugAssert(!rel.isNull(), "Expected known identifier");
        DebugAssert(rel.isSymbol() && rel.getKind()==UFUNC && expr.arity()==2,
                    "Unexpected use of transitive closure: "+expr.toString());

        // Insert into transitive closure table
        ExprMap<TCMapPair*>::iterator i = d_transClosureMap.find(rel);
        TCMapPair* pTable;
        if (i == d_transClosureMap.end()) {
          pTable = new TCMapPair();
          d_transClosureMap[rel] = pTable;
        }
        else {
          pTable = (*i).second;
        }

        ExprMap<CDList<Theorem>*>::iterator i2 = pTable->appearsFirstMap.find(expr[0]);
        CDList<Theorem>* pList;
        if (i2 == pTable->appearsFirstMap.end()) {
          pList = new(true) CDList<Theorem>(theoryCore()->getCM()->getCurrentContext());
          pTable->appearsFirstMap[expr[0]] = pList;
        }
        else {
          pList = (*i2).second;
        }
        pList->push_back(e);

        i2 = pTable->appearsSecondMap.find(expr[1]);
        if (i2 == pTable->appearsSecondMap.end()) {
          pList = new(true) CDList<Theorem>(theoryCore()->getCM()->getCurrentContext());
          pTable->appearsSecondMap[expr[1]] = pList;
        }
        else {
          pList = (*i2).second;
        }
        pList->push_back(e);

        // Compute transitive closure with existing relations
        size_t s,l;
        i2 = pTable->appearsFirstMap.find(expr[1]);
        if (i2 != pTable->appearsFirstMap.end()) {
          pList = (*i2).second;
          s = pList->size();
          for (l = 0; l < s; ++l) {
            enqueueFact(d_rules->relTrans(e,(*pList)[l]));
          }
        }

        i2 = pTable->appearsSecondMap.find(expr[0]);
        if (i2 != pTable->appearsSecondMap.end()) {
          pList = (*i2).second;
          s = pList->size();
          for (l = 0; l < s; ++l) {
            enqueueFact(d_rules->relTrans((*pList)[l],e));
          }
        }
      }
      break;
    default:
      break;
  }
}


void TheoryUF::checkSat(bool fullEffort)
{
  // Check for any unexpanded lambdas
  bool enqueued = false;
  for(; d_funApplicationsIdx < d_funApplications.size();
      d_funApplicationsIdx = d_funApplicationsIdx + 1) {
    const Expr& e = d_funApplications[d_funApplicationsIdx];
    if(e.getOp().getExpr().isLambda()) {
      IF_DEBUG(debugger.counter("Expanded lambdas (checkSat)")++;)
      enqueueFact(d_rules->applyLambda(e));
      enqueued = true;
    }
  }

  // If something has been returned, we are done
  if (!fullEffort || enqueued) return;

  // Expand on the shared terms
  for( ; d_sharedIdx1 < d_funApplications.size(); d_sharedIdx1 = d_sharedIdx1
      + 1, d_sharedIdx2 = 0 ) {
    Expr f1 = d_funApplications[d_sharedIdx1];
    if( f1.getOpKind() == UFUNC && !f1.getSig().isNull() ) {
      f1 = f1.getSig().getRHS();
      Expr f1_fun = f1.getOp().getExpr();
      for( ; d_sharedIdx2 < d_sharedIdx1; d_sharedIdx2 = d_sharedIdx2 + 1 ) {
        Expr f2 = d_funApplications[d_sharedIdx2];
        if (f2.getOpKind() == UFUNC && !f2.getSig().isNull() ) {
          f2 = f2.getSig().getRHS();
          Expr f2_fun = f2.getOp().getExpr();
          if( f1 != f2 && find(f1).getRHS() != find(f2).getRHS() && f1_fun == f2_fun ) {
            for( int k = 0; k < f1.arity(); ++k ) {
              Expr x_k = f1[k];
              Expr y_k = f2[k];
              if( d_sharedTermsMap.find(x_k) == d_sharedTermsMap.end() )
                continue;
              if( d_sharedTermsMap.find(y_k) == d_sharedTermsMap.end() )
                continue;
              Expr eq = x_k.eqExpr(y_k);
              if( !simplify(eq).getRHS().isBoolConst() ) {
                TRACE("sharing", "splitting " + y_k.toString(), " and ", x_k.toString());
                TRACE("sharing", "from " + f2.toString(), " and ", f1.toString());
                addSplitter(eq);
                enqueued = true;
              }
            }
            if( enqueued )
              return;
          }
        }
      }
    }
  }
}


Theorem TheoryUF::rewrite(const Expr& e)
{
  if (e.isApply()) {
    const Expr& op = e.getOpExpr();
    int opKind = op.getKind(); 
    switch(opKind) {
      case LAMBDA: {
        Theorem res = d_rules->applyLambda(e);
        // Simplify recursively
        res = transitivityRule(res, simplify(res.getRHS()));
        IF_DEBUG(debugger.counter("Expanded lambdas")++;)
        return res;
      }
      default: // A truly uninterpreted function
        if (e.getType().isBool()) return reflexivityRule(e);
        else return rewriteCC(e);
    }
  }
  else {
    e.setRewriteNormal();
    return reflexivityRule(e);
  }
}


void TheoryUF::setup(const Expr& e)
{
  if (e.isTerm() && e.getType().card() != CARD_INFINITE) {
    addSharedTerm(e);
    theoryOf(e.getType())->addSharedTerm(e);
  }
  if (e.getKind() != APPLY) return;
//   if (d_useAckermann) {
//     Theorem thm = getCommonRules()->varIntroSkolem(e);
//     theoryCore()->addToVarDB(thm.getRHS());
//     enqueueFact(thm);
//   }
//   else {
    setupCC(e);
//   }
  // Add this function application for concrete model generation
  TRACE("model", "TheoryUF: add function application ", e, "");
  d_funApplications.push_back(e);
}


void TheoryUF::update(const Theorem& e, const Expr& d)
{
  /*
  int k, ar(d.arity());
  const Theorem& dEQdsig = d.getSig();
  if (!dEQdsig.isNull()) {
    Expr dsig = dEQdsig.getRHS();
    Theorem thm = updateHelper(d);
    const Expr& sigNew = thm.getRHS();
    if (sigNew == dsig) return;
    dsig.setRep(Theorem());
    const Theorem& repEQsigNew = sigNew.getRep();
    if (!repEQsigNew.isNull()) {
      d.setSig(Theorem());
      enqueueFact(transitivityRule(repEQsigNew, symmetryRule(thm)));
    }
    else {
      for (k = 0; k < ar; ++k) {
	if (sigNew[k] != dsig[k]) {
	  sigNew[k].addToNotify(this, d);
	}
      }
      d.setSig(thm);
      sigNew.setRep(thm);

      if (d_compute_trans_closure && d.getKind() == APPLY &&
	  d.arity() == 2 && findExpr(d).isTrue()) {
	thm = iffTrueElim(transitivityRule(symmetryRule(thm),find(d)));
	enqueueFact(d_rules->relToClosure(thm));
      }

    }
  }
  */
  // Record the original signature
  const Theorem& dEQdsig = d.getSig();
  if (!dEQdsig.isNull()) {
    const Expr& dsig = dEQdsig.getRHS();
    Theorem thm = updateHelper(d);
    const Expr& sigNew = thm.getRHS();
    if (sigNew == dsig) {
      //      TRACE_MSG("facts update", "updateCC["+getName()+"]() [no change] => }");
      return;
    }
    dsig.setRep(Theorem());
    const Theorem& repEQsigNew = sigNew.getRep();
    if (!repEQsigNew.isNull()) {
      d.setSig(Theorem());
      enqueueFact(transitivityRule(repEQsigNew, symmetryRule(thm)));
    }
    else if (d.getType().isBool()) {
      d.setSig(Theorem());
      enqueueFact(thm);
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
      if (dsig != sigNew && d.isApply() && findExpr(d).isTrue()) {
        if (d.getOpExpr().computeTransClosure()) {
          thm = getCommonRules()->iffTrueElim(transitivityRule(symmetryRule(thm),
                                                               find(d)));
          enqueueFact(d_rules->relToClosure(thm));
        }
        else if (d.getOpKind() == TRANS_CLOSURE) {
          thm = getCommonRules()->iffTrueElim(transitivityRule(symmetryRule(thm),
                                                               find(d)));
          enqueueFact(thm);
        }
      }
    }
  }
}


void TheoryUF::checkType(const Expr& e)
{
  switch (e.getKind()) {
    case ARROW: {
      if (e.arity() < 2) throw Exception
            ("Function type needs at least two arguments"
             +e.toString());
      Expr::iterator i = e.begin(), iend = e.end();
      for (; i != iend; ) {
        Type t(*i);
        ++i;
        if (i == iend && t.isBool()) break;
        if (t.isBool()) throw Exception
            ("Function argument types must be non-Boolean: "
             +e.toString());
        if (t.isFunction()) throw Exception
            ("Function domain or range types cannot be functions: "
             +e.toString());
      }
      break;
    }
    case TYPEDECL: {
      break;
    }
    default:
      DebugAssert(false, "Unexpected kind in TheoryUF::checkType"
                  +getEM()->getKindName(e.getKind()));
  }
}


Cardinality TheoryUF::finiteTypeInfo(Expr& e, Unsigned& n,
                                     bool enumerate, bool computeSize)
{
  if (e.getKind() != ARROW) {
    // uninterpreted type
    return CARD_UNKNOWN;
  }
  Expr::iterator i = e.begin(), iend = e.end();
  Cardinality card = CARD_FINITE, cardTmp;
  Unsigned thisSize = 1, size;
  bool getSize = enumerate || computeSize;
  for (; i != iend; ) {
    Expr e2 = (*i);
    cardTmp = theoryOf(e2)->finiteTypeInfo(e2, size, getSize, false);
    if (cardTmp == CARD_INFINITE) {
      return CARD_INFINITE;
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
        getSize = false;
      }
    }
  }

  if (card == CARD_FINITE) {

    if (enumerate) {
      // TODO: enumerate functions? maybe at least n == 0
      e = Expr();
    }

    if (computeSize) {
      n = thisSize;
    }

  }

  return card;
}


void TheoryUF::computeType(const Expr& e)
{
  switch (e.getKind()) {
    case LAMBDA: {
      vector<Type> args;
      const vector<Expr>& vars = e.getVars();
      DebugAssert(vars.size() > 0,
                  "TheorySimulate::computeType("+e.toString()+")");
      for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
          i!=iend; ++i)
        args.push_back((*i).getType());
      e.setType(Type::funType(args, e.getBody().getType()));
      break;
    }
    case APPLY: {
      theoryOf(APPLY)->computeType(e);
      break;
    }
    case TRANS_CLOSURE: {
      DebugAssert(e.isSymbol(), "Expected symbol");
      Expr funExpr = resolveID(e.getName());
      if (funExpr.isNull()) {
        throw TypecheckException
          ("Attempt to take transitive closure of unknown id: "
           +e.getName());
      }
      Type funType = funExpr.getType();
      if(!funType.isFunction()) {
	throw TypecheckException
	  ("Attempt to take transitive closure of non-function:\n\n"
	   +funExpr.toString() + "\n\n which has type: "
	   +funType.toString());
      }
      if(funType.arity()!=3) {
        throw TypecheckException
          ("Attempt to take transitive closure of non-binary function:\n\n"
           +funExpr.toString() + "\n\n which has type: "
           +funType.toString());
      }
      if (!funType[2].isBool()) {
        throw TypecheckException
          ("Attempt to take transitive closure of function:\n\n"
           +funExpr.toString() + "\n\n which does not return BOOLEAN");
      }
      e.setType(funType);
      break;
    }
    default:
      DebugAssert(false,"Unexpected type: "+e.toString());
      break;
  }
}


Type TheoryUF::computeBaseType(const Type& t) {
  const Expr& e = t.getExpr();
  switch(e.getKind()) {
  case ARROW: {
    DebugAssert(e.arity() > 0, "Expected non-empty ARROW");
    vector<Expr> kids;
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
      kids.push_back(getBaseType(Type(*i)).getExpr());
    }
    return Type(Expr(e.getOp(), kids));
  }
  case TYPEDECL: return t;
  default:
    DebugAssert(false,
		"TheoryUF::computeBaseType("+t.toString()+")");
    return t;
  }
}


void TheoryUF::computeModelTerm(const Expr& e, std::vector<Expr>& v) {
  for(CDList<Expr>::const_iterator i=d_funApplications.begin(),
	iend=d_funApplications.end(); i!=iend; ++i) {
    if((*i).isApply() && (*i).getOp().getExpr() == e) {
      // Add both the function application
      // getModelTerm(*i, v);
      v.push_back(*i);
      // and the arguments to the model terms.  Reason: the argument
      // to the function better be a concrete value, and it might not
      // necessarily be in the current list of model terms.
      for(Expr::iterator j=(*i).begin(), jend=(*i).end(); j!=jend; ++j)
	// getModelTerm(*j, v);
	v.push_back(*j);
    }
  }
}


void TheoryUF::computeModel(const Expr& e, std::vector<Expr>& vars) {
  // Repeat the same search for applications of e as in
  // computeModelTerm(), but this time get the concrete values of the
  // arguments, and return the applications of e to concrete values in
  // vars.

  // We'll assign 'e' a value later.
  vars.push_back(e);
  // Map of f(c) to val for concrete values of c and val
  ExprHashMap<Expr> appls;
  for(CDList<Expr>::const_iterator i=d_funApplications.begin(),
	iend=d_funApplications.end(); i!=iend; ++i) {
    if((*i).isApply() && (*i).getOp().getExpr() == e) {
      // Update all arguments with concrete values
      vector<Theorem> thms;
      vector<unsigned> changed;
      for(int j=0; j<(*i).arity(); ++j) {
	Theorem asst(getModelValue((*i)[j]));
	if(asst.getLHS()!=asst.getRHS()) {
	  thms.push_back(asst);
	  changed.push_back(j);
	}
      }
      Expr var;
      if(changed.size()>0) {
	// Arguments changed.  Compute the new application, and assign
	// it a concrete value
	Theorem subst = substitutivityRule(*i, changed, thms);
	assignValue(transitivityRule(symmetryRule(subst), getModelValue(*i)));
	var = subst.getRHS();
      } else
	var = *i;
      if(d_applicationsInModel) vars.push_back(var);
      // Record it in the map
      appls[var] = getModelValue(var).getRHS();
    }
  }
  // Create a LAMBDA expression for e
  if(appls.size()==0) { // Leave it fully uninterpreted
    assignValue(reflexivityRule(e));
  } else {
    // Bound vars
    vector<Expr> args;
    Type tp(e.getType());
    static unsigned count(0);
    DebugAssert(tp.isFunction(), "TheoryUF::computeModel("+e.toString()
		+" : "+tp.toString()+")");
    for(int i=0, iend=tp.arity()-1; i<iend; ++i) {
      string str = "uf_"+int2string(count);
      Expr v = getEM()->newBoundVarExpr(str, int2string(count++));
      v.setType(tp[i]);
      args.push_back(v);
    }
    DebugAssert(args.size()>0, "TheoryUF::computeModel()");
    ExprHashMap<Expr>::iterator i=appls.begin(), iend=appls.end();
    DebugAssert(i!=iend, "TheoryUF::computeModel(): empty appls hash");
    // Use one of the concrete values as a default
    Expr res((*i).second); ++i;
    for(; i!=iend; ++i) {
      // Optimization: if the current value is the same as that of the
      // next application, skip this case; i.e. keep 'res' instead of
      // building ite(cond, res, res).
      if((*i).second == res) continue;

      // Create an ITE condition
      Expr cond;
      vector<Expr> eqs;
      for(int j=0, jend=args.size(); j<jend; ++j)
	eqs.push_back(args[j].eqExpr((*i).first[j]));
      if(eqs.size()==1)
	cond = eqs[0];
      else
	cond = andExpr(eqs);
      // Create an ITE
      res = cond.iteExpr((*i).second, res);
    }
    res = lambdaExpr(args, res);
    assignValue(e, res);
  }
}


Expr TheoryUF::computeTCC(const Expr& e)
{
  switch (e.getKind()) {
    case APPLY: {
      // Compute subtype predicates from the domain types applied to
      // the corresponding arguments.  That is, if f: (T0,..,Tn)->T,
      // and e = f(e0,...,en), then the TCC is
      //
      //   pred_T0(e0) & ... & pred_Tn(en) & TCC(e),
      //
      // where the last TCC(e) is the conjunction of TCCs for the
      // arguments, which ensures that all arguments are defined.
      //
      // If the operator is a lambda-expression, compute the TCC for
      // the beta-reduced expression.  We do this in a somewhat sneaky
      // but an efficient way: first, compute TCC of the op.body
      // (which depends on the bound vars), then wrap that into
      // lambda, and apply it to the arguments:
      //
      //   (LAMBDA(x0...xn): TCC(op.body)) (e0 ... en)
      //
      // The reason it is more efficient is that TCC(op.body) is cached,
      // and doesn't change with the arguments.
      
      vector<Expr> preds;
      preds.push_back(Theory::computeTCC(e));
      DebugAssert(e.isApply(), "Should be application");
      Expr op(e.getOp().getExpr());
      Type funType(op.getType());
      DebugAssert(funType.isFunction() || funType.isBool(),
		  "TheoryUF::computeTCC(): funType = "
		  +funType.toString());
      if(funType.isFunction()) {
	DebugAssert(funType.arity() == e.arity()+1,
		    "TheoryUF::computeTCC(): funType = "
		    +funType.toString()+"\n e = "+e.toString());
	for(int i=0, iend=e.arity(); i<iend; ++i) {
	  // Optimization: if the type of the formal argument is
	  // exactly the same as the type of the actual, then skip the
	  // type predicate for that argument
	  if(funType[i] != e[i].getType())
	    preds.push_back(getTypePred(funType[i], e[i]));
	}
      }
      // Now strip off all the LETDECL
      while(op.getKind()==LETDECL) op = op[1];
      // and add a TCC for the lambda-expression
      if(op.isLambda()) {
	preds.push_back(Expr(lambdaExpr(op.getVars(),
                                        getTCC(op.getBody())).mkOp(),
                             e.getKids()));
      }
      return rewriteAnd(andExpr(preds)).getRHS();
    }
    case LAMBDA:
      return trueExpr();
    default:
      DebugAssert(false,"Unexpected type: "+e.toString());
      return trueExpr();
  }
}

///////////////////////////////////////////////////////////////////////////////
// Pretty-printing			                                     //
///////////////////////////////////////////////////////////////////////////////

void TheoryUF::printSmtLibShared(ExprStream& os, const Expr& e) {
  DebugAssert( os.lang() == SMTLIB_LANG || os.lang() == SMTLIB_V2_LANG, "Illegal state in printSmtLibShared");
  switch( e.getKind() ) {
  case TYPEDECL:
    if( e.arity() == 1 && e[0].isString() ) {
      os << e[0].getString();
      break;
    }
    // If it's straight from the parser, we may have several type
    // names in one declaration.  Print these in LISP format.
    // Otherwise, print the name of the type.
    throw SmtlibException("TheoryUF::print: TYPEDECL not supported");
    //       if(e.arity() != 1) e.print(os);
    //       else if(e[0].isString()) os << e[0].getString();
    //       else e[0].print(os);
    break;
  case APPLY:
    if( e.arity() == 0 )
      os << e.getOp().getExpr();
    else {
      os << "(" << push << e.getOp().getExpr();
      for( int i = 0, iend = e.arity(); i < iend; ++i )
        os << space << e[i];
      if( e.getOpKind() == TRANS_CLOSURE ) {
        os << space << ":transclose";
      }
      os << push << ")";
    }
    break;
  case TRANS_CLOSURE:
    os << e.getName();
    break;
  case UFUNC:
    DebugAssert(e.isSymbol(), "Expected symbol");
    os << theoryCore()->getTranslator()->fixConstName(e.getName());
    break;
  default: {
    DebugAssert(false, "TheoryUF::print: SMTLIB_LANG: Unexpected expression: "
        +getEM()->getKindName(e.getKind()));
  }
  }
}

ExprStream& TheoryUF::print(ExprStream& os, const Expr& e) {
  switch(os.lang()) {
  case SIMPLIFY_LANG:
    switch(e.getKind()) {
    case OLD_ARROW:
    case ARROW:
      os<<"ERROR:ARROW:unsupported in Simplify\n";
      break;
    case LAMBDA: {
      os<<"ERROR:LAMBDA:unsupported in Simplify\n";
      break;
    }
    case TRANS_CLOSURE:
      os<<"ERROR:TRANS_CLOSURE:unsupported in Simplify\n";
      break;
    case TYPEDECL:
      os<<"ERROR:TYPEDECL:unsupported in Simplify\n";
      break;
    case UFUNC:
    case APPLY:
      if(e.isApply()) os << "(" << e.getOp().getExpr()<<" ";
      if(e.arity() > 0) {
	bool first(true);
	for (Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	  if(first) first = false;
	  else os << " " ;
	  os << *i;
	}
      os <<  ")";
      }
      break;
    default: {
      DebugAssert(false, "TheoryUF::print: Unexpected expression: "
		  +getEM()->getKindName(e.getKind()));
    }
    }
    break; // end of case SIMPLIFY_LANGUAGE

  case TPTP_LANG:
    switch(e.getKind()) {
    case OLD_ARROW:
    case ARROW:
      if(e.arity() < 2) e.printAST(os);
      else {
	os << "(" << push;
	bool first(true);
	for(int i=0, iend=e.arity()-1; i<iend; ++i) {
	  if(first) first=false;
	  else os << " * " ;
	  os << e[i];
	}
	os << ")" ;
	os <<  " > "  << e[e.arity()-1];
      }
      break;

    case LAMBDA: {
      os<<"ERROR:LAMBDA:unsupported in TPTP\n";
      break;
    }
    case TRANS_CLOSURE:
      os<<"ERROR:TRANS_CLOSURE:unsupported in TPTP\n";
      break;
    case TYPEDECL:
      if(e.arity() != 1) e.printAST(os);
      else os << e[0].getString();
      break;

    case UFUNC:
      DebugAssert(e.isSymbol(), "Expected symbol");
      os << to_lower(e.getName());
      break;

    case APPLY:
      if(e.isApply()) os <<e.getOpExpr()<<"(";
      if(e.arity() > 0) {
	bool first(true);
	for (Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	  if(first) first = false;
	  else os << "," ;
	  os << *i;
	}
      os <<  ")";
      }
      break;
    default: {
      DebugAssert(false, "TheoryUF::print: Unexpected expression: "
		  +getEM()->getKindName(e.getKind()));
    }
    }
    break; // end of case TPTP_LANGUAGE


  case PRESENTATION_LANG:
    switch(e.getKind()) {
    case OLD_ARROW:
    case ARROW:
      if(e.arity() < 2) e.printAST(os);
      else {
	if(e.arity() == 2)
	  os << e[0];
	else {
	  os << "(" << push;
	  bool first(true);
	  for(int i=0, iend=e.arity()-1; i<iend; ++i) {
	    if(first) first=false;
	    else os << "," << space;
	    os << e[i];
	  }
	  os << push << ")" << pop << pop;
	}
	os << space << "->" << space << e[e.arity()-1];
      }
      break;
    case TYPEDECL:
      // If it's straight from the parser, we may have several type
      // names in one declaration.  Print these in LISP format.
      // Otherwise, print the name of the type.
      if(e.arity() != 1) e.printAST(os);
      else os << e[0].getString();
      break;
    case LAMBDA: {
      DebugAssert(e.isLambda(), "Expected Lambda");
      os << "(" << push <<  "LAMBDA" << space << push;
      const vector<Expr>& vars = e.getVars();
      bool first(true);
      os << "(" << push;
      for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
          i!=iend; ++i) {
        if(first) first = false;
        else os << push << "," << pop << space;
        os << *i;
        // The lambda Expr may be in a raw parsed form, in which case
        // the type is not assigned yet
        if(i->isVar())
          os << ":" << space << pushdag << (*i).getType() << popdag;
      }
      os << push << "): " << pushdag << push
         << e.getBody() << push << ")";
      break;
    }
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
    case TRANS_CLOSURE:
      DebugAssert(e.isSymbol(), "Expected symbol");
      os << e.getName() << "*";
      break;
    case UFUNC:
      DebugAssert(e.isSymbol(), "Expected symbol");
      os << e.getName();
      break;
    default: {
      DebugAssert(false, "TheoryUF::print: Unexpected expression: "
		  +getEM()->getKindName(e.getKind()));
    }
    }
    break; // end of case PRESENTATION_LANGUAGE
  case SMTLIB_LANG:
    switch(e.getKind()) {
    case OLD_ARROW:
    case ARROW: {
      if(e.arity() < 2) {
        throw SmtlibException("TheoryUF::print: Expected 2 or more arguments to ARROW");
        //        e.print(os);
      }
      d_theoryUsed = true;
      os << push;
      bool oldDagFlag = os.dagFlag(false);
      int iend = e.arity();
      if (e[iend-1].getKind() == BOOLEAN) --iend;
      for(int i=0; i<iend; ++i) {
        if (i != 0) os << space;
	os << e[i];
      }
      os.dagFlag(oldDagFlag);
      break;
    }
    default:
      printSmtLibShared(os,e);
    }
    break; // End of SMT_LIB
  case SMTLIB_V2_LANG:
    switch(e.getKind()) {
    case OLD_ARROW:
    case ARROW: {
      /* Prints out a function type (A,B,C) -> D as "(A B C) D" */
      if(e.arity() < 2) {
        throw SmtlibException("TheoryUF::print: Expected 2 or more arguments to ARROW");
        //        e.print(os);
      }
      d_theoryUsed = true;
      bool oldDagFlag = os.dagFlag(false);
      os << push << "(";
      for( int i = 0; i < e.arity() - 1; ++i ) {
        if( i != 0 ) {
          os << space;
        }
        os << e[i];
      }
      os << ")" << space << e[e.arity() - 1] << pop ;
      os.dagFlag(oldDagFlag);
      break;
    }
    default:
      printSmtLibShared(os,e);
    }
    break; // End of SMT-LIB v2
  case LISP_LANG:
    switch(e.getKind()) {
    case OLD_ARROW:
    case ARROW:
      if(e.arity() < 2) e.printAST(os);
      os << "(" << push << "ARROW";
      for(int i=0, iend=e.arity(); i<iend; ++i)
	os << space << e[i];
      os << push << ")";
      break;
    case TRANS_CLOSURE:
      e.printAST(os);
      break;
    case TYPEDECL:
      // If it's straight from the parser, we may have several type
      // names in one declaration.  Print these in LISP format.
      // Otherwise, print the name of the type.
      if(e.arity() != 1) e.printAST(os);
      else if(e[0].isString()) os << e[0].getString();
      else e[0].print(os);
      break;
    case LAMBDA: {
      DebugAssert(e.isLambda(), "Expected LAMBDA");
      os << "(" << push <<  "LAMBDA" << space;
      const vector<Expr>& vars = e.getVars();
      bool first(true);
      os << "(" << push;
      for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
          i!=iend; ++i) {
        if(first) first = false;
        else os << space;
        os << "(" << push << *i;
        // The expression may be in a raw parsed form, in which case
        // the type is not assigned yet
        if(i->isVar())
          os << space << pushdag << (*i).getType() << popdag;
        os << push << ")" << pop << pop;
      }
      os << push << ")" << pop << pop << pushdag
         << e.getBody() << push << ")";
      break;
    }
    case APPLY:
      DebugAssert(e.isApply(), "Expected Apply");
      if (e.arity() == 0) os << e.getOp().getExpr();
      else {
	os << "(" << push << e.getOp().getExpr();
	for (int i=0, iend=e.arity(); i<iend; ++i)
	  os << space << e[i];
	os << push << ")";
      }
      break;
    default: {
      DebugAssert(false, "TheoryUF::print: Unexpected expression: "
		  +getEM()->getKindName(e.getKind()));
    }
    }
    break; // End of LISP_LANG
  case SPASS_LANG:
    switch(e.getKind()) {
    case UFUNC:
      os << e.getName();
      break;
    case APPLY:
      os << push << e.getOp().getExpr();
      if(e.arity() > 0) {
        os << "(" << e[0];
	for (int i=1, iend=e.arity(); i<iend; ++i)
          os << "," << space << e[i];
        os << ")";
      }
      os << push;
      break;
    case OLD_ARROW:
    case ARROW:
    case TRANS_CLOSURE:
    case TYPEDECL:
    case LAMBDA:
    default:
      throw SmtlibException("TheoryUF::print: Unexpected expression for SPASS_LANG: "
                            +getEM()->getKindName(e.getKind()));
    }
    break;
  default:
    // Print the top node in the default format, continue with
    // pretty-printing for children.
    e.printAST(os);
    break;
  }
  return os;
}

//////////////////////////////////////////////////////////////////////////////
//parseExprOp:
//translating special Exprs to regular EXPR??
///////////////////////////////////////////////////////////////////////////////
Expr
TheoryUF::parseExprOp(const Expr& e) {
  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  if(RAW_LIST != e.getKind()) return e;

  DebugAssert(e.arity() > 0,
	      "TheoryUF::parseExprOp:\n e = "+e.toString());

  if (e[0].getKind() == RAW_LIST) {
    if(e.arity() < 2)
      throw ParserException("Bad function application: "+e.toString());
    Expr::iterator i=e.begin(), iend=e.end();
    Expr op(parseExpr(*i)); ++i;
    vector<Expr> args;
    for(; i!=iend; ++i) args.push_back(parseExpr(*i));
    return Expr(op.mkOp(), args);
  }

  DebugAssert(e[0].getKind() == ID || e[0][0].getKind() == ID,
              "Expected identifier");
  int kind = e[0].getKind();
  if (kind == ID) kind = getEM()->getKind(e[0][0].getString());
  switch(kind) {
  case OLD_ARROW: {
    if (!theoryCore()->getFlags()["old-func-syntax"].getBool()) {
      throw ParserException("You seem to be using the old syntax for function types.\n"
                            "Please convert to the new syntax or run with +old-func-syntax");
    }
    DebugAssert(e.arity()==3,"Expected arity 3 in OLD_ARROW");
    Expr arg = parseExpr(e[1]);
    vector<Expr> k;
    if (arg.getOpKind() == TUPLE_TYPE) {
      Expr::iterator i = arg.begin(), iend=arg.end();
      for (; i != iend; ++i) {
        k.push_back(*i);
      }
    }
    else k.push_back(arg);
    k.push_back(parseExpr(e[2]));
    return Expr(ARROW, k);
  }
  case ARROW:
  case TYPEDECL: {
    vector<Expr> k;
    Expr::iterator i = e.begin(), iend=e.end();
    // Skip first element of the vector of kids in 'e'.
    // The first element is the operator.
    ++i; 
    // Parse the kids of e and push them into the vector 'k'
    for(; i!=iend; ++i) 
      k.push_back(parseExpr(*i));
    return Expr(kind, k, e.getEM());
    break;
  }
  case TRANS_CLOSURE: {
    if(e.arity() != 4)
      throw ParserException("Wrong number of arguments to "
			    "TRANS_CLOSURE expression\n"
			    " (expected 3 arguments): "+e.toString());
    const string& name = e[1][0].getString();
    Expr funExpr = resolveID(name);
    if (funExpr.isNull())
      throw ParserException("Attempt to take transitive closure of unknown "
                            "predicate"+name);
    return transClosureExpr(name, parseExpr(e[2]), parseExpr(e[3]));
  }
  case LAMBDA: { // (LAMBDA ((v1 ... vn tp1) ...) body)
    if(!(e.arity() == 3 && e[1].getKind() == RAW_LIST && e[1].arity() > 0))
      throw ParserException("Bad LAMBDA expression: "+e.toString());
    // Iterate through the groups of bound variables
    vector<pair<string,Type> > vars; // temporary stack of bound variables
    for(Expr::iterator i=e[1].begin(), iend=e[1].end(); i!=iend; ++i) {
      if(i->getKind() != RAW_LIST || i->arity() < 2)
	throw ParserException("Bad variable declaration block in LAMBDA "
			    "expression: "+i->toString()+
			    "\n e = "+e.toString());
      // Iterate through individual bound vars in the group.  The
      // last element is the type, which we have to rebuild and
      // parse, since it is used in the creation of bound variables.
      Type tp(parseExpr((*i)[i->arity()-1]));
      for(int j=0, jend=i->arity()-1; j<jend; ++j) {
	if((*i)[j].getKind() != ID)
	  throw ParserException("Bad variable declaration in LAMBDA"
			      " expression: "+(*i)[j].toString()+
			      "\n e = "+e.toString());
	vars.push_back(pair<string,Type>((*i)[j][0].getString(), tp));
      }
    }
    // Create all the bound vars and save them in a vector
    vector<Expr> boundVars;
    for(vector<pair<string,Type> >::iterator i=vars.begin(), iend=vars.end();
	i!=iend; ++i)
      boundVars.push_back(addBoundVar(i->first, i->second));
    // Rebuild the body
    Expr body(parseExpr(e[2]));
    // Build the resulting Expr as (LAMBDA (vars) body)
    return lambdaExpr(boundVars, body);
    break;
  }
  case RAW_LIST: // Lambda application
  default: { // Application of an uninterpreted function
    if(e.arity() < 2)
      throw ParserException("Bad function application: "+e.toString());
    Expr::iterator i=e.begin(), iend=e.end();
    Expr op(parseExpr(*i)); ++i;
    vector<Expr> args;
    for(; i!=iend; ++i) args.push_back(parseExpr(*i));
    return Expr(op.mkOp(), args);
  }
  }
  return e;
}


Expr TheoryUF::lambdaExpr(const vector<Expr>& vars, const Expr& body) {
  return getEM()->newClosureExpr(LAMBDA, vars, body);
}


Expr TheoryUF::transClosureExpr(const std::string& name, const Expr& e1,
				const Expr& e2) {
  return Expr(getEM()->newSymbolExpr(name, TRANS_CLOSURE).mkOp(), e1, e2);
}

void TheoryUF::addSharedTerm(const CVC3::Expr& e) {
  d_sharedTermsMap[e] = true;
}
