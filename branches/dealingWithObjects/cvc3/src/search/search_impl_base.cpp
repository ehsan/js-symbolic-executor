/*****************************************************************************/
/*!
 * \file search_impl_base.cpp
 * 
 * Author: Clark Barrett, Vijay Ganesh (CNF Converter)
 * 
 * Created: Fri Jan 17 14:19:54 2003
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


#include "search_impl_base.h"
#include "theory.h"
#include "eval_exception.h"
#include "search_rules.h"
#include "variable.h"
#include "command_line_flags.h"
#include "statistics.h"
#include "theorem_manager.h"
#include "expr_transform.h"
#include "assumptions.h"


using namespace std;


namespace CVC3 {


  class CoreSatAPI_implBase :public TheoryCore::CoreSatAPI {
    SearchImplBase* d_se;
  public:
    CoreSatAPI_implBase(SearchImplBase* se) : d_se(se) {}
    virtual ~CoreSatAPI_implBase() {}
    virtual void addLemma(const Theorem& thm, int priority, bool atBottomScope)
      { d_se->addFact(thm); }
    virtual Theorem addAssumption(const Expr& assump)
      { return d_se->newIntAssumption(assump); }
    virtual void addSplitter(const Expr& e, int priority)
      { d_se->addSplitter(e, priority); }
    virtual bool check(const Expr& e);
  };

bool CoreSatAPI_implBase::check(const Expr& e)
{
  Theorem thm;
  int scope = d_se->theoryCore()->getCM()->scopeLevel();
  d_se->theoryCore()->getCM()->push();
  QueryResult res = d_se->checkValid(e, thm);
  d_se->theoryCore()->getCM()->popto(scope);
  return res == VALID;
}



}


using namespace CVC3;


// class SearchImplBase::Splitter methods

// Constructor
SearchImplBase::Splitter::Splitter(const Literal& lit): d_lit(lit) {
d_lit.count()++;
  TRACE("Splitter", "Splitter(", d_lit, ")");
}

// Copy constructor
SearchImplBase::Splitter::Splitter(const SearchImplBase::Splitter& s)
  : d_lit(s.d_lit) {
  d_lit.count()++;
  TRACE("Splitter", "Splitter[copy](", d_lit, ")");
}

// Assignment
SearchImplBase::Splitter&
SearchImplBase::Splitter::operator=(const SearchImplBase::Splitter& s) {
  if(this == &s) return *this; // Self-assignment
  d_lit.count()--;
  d_lit = s.d_lit;
  d_lit.count()++;
  TRACE("Splitter", "Splitter[assign](", d_lit, ")");
  return *this;
}

// Destructor
SearchImplBase::Splitter::~Splitter() {
  d_lit.count()--;
  TRACE("Splitter", "~Splitter(", d_lit, ")");
}



//! Constructor
SearchImplBase::SearchImplBase(TheoryCore* core)
  : SearchEngine(core),
    d_bottomScope(core->getCM()->getCurrentContext()),
    d_dpSplitters(core->getCM()->getCurrentContext()),
    d_lastValid(d_commonRules->trueTheorem()),
    d_assumptions(core->getCM()->getCurrentContext()),
    d_cnfCache(core->getCM()->getCurrentContext()),
    d_cnfVars(core->getCM()->getCurrentContext()),
    d_cnfOption(&(core->getFlags()["cnf"].getBool())),
    d_ifLiftOption(&(core->getFlags()["iflift"].getBool())),
    d_ignoreCnfVarsOption(&(core->getFlags()["ignore-cnf-vars"].getBool())),
    d_origFormulaOption(&(core->getFlags()["orig-formula"].getBool())),
    d_enqueueCNFCache(core->getCM()->getCurrentContext()),
    d_applyCNFRulesCache(core->getCM()->getCurrentContext()),
    d_replaceITECache(core->getCM()->getCurrentContext())
{
  d_vm = new VariableManager(core->getCM(), d_rules,
			     core->getFlags()["mm"].getString());
  IF_DEBUG(d_assumptions.setName("CDList[SearchImplBase::d_assumptions]");)
  d_coreSatAPI_implBase = new CoreSatAPI_implBase(this);
  core->registerCoreSatAPI(d_coreSatAPI_implBase);
}


//! Destructor
SearchImplBase::~SearchImplBase()
{
  delete d_coreSatAPI_implBase;
  delete d_vm;
}


// Returns a new theorem if e has not already been asserted, otherwise returns
// a NULL theorem.
Theorem SearchImplBase::newUserAssumption(const Expr& e) {
  Theorem thm;
  CDMap<Expr,Theorem>::iterator i(d_assumptions.find(e));
  IF_DEBUG(if(debugger.trace("search verbose")) {
    ostream& os(debugger.getOS());
    os << "d_assumptions = [";
    for(CDMap<Expr,Theorem>::iterator i=d_assumptions.begin(),
	  iend=d_assumptions.end(); i!=iend; ++i) {
      debugger.getOS() << "(" << (*i).first << " => " << (*i).second << "), ";
    }
    os << "]" << endl;
  })
  if(i!=d_assumptions.end()) {
    TRACE("search verbose", "newUserAssumption(", e,
	  "): assumption already exists");
  } else {
    thm = d_commonRules->assumpRule(e);
    d_assumptions[e] = thm;
    e.setUserAssumption();
    TRACE("search verbose", "newUserAssumption(", thm,
	  "): created new assumption");
  }
  if (!thm.isNull()) d_core->addFact(d_core->getExprTrans()->preprocess(thm));
  return thm;
}


// Same as newUserAssertion, except it's an error to assert something that's
// already been asserted.
Theorem SearchImplBase::newIntAssumption(const Expr& e) {
  Theorem thm = d_commonRules->assumpRule(e);
  Expr atom = e.isNot() ? e[0] : e;
  thm.setQuantLevel(theoryCore()->getQuantLevelForTerm(atom));
  newIntAssumption(thm);
  return thm;
}


void SearchImplBase::newIntAssumption(const Theorem& thm) {
  DebugAssert(!d_assumptions.count(thm.getExpr()),
	      "newIntAssumption: repeated assertion: "+thm.getExpr().toString());
    d_assumptions[thm.getExpr()] = thm;
    thm.getExpr().setIntAssumption();
    TRACE("search verbose", "newIntAssumption(", thm,
	  "): new assumption");
}


void SearchImplBase::getUserAssumptions(vector<Expr>& assumptions)
{
  for(CDMap<Expr,Theorem>::orderedIterator i=d_assumptions.orderedBegin(),
	iend=d_assumptions.orderedEnd(); i!=iend; ++i)
    if ((*i).first.isUserAssumption()) assumptions.push_back((*i).first);
}


void SearchImplBase::getInternalAssumptions(std::vector<Expr>& assumptions)
{
  for(CDMap<Expr,Theorem>::orderedIterator i=d_assumptions.orderedBegin(),
	iend=d_assumptions.orderedEnd(); i!=iend; ++i)
    if ((*i).first.isIntAssumption()) assumptions.push_back((*i).first);
}


void SearchImplBase::getAssumptions(std::vector<Expr>& assumptions)
{
  for(CDMap<Expr,Theorem>::orderedIterator i=d_assumptions.orderedBegin(),
	iend=d_assumptions.orderedEnd(); i!=iend; ++i)
    assumptions.push_back((*i).first);
}


bool SearchImplBase::isAssumption(const Expr& e) {
  return d_assumptions.count(e) > 0;
}


void SearchImplBase::addCNFFact(const Theorem& thm, bool fromCore) {
  TRACE("addCNFFact", "addCNFFact(", thm.getExpr(), ") {");
  if(thm.isAbsLiteral()) {
    addLiteralFact(thm);
    // These literals are derived, and  should also be reported to the core.  
    if(!fromCore) d_core->enqueueFact(thm);
  } else {
    addNonLiteralFact(thm);
  }
  TRACE_MSG("addCNFFact", "addCNFFact => }");
}


void SearchImplBase::addFact(const Theorem& thm) {
  TRACE("search addFact", "SearchImplBase::addFact(", thm.getExpr(), ") {");
  if(*d_cnfOption)
    enqueueCNF(thm);
  else
    addCNFFact(thm, true);
  TRACE_MSG("search addFact", "SearchImplBase::addFact => }");
}


void SearchImplBase::addSplitter(const Expr& e, int priority) {
  DebugAssert(e.isAbsLiteral(), "SearchImplBase::addSplitter("+e.toString()+")");
  d_dpSplitters.push_back(Splitter(newLiteral(e)));
}


void SearchImplBase::getCounterExample(vector<Expr>& assertions, bool inOrder)
{
  if(!d_core->getTM()->withAssumptions())
    throw EvalException
      ("Method getCounterExample() (or command COUNTEREXAMPLE) cannot be used\n"
       " without assumptions activated");
  if(!d_lastValid.isNull())
    throw EvalException
      ("Method getCounterExample() (or command COUNTEREXAMPLE)\n"
       " must be called only after failed QUERY");
  getInternalAssumptions(assertions);
  /*

  if(!d_lastCounterExample.empty()) {
    if (inOrder) {
      for(CDMap<Expr,Theorem>::orderedIterator i=d_assumptions.orderedBegin(),
            iend=d_assumptions.orderedEnd(); i!=iend; ++i) {
        if (d_lastCounterExample.find((*i).first) != d_lastCounterExample.end()) {
          assertions.push_back((*i).first);
        }
      }
      DebugAssert(assertions.size()==d_lastCounterExample.size(),
                  "getCounterExample: missing assertion");
    }
    else {
      ExprHashMap<bool>::iterator i=d_lastCounterExample.begin(),
        iend = d_lastCounterExample.end();
      for(; i!=iend; ++i) assertions.push_back((*i).first);
    }
  }
  */
}


Proof 
SearchImplBase::getProof()
{
  if(!d_core->getTM()->withProof())
    throw EvalException
      ("DUMP_PROOF cannot be used without proofs activated");
  if(d_lastValid.isNull())
    throw EvalException
      ("DUMP_PROOF must be called only after successful QUERY");
  // Double-check for optimized version
  if(d_lastValid.isNull()) return Proof();
  return d_lastValid.getProof();
}


const Assumptions&
SearchImplBase::getAssumptionsUsed()
{
  if(!d_core->getTM()->withAssumptions())
    throw EvalException
      ("DUMP_ASSUMPTIONS cannot be used without assumptions activated");
  if(d_lastValid.isNull())
    throw EvalException
      ("DUMP_ASSUMPTIONS must be called only after successful QUERY");
  // Double-check for optimized version
  if(d_lastValid.isNull()) return Assumptions::emptyAssump();
  return d_lastValid.getAssumptionsRef();
}

/*! 
 * Given a proof of FALSE ('res') from an assumption 'e', derive the
 * proof of the inverse of e.
 *
 * \param res is a proof of FALSE
 * \param e is the assumption used in the above proof
 */
void SearchImplBase::processResult(const Theorem& res, const Expr& e)
{
  // Result must be either Null (== SAT) or false (== unSAT)
  DebugAssert(res.isNull() || res.getExpr().isFalse(),
	      "processResult: bad input"
	      + res.toString());
  if(res.isNull()) {
    // Didn't prove valid (if CVC-lite is complete, it means invalid).
    // The assumptions for the counterexample must have been already
    // set by checkSAT().
    d_lastValid = Theorem(); // Reset last proof
    // Remove !e, keep just the counterexample
    d_lastCounterExample.erase(!e);
    if (e.isNot()) d_lastCounterExample.erase(e[0]);
  } else {
    // Proved valid
    Theorem res2 =
      d_rules->eliminateSkolemAxioms(res, d_commonRules->getSkolemAxioms());
    if(e.isNot())
      d_lastValid = d_rules->negIntro(e, res2);
    else
      d_lastValid = d_rules->proofByContradiction(e, res2);
    d_lastCounterExample.clear(); // Reset counterexample
  }
}


QueryResult SearchImplBase::checkValid(const Expr& e, Theorem& result) {
  d_commonRules->clearSkolemAxioms();
  QueryResult qres = checkValidInternal(e);
  result = d_lastValid;
  return qres;
}


QueryResult SearchImplBase::restart(const Expr& e, Theorem& result) {
  QueryResult qres = restartInternal(e);
  result = d_lastValid;
  return qres;
}


void 
SearchImplBase::enqueueCNF(const Theorem& beta) {
  TRACE("mycnf", "enqueueCNF(", beta, ") {");
  if(*d_origFormulaOption)
    addCNFFact(beta);

  enqueueCNFrec(beta);
  TRACE_MSG("mycnf", "enqueueCNF => }");
}


void 
SearchImplBase::enqueueCNFrec(const Theorem& beta) {
  Theorem theta = beta;

  TRACE("mycnf","enqueueCNFrec(", theta.getExpr(), ") { ");
  TRACE("cnf-clauses", "enqueueCNF call", theta.getExpr(), "");
  // The theorem scope shouldn't be higher than current
  DebugAssert(theta.getScope() <= scopeLevel(),
	      "\n theta.getScope()="+int2string(theta.getScope())
	      +"\n scopeLevel="+int2string(scopeLevel())
	      +"\n e = "+theta.getExpr().toString());

  Expr thetaExpr = theta.getExpr();

  if(d_enqueueCNFCache.count(thetaExpr) > 0) {
    TRACE_MSG("mycnf", "enqueueCNFrec[cached] => }");
    return;
  }

  d_enqueueCNFCache[thetaExpr] = true;

  //   // Strip double negations first
  while(thetaExpr.isNot() && thetaExpr[0].isNot()) {
    theta = d_commonRules->notNotElim(theta);
    thetaExpr = theta.getExpr();
    // Cache all the derived theorems too
    d_enqueueCNFCache[thetaExpr] = true;
  }

  // Check for a propositional literal
  if(thetaExpr.isPropLiteral()) {
    theta = d_commonRules->iffMP(theta, replaceITE(thetaExpr));
    DebugAssert(!*d_ifLiftOption || theta.isAbsLiteral(),
		"Must be a literal: theta = "
		+theta.getExpr().toString());
    addCNFFact(theta);
    TRACE_MSG("mycnf", "enqueueCNFrec[literal] => }");
    TRACE("cnf-clauses", "literal with proofs(", theta.getExpr(), ")");
    return;
  }
  
  thetaExpr = theta.getExpr();
  // Obvious optimizations for AND and OR  
  switch(thetaExpr.getKind()) {
  case AND:
    // Split up the top-level conjunction and translate individually
    for(int i=0; i<thetaExpr.arity(); i++)
      enqueueCNFrec(d_commonRules->andElim(theta, i));
    TRACE_MSG("mycnf", "enqueueCNFrec[AND] => }");
    return;
  case OR: {
    // Check if we are already in CNF (ignoring ITEs in the terms),
    // and if we are, translate term ITEs on the way
    bool cnf(true);
    TRACE("bv mycnf", "enqueueCNFrec[OR] ( ", theta.getExpr().toString(), ")");
    for(Expr::iterator i=thetaExpr.begin(),iend=thetaExpr.end();
	i!=iend && cnf; i++) {
      if(!(*i).isPropLiteral())
	cnf = false;
    }
    if(cnf) {
      vector<Theorem> thms;
      vector<unsigned int> changed;
      unsigned int cc=0;
      for(Expr::iterator i=thetaExpr.begin(),iend=thetaExpr.end();
	  i!=iend; i++,cc++) {
	Theorem thm = replaceITE(*i);	
	if(thm.getLHS() != thm.getRHS()) {
	  thms.push_back(thm);
	  changed.push_back(cc);
	}
      }
      if(changed.size() > 0) {
	Theorem rewrite =
	  d_commonRules->substitutivityRule(theta.getExpr(), changed, thms);
	theta = d_commonRules->iffMP(theta, rewrite);
      }
      addCNFFact(theta);
      TRACE_MSG("mycnf", "enqueueCNFrec[cnf] => }");
      return;           
    }
    break;
  }
  case IFF: { // Check for "var <=> phi" and "phi <=> var"
    const Expr& t0 = thetaExpr[0];
    const Expr& t1 = thetaExpr[1];
    if(t1.isPropLiteral()) {
      if(!t1.isAbsLiteral())
	theta = d_commonRules->transitivityRule(theta, replaceITE(t1));
      applyCNFRules(theta);
      return;
    } else if(thetaExpr[0].isPropLiteral()) {
      theta = d_commonRules->symmetryRule(theta);
      if(!t0.isAbsLiteral())
	theta = d_commonRules->transitivityRule(theta, replaceITE(t0));
      applyCNFRules(theta);
      return;
    }
    break;
  }
  case ITE:
    if(thetaExpr[0].isPropLiteral() && thetaExpr[1].isPropLiteral()
       && thetaExpr[2].isPropLiteral()) {
      // Replace ITEs
      vector<Theorem> thms;
      vector<unsigned int> changed;
      for(int c=0, cend=thetaExpr.arity(); c<cend; ++c) {
	Theorem thm = replaceITE(thetaExpr[c]);
	if(thm.getLHS() != thm.getRHS()) {
	  DebugAssert(!*d_ifLiftOption || thm.getRHS().isAbsLiteral(),
		      "thm = "+thm.getExpr().toString());
	  thms.push_back(thm);
	  changed.push_back(c);
	}
      }
      if(changed.size() > 0) {
	Theorem rewrite =
	  d_commonRules->substitutivityRule(theta.getExpr(), changed, thms);
	theta = d_commonRules->iffMP(theta, rewrite);
      }
      // Convert to clauses
      Theorem thm = d_rules->iteToClauses(theta);
      DebugAssert(thm.getExpr().isAnd() && thm.getExpr().arity()==2,
		  "enqueueCNFrec [ITE over literals]\n thm = "
		  +thm.getExpr().toString());
      addCNFFact(d_commonRules->andElim(thm, 0));
      addCNFFact(d_commonRules->andElim(thm, 1));
      return;
    }
    break;
  default: 
    break;
  }

  // Now do the real work
  Theorem res = findInCNFCache(theta.getExpr());
  if(!res.isNull()) {
    Theorem thm = d_commonRules->iffMP(theta, res);
    DebugAssert(thm.isAbsLiteral(), "thm = "+thm.getExpr().toString());
    addCNFFact(thm);
    TRACE("cnf-clauses", "enqueueCNFrec call[cache hit]:(",
	  thm.getExpr(), ")");
    applyCNFRules(res);
    TRACE_MSG("mycnf", "enqueueCNFrec[cached] => }");
    return;
  }

  //  std::vector<Theorem> clauses;
  Theorem result;
  // (\phi <==> v)
  result = d_commonRules->varIntroSkolem(theta.getExpr());

  TRACE("mycnf", "enqueueCNFrec: varIntroSkolem => ", result.getExpr(),
	" @ "+int2string(result.getScope())
	+" (current="+int2string(scopeLevel())+")");

  //result = skolemize(result, false);

  TRACE("mycnf", "enqueueCNFrec: skolemize => ", result.getExpr(),
	" @ "+int2string(result.getScope())
	+" (current="+int2string(scopeLevel())+")");
  DebugAssert(result.isRewrite(),
	      "SearchImplBase::CNF(): result = "+result.toString());
  DebugAssert(!result.getLHS().isPropLiteral() && 
	      result.getRHS().isPropLiteral(),
	      "SearchImplBase::CNF(): result = "+result.toString());
  DebugAssert(result.getLHS() == theta.getExpr(),
	      "SearchImplBase::CNF(): result = "+result.toString()
	      +"\n theta = "+theta.toString());
  
  //enqueue v
  Theorem var(d_commonRules->iffMP(theta, result));
  // Add variable to the set of CNF vars
  d_cnfVars[var.getExpr()] = true;
  TRACE("mycnf", "enqueueCNFrec: theta = ", theta.getExpr(),
	" @ "+int2string(theta.getScope())
	+" (current="+int2string(scopeLevel())+")");
  TRACE("mycnf", "enqueueCNFrec: var = ", var.getExpr(),
	" @ "+int2string(var.getScope())
	+" (current="+int2string(scopeLevel())+")");
  DebugAssert(var.isAbsLiteral(), "var = "+var.getExpr().toString());
  addCNFFact(var);
  // phi <=> v
  addToCNFCache(result);
  applyCNFRules(result);
  TRACE_MSG("mycnf", "enqueueCNFrec => }");
}


/*!
 * \param thm is the input of the form phi <=> v
 */
void
SearchImplBase::applyCNFRules(const Theorem& thm) {
  TRACE("mycnf", "applyCNFRules(", thm.getExpr(), ") { ");
  
  Theorem result = thm;
  DebugAssert(result.isRewrite(),
	      "SearchImplBase::applyCNFRules: input must be an iff: " + 
	      result.getExpr().toString());
  Expr lhs = result.getLHS();
  Expr rhs = result.getRHS();
  DebugAssert(rhs.isAbsLiteral(),
	      "SearchImplBase::applyCNFRules: rhs of input must be literal: " +
	      result.getExpr().toString());

  // Eliminate negation first
  while(result.getLHS().isNot())
    result = d_commonRules->iffContrapositive(result);
  lhs = result.getLHS();
  rhs = result.getRHS();
  
  CDMap<Expr,bool>::iterator it = d_applyCNFRulesCache.find(lhs);
  if(it == d_applyCNFRulesCache.end())
    d_applyCNFRulesCache[lhs] = true;
  else {
    TRACE_MSG("mycnf","applyCNFRules[temp cache] => }");
    return;
  }
  
  // Catch the trivial case v1 <=> v2
  if(lhs.isPropLiteral()) {
    if(!lhs.isAbsLiteral()) {
      Theorem replaced = d_commonRules->symmetryRule(replaceITE(lhs));
      result = d_commonRules->transitivityRule(replaced, result);
      lhs = result.getLHS();
      DebugAssert(rhs == result.getRHS(),
		  "applyCNFRules [literal lhs]\n result = "
    		  +result.getExpr().toString()
    		  +"\n rhs = "+rhs.toString());
    }
    Theorem thm = d_rules->iffToClauses(result);
    DebugAssert(thm.getExpr().isAnd() && thm.getExpr().arity()==2,
		"applyCNFRules [literal lhs]\n thm = "
		+thm.getExpr().toString());
    addCNFFact(d_commonRules->andElim(thm, 0));
    addCNFFact(d_commonRules->andElim(thm, 1));
    return;
  }
  
  // Check the kids in e[0], replace them with cache[e[0][i]], rebuild thm
  vector<unsigned> changed;
  vector<Theorem> substitutions;
  int c=0;
  for(Expr::iterator j = lhs.begin(), jend = lhs.end(); j!=jend; ++c,++j) {
    const Expr& phi = *j;
    if(!phi.isPropLiteral()) {
      Theorem phiIffVar = findInCNFCache(phi);
      if(phiIffVar.isNull()) {
	// Create a new variable for this child
	phiIffVar = d_commonRules->varIntroSkolem(phi);
	addToCNFCache(phiIffVar);
      }
      DebugAssert(phiIffVar.isRewrite(),
		  "SearchImplBase::applyCNFRules: result = " +
		  result.toString());
      DebugAssert(phi == phiIffVar.getLHS(),
		  "SearchImplBase::applyCNFRules:\n phi = " + 
		  phi.toString()
		  + "\n\n phiIffVar = " + phiIffVar.toString());
      DebugAssert(phiIffVar.getRHS().isAbsLiteral(),
		  "SearchImplBase::applyCNFRules: phiIffVar = " +
		  phiIffVar.toString());
      changed.push_back(c);
      substitutions.push_back(phiIffVar);
      applyCNFRules(phiIffVar);
    }
  }
  if(changed.size() > 0) {
    Theorem subst = 
      d_commonRules->substitutivityRule(lhs, changed, substitutions);
    subst = d_commonRules->symmetryRule(subst);
    result = d_commonRules->transitivityRule(subst, result);
  }

  switch(result.getLHS().getKind()) {
  case AND:
    result = d_rules->andCNFRule(result);
    break;
  case OR:
    result = d_rules->orCNFRule(result);
    break;
  case IFF:
    result = d_rules->iffCNFRule(result);
    break;
  case IMPLIES:
    result = d_rules->impCNFRule(result);
    break;
  case ITE:
    result = d_rules->iteCNFRule(result);
    break;
  default:
    DebugAssert(false,
		"SearchImplBase::applyCNFRules: "
		"the input operator must be and|or|iff|imp|ite\n result = " + 
		result.getLHS().toString());
    break;
  }

  // FIXME: eliminate this once debugged
  Theorem clauses(result);

  // Enqueue the clauses
  DebugAssert(!clauses.isNull(), "Oops!..");
  DebugAssert(clauses.getExpr().isAnd(), "clauses = "
	      +clauses.getExpr().toString());

  // The clauses may containt term ITEs, and we need to translate those
  
  for(int i=0, iend=clauses.getExpr().arity(); i<iend; ++i) {
    Theorem clause(d_commonRules->andElim(clauses,i));
    addCNFFact(clause);
  }
  TRACE_MSG("mycnf","applyCNFRules => }");
}


bool SearchImplBase::isClause(const Expr& e) {
  if(e.isAbsLiteral()) return true;
  if(!e.isOr()) return false;

  bool cnf(true);
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend && cnf; ++i)
    cnf = (*i).isAbsLiteral();
  return cnf;
}


bool
SearchImplBase::isPropClause(const Expr& e) {
  if(e.isPropLiteral()) return true;
  if(!e.isOr()) return false;

  bool cnf(true);
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend && cnf; ++i)
    cnf = (*i).isPropLiteral();
  return cnf;
}


bool
SearchImplBase::isGoodSplitter(const Expr& e) {
  if(!*d_ignoreCnfVarsOption) return true;
  TRACE("isGoodSplitter", "isGoodSplitter(", e, ") {");
  // Check for var being an auxiliary CNF variable
  const Expr& var = e.isNot()? e[0] : e;
  bool res(!isCNFVar(var));
  TRACE("isGoodSplitter", "isGoodSplitter => ", res? "true" : "false", " }");
  return res;
}


void
SearchImplBase::addToCNFCache(const Theorem& thm) {
  TRACE("mycnf", "addToCNFCache(", thm.getExpr(), ")");

  d_core->getStatistics().counter("CNF New Vars")++;

  Theorem result = thm;
  DebugAssert(result.isRewrite(),
	      "SearchImplBase::addToCNFCache: input must be an iff: " + 
	      result.getExpr().toString());
  // Record the CNF variable
  d_cnfVars[thm.getRHS()] = true;

  Theorem t(thm);
  Expr phi = thm.getLHS();
  while(phi.isNot()) {
    t = d_commonRules->iffContrapositive(thm);
    phi = phi[0];
  }
  DebugAssert(d_cnfCache.count(phi) == 0, 
	      "thm = "+thm.getExpr().toString() + 
	      "\n t = "+ t.getExpr().toString());
  //d_cnfCache.insert(phi, t);
  d_cnfCache.insert(phi, t, d_bottomScope);
}


Theorem 
SearchImplBase::findInCNFCache(const Expr& e) { 
  TRACE("mycnf", "findInCNFCache(", e, ") { ");
  Expr phi(e);

  int numNegs(0);
  // Strip all the top-level negations from e
  while(phi.isNot()) {
    phi = phi[0]; numNegs++;
  }
  CDMap<Expr,Theorem>::iterator it = d_cnfCache.find(phi);
  if(it != d_cnfCache.end()) {
    // IF_DEBUG(debugger.counter("CNF cache hits")++;)
    d_core->getStatistics().counter("CNF cache hits")++;
    Theorem thm = (*it).second;
    
    DebugAssert(thm.isRewrite() && thm.getLHS() == phi,
		"SearchImplBase::findInCNFCache: thm must be an iff: " + 
		thm.getExpr().toString());
    
    // Now put all the negations back.  If the number of negations is
    // odd, first transform phi<=>v into !phi<=>!v.  Then apply
    // !!phi<=>phi rewrite as many times as needed.
    if(numNegs % 2 != 0) {
      thm = d_commonRules->iffContrapositive(thm); 
      numNegs--;
    }
    for(; numNegs > 0; numNegs-=2) {
      Theorem t = d_commonRules->rewriteNotNot(!!(thm.getLHS()));
      thm = d_commonRules->transitivityRule(t,thm);
    }

    DebugAssert(numNegs == 0, "numNegs = "+int2string(numNegs));
    TRACE("mycnf", "findInCNFCache => ", thm.getExpr(), " }");
    return thm;
  }
  TRACE_MSG("mycnf", "findInCNFCache => null  }");
  return Theorem();
}

/*!
 * Strategy:
 *
 * For a given atomic formula phi(ite(c, t1, t2)) which depends on a
 * term ITE, generate an equisatisfiable formula:
 *
 * phi(x) & ite(c, t1=x, t2=x),
 *
 * where x is a new variable.
 *
 * The phi(x) part will be generated by the caller, and our job is to
 * assert the 'ite(c, t1=x, t2=x)', and return a rewrite theorem
 * phi(ite(c, t1, t2)) <=> phi(x).
 */
Theorem
SearchImplBase::replaceITE(const Expr& e) {
  TRACE("replaceITE","replaceITE(", e, ") { ");
  Theorem res;

  CDMap<Expr,Theorem>::iterator i=d_replaceITECache.find(e),
    iend=d_replaceITECache.end();
  if(i!=iend) {
    TRACE("replaceITE", "replaceITE[cached] => ", (*i).second, " }");
    return (*i).second;
  }
  
  if(e.isAbsLiteral())
    res = d_core->rewriteLiteral(e);
  else
    res = d_commonRules->reflexivityRule(e);


  // If 'res' is e<=>phi, and the resulting formula phi is not a
  // literal, introduce a new variable x, enqueue phi<=>x, and return
  // e<=>x.
  if(!res.getRHS().isPropLiteral()) {
    Theorem varThm(findInCNFCache(res.getRHS()));
    if(varThm.isNull()) {
      varThm = d_commonRules->varIntroSkolem(res.getRHS());
      Theorem var;
      if(res.isRewrite())
	var = d_commonRules->transitivityRule(res,varThm);
      else 
	var = d_commonRules->iffMP(res,varThm);
      //d_cnfVars[var.getExpr()] = true;
      //addCNFFact(var);
      addToCNFCache(varThm);
    }
    applyCNFRules(varThm);
    //enqueueCNFrec(varThm);
    res = d_commonRules->transitivityRule(res, varThm);
  }
  
  d_replaceITECache[e] = res;
  
  TRACE("replaceITE", "replaceITE => ", res, " }");
  return res;
}
