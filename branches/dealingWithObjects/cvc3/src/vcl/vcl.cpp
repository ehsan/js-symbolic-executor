/*****************************************************************************/
/*!
 * \file vcl.cpp
 *
 * Author: Clark Barrett
 *
 * Created: Tue Dec 31 18:27:11 2002
 *
 * <hr>
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 *
 * <hr>
 *
 */
/*****************************************************************************/


#include <fstream>
#include "os.h"
#include "vcl.h"
#include "parser.h"
#include "vc_cmd.h"
#include "search_simple.h"
#include "search_fast.h"
#include "search_sat.h"
#include "theory_core.h"
#include "theory_uf.h"
#include "theory_arith_old.h"
#include "theory_arith_new.h"
#include "theory_arith3.h"
#include "theory_bitvector.h"
#include "theory_array.h"
#include "theory_quant.h"
#include "theory_records.h"
#include "theory_simulate.h"
#include "theory_datatype.h"
#include "theory_datatype_lazy.h"
#include "translator.h"
#include "typecheck_exception.h"
#include "eval_exception.h"
#include "expr_transform.h"
#include "theorem_manager.h"
#include "assumptions.h"
#include "parser_exception.h"


using namespace std;
using namespace CVC3;

//namespace CVC3{
//  VCL* myvcl;
//}

///////////////////////////////////////////////////////////////////////////////
// Static ValidityChecker methods
///////////////////////////////////////////////////////////////////////////////



ValidityChecker* ValidityChecker::create(const CLFlags& flags)
{
  return new VCL(flags);
}


CLFlags ValidityChecker::createFlags() {
  CLFlags flags;
  // We expect the user to type cvc3 -h to get help, which will set
  // the "help" flag to false; that's why it's initially true.

  // Overall system control flags
  flags.addFlag("timeout", CLFlag(0, "Kill cvc3 process after given number of seconds (0==no limit)"));
  flags.addFlag("stimeout", CLFlag(0, "Set time resource limit in tenths of seconds for a query(0==no limit)"));
  flags.addFlag("resource", CLFlag(0, "Set finite resource limit (0==no limit)"));
  flags.addFlag("mm", CLFlag("chunks", "Memory manager (chunks, malloc)"));

  // Information printing flags
  flags.addFlag("help",CLFlag(true, "print usage information and exit"));
  flags.addFlag("unsupported",CLFlag(true, "print usage for old/unsupported/experimental options"));
  flags.addFlag("version",CLFlag(true, "print version information and exit"));
  flags.addFlag("interactive", CLFlag(false, "Interactive mode"));
  flags.addFlag("stats", CLFlag(false, "Print run-time statistics"));
  flags.addFlag("seed", CLFlag(1, "Set the seed for random sequence"));
  flags.addFlag("printResults", CLFlag(true, "Print results of interactive commands."));
  flags.addFlag("dump-log", CLFlag("", "Dump API call log in CVC3 input "
				   "format to given file "
				   "(off when file name is \"\")"));
  flags.addFlag("parse-only", CLFlag(false,"Parse the input, then exit."));

  //Translation related flags
  flags.addFlag("expResult", CLFlag("", "For smtlib translation.  Give the expected result", false));
  flags.addFlag("category", CLFlag("unknown", "For smtlib translation.  Give the category", false));
  flags.addFlag("translate", CLFlag(false, "Produce a complete translation from "
                                    "the input language to output language.  "));
  flags.addFlag("real2int", CLFlag(false, "When translating, convert reals to integers.", false));
  flags.addFlag("convertArith", CLFlag(false, "When translating, try to rewrite arith terms into smt-lib subset", false));
  flags.addFlag("convert2diff", CLFlag("", "When translating, try to force into difference logic.  Legal values are int and real.", false));
  flags.addFlag("iteLiftArith", CLFlag(false, "For translation.  If true, ite's are lifted out of arith exprs.", false));
  flags.addFlag("convertArray", CLFlag(false, "For translation.  If true, arrays are converted to uninterpreted functions if possible.", false));
  flags.addFlag("combineAssump", CLFlag(false, "For translation.  If true, assumptions are combined into the query.", false));
  flags.addFlag("convert2array", CLFlag(false, "For translation. If true, try to convert to array-only theory", false));
  flags.addFlag("convertToBV",CLFlag(0, "For translation.  Set to nonzero to convert ints to bv's of that length", false));
  flags.addFlag("convert-eq-iff",CLFlag(false, "Convert equality on Boolean expressions to iff.", false));
  flags.addFlag("preSimplify",CLFlag(false, "Simplify each assertion or query before translating it", false));
  flags.addFlag("dump-tcc", CLFlag(false, "Compute and dump TCC only"));
  flags.addFlag("trans-skip-pp", CLFlag(false, "Skip preprocess step in translation module", false));
  flags.addFlag("trans-skip-difficulty", CLFlag(false, "Leave out difficulty attribute during translation to SMT v2.0", false));
  flags.addFlag("promote", CLFlag(true, "Promote undefined logic combinations to defined logic combinations during translation to SMT", false));

  // Parser related flags
  flags.addFlag("old-func-syntax",CLFlag(false, "Enable parsing of old-style function syntax", false));

  // Pretty-printing related flags
  flags.addFlag("dagify-exprs",
		CLFlag(true, "Print expressions with sharing as DAGs"));
  flags.addFlag("lang", CLFlag("presentation", "Input language "
			       "(presentation, smt, smt2, internal)"));
  flags.addFlag("output-lang", CLFlag("", "Output language "
				      "(presentation, smtlib, simplify, internal, lisp, tptp, spass)"));
  flags.addFlag("indent", CLFlag(false, "Print expressions with indentation"));
  flags.addFlag("width", CLFlag(80, "Suggested line width for printing"));
  flags.addFlag("print-depth", CLFlag(-1, "Max. depth to print expressions "));
  flags.addFlag("print-assump", CLFlag(false, "Print assumptions in Theorems "));

  // Search Engine (SAT) related flags
  flags.addFlag("sat",CLFlag("minisat", "choose a SAT solver to use "
			     "(sat, minisat)"));
  flags.addFlag("de",CLFlag("dfs", "choose a decision engine to use "
			    "(dfs, sat)"));

  // Proofs and Assumptions
  flags.addFlag("proofs", CLFlag(false, "Produce proofs"));
  flags.addFlag("check-proofs",
		CLFlag(IF_DEBUG(true ||) false, "Check proofs on-the-fly"));
  flags.addFlag("minimizeClauses", CLFlag(false, "Use brute-force minimization of clauses", false));
  flags.addFlag("dynack", CLFlag(false, "Use dynamic Ackermannization", false));
  flags.addFlag("smart-clauses", CLFlag(true, "Learn multiple clauses per conflict"));


  // Core framework switches
  flags.addFlag("tcc", CLFlag(false, "Check TCCs for each ASSERT and QUERY"));
  flags.addFlag("cnf", CLFlag(true, "Convert top-level Boolean formulas to CNF", false));
  flags.addFlag("ignore-cnf-vars", CLFlag(false, "Do not split on aux. CNF vars (with +cnf)", false));
  flags.addFlag("orig-formula", CLFlag(false, "Preserve the original formula with +cnf (for splitter heuristics)", false));
  flags.addFlag("liftITE", CLFlag(false, "Eagerly lift all ITE exprs"));
  flags.addFlag("iflift", CLFlag(false, "Translate if-then-else terms to CNF (with +cnf)", false));
  flags.addFlag("circuit", CLFlag(false, "With +cnf, use circuit propagation", false));
  flags.addFlag("un-ite-ify", CLFlag(false, "Unconvert ITE expressions", false));
  flags.addFlag("ite-cond-simp",
		CLFlag(false, "Replace ITE condition by TRUE/FALSE in subexprs", false));
  flags.addFlag("preprocess", CLFlag(true, "Preprocess queries"));
  flags.addFlag("pp-pushneg", CLFlag(false, "Push negation in preprocessor"));
  flags.addFlag("pp-bryant", CLFlag(false, "Enable Bryant algorithm for UF", false));
  flags.addFlag("pp-budget", CLFlag(0, "Budget for new preprocessing step", false));
  flags.addFlag("pp-care", CLFlag(true, "Enable care-set preprocessing step", false));
  flags.addFlag("simp-and", CLFlag(false, "Rewrite x&y to x&y[x/true]", false));
  flags.addFlag("simp-or", CLFlag(false, "Rewrite x|y to x|y[x/false]", false));
  flags.addFlag("pp-batch", CLFlag(false, "Ignore assumptions until query, then process all at once"));

  // Negate the query when translate into tptp
  flags.addFlag("negate-query", CLFlag(true, "Negate the query when translate into TPTP format"));;

  // Concrete model generation (counterexamples) flags
  flags.addFlag("counterexample", CLFlag(false, "Dump counterexample if formula is invalid or satisfiable"));
  flags.addFlag("model", CLFlag(false, "Dump model if formula is invalid or satisfiable"));
  flags.addFlag("unknown-check-model", CLFlag(false, "Try to generate model if formula is unknown"));
  flags.addFlag("applications", CLFlag(true, "Add relevant function applications and array accesses to the concrete countermodel"));
  // Debugging flags (only for the debug build)
  // #ifdef _CVC3_DEBUG_MODE
  vector<pair<string,bool> > sv;
  flags.addFlag("trace", CLFlag(sv, "Tracing.  Multiple flags add up."));
  flags.addFlag("dump-trace", CLFlag("", "Dump debugging trace to "
				   "given file (off when file name is \"\")"));
  // #endif
  // DP-specific flags

  // Arithmetic
  flags.addFlag("arith-new",CLFlag(false, "Use new arithmetic dp", false));
  flags.addFlag("arith3",CLFlag(false, "Use old arithmetic dp that works well with combined theories", false));
  flags.addFlag("var-order",
		CLFlag(false, "Use simple variable order in arith", false));
  flags.addFlag("ineq-delay", CLFlag(0, "Accumulate this many inequalities before processing (-1 for don't process until necessary)"));

  flags.addFlag("nonlinear-sign-split", CLFlag(true, "Whether to split on the signs of nontrivial nonlinear terms"));

  flags.addFlag("grayshadow-threshold", CLFlag(-1, "Ignore gray shadows bigger than this (makes solver incomplete)"));
  flags.addFlag("pathlength-threshold", CLFlag(-1, "Ignore gray shadows bigger than this (makes solver incomplete)"));

  // Arrays
  flags.addFlag("liftReadIte", CLFlag(true, "Lift read of ite"));

  //for LFSC stuff, disable Tseitin CNF conversion, by Yeting
  flags.addFlag("cnf-formula", CLFlag(false, "The input must be in CNF. This option automatically enables '-de sat' and disable preprocess"));

  //for LFSC print out, by Yeting
  //flags.addFlag("lfsc", CLFlag(false, "the input is already in CNF. This option automatically enables -de sat and disable -preprocess"));

  // for LFSC print, allows different modes by Liana
  flags.addFlag("lfsc-mode",
                  CLFlag(0, "lfsc mode 0: off, 1:normal, 2:cvc3-mimic etc."));


  // Quantifiers
  flags.addFlag("max-quant-inst", CLFlag(200, "The maximum number of"
			       	" naive instantiations"));

  flags.addFlag("quant-new",
		 CLFlag(true, "If this option is false, only naive instantiation is called"));

  flags.addFlag("quant-lazy", CLFlag(false, "Instantiate lazily", false));

  flags.addFlag("quant-sem-match",
		CLFlag(false, "Attempt to match semantically when instantiating", false));

//   flags.addFlag("quant-const-match",
//                 CLFlag(true, "When matching semantically, only match with constants", false));

  flags.addFlag("quant-complete-inst",
		CLFlag(false, "Try complete instantiation heuristic.  +pp-batch will be automatically enabled"));

  flags.addFlag("quant-max-IL",
		CLFlag(100, "The maximum Instantiation Level allowed"));

  flags.addFlag("quant-inst-lcache",
                CLFlag(true, "Cache instantiations"));

  flags.addFlag("quant-inst-gcache",
                CLFlag(false, "Cache instantiations", false));

  flags.addFlag("quant-inst-tcache",
                CLFlag(false, "Cache instantiations", false));


  flags.addFlag("quant-inst-true",
                CLFlag(true, "Ignore true instantiations"));

  flags.addFlag("quant-pullvar",
                CLFlag(false, "Pull out vars", false));

  flags.addFlag("quant-score",
                CLFlag(true, "Use instantiation level"));

  flags.addFlag("quant-polarity",
                CLFlag(false, "Use polarity ", false));

  flags.addFlag("quant-eqnew",
                CLFlag(true, "Use new equality matching"));

  flags.addFlag("quant-max-score",
                CLFlag(0, "Maximum initial dynamic score"));

  flags.addFlag("quant-trans3",
                CLFlag(true, "Use trans heuristic"));

  flags.addFlag("quant-trans2",
                CLFlag(true, "Use trans2 heuristic"));

  flags.addFlag("quant-naive-num",
                CLFlag(1000, "Maximum number to call naive instantiation"));

  flags.addFlag("quant-naive-inst",
                CLFlag(true, "Use naive instantiation"));

  flags.addFlag("quant-man-trig",
                CLFlag(true, "Use manual triggers"));

  flags.addFlag("quant-gfact",
                CLFlag(false, "Send facts to core directly", false));

  flags.addFlag("quant-glimit",
                CLFlag(1000, "Limit for gfacts", false));

  flags.addFlag("print-var-type", //by yeting, as requested by Sascha Boehme for proofs
                CLFlag(false, "Print types for bound variables"));

  //Bitvectors
  flags.addFlag("bv32-flag",
		CLFlag(false, "assume that all bitvectors are 32bits with no overflow", false));

  // Uninterpreted Functions
  flags.addFlag("trans-closure",
		CLFlag(false,"enables transitive closure of binary relations", false));

  // Datatypes
  flags.addFlag("dt-smartsplits",
                CLFlag(true, "enables smart splitting in datatype theory", false));
  flags.addFlag("dt-lazy",
                CLFlag(false, "lazy splitting on datatypes", false));


  return flags;
}


ValidityChecker* ValidityChecker::create()
{
  return new VCL(createFlags());
}


///////////////////////////////////////////////////////////////////////////////
// VCL private methods
///////////////////////////////////////////////////////////////////////////////


Theorem3 VCL::deriveClosure(const Theorem3& thm) {
  vector<Expr> assump;
  set<UserAssertion> assumpSet;
  // Compute the vector of assumptions for thm, and iteratively move
  // the assumptions to the RHS until done.  Each closure step may
  // introduce new assumptions from the proofs of TCCs, so those need
  // to be dealt with in the same way, until no assumptions remain.
  Theorem3 res = thm;
  vector<Theorem> tccs;
  while(true) {
    {
      const Assumptions& a(res.getAssumptionsRef());
      if (a.empty()) break;
      assump.clear();
      assumpSet.clear();
      Assumptions::iterator i=a.begin(), iend=a.end();
      if(i!=iend) i->clearAllFlags();
      // Collect the assumptions of 'res' *without* TCCs
      for(; i!=iend; ++i)
        getAssumptionsRec(*i, assumpSet, false);

      // Build the vectors of assumptions and TCCs
      if(getFlags()["tcc"].getBool()) {
        tccs.clear();
        for(set<UserAssertion>::iterator i=assumpSet.begin(),
              iend=assumpSet.end(); i!=iend; ++i) {
          assump.push_back(i->thm().getExpr());
          tccs.push_back(i->tcc());
        }
      }
    }
    // Derive the closure
    res = d_se->getCommonRules()->implIntro3(res, assump, tccs);
  }
  return res;
}


//! Recursive assumption graph traversal to find user assumptions
/*!
 *  If an assumption has a TCC, traverse the proof of TCC and add its
 *  assumptions to the set recursively.
 */
void VCL::getAssumptionsRec(const Theorem& thm,
			    set<UserAssertion>& assumptions,
			    bool addTCCs) {
  if(thm.isNull() || thm.isRefl() || thm.isFlagged()) return;
  thm.setFlag();
  if(thm.isAssump()) {
    if(d_userAssertions->count(thm.getExpr())>0) {
      const UserAssertion& a = (*d_userAssertions)[thm.getExpr()];
      assumptions.insert(a);
      if(addTCCs) {
	DebugAssert(!a.tcc().isNull(), "getAssumptionsRec(a="
		    +a.thm().toString()+", thm = "+thm.toString()+")");
	getAssumptionsRec(a.tcc(), assumptions, true);
      }
    } else { // it's a splitter
      UserAssertion a(thm, Theorem(), d_nextIdx++);
      assumptions.insert(a);
    }
  }
  else {
    const Assumptions& a(thm.getAssumptionsRef());
    for(Assumptions::iterator i=a.begin(), iend=a.end(); i!=iend; ++i)
      getAssumptionsRec(*i, assumptions, addTCCs);
  }
}


void VCL::getAssumptions(const Assumptions& a, vector<Expr>& assumptions)
{
  set<UserAssertion> assumpSet;
  if(a.empty()) return;
  Assumptions::iterator i=a.begin(), iend=a.end();
  if(i!=iend) i->clearAllFlags();
  for(; i!=iend; ++i)
    getAssumptionsRec(*i, assumpSet, getFlags()["tcc"].getBool());
  // Order assumptions by their creation time
  for(set<UserAssertion>::iterator i=assumpSet.begin(), iend=assumpSet.end();
      i!=iend; ++i)
    assumptions.push_back(i->thm().getExpr());
}


IF_DEBUG(
void VCL::dumpTrace(int scope) {
  vector<StrPair> fields;
  fields.push_back(strPair("scope", int2string(scope)));
  debugger.dumpTrace("scope", fields);
}
)


///////////////////////////////////////////////////////////////////////////////
// Public VCL methods
///////////////////////////////////////////////////////////////////////////////


VCL::VCL(const CLFlags& flags)
  : d_flags(new CLFlags(flags))
{
  // Set the dependent flags so that they are consistent

  if ((*d_flags)["dump-tcc"].getBool()) {
    d_flags->setFlag("translate", true);
    d_flags->setFlag("pp-batch", true);
    d_flags->setFlag("tcc", true);
  }

  if ((*d_flags)["translate"].getBool()) {
    d_flags->setFlag("printResults", false);
  }

  if ((*d_flags)["pp-bryant"].getBool()) {
    d_flags->setFlag("pp-batch", true);
  }

  //added by Yeting
  if ((*d_flags)["quant-complete-inst"].getBool() && !(*d_flags)["translate"].getBool()) {
    d_flags->setFlag("pp-batch", true);
  }

  //added by Yeting
  if ((*d_flags)["cnf-formula"].getBool()) {
    d_flags->setFlag("de", "sat");
    d_flags->setFlag("preprocess", false);
  }


  IF_DEBUG( // Initialize the global debugger
	   CVC3::debugger.init(&((*d_flags)["trace"].getStrVec()),
                               &((*d_flags)["dump-trace"].getString()));
  )
  init();
}


void VCL::init()
{
  d_nextIdx = 0;

  d_statistics = new Statistics();

  d_cm = new ContextManager();

  // Initialize the database of user assertions.  It has to be
  // initialized after d_cm.
  d_userAssertions = new(true) CDMap<Expr,UserAssertion>(getCurrentContext());
  d_batchedAssertions = new(true) CDList<Expr>(getCurrentContext());
  d_batchedAssertionsIdx = new(true) CDO<unsigned>(getCurrentContext(), 0);

  d_em = new ExprManager(d_cm, *d_flags);

  d_tm = new TheoremManager(d_cm, d_em, *d_flags);
  d_em->setTM(d_tm);

  d_translator = new Translator(d_em,
                                (*d_flags)["translate"].getBool(),
                                (*d_flags)["real2int"].getBool(),
                                (*d_flags)["convertArith"].getBool(),
                                (*d_flags)["convert2diff"].getString(),
                                (*d_flags)["iteLiftArith"].getBool(),
                                (*d_flags)["expResult"].getString(),
                                (*d_flags)["category"].getString(),
                                (*d_flags)["convertArray"].getBool(),
                                (*d_flags)["combineAssump"].getBool(),
                                (*d_flags)["convertToBV"].getInt());

  d_dump = d_translator->start((*d_flags)["dump-log"].getString());

  d_theoryCore = new TheoryCore(d_cm, d_em, d_tm, d_translator, *d_flags, *d_statistics);

  DebugAssert(d_theories.size() == 0, "Expected empty theories array");
  d_theories.push_back(d_theoryCore);

  // Fast rewriting of literals is done by setting their find to true or false.
  falseExpr().setFind(d_theoryCore->reflexivityRule(falseExpr()));
  trueExpr().setFind(d_theoryCore->reflexivityRule(trueExpr()));

  d_theories.push_back(d_theoryUF = new TheoryUF(d_theoryCore));

  if ((*d_flags)["arith-new"].getBool()) {
    d_theories.push_back(d_theoryArith = new TheoryArithNew(d_theoryCore));
  }
  else if ((*d_flags)["arith3"].getBool()) {
    d_theories.push_back(d_theoryArith = new TheoryArith3(d_theoryCore));
  }
  else {
    d_theories.push_back(d_theoryArith = new TheoryArithOld(d_theoryCore));
  }
  d_theoryCore->getExprTrans()->setTheoryArith(d_theoryArith);
  d_theories.push_back(d_theoryArray = new TheoryArray(d_theoryCore));
  d_theories.push_back(d_theoryRecords = new TheoryRecords(d_theoryCore));
  d_theories.push_back(d_theorySimulate = new TheorySimulate(d_theoryCore));
  d_theories.push_back(d_theoryBitvector = new TheoryBitvector(d_theoryCore));
  if ((*d_flags)["dt-lazy"].getBool()) {
    d_theories.push_back(d_theoryDatatype = new TheoryDatatypeLazy(d_theoryCore));
  }
  else {
    d_theories.push_back(d_theoryDatatype = new TheoryDatatype(d_theoryCore));
  }
  d_theories.push_back(d_theoryQuant = new TheoryQuant(d_theoryCore));

  d_translator->setTheoryCore(d_theoryCore);
  d_translator->setTheoryUF(d_theoryUF);
  d_translator->setTheoryArith(d_theoryArith);
  d_translator->setTheoryArray(d_theoryArray);
  d_translator->setTheoryQuant(d_theoryQuant);
  d_translator->setTheoryRecords(d_theoryRecords);
  d_translator->setTheorySimulate(d_theorySimulate);
  d_translator->setTheoryBitvector(d_theoryBitvector);
  d_translator->setTheoryDatatype(d_theoryDatatype);

  // Must be created after TheoryCore, since it needs it.
  // When we have more than one search engine, select one to create
  // based on flags
  const string& satEngine = (*d_flags)["sat"].getString();
  if (satEngine == "simple")
    d_se = new SearchSimple(d_theoryCore);
  else if (satEngine == "fast")
    d_se = new SearchEngineFast(d_theoryCore);
  else if (satEngine == "sat" || satEngine == "minisat")
    d_se = new SearchSat(d_theoryCore, satEngine);
  else
    throw CLException("Unrecognized SAT solver name: "
                      +(*d_flags)["sat"].getString());

  // Initial scope level should be 1
  d_cm->push();

  d_stackLevel = new(true) CDO<int>(d_cm->getCurrentContext(), 0);

  d_theoryCore->setResourceLimit((unsigned)((*d_flags)["resource"].getInt()));
  d_theoryCore->setTimeLimit((unsigned)((*d_flags)["stimeout"].getInt()));

  //  myvcl = this;
}


void VCL::destroy()
{
  popto(0);
  d_cm->popto(0);
  delete d_stackLevel;
  free(d_stackLevel);
  d_translator->finish();
  delete d_translator;

  TRACE_MSG("delete", "Deleting SearchEngine {");
  delete d_se;
  TRACE_MSG("delete", "Finished deleting SearchEngine }");
  // This map contains expressions and theorems; delete it before
  // d_em, d_tm, and d_cm.
  TRACE_MSG("delete", "Deleting d_userAssertions {");
  delete d_batchedAssertionsIdx;
  free(d_batchedAssertionsIdx);
  delete d_batchedAssertions;
  free(d_batchedAssertions);
  delete d_userAssertions;
  free(d_userAssertions);
  TRACE_MSG("delete", "Finished deleting d_userAssertions }");
  // and set these to null so their destructors don't blow up
  d_lastQuery = Theorem3();
  d_lastQueryTCC = Theorem();
  d_lastClosure = Theorem3();
  // Delete ExprManager BEFORE TheoremManager, since Exprs use Theorems
  TRACE_MSG("delete", "Clearing d_em {");
  d_em->clear();
  d_tm->clear();
  TRACE_MSG("delete", "Finished clearing d_em }");

  for(size_t i=d_theories.size(); i!= 0; ) {
    --i;
    string name(d_theories[i]->getName());
    TRACE("delete", "Deleting Theory[", name, "] {");
    delete d_theories[i];
    TRACE("delete", "Finished deleting Theory[", name, "] }");
  }
  d_theories.clear();

  // TheoremManager does not call ~Theorem() destructors, and only
  // releases memory.  At worst, we'll lose some Assumptions.
  TRACE_MSG("delete", "Deleting d_tm {");
  delete d_tm;
  TRACE_MSG("delete", "Finished deleting d_tm }");

  TRACE_MSG("delete", "Deleting d_em {");
  delete d_em;
  TRACE_MSG("delete", "Finished deleting d_em }");

  TRACE_MSG("delete", "Deleting d_cm {");
  delete d_cm;
  TRACE_MSG("delete", "Finished deleting d_cm }");
  delete d_statistics;
  TRACE_MSG("delete", "Finished deleting d_statistics }");
}


VCL::~VCL()
{
  destroy();
  TRACE_MSG("delete", "Deleting d_flags [end of ~VCL()]");
  delete d_flags;
  // No more TRACE-ing after this point (it needs d_flags)
  // Finalize the global debugger,
  // otherwise applications with more than one instance of VCL
  // may use refer to deallocated flags (e.g. test6 uses 2 VLCs)
  IF_DEBUG(
	   CVC3::debugger.finalize();
  )
}


void VCL::reprocessFlags() {
  if (d_se->getName() != (*d_flags)["sat"].getString()) {
    delete d_se;
    const string& satEngine = (*d_flags)["sat"].getString();
    if (satEngine == "simple")
      d_se = new SearchSimple(d_theoryCore);
    else if (satEngine == "fast")
      d_se = new SearchEngineFast(d_theoryCore);
    else if (satEngine == "sat" || satEngine == "minisat")
      d_se = new SearchSat(d_theoryCore, satEngine);
    else
      throw CLException("Unrecognized SAT solver name: "
                        +(*d_flags)["sat"].getString());
  }

  int arithCur;
  if (d_theoryArith->getName() == "ArithmeticOld") arithCur = 1;
  else if (d_theoryArith->getName() == "ArithmeticNew") arithCur = 2;
  else {
    DebugAssert(d_theoryArith->getName() == "Arithmetic3", "unexpected name");
    arithCur = 3;
  }

  int arithNext;
  if ((*d_flags)["arith-new"].getBool()) arithNext = 2;
  else if ((*d_flags)["arith3"].getBool()) arithNext = 3;
  else arithNext = 1;

  if (arithCur != arithNext) {
    delete d_theoryArith;
    switch (arithNext) {
      case 1:
        d_theoryArith = new TheoryArithOld(d_theoryCore);
        break;
      case 2:
        d_theoryArith = new TheoryArithNew(d_theoryCore);
        break;
      case 3:
        d_theoryArith = new TheoryArith3(d_theoryCore);
        break;
    }
    d_theories[2] = d_theoryArith;
    d_translator->setTheoryArith(d_theoryArith);
  }

  if ((*d_flags)["dump-tcc"].getBool()) {
    d_flags->setFlag("translate", true);
    d_flags->setFlag("pp-batch", true);
    d_flags->setFlag("tcc", true);
  }

  if ((*d_flags)["translate"].getBool()) {
    d_flags->setFlag("printResults", false);
  }

  if ((*d_flags)["pp-bryant"].getBool()) {
    d_flags->setFlag("pp-batch", true);
  }

  //added by Yeting
  if ((*d_flags)["quant-complete-inst"].getBool() && !(*d_flags)["translate"].getBool()) {
    d_flags->setFlag("pp-batch", true);
  }

  if ((*d_flags)["cnf-formula"].getBool()) {
    d_flags->setFlag("de", "sat");
    d_flags->setFlag("preprocess", false);
  }


  //TODO: handle more flags
}

TheoryCore* VCL::core(){
  return d_theoryCore;
}

Type VCL::boolType(){
  return d_theoryCore->boolType();
}


Type VCL::realType()
{
  return d_theoryArith->realType();
}


Type VCL::intType() {
  return d_theoryArith->intType();
}


Type VCL::subrangeType(const Expr& l, const Expr& r) {
  return d_theoryArith->subrangeType(l, r);
}


Type VCL::subtypeType(const Expr& pred, const Expr& witness)
{
  return d_theoryCore->newSubtypeExpr(pred, witness);
}


Type VCL::tupleType(const Type& type0, const Type& type1)
{
  vector<Type> types;
  types.push_back(type0);
  types.push_back(type1);
  return d_theoryRecords->tupleType(types);
}


Type VCL::tupleType(const Type& type0, const Type& type1, const Type& type2)
{
  vector<Type> types;
  types.push_back(type0);
  types.push_back(type1);
  types.push_back(type2);
  return d_theoryRecords->tupleType(types);
}


Type VCL::tupleType(const vector<Type>& types)
{
  return d_theoryRecords->tupleType(types);
}


Type VCL::recordType(const string& field, const Type& type)
{
  vector<string> fields;
  vector<Type> kids;
  fields.push_back(field);
  kids.push_back(type);
  return Type(d_theoryRecords->recordType(fields, kids));
}


Type VCL::recordType(const string& field0, const Type& type0,
		     const string& field1, const Type& type1) {
  vector<string> fields;
  vector<Type> kids;
  fields.push_back(field0);
  fields.push_back(field1);
  kids.push_back(type0);
  kids.push_back(type1);
  sort2(fields, kids);
  return Type(d_theoryRecords->recordType(fields, kids));
}


Type VCL::recordType(const string& field0, const Type& type0,
		     const string& field1, const Type& type1,
		     const string& field2, const Type& type2)
{
  vector<string> fields;
  vector<Type> kids;
  fields.push_back(field0);
  fields.push_back(field1);
  fields.push_back(field2);
  kids.push_back(type0);
  kids.push_back(type1);
  kids.push_back(type2);
  sort2(fields, kids);
  return Type(d_theoryRecords->recordType(fields, kids));
}


Type VCL::recordType(const vector<string>& fields,
		     const vector<Type>& types)
{
  DebugAssert(fields.size() == types.size(),
	      "VCL::recordType: number of fields is different \n"
	      "from the number of types");
  // Create copies of the vectors to sort them
  vector<string> fs(fields);
  vector<Type> ts(types);
  sort2(fs, ts);
  return Type(d_theoryRecords->recordType(fs, ts));
}


Type VCL::dataType(const string& name,
                   const string& constructor,
                   const vector<string>& selectors, const vector<Expr>& types)
{
  vector<string> constructors;
  constructors.push_back(constructor);

  vector<vector<string> > selectorsVec;
  selectorsVec.push_back(selectors);

  vector<vector<Expr> > typesVec;
  typesVec.push_back(types);

  return dataType(name, constructors, selectorsVec, typesVec);
}


Type VCL::dataType(const string& name,
                   const vector<string>& constructors,
                   const vector<vector<string> >& selectors,
                   const vector<vector<Expr> >& types)
{
  Expr res = d_theoryDatatype->dataType(name, constructors, selectors, types);
  if(d_dump) {
    d_translator->dump(res);
  }
  return Type(res[0]);
}


void VCL::dataType(const vector<string>& names,
                   const vector<vector<string> >& constructors,
                   const vector<vector<vector<string> > >& selectors,
                   const vector<vector<vector<Expr> > >& types,
                   vector<Type>& returnTypes)
{
  Expr res = d_theoryDatatype->dataType(names, constructors, selectors, types);
  if(d_dump) {
    d_translator->dump(res);
  }
  for (int i = 0; i < res.arity(); ++i) {
    returnTypes.push_back(Type(res[i]));
  }
}


Type VCL::arrayType(const Type& typeIndex, const Type& typeData)
{
  return ::arrayType(typeIndex, typeData);
}


Type VCL::bitvecType(int n)
{
  return d_theoryBitvector->newBitvectorType(n);
}


Type VCL::funType(const Type& typeDom, const Type& typeRan)
{
  return typeDom.funType(typeRan);
}


Type VCL::funType(const vector<Type>& typeDom, const Type& typeRan) {
  DebugAssert(typeDom.size() >= 1, "VCL::funType: missing domain types");
  return Type::funType(typeDom, typeRan);
}


Type VCL::createType(const string& typeName)
{
  if(d_dump) {
    d_translator->dump(Expr(TYPE, listExpr(idExpr(typeName))));
  }
  return d_theoryCore->newTypeExpr(typeName);
}


Type VCL::createType(const string& typeName, const Type& def)
{
  if (d_dump) {
    d_translator->dump(Expr(TYPE, idExpr(typeName), def.getExpr()), true);
  }
  return d_theoryCore->newTypeExpr(typeName, def);
}


Type VCL::lookupType(const string& typeName)
{
  return d_theoryCore->lookupTypeExpr(typeName);
}


Expr VCL::varExpr(const string& name, const Type& type)
{
  // Check if the ofstream is open (as opposed to the command line flag)
  if(d_dump) {
    d_translator->dump(Expr(CONST, idExpr(name), type.getExpr()));
  }
  return d_theoryCore->newVar(name, type);
}


Expr VCL::varExpr(const string& name, const Type& type, const Expr& def)
{
  // Check if the ofstream is open (as opposed to the command line flag)
  if(d_dump) {
    d_translator->dump(Expr(CONST, idExpr(name), type.getExpr(), def), true);
  }
  // Prove the TCCs of the definition
  if(getFlags()["tcc"].getBool()) {
    Type tpDef(def.getType()), tpVar(type);
    // Make sure that def is in the subtype of tpVar; that is, prove
    // FORALL (x: tpDef): x = def => typePred(tpVar)(x)
    if(tpDef != tpVar) {
      // Typecheck the base types
      if(getBaseType(tpDef) != getBaseType(type)) {
	throw TypecheckException("Type mismatch in constant definition:\n"
				 "Constant "+name+
				 " is declared with type:\n  "
				 +type.toString()
				 +"\nBut the type of definition is\n  "
				 +tpDef.toString());
      }
      TRACE("tccs", "CONST def: "+name+" : "+tpVar.toString()
	    +" := <value> : ", tpDef, ";");
      vector<Expr> boundVars;
      boundVars.push_back(boundVarExpr(name, "tcc", tpDef));
      Expr body(boundVars[0].eqExpr(def).impExpr(getTypePred(tpVar, boundVars[0])));
      Expr quant(forallExpr(boundVars, body));
      try {
        checkTCC(quant);
      } catch(TypecheckException&) {
	throw TypecheckException
	  ("Type mismatch in constant definition:\n"
	   "Constant "+name+
	   " is declared with type:\n  "
	   +type.toString()
	   +"\nBut the type of definition is\n  "
	   +def.getType().toString()
	   +"\n\n which is not a subtype of the constant");
      }
    }
  }
  return d_theoryCore->newVar(name, type, def);
}


Expr VCL::lookupVar(const string& name, Type* type)
{
  return d_theoryCore->lookupVar(name, type);
}


Type VCL::getType(const Expr& e)
{
  return e.getType();
}


Type VCL::getBaseType(const Expr& e)
{
  return d_theoryCore->getBaseType(e);
}


Type VCL::getBaseType(const Type& t)
{
  return d_theoryCore->getBaseType(t);
}


Expr VCL::getTypePred(const Type&t, const Expr& e)
{
  return d_theoryCore->getTypePred(t, e);
}


Expr VCL::stringExpr(const string& str) {
  return getEM()->newStringExpr(str);
}


Expr VCL::idExpr(const string& name) {
  return Expr(ID, stringExpr(name));
}


Expr VCL::listExpr(const vector<Expr>& kids) {
  return Expr(RAW_LIST, kids, getEM());
}


Expr VCL::listExpr(const Expr& e1) {
  return Expr(RAW_LIST, e1);
}


Expr VCL::listExpr(const Expr& e1, const Expr& e2) {
  return Expr(RAW_LIST, e1, e2);
}


Expr VCL::listExpr(const Expr& e1, const Expr& e2, const Expr& e3) {
  return Expr(RAW_LIST, e1, e2, e3);
}


Expr VCL::listExpr(const string& op, const vector<Expr>& kids) {
  vector<Expr> newKids;
  newKids.push_back(idExpr(op));
  newKids.insert(newKids.end(), kids.begin(), kids.end());
  return listExpr(newKids);
}


Expr VCL::listExpr(const string& op, const Expr& e1) {
  return Expr(RAW_LIST, idExpr(op), e1);
}


Expr VCL::listExpr(const string& op, const Expr& e1,
		   const Expr& e2) {
  return Expr(RAW_LIST, idExpr(op), e1, e2);
}


Expr VCL::listExpr(const string& op, const Expr& e1,
		   const Expr& e2, const Expr& e3) {
  vector<Expr> kids;
  kids.push_back(idExpr(op));
  kids.push_back(e1);
  kids.push_back(e2);
  kids.push_back(e3);
  return listExpr(kids);
}


void VCL::printExpr(const Expr& e) {
  printExpr(e, cout);
}


void VCL::printExpr(const Expr& e, ostream& os) {
  os << e << endl;
}


Expr VCL::parseExpr(const Expr& e) {
  return d_theoryCore->parseExprTop(e);
}


Type VCL::parseType(const Expr& e) {
  return Type(d_theoryCore->parseExpr(e));
}


Expr VCL::importExpr(const Expr& e)
{
  return d_em->rebuild(e);
}


Type VCL::importType(const Type& t)
{
  return Type(d_em->rebuild(t.getExpr()));
}

void VCL::cmdsFromString(const std::string& s, InputLanguage lang=PRESENTATION_LANG)
{
  stringstream ss(s,stringstream::in);
  return loadFile(ss,lang,false);
}

Expr VCL::exprFromString(const std::string& s)
{
  stringstream ss("PRINT " + s + ";",stringstream::in);
  Parser p(this,d_translator,PRESENTATION_LANG,ss);
  Expr e = p.next();
  if( e.isNull() ) {
    throw ParserException("Parser result is null: '" + s + "'");
  }
  DebugAssert(e.getKind() == RAW_LIST, "Expected list expression");
  DebugAssert(e.arity() == 2, "Expected two children");
  return parseExpr(e[1]);
}

Expr VCL::trueExpr()
{
  return d_em->trueExpr();
}


Expr VCL::falseExpr()
{
  return d_em->falseExpr();
}


Expr VCL::notExpr(const Expr& child)
{
  return !child;
}


Expr VCL::andExpr(const Expr& left, const Expr& right)
{
  return left && right;
}


Expr VCL::andExpr(const vector<Expr>& children)
{
  if (children.size() == 0)
    throw Exception("andExpr requires at least one child");
  return Expr(AND, children);
}


Expr VCL::orExpr(const Expr& left, const Expr& right)
{
  return left || right;
}


Expr VCL::orExpr(const vector<Expr>& children)
{
  if (children.size() == 0)
    throw Exception("orExpr requires at least one child");
  return Expr(OR, children);
}


Expr VCL::impliesExpr(const Expr& hyp, const Expr& conc)
{
  return hyp.impExpr(conc);
}


Expr VCL::iffExpr(const Expr& left, const Expr& right)
{
  return left.iffExpr(right);
}


Expr VCL::eqExpr(const Expr& child0, const Expr& child1)
{
  return child0.eqExpr(child1);
}

Expr VCL::distinctExpr(const std::vector<Expr>& children)
{
	return Expr(DISTINCT, children);
}

Expr VCL::iteExpr(const Expr& ifpart, const Expr& thenpart, const Expr& elsepart)
{
  return ifpart.iteExpr(thenpart, elsepart);
}


Op VCL::createOp(const string& name, const Type& type)
{
  if (!type.isFunction())
    throw Exception("createOp: expected function type");
  if(d_dump) {
    d_translator->dump(Expr(CONST, idExpr(name), type.getExpr()));
  }
  return d_theoryCore->newFunction(name, type,
                                   getFlags()["trans-closure"].getBool());
}


Op VCL::createOp(const string& name, const Type& type, const Expr& def)
{
  if (!type.isFunction())
    throw TypecheckException
	  ("Type error in createOp:\n"
	   "Constant "+name+
	   " is declared with type:\n  "
	   +type.toString()
	   +"\n which is not a function type");
  if (getBaseType(type) != getBaseType(def.getType()))
    throw TypecheckException
	  ("Type mismatch in createOp:\n"
	   "Function "+name+
	   " is declared with type:\n  "
	   +type.toString()
	   +"\nBut the type of definition is\n  "
	   +def.getType().toString()
	   +"\n\n which does not match");
  if(d_dump) {
    d_translator->dump(Expr(CONST, idExpr(name), type.getExpr(), def), true);
  }
  // Prove the TCCs of the definition
  if(getFlags()["tcc"].getBool()) {
    Type tpDef(def.getType());
    // Make sure that def is within the subtype; that is, prove
    // FORALL (xs: argType): typePred_{return_type}(def(xs))
    if(tpDef != type) {
      vector<Expr> boundVars;
      for (int i = 0; i < type.arity()-1; ++i) {
        boundVars.push_back(d_em->newBoundVarExpr(type[i]));
      }
      Expr app = Expr(def.mkOp(), boundVars);
      Expr body(getTypePred(type[type.arity()-1], app));
      Expr quant(forallExpr(boundVars, body));
      Expr tcc = quant.andExpr(d_theoryCore->getTCC(quant));
      // Query the subtyping formula
      bool typesMatch = true;
      try {
        checkTCC(tcc);
      } catch (TypecheckException&) {
        typesMatch = false;
      }
      if(!typesMatch) {
	throw TypecheckException
	  ("Type mismatch in createOp:\n"
	   "Function "+name+
	   " is declared with type:\n  "
	   +type.toString()
	   +"\nBut the definition is\n  "
	   +def.toString()
	   +"\n\nwhose type could not be proved to be a subtype");
      }
    }
  }
  return d_theoryCore->newFunction(name, type, def);
}


Op VCL::lookupOp(const string& name, Type* type)
{
  return d_theoryCore->lookupFunction(name, type);
}


Expr VCL::funExpr(const Op& op, const Expr& child)
{
  return Expr(op, child);
}


Expr VCL::funExpr(const Op& op, const Expr& left, const Expr& right)
{
  return Expr(op, left, right);
}


Expr VCL::funExpr(const Op& op, const Expr& child0, const Expr& child1, const Expr& child2)
{
  return Expr(op, child0, child1, child2);
}


Expr VCL::funExpr(const Op& op, const vector<Expr>& children)
{
  return Expr(op, children);
}

bool VCL::addPairToArithOrder(const Expr& smaller, const Expr& bigger)
{
  if (d_dump) {
    d_translator->dump(Expr(ARITH_VAR_ORDER, smaller, bigger), true);
  }
  return d_theoryArith->addPairToArithOrder(smaller, bigger);
}

Expr VCL::ratExpr(int n, int d)
{
  DebugAssert(d != 0,"denominator cannot be 0");
  return d_em->newRatExpr(Rational(n,d));
}


Expr VCL::ratExpr(const string& n, const string& d, int base)
{
  return d_em->newRatExpr(Rational(n.c_str(), d.c_str(), base));
}


Expr VCL::ratExpr(const string& n, int base)
{
  string::size_type pos = n.rfind(".");
  if (pos == string::npos) {
    return d_em->newRatExpr(Rational(n.c_str(), base));
  }
  string afterdec = n.substr(pos+1);
  string beforedec = n.substr(0, pos);
  if (afterdec.size() == 0 || beforedec.size() == 0) {
    throw Exception("Cannot convert string to rational: "+n);
  }
  pos = beforedec.rfind(".");
  if (pos != string::npos) {
    throw Exception("Cannot convert string to rational: "+n);
  }
  Rational r = Rational(beforedec.c_str(), base);
  Rational fracPart = Rational(afterdec.c_str(), base);
  if( r < 0 || ((r == 0) && (beforedec.rfind("-") != string::npos)) ) {
    r = r - (fracPart / pow(afterdec.size(), (Rational)base));
  }
  else {
    r = r + (fracPart / pow(afterdec.size(), (Rational)base));
  }
  return d_em->newRatExpr(r);
}


Expr VCL::uminusExpr(const Expr& child)
{
  return -child;
}


Expr VCL::plusExpr(const Expr& left, const Expr& right)
{
  return left + right;
}

Expr VCL::plusExpr(const std::vector<Expr>& children)
{
	return Expr(PLUS, children);
}


Expr VCL::minusExpr(const Expr& left, const Expr& right)
{
  return left - right;
}


Expr VCL::multExpr(const Expr& left, const Expr& right)
{
  return left * right;
}


Expr VCL::powExpr(const Expr& x, const Expr& n)
{
  return ::powExpr(n, x);
}


Expr VCL::divideExpr(const Expr& num, const Expr& denom)
{
  return ::divideExpr(num,denom);
}


Expr VCL::ltExpr(const Expr& left, const Expr& right)
{
  return ::ltExpr(left, right);
}


Expr VCL::leExpr(const Expr& left, const Expr& right)
{
  return ::leExpr(left, right);
}


Expr VCL::gtExpr(const Expr& left, const Expr& right)
{
  return ::gtExpr(left, right);
}


Expr VCL::geExpr(const Expr& left, const Expr& right)
{
  return ::geExpr(left, right);
}


Expr VCL::recordExpr(const string& field, const Expr& expr)
{
  vector<string> fields;
  vector<Expr> kids;
  kids.push_back(expr);
  fields.push_back(field);
  return d_theoryRecords->recordExpr(fields, kids);
}


Expr VCL::recordExpr(const string& field0, const Expr& expr0,
		     const string& field1, const Expr& expr1)
{
  vector<string> fields;
  vector<Expr> kids;
  fields.push_back(field0);
  fields.push_back(field1);
  kids.push_back(expr0);
  kids.push_back(expr1);
  sort2(fields, kids);
  return d_theoryRecords->recordExpr(fields, kids);
}


Expr VCL::recordExpr(const string& field0, const Expr& expr0,
		     const string& field1, const Expr& expr1,
		     const string& field2, const Expr& expr2)
{
  vector<string> fields;
  vector<Expr> kids;
  fields.push_back(field0);
  fields.push_back(field1);
  fields.push_back(field2);
  kids.push_back(expr0);
  kids.push_back(expr1);
  kids.push_back(expr2);
  sort2(fields, kids);
  return d_theoryRecords->recordExpr(fields, kids);
}


Expr VCL::recordExpr(const vector<string>& fields,
		     const vector<Expr>& exprs)
{
  DebugAssert(fields.size() > 0, "VCL::recordExpr()");
  DebugAssert(fields.size() == exprs.size(),"VCL::recordExpr()");
  // Create copies of the vectors to sort them
  vector<string> fs(fields);
  vector<Expr> es(exprs);
  sort2(fs, es);
  return d_theoryRecords->recordExpr(fs, es);
}


Expr VCL::recSelectExpr(const Expr& record, const string& field)
{
  return d_theoryRecords->recordSelect(record, field);
}


Expr VCL::recUpdateExpr(const Expr& record, const string& field,
			const Expr& newValue)
{
  return d_theoryRecords->recordUpdate(record, field, newValue);
}


Expr VCL::readExpr(const Expr& array, const Expr& index)
{
  return Expr(READ, array, index);
}


Expr VCL::writeExpr(const Expr& array, const Expr& index, const Expr& newValue)
{
  return Expr(WRITE, array, index, newValue);
}


Expr VCL::newBVConstExpr(const std::string& s, int base)
{
  return d_theoryBitvector->newBVConstExpr(s, base);
}


Expr VCL::newBVConstExpr(const std::vector<bool>& bits)
{
  return d_theoryBitvector->newBVConstExpr(bits);
}


Expr VCL::newBVConstExpr(const Rational& r, int len)
{
  return d_theoryBitvector->newBVConstExpr(r, len);
}


Expr VCL::newConcatExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newConcatExpr(t1, t2);
}


Expr VCL::newConcatExpr(const std::vector<Expr>& kids)
{
  return d_theoryBitvector->newConcatExpr(kids);
}


Expr VCL::newBVExtractExpr(const Expr& e, int hi, int low)
{
  return d_theoryBitvector->newBVExtractExpr(e, hi, low);
}


Expr VCL::newBVNegExpr(const Expr& t1)
{
  return d_theoryBitvector->newBVNegExpr(t1);
}


Expr VCL::newBVAndExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVAndExpr(t1, t2);
}


Expr VCL::newBVAndExpr(const std::vector<Expr>& kids)
{
  return d_theoryBitvector->newBVAndExpr(kids);
}


Expr VCL::newBVOrExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVOrExpr(t1, t2);
}


Expr VCL::newBVOrExpr(const std::vector<Expr>& kids)
{
  return d_theoryBitvector->newBVOrExpr(kids);
}


Expr VCL::newBVXorExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVXorExpr(t1, t2);
}


Expr VCL::newBVXorExpr(const std::vector<Expr>& kids)
{
  return d_theoryBitvector->newBVXorExpr(kids);
}


Expr VCL::newBVXnorExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVXnorExpr(t1, t2);
}


Expr VCL::newBVXnorExpr(const std::vector<Expr>& kids)
{
  return d_theoryBitvector->newBVXnorExpr(kids);
}


Expr VCL::newBVNandExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVNandExpr(t1, t2);
}


Expr VCL::newBVNorExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVNorExpr(t1, t2);
}


Expr VCL::newBVCompExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVCompExpr(t1, t2);
}


Expr VCL::newBVLTExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVLTExpr(t1, t2);
}


Expr VCL::newBVLEExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVLEExpr(t1, t2);
}


Expr VCL::newBVSLTExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVSLTExpr(t1, t2);
}


Expr VCL::newBVSLEExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVSLEExpr(t1, t2);
}


Expr VCL::newSXExpr(const Expr& t1, int len)
{
  return d_theoryBitvector->newSXExpr(t1, len);
}


Expr VCL::newBVUminusExpr(const Expr& t1)
{
  return d_theoryBitvector->newBVUminusExpr(t1);
}


Expr VCL::newBVSubExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVSubExpr(t1, t2);
}


Expr VCL::newBVPlusExpr(int numbits, const std::vector<Expr>& k)
{
  return d_theoryBitvector->newBVPlusPadExpr(numbits, k);
}

Expr VCL::newBVPlusExpr(int numbits, const Expr& t1, const Expr& t2)
{
	std::vector<Expr> k;
	k.push_back(t1);
	k.push_back(t2);
	return newBVPlusExpr(numbits, k);
}


Expr VCL::newBVMultExpr(int numbits, const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVMultPadExpr(numbits, t1, t2);
}

Expr VCL::newBVUDivExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVUDivExpr(t1, t2);
}

Expr VCL::newBVURemExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVURemExpr(t1, t2);
}

Expr VCL::newBVSDivExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVSDivExpr(t1, t2);
}

Expr VCL::newBVSRemExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVSRemExpr(t1, t2);
}

Expr VCL::newBVSModExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVSModExpr(t1, t2);
}


Expr VCL::newFixedLeftShiftExpr(const Expr& t1, int r)
{
  return d_theoryBitvector->newFixedLeftShiftExpr(t1, r);
}


Expr VCL::newFixedConstWidthLeftShiftExpr(const Expr& t1, int r)
{
  return d_theoryBitvector->newFixedConstWidthLeftShiftExpr(t1, r);
}


Expr VCL::newFixedRightShiftExpr(const Expr& t1, int r)
{
  return d_theoryBitvector->newFixedRightShiftExpr(t1, r);
}


Expr VCL::newBVSHL(const Expr& t1, const Expr& t2)
{
  return Expr(BVSHL, t1, t2);
}


Expr VCL::newBVLSHR(const Expr& t1, const Expr& t2)
{
  return Expr(BVLSHR, t1, t2);
}


Expr VCL::newBVASHR(const Expr& t1, const Expr& t2)
{
  return Expr(BVASHR, t1, t2);
}


Rational VCL::computeBVConst(const Expr& e)
{
  return d_theoryBitvector->computeBVConst(e);
}


Expr VCL::tupleExpr(const vector<Expr>& exprs) {
  DebugAssert(exprs.size() > 0, "VCL::tupleExpr()");
  return d_theoryRecords->tupleExpr(exprs);
}


Expr VCL::tupleSelectExpr(const Expr& tuple, int index)
{
  return d_theoryRecords->tupleSelect(tuple, index);
}


Expr VCL::tupleUpdateExpr(const Expr& tuple, int index, const Expr& newValue)
{
  return d_theoryRecords->tupleUpdate(tuple, index, newValue);
}


Expr VCL::datatypeConsExpr(const string& constructor, const vector<Expr>& args)
{
  return d_theoryDatatype->datatypeConsExpr(constructor, args);
}


Expr VCL::datatypeSelExpr(const string& selector, const Expr& arg)
{
  return d_theoryDatatype->datatypeSelExpr(selector, arg);
}


Expr VCL::datatypeTestExpr(const string& constructor, const Expr& arg)
{
  return d_theoryDatatype->datatypeTestExpr(constructor, arg);
}


Expr VCL::boundVarExpr(const string& name, const string& uid,
		       const Type& type) {
  return d_em->newBoundVarExpr(name, uid, type);
}


Expr VCL::forallExpr(const vector<Expr>& vars, const Expr& body) {
  DebugAssert(vars.size() > 0, "VCL::foralLExpr()");
  return d_em->newClosureExpr(FORALL, vars, body);
}

Expr VCL::forallExpr(const vector<Expr>& vars, const Expr& body,
                     const Expr& trigger) {
  DebugAssert(vars.size() > 0, "VCL::foralLExpr()");
  return d_em->newClosureExpr(FORALL, vars, body, trigger);
}

Expr VCL::forallExpr(const vector<Expr>& vars, const Expr& body,
                     const vector<Expr>& triggers) {
  DebugAssert(vars.size() > 0, "VCL::foralLExpr()");
  return d_em->newClosureExpr(FORALL, vars, body, triggers);
}

Expr VCL::forallExpr(const vector<Expr>& vars, const Expr& body,
		     const vector<vector<Expr> >& triggers) {
  DebugAssert(vars.size() > 0, "VCL::foralLExpr()");
  return d_em->newClosureExpr(FORALL, vars, body, triggers);
}

void VCL::setTriggers(const Expr& e, const vector< vector<Expr> >& triggers) {
  e.setTriggers(triggers);
}

void VCL::setTriggers(const Expr& e, const vector<Expr>& triggers) {
  e.setTriggers(triggers);
}

void VCL::setTrigger(const Expr& e, const Expr& trigger) {
  e.setTrigger(trigger);
}

void VCL::setMultiTrigger(const Expr& e, const vector<Expr>& multiTrigger) {
  e.setMultiTrigger(multiTrigger);
}

Expr VCL::existsExpr(const vector<Expr>& vars, const Expr& body) {
  return d_em->newClosureExpr(EXISTS, vars, body);
}


Op VCL::lambdaExpr(const vector<Expr>& vars, const Expr& body) {
  return d_em->newClosureExpr(LAMBDA, vars, body).mkOp();
}

Op VCL::transClosure(const Op& op) {
  const string& name = op.getExpr().getName();
  return d_em->newSymbolExpr(name, TRANS_CLOSURE).mkOp();
}


Expr VCL::simulateExpr(const Expr& f, const Expr& s0,
		       const vector<Expr>& inputs, const Expr& n) {
  vector<Expr> kids;
  kids.push_back(f);
  kids.push_back(s0);
  kids.insert(kids.end(), inputs.begin(), inputs.end());
  kids.push_back(n);
  return Expr(SIMULATE, kids);
}


void VCL::setResourceLimit(unsigned limit)
{
  d_theoryCore->setResourceLimit(limit);
}


Theorem VCL::checkTCC(const Expr& tcc)
{
  Theorem tccThm;
  d_se->push();
  QueryResult res = d_se->checkValid(tcc, tccThm);
  switch (res) {
    case VALID:
      d_lastQueryTCC = tccThm;
      d_se->pop();
      break;
    case INVALID:
      throw TypecheckException("Failed TCC:\n\n  "
                               +tcc.toString()
                               +"\n\nWhich simplified to:\n\n  "
                               +simplify(tcc).toString()
                               +"\n\nAnd the last formula is not valid "
                               "in the current context.");
    case ABORT:
      throw TypecheckException("Budget exceeded:\n\n  "
                               "Unable to verify TCC:\n\n  "
                               +tcc.toString()
                               +"\n\nWhich simplified to:\n\n  "
                               +simplify(tcc).toString());
    case UNKNOWN:
      throw TypecheckException("Result unknown:\n\n  "
                               "Unable to verify TCC:\n\n  "
                               +tcc.toString()
                               +"\n\nWhich simplified to:\n\n  "
                               +simplify(tcc).toString()
                               +"\n\nAnd the last formula is unknown "
                               "in the current context.");
    default:
      FatalAssert(false, "Unexpected case");
  }
  return tccThm;
}


void VCL::assertFormula(const Expr& e)
{
  // Typecheck the user input
  if(!e.getType().isBool()) {
    throw TypecheckException("Non-BOOLEAN formula in ASSERT:\n  "
			     +Expr(ASSERT, e).toString()
			     +"\nDerived type of the formula:\n  "
			     +e.getType().toString());
  }

  if (getFlags()["pp-batch"].getBool()) {
    d_batchedAssertions->push_back(e);
  }
  else {
    // Check if the ofstream is open (as opposed to the command line flag)
    if(d_dump) {
      Expr e2 = e;
      if (getFlags()["preSimplify"].getBool()) {
        e2 = simplify(e);
      }
      if (d_translator->dumpAssertion(e2)) return;
    }

    TRACE("vclassertFormula", "VCL::assertFormula(", e, ") {");

    // See if e was already asserted before
    if(d_userAssertions->count(e) > 0) {
      TRACE_MSG("vclassertFormula", "VCL::assertFormula[repeated assertion] => }");
      return;
    }
    // Check the validity of the TCC
    Theorem tccThm;
    if(getFlags()["tcc"].getBool()) {
      Expr tcc(d_theoryCore->getTCC(e));
      tccThm = checkTCC(tcc);
    }

    Theorem thm = d_se->newUserAssumption(e);
    (*d_userAssertions)[e] = UserAssertion(thm, tccThm, d_nextIdx++);
  }
  TRACE_MSG("vclassertFormula", "VCL::assertFormula => }");
}


void VCL::registerAtom(const Expr& e)
{
  //TODO: add to interactive interface
  d_se->registerAtom(e);
}


Expr VCL::getImpliedLiteral()
{
  //TODO: add to interactive interface
  Theorem thm = d_se->getImpliedLiteral();
  if (thm.isNull()) return Expr();
  return thm.getExpr();
}


Expr VCL::simplify(const Expr& e) {
  //TODO: add to interactive interface
  return simplifyThm(e).getRHS();
}


Theorem VCL::simplifyThm(const Expr& e)
{
  e.getType();
  Theorem res = d_theoryCore->getExprTrans()->preprocess(e);
  Theorem simpThm =  d_theoryCore->simplify(res.getRHS());
  res = d_theoryCore->transitivityRule(res, simpThm);
  return res;
}


QueryResult VCL::query(const Expr& e)
{
  TRACE("query", "VCL::query(", e,") {");
  // Typecheck the user input
  if(!e.getType().isBool()) {
    throw TypecheckException("Non-BOOLEAN formula in QUERY:\n  "
			     +Expr(QUERY, e).toString()
			     +"\nDerived type of the formula:\n  "
			     +e.getType().toString());
  }

  Expr qExpr = e;
  if (getFlags()["pp-batch"].getBool()) {
    // Add batched assertions
    vector<Expr> kids;
    for (; (*d_batchedAssertionsIdx) < d_batchedAssertions->size();
         (*d_batchedAssertionsIdx) = (*d_batchedAssertionsIdx) + 1) {
      kids.push_back((*d_batchedAssertions)[(*d_batchedAssertionsIdx)]);
    }
    if (kids.size() > 0) {
      qExpr = kids.size() == 1 ? kids[0] : Expr(AND, kids);
      qExpr = qExpr.impExpr(e);
    }
  }

  if (d_dump && !getFlags()["dump-tcc"].getBool()) {
    Expr e2 = qExpr;
    if (getFlags()["preSimplify"].getBool()) {
      e2 = simplify(qExpr);
    }
    if (d_translator->dumpQuery(e2)) return UNKNOWN;
  }

  // Check the validity of the TCC
  Theorem tccThm = d_se->getCommonRules()->trueTheorem();
  if(getFlags()["tcc"].getBool()) {
    Expr tcc(d_theoryCore->getTCC(qExpr));
    if (getFlags()["dump-tcc"].getBool()) {
      Expr e2 = tcc;
      if (getFlags()["preSimplify"].getBool()) {
        e2 = simplify(tcc);
      }
      if (d_translator->dumpQuery(e2)) return UNKNOWN;
    }
    // FIXME: we have to guarantee that the TCC of 'tcc' is always valid
    tccThm = checkTCC(tcc);
  }
  Theorem res;
  QueryResult qres = d_se->checkValid(qExpr, res);
  switch (qres) {
    case VALID:
      d_lastQuery = d_se->getCommonRules()->queryTCC(res, tccThm);
      break;
    default:
      d_lastQueryTCC = Theorem();
      d_lastQuery = Theorem3();
      d_lastClosure = Theorem3();
  }
  TRACE("query", "VCL::query => ",
        qres == VALID ? "VALID" :
        qres == INVALID ? "INVALID" :
        qres == ABORT ? "ABORT" : "UNKNOWN", " }");

  if (d_dump) d_translator->dumpQueryResult(qres);

  return qres;
}


QueryResult VCL::checkUnsat(const Expr& e)
{
  return query(e.negate());
}


QueryResult VCL::checkContinue()
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(CONTINUE), true);
  }
  vector<Expr> assertions;
  d_se->getCounterExample(assertions);
  Theorem thm;
  if (assertions.size() == 0) {
    return d_se->restart(falseExpr(), thm);
  }
  Expr eAnd = assertions.size() == 1 ? assertions[0] : andExpr(assertions);
  return d_se->restart(!eAnd, thm);
}


QueryResult VCL::restart(const Expr& e)
{
  if (d_dump) {
    d_translator->dump(Expr(RESTART, e), true);
  }
  Theorem thm;
  return d_se->restart(e, thm);
}


void VCL::returnFromCheck()
{
  //TODO: add to interactive interface
  d_se->returnFromCheck();
}


void VCL::getUserAssumptions(vector<Expr>& assumptions)
{
  // TODO: add to interactive interface
  d_se->getUserAssumptions(assumptions);
}


void VCL::getInternalAssumptions(vector<Expr>& assumptions)
{
  // TODO: add to interactive interface
  d_se->getInternalAssumptions(assumptions);
}


void VCL::getAssumptions(vector<Expr>& assumptions)
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(ASSUMPTIONS), true);
  }
  d_se->getAssumptions(assumptions);
}


//yeting, for proof translation
Expr VCL::getProofQuery()
{
  if (d_lastQuery.isNull()){
    throw EvalException
      ("Invalid Query,n");
  }
  return d_lastQuery.getExpr();

  //  Theorem thm = d_se->lastThm();
  //  if (thm.isNull()) return;
  //  thm.getLeafAssumptions(assumptions);
}


void VCL::getAssumptionsUsed(vector<Expr>& assumptions)
{
  throw EvalException ("getAssumptionsUsed not currently supported");
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_ASSUMPTIONS), true);
  }
  Theorem thm = d_se->lastThm();
  if (thm.isNull()) return;
  thm.getLeafAssumptions(assumptions);
}


void VCL::getCounterExample(vector<Expr>& assertions, bool inOrder)
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(COUNTEREXAMPLE), true);
  }
  if (!(*d_flags)["translate"].getBool())
    d_se->getCounterExample(assertions, inOrder);
}


void VCL::getConcreteModel(ExprMap<Expr> & m)
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(COUNTERMODEL), true);
  }
  if (!(*d_flags)["translate"].getBool())
    d_se->getConcreteModel(m);
}

QueryResult VCL::tryModelGeneration() {
	if (!d_theoryCore->incomplete()) throw Exception("Model generation should be called only after an UNKNOWN result");
	QueryResult qres = UNKNOWN;
	int scopeLevel = d_cm->scopeLevel();
	try  {
          while (qres == UNKNOWN)
            {
              Theorem thm;
              d_se->push();
              // Try to generate the model
              if (d_se->tryModelGeneration(thm))
                // If success, we are satisfiable
                qres = INVALID;
              else
                {
                  // Generate the clause to get rid of the faults
                  vector<Expr> assumptions;
                  thm.getLeafAssumptions(assumptions, true /*negate*/);
                  if (!thm.getExpr().isFalse()) assumptions.push_back(thm.getExpr());
                  // Pop back to where we were
                  while (d_cm->scopeLevel() > scopeLevel) d_se->pop();
                  // Restart with the new clause
                  qres = restart(orExpr(assumptions));
                  // Keep this level
                  scopeLevel = d_cm->scopeLevel();
                }
            }
        } catch (Exception& e) {
          // Pop back to where we were
          while (d_cm->scopeLevel() > scopeLevel) d_se->pop();
        }
	return qres;
}

FormulaValue VCL::value(const Expr& e) {
  DebugAssert(!e.isTerm(), "vcl::value: e is not a formula");
  return d_se->getValue(e);
}

bool VCL::inconsistent(vector<Expr>& assumptions)
{
  // TODO: add to interactive interface
  if (d_theoryCore->inconsistent()) {
    // TODO: do we need local getAssumptions?
    getAssumptions(d_theoryCore->inconsistentThm().getAssumptionsRef(),
		   assumptions);
    return true;
  }
  return false;
}

bool VCL::inconsistent()
{
  return d_theoryCore->inconsistent();
}


bool VCL::incomplete() {
  // TODO: add to interactive interface
  // Return true only after a failed query
  return (d_lastQuery.isNull() && d_theoryCore->incomplete());
}


bool VCL::incomplete(vector<string>& reasons) {
  // TODO: add to interactive interface
  // Return true only after a failed query
  return (d_lastQuery.isNull() && d_theoryCore->incomplete(reasons));
}


Proof VCL::getProof()
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_PROOF), true);
  }

  if(d_lastQuery.isNull())
    throw EvalException
      ("Method getProof() (or command DUMP_PROOF)\n"
       " must be called only after a Valid QUERY");
  return d_se->getProof();
}


Expr VCL::getTCC(){
  static Expr null;
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_TCC), true);
  }
  if(d_lastQueryTCC.isNull()) return null;
  else return d_lastQueryTCC.getExpr();
}


void VCL::getAssumptionsTCC(vector<Expr>& assumptions)
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_TCC_ASSUMPTIONS), true);
  }
  if(d_lastQuery.isNull())
    throw EvalException
      ("Method getAssumptionsTCC() (or command DUMP_TCC_ASSUMPTIONS)\n"
       " must be called only after a Valid QUERY");
  getAssumptions(d_lastQueryTCC.getAssumptionsRef(), assumptions);
}


Proof VCL::getProofTCC() {
  static Proof null;
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_TCC_PROOF), true);
  }
  if(d_lastQueryTCC.isNull()) return null;
  else return d_lastQueryTCC.getProof();
}


Expr VCL::getClosure() {
  static Expr null;
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_CLOSURE), true);
  }
  if(d_lastClosure.isNull() && !d_lastQuery.isNull()) {
    // Construct the proof of closure and cache it in d_lastClosure
    d_lastClosure = deriveClosure(d_lastQuery);
  }
  if(d_lastClosure.isNull()) return null;
  else return d_lastClosure.getExpr();
}


Proof VCL::getProofClosure() {
  static Proof null;
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_CLOSURE_PROOF), true);
  }
  if(d_lastClosure.isNull() && !d_lastQuery.isNull()) {
    // Construct the proof of closure and cache it in d_lastClosure
    d_lastClosure = deriveClosure(d_lastQuery);
  }
  if(d_lastClosure.isNull()) return null;
  else return d_lastClosure.getProof();
}


int VCL::stackLevel()
{
  return d_stackLevel->get();
}


void VCL::push()
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(PUSH), true);
  }
  d_se->push();
  d_stackLevel->set(stackLevel()+1);
}


void VCL::pop()
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(POP), true);
  }
  if (stackLevel() == 0) {
    throw EvalException
      ("POP called with no previous call to PUSH");
  }
  int level = stackLevel();
  while (level == stackLevel())
    d_se->pop();
}


void VCL::popto(int toLevel)
{
  // Check if the ofstream is open (as opposed to the command line flag)
  if(d_dump) {
    d_translator->dump(Expr(POPTO, ratExpr(toLevel, 1)), true);
  }
  if (toLevel < 0) toLevel = 0;
  while (stackLevel() > toLevel) {
    d_se->pop();
  }
}


int VCL::scopeLevel()
{
  return d_cm->scopeLevel();
}


void VCL::pushScope()
{
  throw EvalException ("Scope-level push/pop is no longer supported");
  d_cm->push();
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(PUSH_SCOPE), true);
  }
  IF_DEBUG(if((*d_flags)["dump-trace"].getString() != "")
	   dumpTrace(scopeLevel());)
}


void VCL::popScope()
{
  throw EvalException ("Scope-level push/pop is no longer supported");
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(POP_SCOPE), true);
  }
  if (scopeLevel() == 1) {
    cout << "Cannot POP from scope level 1" << endl;
  }
  else d_cm->pop();
  IF_DEBUG(if((*d_flags)["dump-trace"].getString() != "")
	   dumpTrace(scopeLevel());)
}


void VCL::poptoScope(int toLevel)
{
  throw EvalException ("Scope-level push/pop is no longer supported");
  if(d_dump) {
    d_translator->dump(Expr(POPTO_SCOPE, ratExpr(toLevel, 1)), true);
  }
  if (toLevel < 1) {
    d_cm->popto(0);
    d_cm->push();
  }
  else d_cm->popto(toLevel);
  IF_DEBUG(if((*d_flags)["dump-trace"].getString() != "")
	   dumpTrace(scopeLevel());)
}


Context* VCL::getCurrentContext()
{
  return d_cm->getCurrentContext();
}


void VCL::reset()
{
  destroy();
  init();
}

void VCL::logAnnotation(const Expr& annot)
{
  if (d_dump) {
    d_translator->dump(annot);
  }
}

void VCL::loadFile(const string& fileName, InputLanguage lang,
		   bool interactive, bool calledFromParser) {
  // TODO: move these?
  Parser parser(this, d_translator, lang, interactive, fileName);
  VCCmd cmd(this, &parser, calledFromParser);
  cmd.processCommands();
}


void VCL::loadFile(istream& is, InputLanguage lang,
		   bool interactive) {
  // TODO: move these?
  Parser parser(this, d_translator, lang, is, interactive);
  VCCmd cmd(this, &parser);
  cmd.processCommands();
}


// Verbosity: <= 0 = print nothing, only calculate
//            1 = only print current level
//            n = print n recursive levels

unsigned long VCL::getMemory(int verbosity)
{
  unsigned long memSelf = sizeof(VCL);
  unsigned long mem = 0;

  mem += d_cm->getMemory(verbosity - 1);
  mem += d_em->getMemory(verbosity - 1);
//   mem += d_tm->getMemory(verbosity - 1);
//   mem += d_se->getMemory(verbosity - 1);

//   mem += d_theoryCore->getMemory(verbosity - 1);
//   mem += d_theoryUF->getMemory(verbosity - 1);
//   mem += d_theoryArith->getMemory(verbosity - 1);
//   mem += d_theoryArray->getMemory(verbosity - 1);
//   mem += d_theoryQuant->getMemory(verbosity - 1);
//   mem += d_theoryRecords->getMemory(verbosity - 1);
//   mem += d_theorySimulate->getMemory(verbosity - 1);
//   mem += d_theoryBitvector->getMemory(verbosity - 1);
//   mem += d_theoryDatatype->getMemory(verbosity - 1);
//   mem += d_translator->getMemory(verbosity - 1);

//   mem += getMemoryVec(verbosity, d_theories, false, true);

//   mem += d_flags->getMemory(verbosity - 1);
//   mem += d_stackLevel->getMemory(verbosity - 1);
//   mem += d_statistics->getMemory(verbosity - 1);
//   mem += d_userAssertions->getMemory(verbosity - 1);
//   mem += d_batchedAssertions->getMemory(verbosity - 1);
//   mem += d_batchedAssertionsIdx->getMemory(verbosity - 1);

  //TODO: how to get memory for Expr and Theorems?

  MemoryTracker::print("VCL", verbosity, memSelf, mem);

  return mem + memSelf;
}

void VCL::setTimeLimit(unsigned limit) {
  d_theoryCore->setTimeLimit(limit);
}
