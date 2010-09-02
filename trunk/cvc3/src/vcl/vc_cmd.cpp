/*****************************************************************************/
/*!
 * \file vc_cmd.cpp
 *
 * Author: Clark Barrett
 *
 * Created: Fri Dec 13 22:39:02 2002
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
#include "vc_cmd.h"
#include "vc.h"
#include "parser.h"
#include "eval_exception.h"
#include "typecheck_exception.h"
#include "command_line_flags.h"
#include "expr_stream.h"

using namespace std;
using namespace CVC3;

VCCmd::VCCmd(ValidityChecker* vc, Parser* parser, bool calledFromParser)
  : d_vc(vc), d_parser(parser), d_name_of_cur_ctxt("DEFAULT"),
    d_calledFromParser(calledFromParser)
{
  d_map[d_name_of_cur_ctxt.c_str()] = d_vc->getCurrentContext();
}

VCCmd::~VCCmd() { }

void VCCmd::findAxioms(const Expr& e,  ExprMap<bool>& skolemAxioms,
		       ExprMap<bool>& visited) {
  if(visited.count(e)>0)
    return;
  else visited[e] = true;
  if(e.isSkolem()) {
    skolemAxioms.insert(e.getExistential(), true);
    return;
  }
  if(e.isClosure()) {
    findAxioms(e.getBody(), skolemAxioms, visited);
  }
  if(e.arity()>0) {
    Expr::iterator end = e.end();
    for(Expr::iterator i = e.begin(); i!=end; ++i)
      findAxioms(*i, skolemAxioms, visited);
  }

}

Expr VCCmd::skolemizeAx(const Expr& e)
{
  vector<Expr>vars;
  const vector<Expr>boundVars = e.getVars();
  for(unsigned int i=0; i<boundVars.size(); i++) {
    Expr skolV(e.skolemExpr(i));
    vars.push_back(skolV);
  }
  Expr sub = e.getBody().substExpr(boundVars, vars);
  return e.iffExpr(sub);
}

bool VCCmd::evaluateNext()
{
readAgain:
  if(d_parser->done()) return false; // No more commands
  Expr e;
  try {
    TRACE_MSG("commands", "** [commands] Parsing command...");
    e = d_parser->next();
    TRACE("commands verbose", "evaluateNext(", e, ")");
  }
  catch(Exception& e) {
    cerr << "*** " << e << endl;
    IF_DEBUG(++(debugger.counter("parse errors"));)
  }
  // The parser may return a Null Expr in case of parse errors or end
  // of file.  The right thing to do is to ignore it and repeat
  // reading.
  if(e.isNull()) {
    TRACE_MSG("commands", "** [commands] Null command; read again");
    goto readAgain;
  }
  if( d_vc->getFlags()["parse-only"].getBool() ) {
    TRACE_MSG("commands", "** [commands] parse-only; skipping evaluateCommand");
    goto readAgain;
  }

  return evaluateCommand(e);
}

void VCCmd::reportResult(QueryResult qres, bool checkingValidity)
{
  if (d_vc->getFlags()["printResults"].getBool()) {
    if (d_vc->getEM()->getOutputLang() == SMTLIB_LANG
        || d_vc->getEM()->getOutputLang() == SMTLIB_V2_LANG) {
      switch (qres) {
        case VALID:
          cout << "unsat" << endl;
          break;
        case INVALID:
          cout << "sat" << endl;
          break;
        case ABORT:
        case UNKNOWN:
          cout << "unknown" << endl;
          break;
        default:
          FatalAssert(false, "Unexpected case");
      }
    }
    else {
      switch (qres) {
        case VALID:
          cout << (checkingValidity ? "Valid." : "Unsatisfiable.") << endl;
          break;
        case INVALID:
          cout << (checkingValidity ? "Invalid." : "Satisfiable.") << endl;
          break;
        case ABORT:
          cout << "Unknown: resource limit exhausted." << endl;
          break;
        case UNKNOWN: {
          // Vector of reasons in case of incomplete result
          vector<string> reasons;
          IF_DEBUG(bool b =) d_vc->incomplete(reasons);
          DebugAssert(b, "Expected incompleteness");
          cout << "Unknown.\n\n";
          cout << "CVC3 was incomplete in this example due to:";
          for(vector<string>::iterator i=reasons.begin(), iend=reasons.end();
              i!=iend; ++i)
            cout << "\n * " << (*i);
          cout << endl << endl;
          break;
        }
        default:
          FatalAssert(false, "Unexpected case");
      }
    }
    cout << flush;
  }
  //d_vc->printStatistics();
  //  exit(0);
}


void VCCmd::printModel()
{
  ExprMap<Expr> m;
  d_vc->getConcreteModel(m);

  cout << "Current scope level is " << d_vc->scopeLevel() << "." << endl;
  ExprMap<Expr>::iterator it = m.begin(), end = m.end();
  if(it == end)
    cout << " Did not find concrete model for any vars" << endl;
  else {
    cout << "%Satisfiable  Variable Assignment: % \n";
    for(; it!= end; it++) {
      Expr eq;
      if(it->first.getType().isBool()) {
        DebugAssert((it->second).isBoolConst(),
                    "Bad variable assignement: e = "+(it->first).toString()
                    +"\n\n val = "+(it->second).toString());
        if((it->second).isTrue())
          eq = it->first;
        else
          eq = !(it->first);
      }
      else
        eq = (it->first).eqExpr(it->second);
      cout << Expr(ASSERT,  eq) << "\n";
    }
  }
}


// For debugging: there are missing cases: user-defined types, symbols inside of quantifiers, etc.
void VCCmd::printSymbols(Expr e, ExprMap<bool>& cache)
{
  if (cache.find(e) != cache.end()) return;
  switch (e.getKind()) {
    case SKOLEM_VAR:
    case UCONST: {
      cout << e << " : ";
      ExprStream os(d_vc->getEM());
      os.dagFlag(false);
      os << e.getType().getExpr();
      cout << ";" << endl;
      break;
    }
    case APPLY: {
      Expr op = e.getOpExpr();
      if ((op.getKind() == UFUNC) && (cache.find(op) == cache.end())) {
        cout << op << " : ";
        ExprStream os(d_vc->getEM());
        os.dagFlag(false);
        os << op.getType().getExpr();
        cout << ";" << endl;
        cache[op] = true;
      }
      // fall through
    }
    default: {
      Expr::iterator i = e.begin(), iend = e.end();
      for (; i != iend; ++i) {
        printSymbols(*i, cache);
      }
      break;
    }
  }
  cache[e] = true;
}


bool debug_skolem = false;


void VCCmd::printCounterExample()
{
  vector<Expr> assertions;
  ExprMap<bool> skolemAxioms;
  ExprMap<bool> visited;

  d_vc->getCounterExample(assertions);

  // get variable information
  ExprMap<bool> cache;
  unsigned i;
  for (i = 0; i < assertions.size(); i++) {
    printSymbols(assertions[i], cache);
  }

  cout << "% Current scope level is " << d_vc->scopeLevel() << "." << endl;
  if (assertions.size() == 0) {
    cout << "% There are no assertions\n";
  } else {

    cout << "% Assertions which make the QUERY invalid:\n";

    for (i = 0; i < assertions.size(); i++) {
      cout << Expr(ASSERT, assertions[i]) << "\n";
      findAxioms(assertions[i], skolemAxioms, visited);
    }

    if (debug_skolem) {
      cout << "% Including skolemization axioms:\n";

      ExprMap<bool>::iterator end = skolemAxioms.end();
      for(ExprMap<bool>::iterator it = skolemAxioms.begin(); it!=end; it++)
        cout << "ASSERT " << skolemizeAx((*it).first) << ";" << endl;
    }
  }
  cout << endl;
}


bool VCCmd::evaluateCommand(const Expr& e0)
{
  TRACE("commands", "evaluateCommand(", e0.toString(PRESENTATION_LANG), ") {");
  Expr e(e0);
  if(e.getKind() != RAW_LIST || e.arity() == 0 || e[0].getKind() != ID)
    throw EvalException("Invalid command: "+e.toString());
  const string& kindName = e[0][0].getString();
  int kind = d_vc->getEM()->getKind(kindName);
  if(kind == NULL_KIND)
    throw EvalException("Unknown command: "+e.toString());
  switch(kind) {
  case CONST: { // (CONST (id_1 ... id_n) type) or (CONST id type)
    if(e.arity() == 3) {
      Type t(d_vc->parseExpr(e[2]));
      vector<Expr> vars;
      if(e[1].getKind() == RAW_LIST)
	vars = e[1].getKids();
      else
	vars.push_back(e[1]);
      for(vector<Expr>::iterator i=vars.begin(), iend=vars.end(); i!=iend; ++i) {
	if((*i).getKind() != ID)
	  throw EvalException("Constant name must be an identifier: "
			      +i->toString());
      }
      if (t.isFunction()) {
	for(vector<Expr>::iterator i=vars.begin(), iend=vars.end();
	    i!=iend; ++i) {
	  Op op = d_vc->createOp((*i)[0].getString(), t);
	  TRACE("commands", "evaluateNext: declare new uninterpreted function: ",
		op, "");
	}
      }
      else {
	for(vector<Expr>::iterator i=vars.begin(), iend=vars.end();
	    i!=iend; ++i) {
	  // Add to variable list
	  Expr v = d_vc->varExpr((*i)[0].getString(), t);
	  TRACE_MSG("commands", "** [commands] Declare new variable");
	  TRACE("commands verbose", "evaluateNext: declare new UCONST: ",
		v, "");
	}
      }
    } else if(e.arity() == 4) { // Constant definition (CONST id type def)
      TRACE_MSG("commands", "** [commands] Define new constant");
      // Set the type for later typechecking
      DebugAssert(e[1].getKind() == ID, "Expected ID kind");
      Type t(d_vc->parseExpr(e[2]));
      Expr def(d_vc->parseExpr(e[3]));

      if(t.isFunction()) {
	d_vc->createOp(e[1][0].getString(), t, def);
	TRACE("commands verbose", "evaluateNext: define new function: ",
	      e[1][0].getString(), "");
      } else {
	d_vc->varExpr(e[1][0].getString(), t, def);
	TRACE("commands verbose", "evaluateNext: define new variable: ",
	      e[1][0].getString(), "");
      }
    } else
      throw EvalException("Wrong number of arguments in CONST: "+e.toString());
    break;
  }
  case DEFUN: { // (DEFUN name ((x y z type1) ... ) resType [ body ])
    if(e.arity() != 5 && e.arity() != 4)
      throw EvalException
	("DEFUN requires 3 or 4 arguments:"
	 " (DEFUN f (args) type [ body ]):\n\n  "
	 +e.toString());
    if(e[2].getKind() != RAW_LIST)
      throw EvalException
	("2nd argument of DEFUN must be a list of arguments:\n\n  "
	 +e.toString());

    // Build a CONST declaration and parse it recursively

    // Build the function type
    vector<Expr> argTps;
    for(Expr::iterator i=e[2].begin(), iend=e[2].end(); i!=iend; ++i) {
      if(i->getKind() != RAW_LIST || i->arity() < 2)
	throw EvalException
	  ("DEFUN: bad argument declaration:\n\n  "+i->toString()
	   +"\n\nIn the following statement:\n\n  "
	   +e.toString());
      Expr tp((*i)[i->arity()-1]);
      for(int j=0, jend=i->arity()-1; j<jend; ++j)
	argTps.push_back(tp);
    }
    argTps.push_back(e[3]);
    Expr fnType = d_vc->listExpr("ARROW", argTps);
    Expr newDecl; // The resulting transformed declaration
    if(e.arity() == 5) {
      // Build the LAMBDA expression
      Expr lambda(d_vc->listExpr("LAMBDA", e[2], e[4]));
      // Construct the (CONST name fnType lambda) declaration
      newDecl = d_vc->listExpr("CONST", e[1], fnType, lambda);
    } else {
      newDecl = d_vc->listExpr("CONST", e[1], fnType);
    }
    // Parse the new declaration
    return evaluateCommand(newDecl);
    break;
  }
  case TYPEDEF: {
    if (e.arity() == 2) {
      // Datatype command
      DebugAssert(e.arity() == 2, "Bad TYPEDEF");
      Expr res = d_vc->parseExpr(e[1]);
      // convert res to vectors

      Expr eNames = res[0];
      Expr eCons = res[1];
      Expr eSel = res[2];
      Expr eTypes = res[3];

      vector<string> names;
      vector<vector<string> > constructors(eNames.arity());
      vector<vector<vector<string> > > selectors(eNames.arity());
      vector<vector<vector<Expr> > > types(eNames.arity());

      int i, j, k;
      for (i = 0; i < eNames.arity(); ++i) {
        names.push_back(eNames[i].getString());
        selectors[i].resize(eSel[i].arity());
        types[i].resize(eTypes[i].arity());
        for (j = 0; j < eCons[i].arity(); ++j) {
          constructors[i].push_back(eCons[i][j].getString());
          for (k = 0; k < eSel[i][j].arity(); ++k) {
            selectors[i][j].push_back(eSel[i][j][k].getString());
            types[i][j].push_back(eTypes[i][j][k]);
          }
        }
      }

      vector<Type> returnTypes;
      d_vc->dataType(names, constructors, selectors, types, returnTypes);
      break;
    }
    DebugAssert(e.arity() == 3, "Bad TYPEDEF");
    Expr def(d_vc->parseExpr(e[2]));
    Type t = d_vc->createType(e[1][0].getString(), def);
    TRACE("commands", "evaluateNext: declare new TYPEDEF: ", t, "");
  }
    break;
  case TYPE: {
    if(e.arity() < 2)
      throw EvalException("Bad TYPE declaration: "+e.toString());
    Expr::iterator i=e.begin(), iend=e.end();
    ++i; // Skip "TYPE" symbol
    for(; i!=iend; ++i) {
      if(i->getKind() != ID)
	throw EvalException("Type name must be an identifier: "+i->toString());
      Type t = d_vc->createType((*i)[0].getString());
      TRACE("commands", "evaluateNext: declare new TYPEDECL: ", t, "");
    }
  }
    break;
  case ASSERT: {
    if(e.arity() != 2)
      throw EvalException("ASSERT requires exactly one argument, but is given "
			  +int2string(e.arity()-1)+":\n "+e.toString());
    TRACE_MSG("commands", "** [commands] Asserting formula");
    d_vc->assertFormula(d_vc->parseExpr(e[1]));
    break;
  }
  case QUERY: {
    if(e.arity() != 2)
      throw EvalException("QUERY requires exactly one argument, but is given "
			  +int2string(e.arity()-1)+":\n "+e.toString());
    TRACE_MSG("commands", "** [commands] Query formula");
    QueryResult qres = d_vc->query(d_vc->parseExpr(e[1]));
    if (qres == UNKNOWN && d_vc->getFlags()["unknown-check-model"].getBool())
		qres = d_vc->tryModelGeneration();
    reportResult(qres);
    if (qres == INVALID) {
      if (d_vc->getFlags()["counterexample"].getBool()) {
        printCounterExample();
      }
      if (d_vc->getFlags()["model"].getBool()) {
        printModel();
      }
    }
    break;
  }
  case CHECKSAT: {
    QueryResult qres;
    TRACE_MSG("commands", "** [commands] CheckSat");
    if (e.arity() == 1) {
      qres = d_vc->checkUnsat(d_vc->trueExpr());
    }
    else if (e.arity() == 2) {
      qres = d_vc->checkUnsat(d_vc->parseExpr(e[1]));
    }
    else {
      throw EvalException("CHECKSAT requires no more than one argument, but is given "
			  +int2string(e.arity()-1)+":\n "+e.toString());
    }
    if (qres == UNKNOWN && !d_vc->getFlags()["translate"].getBool() && d_vc->getFlags()["unknown-check-model"].getBool())
    	qres = d_vc->tryModelGeneration();
    reportResult(qres, false);
    if (qres == SATISFIABLE) {
      if (d_vc->getFlags()["counterexample"].getBool()) {
        printCounterExample();
      }
      if (d_vc->getFlags()["model"].getBool()) {
        printModel();
      }
    }
//     {//for debug only by yeting
//       Proof p = d_vc->getProof();
//       if (d_vc->getFlags()["printResults"].getBool()) {
//  	cout << p << endl;
//  	cout << flush;
//       }
//     }


    break;
  }
  case CONTINUE: {
    if (e.arity() != 1) {
      throw EvalException("CONTINUE takes no arguments");
    }
    TRACE_MSG("commands", "** [commands] Continue");
    QueryResult qres = d_vc->checkContinue();
    if (d_vc->getFlags()["printResults"].getBool()) {
      switch (qres) {
        case VALID:
          cout << "No more models found." << endl;
          break;
        case INVALID:
          cout << "Model found" << endl;
          break;
        case ABORT:
          cout << "Unknown: resource limit exhausted." << endl;
          break;
        case UNKNOWN: {
          // Vector of reasons in case of incomplete result
          vector<string> reasons;
          IF_DEBUG(bool b =) d_vc->incomplete(reasons);
          DebugAssert(b, "Expected incompleteness");
          cout << "Unknown.\n\n";
          cout << "CVC3 was incomplete in this example due to:";
          for(vector<string>::iterator i=reasons.begin(), iend=reasons.end();
              i!=iend; ++i)
            cout << "\n * " << (*i);
          cout << endl << endl;
          break;
        }
        default:
          FatalAssert(false, "Unexpected case");
      }
      cout << flush;
    }
    break;
  }
  case RESTART: {
    if(e.arity() != 2)
      throw EvalException("RESTART requires exactly one argument, but is given "
			  +int2string(e.arity()-1)+":\n "+e.toString());
    TRACE_MSG("commands", "** [commands] Restart formula");
    QueryResult qres = d_vc->restart(d_vc->parseExpr(e[1]));
    reportResult(qres);
    if (qres == INVALID) {
      if (d_vc->getFlags()["counterexample"].getBool()) {
        printCounterExample();
      }
      if (d_vc->getFlags()["model"].getBool()) {
        printModel();
      }
    }
    break;
  }
  case TRANSFORM: {
    if(e.arity() != 2)
      throw EvalException
	("TRANSFORM requires exactly one argument, but is given "
	 +int2string(e.arity()-1)+":\n "+e.toString());
    TRACE_MSG("commands", "** [commands] Transforming expression");
    Expr ee = d_vc->parseExpr(e[1]);
    e = d_vc->simplify(ee);
    if (d_vc->getFlags()["printResults"].getBool()) d_vc->printExpr(e);
    break;
  }
  case PRINT:
    if(e.arity() != 2)
      throw EvalException
	("PRINT requires exactly one argument, but is given "
	 +int2string(e.arity()-1)+":\n "+e.toString());
    d_vc->printExpr(d_vc->parseExpr(e[1]));
    break;
  case PUSH:
  case POP:
  case PUSH_SCOPE:
  case POP_SCOPE: {
    int arg;
    if (e.arity() == 1) arg = 1;
    else {
      DebugAssert(e.arity() == 2 && e[1].getKind() == RATIONAL_EXPR,
                  "Bad argument to "+kindName);
      arg = e[1].getRational().getInt();
      if(arg <= 0)
        throw EvalException("Argument to PUSH or POP is <= 0");
    }
    if (kind == PUSH) {
      for (int i = 0; i < arg; i++) {
        d_vc->push();
      }
    }
    else if (kind == POP) {
      if(arg > d_vc->stackLevel())
        throw EvalException("Argument to POP is out of range:\n"
                            " current stack level = "
                            +int2string(d_vc->stackLevel())
                            +"\n argument = "
                            +int2string(arg));
      for (int i = 0; i < arg; i++) {
        d_vc->pop();
      }
    }
    else if (kind == PUSH_SCOPE) {
      for (int i = 0; i < arg; i++) {
        d_vc->pushScope();
      }
    }
    else if (kind == POP_SCOPE) {
      if(arg >= d_vc->scopeLevel())
        throw EvalException("Argument to POP_SCOPE is out of range:\n"
                            " current scope = "
                            +int2string(d_vc->scopeLevel())
                            +"\n argument = "
                            +int2string(arg));
      for (int i = 0; i < arg; i++) {
        d_vc->popScope();
      }
    }
    break;
  }
  case POPTO:
  case POPTO_SCOPE: {
    int arg;
    if (e.arity() == 1) arg = 0;
    else {
      DebugAssert(e.arity() == 2 && e[1].getKind() == RATIONAL_EXPR,
                  "Bad argument to "+kindName);
      arg = e[1].getRational().getInt();
    }
    if (kind == POPTO) {
      d_vc->popto(arg);
    }
    else {
      d_vc->poptoScope(arg);
    }
    break;
  }
  case RESET: {
    throw ResetException();
    break;
  }
  case WHERE:
  case ASSERTIONS:
  case ASSUMPTIONS:
  {
    vector<Expr> assertions;
    ExprMap<bool> skolemAxioms;
    ExprMap<bool> visited;

    d_vc->getAssumptions(assertions);

    if (d_vc->getFlags()["printResults"].getBool()) {
      cout << "Current stack level is " << d_vc->stackLevel()
           << " (scope " << d_vc->scopeLevel() << ")." << endl;
      if (assertions.size() == 0) {
        cout << "% No active assumptions\n";
      } else {
        cout << "% Active assumptions:\n";
        for (unsigned i = 0; i < assertions.size(); i++) {
          cout << "ASSERT " << assertions[i] << ";" << endl;
          findAxioms(assertions[i], skolemAxioms, visited);
        }
        ExprMap<bool>::iterator it = skolemAxioms.begin();
        ExprMap<bool>::iterator end = skolemAxioms.end();
        if (it != end) {
          cout << "% Skolemization axioms" << endl;
          for(; it!=end; ++it)
            cout << "ASSERT " << skolemizeAx((*it).first) << ";" << endl;
        }
      }
      cout << endl;
    }
    break;
  }
  case COUNTEREXAMPLE: {
    if (d_vc->getFlags()["printResults"].getBool()) {
      printCounterExample();
    }
    break;
  }
  case COUNTERMODEL: {
    if (d_vc->getFlags()["printResults"].getBool()) {
      try {
        printModel();
      } catch (Exception& e) {
        throw EvalException(e.toString());
      }
    }
    break;
  }
  case TRACE: { // Set a trace flag
#ifdef _CVC3_DEBUG_MODE
    if(e.arity() != 2)
      throw EvalException("TRACE takes exactly one string argument");
    if(!e[1].isString())
      throw EvalException("TRACE requires a string argument");
    debugger.traceFlag(e[1].getString()) = true;
#endif
  }
    break;
  case UNTRACE: { // Unset a trace flag
#ifdef _CVC3_DEBUG_MODE
    if(e.arity() != 2)
      throw EvalException("UNTRACE takes exactly one string argument");
    if(!e[1].isString())
      throw EvalException("UNTRACE requires a string argument");
    debugger.traceFlag(e[1].getString()) = false;
#endif
  }
    break;
  case OPTION: {
    if(e.arity() != 3)
      throw EvalException("OPTION takes exactly two arguments "
                          "(name and value of a flag)");
    if(!e[1].isString())
      throw EvalException("OPTION: flag name must be a string");
    CLFlags& flags = d_vc->getFlags();
    string name(e[1].getString());
    vector<string> names;
    size_t n = flags.countFlags(name, names);
    if(n != 1)
      throw EvalException("OPTION: found "+int2string(n)
                          +" flags matching "+name
                          +".\nThe flag name must uniquely resolve.");
    name = names[0];
    const CLFlag& flag(flags[name]);
    // If the flag is set on the command line, ignore it
    if(flag.modified()) break;
    switch(flag.getType()) {
    case CLFLAG_BOOL:
      if(!(e[2].isRational() && e[2].getRational().isInteger()))
        throw EvalException("OPTION: flag "+name
                            +" expects a boolean value (0 or 1");
      flags.setFlag(name, e[2].getRational().getInt() != 0);
      break;
    case CLFLAG_INT:
      if(!(e[2].isRational() && e[2].getRational().isInteger()))
        throw EvalException("OPTION: flag "+name+" expects an integer value");
      flags.setFlag(name, e[2].getRational().getInt());
      break;
    case CLFLAG_STRING:
      if(!e[2].isString())
        throw EvalException("OPTION: flag "+name+" expects a string value");
      flags.setFlag(name, e[2].getString());
      break;
    default:
      throw EvalException("OPTION: the type of flag "+name
                          +" is not supported by the OPTION commnand");
      break;
    }
    d_vc->reprocessFlags();
  }
    break;
  case DUMP_PROOF: {
    Proof p = d_vc->getProof();
    if (d_vc->getFlags()["printResults"].getBool()) {
      cout << p << endl;
      cout << flush;
    }
    break;
  }
  case DUMP_ASSUMPTIONS: { // Assumption tracking
    vector<Expr> assertions;
    d_vc->getAssumptionsUsed(assertions);

    if (d_vc->getFlags()["printResults"].getBool()) {
      if(assertions.size() == 0) {
        cout << "% No relevant assumptions\n";
      } else {
        cout << "% Relevant assumptions:\n";
        for (unsigned i = 0; i < assertions.size(); i++) {
          cout << Expr(ASSERT, assertions[i]) << "\n";
        }
      }
      cout << endl << flush;
    }
    break;
  }
  case DUMP_TCC: {
    const Expr& tcc = d_vc->getTCC();

    if (d_vc->getFlags()["printResults"].getBool()) {
      if(tcc.isNull())
        cout << "% No TCC is avaialble" << endl;
      else
        cout << "% TCC for the last declaration, ASSERT, or QUERY:\n\n"
             << tcc << endl;
    }
    break;
  }
  case DUMP_TCC_ASSUMPTIONS: {
    vector<Expr> assertions;
    d_vc->getAssumptionsTCC(assertions);
    if (d_vc->getFlags()["printResults"].getBool()) {
      if(assertions.size() == 0) {
        cout << "% No relevant assumptions\n";
      } else {
        cout << "% Relevant assumptions for the last TCC:\n";
        for (unsigned i = 0; i < assertions.size(); i++) {
          cout << Expr(ASSERT, assertions[i]) << "\n";
        }
      }
      cout << endl << flush;
    }
    break;
  }
  case DUMP_TCC_PROOF: {
    const Proof& tcc = d_vc->getProofTCC();
    if (d_vc->getFlags()["printResults"].getBool()) {
      if(tcc.isNull())
        cout << "% No TCC is avaialble" << endl;
      else
        cout << "% Proof of TCC for the last declaration, ASSERT, or QUERY:\n\n"
             << tcc << endl;
    }
    break;
  }
  case DUMP_CLOSURE: {
    const Expr& cl = d_vc->getClosure();
    if (d_vc->getFlags()["printResults"].getBool()) {
      if(cl.isNull())
        cout << "% No closure is avaialble" << endl;
      else
        cout << "% Closure for the last QUERY:\n\n" << cl << endl;
    }
    break;
  }
  case DUMP_CLOSURE_PROOF: {
    const Proof& cl = d_vc->getProofClosure();
    if (d_vc->getFlags()["printResults"].getBool()) {
      if(cl.isNull())
        cout << "% No closure is avaialble" << endl;
      else
        cout << "% Proof of closure for the last QUERY:\n\n" << cl << endl;
    }
    break;
  }
  case ECHO:
    if(e.arity() != 2)
      throw EvalException("ECHO: wrong number of arguments: "
			  + e.toString());
    if(!e[1].isString())
      throw EvalException("ECHO: the argument must be a string: "
			  +e.toString());
    if (d_vc->getFlags()["printResults"].getBool()) {
      cout << e[1].getString();
      cout << endl << flush;
    }
    break;
  case SEQ: {
    Expr::iterator i=e.begin(), iend=e.end();
    ++i; // Skip "SEQ" symbol
    bool success = true;
    for(; i!=iend; ++i) {
      try {
        success = success && evaluateCommand(*i);
      } catch(ResetException& e) {
        if (++i == iend) throw e;
        throw EvalException("RESET can only be the last command in a sequence");
      }
    }
    return success;
  }
  case ARITH_VAR_ORDER: {
	  if (e.arity() <= 2)
		  throw EvalException("ARITH_VAR_ORDER takes at least two arguments");
	  Expr smaller;
	  Expr bigger = d_vc->parseExpr(e[1]);
	  for (int i = 2; i < e.arity(); i ++) {
		  smaller = bigger;
		  bigger = d_vc->parseExpr(e[i]);
		  if (!d_vc->addPairToArithOrder(smaller, bigger))
			  throw EvalException("ARITH_VAR_ORDER only takes arithmetic terms");
	  }
	  return true;
  }
  case ANNOTATION: {
    for (int i = 1; i < e.arity(); ++i) {
      if (e[i].arity() == 1) {
        d_vc->logAnnotation(Expr(ANNOTATION, e[i][0]));
      }
      else {
        DebugAssert(e[i].arity() == 2, "Expected arity 2");
        d_vc->logAnnotation(Expr(ANNOTATION, e[i][0], e[i][1]));
      }
    }
    break;
  }
  case INCLUDE: { // read in the specified file
    if(e.arity() != 2)
      throw EvalException("INCLUDE takes exactly one string argument");
    if(!e[1].isString())
      throw EvalException("INCLUDE requires a string argument");
    ifstream fs;
    fs.open(e[1].getString().c_str(),ios::in);
    if(!fs.is_open()) {
      fs.close();
      throw EvalException("File "+e[1].getString()+" does not exist");
    }
    fs.close();
    d_vc->loadFile(e[1].getString(),
                   d_vc->getEM()->getInputLang(),
                   d_vc->getFlags()["interactive"].getBool(),
                   true /* nested call */);
    break;
  }
  case HELP:
    cout << "Use the -help command-line option for help." << endl;
    break;
  case DUMP_SIG:
  case DBG:
  case SUBSTITUTE:
  case GET_CHILD:
  case GET_TYPE:
  case CHECK_TYPE:
  case FORGET:
  case CALL:
  default:
    throw EvalException("Unknown command: " + e.toString());
    break;
  }
  TRACE_MSG("commands", "evaluateCommand => true }");
  return true;
}


void VCCmd::processCommands()
{
  bool error(false);
  try {
    bool success(true);
    while(success) {
      try {
        success = evaluateNext();
      } catch (ResetException& e) {
        if (d_calledFromParser) {
          throw EvalException("RESET not supported within INCLUDEd file");
        }
        d_parser->reset();
        d_vc->reset();
        success = true;
      } catch (EvalException& e) {
        error= true;
        cerr << "*** Eval Error:\n  " << e << endl;
      }
    }
    
  }

  catch(Exception& e) {
    cerr << "*** Fatal exception:\n" << e << endl;
    error= true;
  } catch(...) {
    cerr << "*** Unknown fatal exception caught" << endl;
    error= true;
  } 
  
  if (error)
  {
    d_parser->printLocation(cerr);
    cerr << ": this is the location of the error" << endl;
  }
}
