/*****************************************************************************/
/*!
 * \file translator.cpp
 * \brief Description: Code for translation between languages
 *
 * Author: Clark Barrett
 *
 * Created: Sat Jun 25 18:06:52 2005
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


#include <cctype>

#include "translator.h"
#include "expr.h"
#include "theory_core.h"
#include "theory_uf.h"
#include "theory_arith.h"
#include "theory_bitvector.h"
#include "theory_array.h"
#include "theory_quant.h"
#include "theory_records.h"
#include "theory_simulate.h"
#include "theory_datatype.h"
#include "theory_datatype_lazy.h"
#include "smtlib_exception.h"
#include "command_line_flags.h"


using namespace std;
using namespace CVC3;


string Translator::fileToSMTLIBIdentifier(const string& filename)
{
  string tmpName;
  string::size_type pos = filename.rfind("/");
  if (pos == string::npos) {
    tmpName = filename;
  }
  else {
    tmpName = filename.substr(pos+1);
  }
  char c = tmpName[0];
  string res;
  if ((c < 'A' || c > 'Z') && (c < 'a' || c > 'z')) {
    res = "B_";
  }
  for (unsigned i = 0; i < tmpName.length(); ++i) {
    c = tmpName[i];
    if ((c < 'A' || c > 'Z') && (c < 'a' || c > 'z') &&
        (c < '0' || c > '9') && (c != '.' && c != '_')) {
      c = '_';
    }
    res += c;
  }
  return res;
}


Expr Translator::preprocessRec(const Expr& e, ExprMap<Expr>& cache)
{
  ExprMap<Expr>::iterator i(cache.find(e));
  if(i != cache.end()) {
    return (*i).second;
  }

  if (d_theoryCore->getFlags()["liftITE"].getBool() &&
      e.isPropAtom() && e.containsTermITE()) {
    Theorem thm = d_theoryCore->getCommonRules()->liftOneITE(e);
    return preprocessRec(thm.getRHS(), cache);
  }

  if (e.isClosure()) {
    Expr newBody = preprocessRec(e.getBody(), cache);
    Expr e2(e);
    if (newBody != e.getBody()) {
      e2 = d_em->newClosureExpr(e.getKind(), e.getVars(), newBody);
    }
    d_theoryCore->theoryOf(e2)->setUsed();
    cache[e] = e2;
    return e2;
  }

  Expr e2(e);
  vector<Expr> children;
  bool diff = false;

  for(int k = 0; k < e.arity(); ++k) {
    // Recursively preprocess the kids
    Expr child = preprocessRec(e[k], cache);
    if (child != e[k]) diff = true;
    children.push_back(child);
  }
  if (diff) {
    e2 = Expr(e.getOp(), children);
  }

  Rational r;
  switch (e2.getKind()) {
    case RATIONAL_EXPR:
      if (d_convertToBV) {
        Rational r = e2.getRational();
        if (!r.isInteger()) {
          FatalAssert(false, "Cannot convert non-integer constant to BV");
        }
        Rational limit = pow(d_convertToBV-1, (Rational)2);
        if (r >= limit) {
          FatalAssert(false, "Cannot convert to BV: integer too big");
        }
        else if (r < -limit) {
          FatalAssert(false, "Cannot convert to BV: integer too small");
        }
        e2 = d_theoryBitvector->signed_newBVConstExpr(r, d_convertToBV);
        break;
      }

    case READ:
      if (!d_unknown && d_theoryCore->getFlags()["convert2array"].getBool()) {
        if (e2[1].getKind() != UCONST) break;
        map<string, Type>::iterator i = d_arrayConvertMap->find(e2[1].getName());
        if (i == d_arrayConvertMap->end()) {
          (*d_arrayConvertMap)[e2[1].getName()] = *d_indexType;
        }
        else {
          if ((*i).second != (*d_indexType)) {
            d_unknown = true;
          }
        }
      }
      break;

    case WRITE:
      if (!d_unknown && d_theoryCore->getFlags()["convert2array"].getBool()) {
        map<string, Type>::iterator i;
        if (e2[1].getKind() == UCONST) {
          i = d_arrayConvertMap->find(e2[1].getName());
          if (i == d_arrayConvertMap->end()) {
            (*d_arrayConvertMap)[e2[1].getName()] = *d_indexType;
          }
          else {
            if ((*i).second != (*d_indexType)) {
              d_unknown = true;
              break;
            }
          }
        }
        if (e2[2].getKind() != UCONST) break;
        i = d_arrayConvertMap->find(e2[2].getName());
        if (i == d_arrayConvertMap->end()) {
          (*d_arrayConvertMap)[e2[2].getName()] = *d_elementType;
        }
        else {
          if ((*i).second != (*d_elementType)) {
            d_unknown = true;
          }
        }
      }
      break;

    case APPLY:
      // Expand lambda applications
      if (e2.getOpKind() == LAMBDA) {
        Expr lambda(e2.getOpExpr());
        Expr body(lambda.getBody());
        const vector<Expr>& vars = lambda.getVars();
        FatalAssert(vars.size() == (size_t)e2.arity(),
                    "wrong number of arguments applied to lambda\n");
        body = body.substExpr(vars, e2.getKids());
        e2 = preprocessRec(body, cache);
      }
      break;

    case EQ:
      if (d_theoryArith->getBaseType(e2[0]) != d_theoryArith->realType())
        break;
      if (d_theoryCore->getFlags()["convert2array"].getBool() &&
          ((e2[0].getKind() == UCONST && d_arrayConvertMap->find(e2[0].getName()) == d_arrayConvertMap->end()) ||
          (e2[1].getKind() == UCONST && d_arrayConvertMap->find(e2[1].getName()) == d_arrayConvertMap->end()))) {
        d_equalities.push_back(e2);
      }
      goto arith_rewrites;

    case UMINUS:
      if (d_convertToBV) {
        e2 = Expr(BVUMINUS, e2[0]);
        break;
      }
      if (d_theoryArith->isSyntacticRational(e2, r)) {
        e2 = preprocessRec(d_em->newRatExpr(r), cache);
        break;
      }
      goto arith_rewrites;

    case DIVIDE:
      if (d_convertToBV) {
        FatalAssert(false, "Conversion of DIVIDE to BV not implemented yet");
        break;
      }
      if (d_theoryArith->isSyntacticRational(e2, r)) {
        e2 = preprocessRec(d_em->newRatExpr(r), cache);
        break;
      }
      else if (d_convertArith && e2[1].isRational()) {
        r = e2[1].getRational();
        if (r != 0) {
          e2 = d_em->newRatExpr(1/r) * e2[0];
          e2 = preprocessRec(e2, cache);
          break;
        }
      }
      goto arith_rewrites;

    case MINUS:
      if (d_convertToBV) {
        e2 = Expr(BVSUB, e2[0], e2[1]);
        break;
      }
      if (d_convertArith) {
        if (e2[0].isRational() && e2[1].isRational()) {
          e2 = d_em->newRatExpr(e2[0].getRational() - e2[1].getRational());
          break;
        }
      }
      goto arith_rewrites;

    case PLUS:
      if (d_convertToBV) {
        e2 = Expr(Expr(BVPLUS, d_em->newRatExpr(d_convertToBV)).mkOp(), e2.getKids());
        break;
      }
      if (d_convertArith) {
        // Flatten and combine constants
        vector<Expr> terms;
        bool changed = false;
        int numConst = 0;
        r = 0;
        Expr::iterator i = e2.begin(), iend = e2.end();
        for(; i!=iend; ++i) {
          if ((*i).getKind() == PLUS) {
            changed = true;
            Expr::iterator i2 = (*i).begin(), i2end = (*i).end();
            for (; i2 != i2end; ++i2) {
              if ((*i2).isRational()) {
                r += (*i2).getRational();
                numConst++;
              }
              else terms.push_back(*i2);
            }
          }
          else {
            if ((*i).isRational()) {
              r += (*i).getRational();
              numConst++;
              if (numConst > 1) changed = true;
            }
            else terms.push_back(*i);
          }
        }
        if (terms.size() == 0) {
          e2 = preprocessRec(d_em->newRatExpr(r), cache);
          break;
        }
        else if (terms.size() == 1) {
          if (r == 0) {
            e2 = terms[0];
            break;
          }
          else if (r < 0) {
            e2 = preprocessRec(Expr(MINUS, terms[0], d_em->newRatExpr(-r)), cache);
            break;
          }
        }
        if (changed) {
          if (r != 0) terms.push_back(d_em->newRatExpr(r));
          e2 = preprocessRec(Expr(PLUS, terms), cache);
          break;
        }
      }
      goto arith_rewrites;

    case MULT:
      if (d_convertToBV) {
        e2 = Expr(Expr(BVMULT, d_em->newRatExpr(d_convertToBV)).mkOp(), e2.getKids());
        break;
      }
      if (d_convertArith) {
        // Flatten and combine constants
        vector<Expr> terms;
        bool changed = false;
        int numConst = 0;
        r = 1;
        Expr::iterator i = e2.begin(), iend = e2.end();
        for(; i!=iend; ++i) {
          if ((*i).getKind() == MULT) {
            changed = true;
            Expr::iterator i2 = (*i).begin(), i2end = (*i).end();
            for (; i2 != i2end; ++i2) {
              if ((*i2).isRational()) {
                r *= (*i2).getRational();
                numConst++;
              }
              else terms.push_back(*i2);
            }
          }
          else {
            if ((*i).isRational()) {
              r *= (*i).getRational();
              numConst++;
              if (numConst > 1) changed = true;
            }
            else terms.push_back(*i);
          }
        }
        if (r == 0) {
          e2 = preprocessRec(d_em->newRatExpr(0), cache);
          break;
        }
        else if (terms.size() == 0) {
          e2 = preprocessRec(d_em->newRatExpr(r), cache);
          break;
        }
        else if (terms.size() == 1) {
          if (r == 1) {
            e2 = terms[0];
            break;
          }
        }
        if (changed) {
          if (r != 1) terms.push_back(d_em->newRatExpr(r));
          e2 = preprocessRec(Expr(MULT, terms), cache);
          break;
        }
      }
      goto arith_rewrites;

    case POW:
      if (d_convertToBV) {
        FatalAssert(false, "Conversion of POW to BV not implemented");
        break;
      }
      if (d_convertArith && e2[0].isRational()) {
        r = e2[0].getRational();
        if (r.isInteger() && r.getNumerator() == 2) {
          e2 = preprocessRec(e2[1] * e2[1], cache);
          break;
        }
      }
      // fall through

    case LT:
      if (d_convertToBV) {
        e2 = Expr(BVSLT, e2[0], e2[1]);
        break;
      }

    case GT:
      if (d_convertToBV) {
        e2 = Expr(BVSLT, e2[1], e2[0]);
        break;
      }

    case LE:
      if (d_convertToBV) {
        e2 = Expr(BVSLE, e2[0], e2[1]);
        break;
      }

    case GE:
      if (d_convertToBV) {
        e2 = Expr(BVSLE, e2[1], e2[0]);
        break;
      }
      

    case INTDIV:
    case MOD:

  arith_rewrites:
      if (d_iteLiftArith) {
        diff = false;
        children.clear();
        vector<Expr> children2;
        Expr cond;
        for (int k = 0; k < e2.arity(); ++k) {
          if (e2[k].getKind() == ITE && !diff) {
            diff = true;
            cond = e2[k][0];
            children.push_back(e2[k][1]);
            children2.push_back(e2[k][2]);
          }
          else {
            children.push_back(e2[k]);
            children2.push_back(e2[k]);
          }
        }
        if (diff) {
          Expr thenpart = Expr(e2.getOp(), children);
          Expr elsepart = Expr(e2.getOp(), children2);
          e2 = cond.iteExpr(thenpart, elsepart);
          e2 = preprocessRec(e2, cache);
          break;
        }
      }

      if (d_convertToDiff != "" && d_theoryArith->isAtomicArithFormula(e2)) {
        Expr e3 = d_theoryArith->rewriteToDiff(e2);
        if (e2 != e3) {
          DebugAssert(e3 == d_theoryArith->rewriteToDiff(e3), "Expected idempotent rewrite");
          e2 = preprocessRec(e3, cache);
        }
        break;
      }

      break;
    default:
      if (d_convertToBV && isInt(e2.getType())) {
        FatalAssert(e2.isVar(), "Cannot convert non-variables yet");
        e2 = d_theoryCore->newVar(e2.getName()+"_bv", d_theoryBitvector->newBitvectorType(d_convertToBV));
      }

      break;
  }

  // Figure out language
  switch (e2.getKind()) {
    case RATIONAL_EXPR:
      r = e2.getRational();
      if (r.isInteger()) {
        d_intConstUsed = true;
      }
      else {
        d_realUsed = true;
      }
      if (d_langUsed == NOT_USED) d_langUsed = TERMS_ONLY;
      break;
    case IS_INTEGER:
      d_unknown = true;
      break;
    case PLUS: {
      if (e2.arity() == 2) {
        int nonconst = 0, isconst = 0;
        Expr::iterator i = e2.begin(), iend = e2.end();
        for(; i!=iend; ++i) {
          if ((*i).isRational()) {
            if ((*i).getRational() <= 0) {
              d_UFIDL_ok = false;
              break;
            }
            else ++isconst;
          }
          else ++nonconst;
        }
        if (nonconst > 1 || isconst > 1)
          d_UFIDL_ok = false;
      }
      else d_UFIDL_ok = false;
      if (d_langUsed == NOT_USED) d_langUsed = TERMS_ONLY;
      break;
    }
    case MINUS:
      if (!e2[1].isRational() || e2[1].getRational() <= 0) {
        d_UFIDL_ok = false;
      }
      if (d_langUsed == NOT_USED) d_langUsed = TERMS_ONLY;
      break;
    case UMINUS:
      d_UFIDL_ok = false;
      if (d_langUsed == NOT_USED) d_langUsed = TERMS_ONLY;
      break;
    case MULT: {
      d_UFIDL_ok = false;
      if (d_langUsed == NONLINEAR) break;
      d_langUsed = LINEAR;
      bool nonconst = false;
      for (int i=0; i!=e2.arity(); ++i) {
        if (e2[i].isRational()) continue;
        if (nonconst) {
          d_langUsed = NONLINEAR;
          break;
        }
        nonconst = true;
      }
      break;
    }
    case POW:
    case DIVIDE:
      d_unknown = true;
      break;

    case EQ:
      if (d_theoryArith->getBaseType(e2[0]) != d_theoryArith->realType() ||
          (e2[0].getType() == d_theoryArith->intType() && d_theoryCore->getFlags()["convert2array"].getBool()))
        break;
    case LT:
    case GT:
    case LE:
    case GE:
      if (d_langUsed >= LINEAR) break;
      if (!d_theoryArith->isAtomicArithFormula(e2)) {
        d_langUsed = LINEAR;
        break;
      }
      if (e2[0].getKind() == MINUS &&
          d_theoryArith->isLeaf(e2[0][0]) &&
          d_theoryArith->isLeaf(e2[0][1]) &&
          e2[1].isRational()) {
        d_langUsed = DIFF_ONLY;
        break;
      }
      if (d_theoryArith->isLeaf(e2[0]) &&
          d_theoryArith->isLeaf(e2[1])) {
        d_langUsed = DIFF_ONLY;
        break;
      }
      d_langUsed = LINEAR;
      break;
    default:
      break;
  }

  switch (e2.getKind()) {
    case EQ:
    case NOT:
      break;
    case UCONST:
      if (e2.arity() == 0) break;
    default:
      d_theoryCore->theoryOf(e2)->setUsed();
  }

  cache[e] = e2;
  return e2;
}


Expr Translator::preprocess(const Expr& e, ExprMap<Expr>& cache)
{
  Expr result;
  try {
    result = preprocessRec(e, cache);
  } catch (SmtlibException& ex) {
    cerr << "Error while processing the formula:\n"
         << e.toString() << endl;
    throw ex;
  }
  return result;
}


Expr Translator::preprocess2Rec(const Expr& e, ExprMap<Expr>& cache, Type desiredType)
{
  ExprMap<Expr>::iterator i(cache.find(e));
  if(i != cache.end()) {
    if ((desiredType.isNull() &&
         (*i).second.getType() != d_theoryArith->realType()) ||
        (*i).second.getType() == desiredType) {
      return (*i).second;
    }
  }

  if (e.isClosure()) {
    Expr newBody = preprocess2Rec(e.getBody(), cache, Type());
    Expr e2(e);
    if (newBody != e.getBody()) {
      e2 = d_em->newClosureExpr(e.getKind(), e.getVars(), newBody);
    }
    cache[e] = e2;
    return e2;
  }

  bool forceReal = false;
  if (desiredType == d_theoryArith->intType() &&
      e.getType() != d_theoryArith->intType()) {
    d_unknown = true;
//     throw SmtlibException("Unable to separate int and real "+
//                           e.getType().getExpr().toString()+
//                           "\n\nwhile processing the term:\n"+
//                           e.toString(PRESENTATION_LANG));
  }

  // Try to force type-compliance
  switch (e.getKind()) {
    case EQ:
    case LT:
    case GT:
    case LE:
    case GE:
      if (e[0].getType() != e[1].getType()) {
        if (e[0].getType() != d_theoryArith->intType() &&
            e[1].getType() != d_theoryArith->intType()) {
          d_unknown = true;
          throw SmtlibException("Expected each side to be REAL or INT, but we got lhs: "+
                                e[0].getType().getExpr().toString()+" and rhs: "+
                                e[1].getType().getExpr().toString()+
                                "\n\nwhile processing the term:\n"+
                                e.toString());
        }
        forceReal = true;
        break;
      case ITE:
      case UMINUS:
      case PLUS:
      case MINUS:
      case MULT:
        if (desiredType == d_theoryArith->realType())
          forceReal = true;
        break;
      case DIVIDE:
        forceReal = true;
        break;
      default:
        break;
    }
  }

  Expr e2(e);
  vector<Expr> children;
  bool diff = false;

  Type funType;
  if (e.isApply()) {
    funType = e.getOpExpr().getType();
    if (funType.getExpr().getKind() == ANY_TYPE) funType = Type();
  }

  for(int k = 0; k < e.arity(); ++k) {
    Type t;
    if (forceReal && e[k].getType() == d_theoryArith->intType())
      t = d_theoryArith->realType();
    else if (!funType.isNull()) t = funType[k];
    // Recursively preprocess the kids
    Expr child = preprocess2Rec(e[k], cache, t);
    if (child != e[k]) diff = true;
    children.push_back(child);
  }
  if (diff) {
    e2 = Expr(e.getOp(), children);
  }
  else if (e2.getKind() == RATIONAL_EXPR) {
    if (e2.getType() == d_theoryArith->realType() ||
        (e2.getType() == d_theoryArith->intType() &&
         desiredType == d_theoryArith->realType()))
      e2 = Expr(REAL_CONST, e2);
  }
  if (!desiredType.isNull() && e2.getType() != desiredType) {
    d_unknown = true;
    throw SmtlibException("Type error: expected "+
                          desiredType.getExpr().toString()+
                          " but instead got "+
                          e2.getType().getExpr().toString()+
                          "\n\nwhile processing term:\n"+
                          e.toString());
  }

  cache[e] = e2;
  return e2;
}


Expr Translator::preprocess2(const Expr& e, ExprMap<Expr>& cache)
{
  Expr result;
  try {
    result = preprocess2Rec(e, cache, Type());
  } catch (SmtlibException& ex) {
    cerr << "Error while processing the formula:\n"
         << e.toString() << endl;
    throw ex;
  }
  return result;
}




bool Translator::containsArray(const Expr& e)
{
  if (e.getKind() == ARRAY) return true;
  Expr::iterator i = e.begin(), iend=e.end();
  for(; i!=iend; ++i) if (containsArray(*i)) return true;
  return false;
}


Translator::Translator(ExprManager* em,
                       const bool& translate,
                       const bool& real2int,
                       const bool& convertArith,
                       const string& convertToDiff,
                       bool iteLiftArith,
                       const string& expResult,
                       const string& category,
                       bool convertArray,
                       bool combineAssump,
                       int convertToBV)
  : d_em(em), d_translate(translate),
    d_real2int(real2int),
    d_convertArith(convertArith),
    d_convertToDiff(convertToDiff),
    d_iteLiftArith(iteLiftArith),
    d_expResult(expResult),
    d_category(category),
    d_convertArray(convertArray),
    d_combineAssump(combineAssump),
    d_dump(false), d_dumpFileOpen(false),
    d_intIntArray(false), d_intRealArray(false), d_intIntRealArray(false),
    d_ax(false), d_unknown(false),
    d_realUsed(false), d_intUsed(false), d_intConstUsed(false),
    d_langUsed(NOT_USED), d_UFIDL_ok(true), d_arithUsed(false),
    d_zeroVar(NULL), d_convertToBV(convertToBV)
{
  d_arrayConvertMap = new map<string, Type>;
}


Translator::~Translator()
{
  delete d_arrayConvertMap;
}


bool Translator::start(const string& dumpFile)
{
  if (d_translate && (d_em->getOutputLang() == SMTLIB_LANG)) {
    d_dump = true;
    if (dumpFile == "") {
      d_osdump = &cout;
    }
    else {
      d_osdumpFile.open(dumpFile.c_str());
      if(!d_osdumpFile)
        throw Exception("cannot open a log file: "+dumpFile);
      else {
        d_dumpFileOpen = true;
        d_osdump = &d_osdumpFile;
      }
    }

    string tmpName;
    string::size_type pos = dumpFile.rfind("/");
    if (pos == string::npos) {
      tmpName = "README";
    }
    else {
      tmpName = dumpFile.substr(0,pos+1) + "README";
    }
    d_tmpFile.open(tmpName.c_str());

      *d_osdump << "(benchmark " << fileToSMTLIBIdentifier(dumpFile) << endl
          << "  :source {" << endl;

      char c;
      if (d_tmpFile.is_open()) {
        d_tmpFile.get(c);
        while (!d_tmpFile.eof()) {
          if ( c == '{' || c == '}' ) {
            *d_osdump << '\\';
          }
          *d_osdump << c;
          d_tmpFile.get(c);
        }
      }
      else {
        *d_osdump << "Source unknown";
      }
      *d_osdump << endl;

      *d_osdump << "}" << endl;

    d_tmpFile.close();
  }
  else if (d_translate && d_em->getOutputLang() == SPASS_LANG) {
    d_dump = true;
    if (dumpFile == "") {
      d_osdump = &cout;
    }
    else {
      d_osdumpFile.open(dumpFile.c_str());
      if(!d_osdumpFile)
        throw Exception("cannot open a log file: "+dumpFile);
      else {
        d_dumpFileOpen = true;
        d_osdump = &d_osdumpFile;
      }
    }

    *d_osdump << "begin_problem(Unknown). " << endl;
    *d_osdump << endl;
    *d_osdump << "list_of_descriptions. " << endl;
    *d_osdump << "name({* " <<  fileToSMTLIBIdentifier(dumpFile) << " *}). " << endl;
    *d_osdump << "author({* CVC2SPASS translator *})." << endl;
    //end of SPASS
  }
  else {
    if (dumpFile == "") {
      if (d_translate) {
        d_osdump = &cout;
        d_dump = true;
      }
    }
    else {
      d_osdumpFile.open(dumpFile.c_str());
      if(!d_osdumpFile)
        throw Exception("cannot open a log file: "+dumpFile);
      else {
        d_dump = true;
        d_dumpFileOpen = true;
        d_osdump = &d_osdumpFile;
      }
    }
  }
  return d_dump;
}


void Translator::dump(const Expr& e, bool dumpOnly)
{
  DebugAssert(d_dump, "dump called unexpectedly");
  if (!dumpOnly || !d_translate) {
    if (d_convertArray && e.getKind() == CONST &&
        e.arity() == 2) {
      if (e[1].getKind() == ARRAY) {
        if (containsArray(e[1][0]) ||
            containsArray(e[1][1])) {
          throw Exception("convertArray failed because of nested arrays in"+
                          e[1].toString());
        }
        Expr funType = Expr(ARROW, e[1][0], e[1][1]);
        Expr outExpr = Expr(CONST, e[0], funType);
        d_dumpExprs.push_back(outExpr);
      }
      else if (containsArray(e[1])) {
        throw Exception("convertArray failed becauase of use of arrays in"+
                        e[1].toString());
      }
      else {
        d_dumpExprs.push_back(e);
      }
    }
    else {
      d_dumpExprs.push_back(e);
    }
  }
}


bool Translator::dumpAssertion(const Expr& e)
{
  Expr outExpr = Expr(ASSERT, e);
  d_dumpExprs.push_back(outExpr);
  return d_translate;
}


bool Translator::dumpQuery(const Expr& e)
{
  Expr outExpr = Expr(QUERY, e);
  d_dumpExprs.push_back(outExpr);
  return d_translate;
}


void Translator::dumpQueryResult(QueryResult qres)
{
  if( d_translate && d_em->getOutputLang() == SMTLIB_LANG ) {
    *d_osdump << "  :status ";
    switch( qres ) {
    case UNSATISFIABLE:
      *d_osdump << "unsat" << endl;
      break;
    case SATISFIABLE:
      *d_osdump << "sat" << endl;
      break;
    default:
      *d_osdump << "unknown" << endl;
      break;
    }
  } else if( d_translate && d_em->getOutputLang() == SMTLIB_V2_LANG ) {
    *d_osdump << "(set-info :status ";
    switch( qres ) {
    case UNSATISFIABLE:
      *d_osdump << "unsat";
      break;
    case SATISFIABLE:
      *d_osdump << "sat";
      break;
    default:
      *d_osdump << "unknown";
      break;
    }
    *d_osdump << ")" << endl;
  } else if( d_translate && d_em->getOutputLang() == SPASS_LANG ) {
    *d_osdump << "status(";
    switch( qres ) {
    case UNSATISFIABLE:
      *d_osdump << "unsatisfiable";
      break;
    case SATISFIABLE:
      *d_osdump << "satisfiable";
      break;
    default:
      *d_osdump << "unknown";
      break;
    }
    *d_osdump << ")." << endl;
  }
}


/*
Expr Translator::spassPreprocess(const Expr& e, ExprMap<Expr>& mapping,
                                 vector<Expr>& functions,
                                 vector<Expr>& predicates)
{
  if(e.getKind() == LET) {
    if(e.arity() != 2) {
      throw SmtlibException("Translator::spassPreprocess(): LET with arity != 2 not supported");
    }
    char name[80];
    snprintf(name, sizeof(name), "_cvc3_let%u", mapping.size());
    Expr id(ID, d_em->newStringExpr(name));
    cout << "ENCOUNTERED A LET:" << endl << id << endl;
    mapping.insert(e[0][0], e[0][1]);
    functions.push_back(Expr(CONST, id, e[1].getType().getExpr()));
    return spassPreprocess(e[1], mapping, functions, predicates);
  //} else if(e.getKind() == x) {
  } else if(e.arity() > 0) {
    vector<Expr> args;
    for(int i = 0, iend = e.arity(); i < iend; ++i) {
      args.push_back(spassPreprocess(e[i], mapping, functions, predicates));
    }
    Expr out(e.getOp(), args);
    return out;
  }
  return e;
}
*/


Expr Translator::processType(const Expr& e)
{
  switch (e.getKind()) {
    case TYPEDECL:
      return e;
    case INT:
      if (d_convertToBV) {
        return d_theoryBitvector->newBitvectorType(d_convertToBV).getExpr();
      }
      if (d_theoryCore->getFlags()["convert2array"].getBool()) {
        return d_elementType->getExpr();
      }
      d_intUsed = true;
      break;
    case REAL:
      if (d_real2int) {
        d_intUsed = true;
        return d_theoryArith->intType().getExpr();
      }
      else {
        d_realUsed = true;
      }
      break;
    case SUBRANGE:
      d_unknown = true;
      break;
    case ARRAY:
      if (d_theoryCore->getFlags()["convert2array"].getBool()) {
        d_ax = true;
        return d_arrayType->getExpr();
      }
      if (e[0].getKind() == TYPEDECL) {
        DebugAssert(e[0].arity() == 1, "expected arity 1");
        if (e[0][0].getString() == "Index") {
          if (e[1].getKind() == TYPEDECL) {
            DebugAssert(e[1].arity() == 1, "expected arity 1");
            if (e[1][0].getString() == "Element") {
              d_ax = true;
              break;
            }
          }
        }
      }
      else if (isInt(Type(e[0]))) {
        if (isInt(Type(e[1]))) {
          d_intIntArray = true;
          break;
        }
        else if (isReal(Type(e[1]))) {
          d_intRealArray = true;
          break;
        }
        else if (isArray(Type(e[1])) &&
                 isInt(Type(e[1][0])) &&
                 isReal(Type(e[1][1]))) {
          d_intIntRealArray = true;
          break;
        }
      }
      else if (e[0].getKind() == BITVECTOR &&
               e[1].getKind() == BITVECTOR) {
        break;
      }
      d_unknown = true;
      break;
    default:
      break;
  }
  d_theoryCore->theoryOf(e)->setUsed();
  if (e.arity() == 0) return e;
  bool changed = false;
  vector<Expr> vec;
  for (int i = 0; i < e.arity(); ++i) {
    vec.push_back(processType(e[i]));
    if (vec.back() != e[i]) changed = true;
  }
  if (changed)
    return Expr(e.getOp(), vec);
  return e;
}


void Translator::finish()
{
  if (d_translate) {

    if (d_em->getOutputLang() == SPASS_LANG) {
      *d_osdump << "status(";
      if (d_expResult == "invalid" ||
          d_expResult == "satisfiable" ||
          d_expResult == "sat")
        *d_osdump << "satisfiable";
      else if (d_expResult == "valid" ||
               d_expResult == "unsatisfiable" ||
               d_expResult == "unsat")
        *d_osdump << "unsatisfiable";
      else if (d_expResult != "")
        *d_osdump << "unknown";
      else if (status() == "invalid" ||
               status() == "satisfiable" ||
               status() == "sat")
        *d_osdump << "satisfiable";
      else if (status() == "valid" ||
               status() == "unsatisfiable" ||
               status() == "unsat")
        *d_osdump << "unsatisfiable";
      else *d_osdump << "unknown";
      *d_osdump << ")." << endl;
      *d_osdump << "description({* Unknown *})." << endl;
      *d_osdump << "end_of_list." << endl;

      vector<Expr> functions, predicates, sorts;

      for(vector<Expr>::reverse_iterator i = d_dumpExprs.rbegin(), iend = d_dumpExprs.rend(); i != iend; ++i) {
        Expr e = *i;
        switch(e.getKind()) {
        case TYPE:
          sorts.push_back(e);
          d_dumpExprs.erase(i.base() - 1);
          break;
        case CONST:
          if(e.arity() == 2) {
            if (e[1].getKind() == BOOLEAN ||
                (e[1].getKind() == ARROW && e[1][e[1].arity()-1].getKind() == BOOLEAN)) {
              predicates.push_back(e);
            } else {
              functions.push_back(e);
            }
            d_dumpExprs.erase(i.base() - 1);
          } else {
            throw SmtlibException("Translator::finish: SPASS_LANG: CONST not implemented for arity != 2");
          }
          break;
        case ANNOTATION:
          if (d_theoryCore->getFlags()["trans-skip-difficulty"].getBool() &&
              e[0].getKind() == STRING_EXPR && e[0].getString() == "difficulty") {
            // do nothing; skip the difficulty annotation
          } else {
            *d_osdump << "%% ";
            *d_osdump << e[0];
            if (e.arity() > 1) {
              *d_osdump << ": " << e[1];
            }
          }
          d_dumpExprs.erase(i.base() - 1);
          break;

          /*
        case ASSERT:
        case QUERY: {
          ExprMap<Expr> m;
          *i = Expr(e.getKind(), spassPreprocess(e[0], m, functions, predicates));
          break;
        }
          */

        default:
          //*d_osdump << "DOING NOTHING FOR: " << e << endl;
          break;
        }
      }

      // add some built-ins for the translation
      // only arity matters for SPASS; the real type of _cvc3_ite is Bool -> 'a -> 'a -> 'a
      //Expr cvc3ite(CONST, Expr(ID, d_em->newStringExpr("_cvc3_ite")),
      //Expr(ARROW, vector<Expr>(4, d_theoryArith->intType().getExpr())));
      // only arity matters for SPASS; the real type of _cvc3_xor is
      // Bool -> Bool -> Bool, but we can't represent Bool-arg'ed
      // functions
      Expr cvc3xor(CONST, Expr(ID, d_em->newStringExpr("_cvc3_xor")),
                   Expr(ARROW, vector<Expr>(2, d_theoryArith->intType().getExpr())));
      //functions.push_back(cvc3ite);
      predicates.push_back(cvc3xor);

      *d_osdump << endl;
      *d_osdump << "list_of_symbols." << endl;
      if(!functions.empty()) {
        *d_osdump << "functions[";
        vector<Expr>::reverse_iterator i = functions.rbegin(), iend = functions.rend();
        while(i != iend) {
          Expr e = *i;
          *d_osdump << "(" << e[0][0].getString() << "," << ( e[1].getKind() == ARROW ? e[1].arity()-1 : e[1].arity() ) << ")";
          if(++i != iend) {
            *d_osdump << ",";
          }
        }
        *d_osdump << "]." << endl;
      }
      if(!predicates.empty()) {
        *d_osdump << "predicates[";
        vector<Expr>::reverse_iterator i = predicates.rbegin(), iend = predicates.rend();
        while(i != iend) {
          Expr e = *i;
          *d_osdump << "(" << e[0][0].getString() << "," << e[1].arity() << ")";
          if(++i != iend) {
            *d_osdump << ",";
          }
        }
        *d_osdump << "]." << endl;
      }
      if(!sorts.empty()) {
        *d_osdump << "sorts[";
        vector<Expr>::reverse_iterator i = sorts.rbegin(), iend = sorts.rend();
        while(i != iend) {
          Expr e = *i;
          *d_osdump << e[0][0].getString();
          if(++i != iend) {
            *d_osdump << ",";
          }
        }
        *d_osdump << "]." << endl;
      }
      *d_osdump << "end_of_list." << endl;

      *d_osdump << endl;
      *d_osdump << "list_of_declarations." << endl;
      *d_osdump << "end_of_list." << endl;

      // define an ITE operator for the translation
      *d_osdump << endl;
      *d_osdump << "list_of_formulae(axioms)." << endl;
      *d_osdump << "formula(forall([A,B],equiv(_cvc3_xor(A,B),not(equal(A,B)))))." << endl;
      //*d_osdump << "formula(forall([A,B],equal(_cvc3_ite(\ntrue\n,A,B),A)))." << endl;
      //*d_osdump << "formula(forall([A,B],equal(_cvc3_ite(\nfalse\n,A,B),B)))." << endl;
      *d_osdump << "end_of_list." << endl;

      *d_osdump << endl;
      *d_osdump << "list_of_formulae(conjectures)." << endl;
    }

    if (d_em->getOutputLang() == SMTLIB_LANG) {
      // Print the rest of the preamble for smt-lib benchmarks

      *d_osdump << "  :smt-lib-version 1.2" << endl;

      // Get status from expResult flag
      *d_osdump << "  :status ";
      if (d_expResult == "invalid" ||
          d_expResult == "satisfiable")
        *d_osdump << "sat";
      else if (d_expResult == "valid" ||
               d_expResult == "unsatisfiable")
        *d_osdump << "unsat";
      else if (status() != "") {
        *d_osdump << status();
      }
      else *d_osdump << "unknown";
      *d_osdump << endl;

      // difficulty
      //      *d_osdump << "  :difficulty { unknown }" << endl;

      // category
      if (category() != "") {
        *d_osdump << "  :category { ";
        *d_osdump << category() << " }" << endl;
      }

      // Create types for theory QF_AX if needed
      if (d_theoryCore->getFlags()["convert2array"].getBool()) {
        d_indexType = new Type(d_theoryCore->newTypeExpr("Index"));
        d_elementType = new Type(d_theoryCore->newTypeExpr("Element"));
        d_arrayType = new Type(arrayType(*d_indexType, *d_elementType));
      }
    }

    // Preprocess and compute logic for smt-lib
    bool qf_uf = false;

    if (!d_theoryCore->getFlags()["trans-skip-pp"].getBool())
    {
      ExprMap<Expr> cache;
      // Step 1: preprocess asserts, queries, and types
      vector<Expr>::iterator i = d_dumpExprs.begin(), iend = d_dumpExprs.end();
      for (; i != iend; ++i) {
        Expr e = *i;
        switch (e.getKind()) {
          case ASSERT: {
            Expr e2 = preprocess(e[0], cache);
            if (e[0] == e2) break;
            e2.getType();
            *i = Expr(ASSERT, e2);
            break;
          }
          case QUERY: {
            Expr e2 = preprocess(e[0].negate(), cache);
            if (e[0].negate() == e2) break;
            e2.getType();
            *i = Expr(QUERY, e2.negate());
            break;
          }
          case CONST: {
            DebugAssert(e.arity() == 2, "Expected CONST with arity 2");
            if (d_theoryCore->getFlags()["convert2array"].getBool()) break;
            Expr e2 = processType(e[1]);
            if (e[1] == e2) break;
            if (d_convertToBV) {
              Expr newName = Expr(ID, d_em->newStringExpr(e[0][0].getString()+"_bv"));
              *i = Expr(CONST, newName, e2);
            }
            else {
              *i = Expr(CONST, e[0], e2);
            }
            break;
          }
          default:
            break;
        }
      }
    }

    if (d_zeroVar) {
      d_dumpExprs.insert(d_dumpExprs.begin(),
                         Expr(CONST, Expr(ID, d_em->newStringExpr("cvc3Zero")),
                              processType(d_zeroVar->getType().getExpr())));
    }

    // Type inference over equality
    if (!d_unknown && d_theoryCore->getFlags()["convert2array"].getBool()) {
      bool changed;
      do {
        changed = false;
        unsigned i;
        for (i = 0; i < d_equalities.size(); ++i) {
          if (d_equalities[i][0].getKind() == UCONST &&
              d_arrayConvertMap->find(d_equalities[i][0].getName()) == d_arrayConvertMap->end()) {
            if (d_equalities[i][1].getKind() == READ) {
              changed = true;
              (*d_arrayConvertMap)[d_equalities[i][0].getName()] = *d_elementType;
            }
            else if (d_equalities[i][1].getKind() == UCONST) {
              map<string, Type>::iterator it = d_arrayConvertMap->find(d_equalities[i][1].getName());
              if (it != d_arrayConvertMap->end()) {
                changed = true;
                (*d_arrayConvertMap)[d_equalities[i][0].getName()] = (*it).second;
              }
            }
          }
          else if (d_equalities[i][1].getKind() == UCONST &&
                   d_arrayConvertMap->find(d_equalities[i][1].getName()) == d_arrayConvertMap->end()) {
            if (d_equalities[i][0].getKind() == READ) {
              changed = true;
              (*d_arrayConvertMap)[d_equalities[i][1].getName()] = *d_elementType;
            }
            else if (d_equalities[i][0].getKind() == UCONST) {
              map<string, Type>::iterator it = d_arrayConvertMap->find(d_equalities[i][0].getName());
              if (it != d_arrayConvertMap->end()) {
                changed = true;
                (*d_arrayConvertMap)[d_equalities[i][1].getName()] = (*it).second;
              }
            }
          }
        }
      } while (changed);
    }

    if (d_em->getOutputLang() == SMTLIB_LANG ||
        d_em->getOutputLang() == SMTLIB_V2_LANG) {

      // Step 2: If both int and real are used, try to separate them
      if ((!d_unknown && (d_intUsed && d_realUsed)) || (d_theoryCore->getFlags()["convert2array"].getBool())) {
        ExprMap<Expr> cache;
        vector<Expr>::iterator i = d_dumpExprs.begin(), iend = d_dumpExprs.end();
        for (; i != iend; ++i) {
          Expr e = *i;
          switch (e.getKind()) {
            case ASSERT: {
              if (d_theoryCore->getFlags()["convert2array"].getBool()) break;
              Expr e2 = preprocess2(e[0], cache);
              e2.getType();
              *i = Expr(ASSERT, e2);
              break;
            }
            case QUERY: {
              if (d_theoryCore->getFlags()["convert2array"].getBool()) break;
              Expr e2 = preprocess2(e[0].negate(), cache);
              e2.getType();
              *i = Expr(QUERY, e2.negate());
              break;
            }
            case CONST: {
              if (!d_theoryCore->getFlags()["convert2array"].getBool()) break;
              map<string, Type>::iterator it = d_arrayConvertMap->find(e[0][0].getString());
              if (it != d_arrayConvertMap->end()) {
                *i = Expr(CONST, e[0], (*it).second.getExpr());
              }
              else {
                Expr e2 = processType(e[1]);
                if (e[1] == e2) break;
                *i = Expr(CONST, e[0], e2);
              }
              break;
            }
            default:
              break;
          }
        }
      }
      d_arithUsed = d_realUsed || d_intUsed || d_intConstUsed || (d_langUsed != NOT_USED);

      // Step 3: Go through the cases and figure out the right logic
      if (d_em->getOutputLang() == SMTLIB_LANG) {
        *d_osdump << "  :logic ";
      }
      else {// d_em->getOutputLang() == SMTLIB_V2_LANG
        *d_osdump << "(set-logic ";
      }
      if (d_unknown ||
          d_theoryRecords->theoryUsed() ||
          d_theorySimulate->theoryUsed() ||
          d_theoryDatatype->theoryUsed()) {
        *d_osdump << "unknown";
      }
      else {
        if ((d_ax && (d_arithUsed ||
                      d_theoryBitvector->theoryUsed() ||
                      d_theoryUF->theoryUsed())) ||
            (d_intIntArray && d_realUsed) ||
            (d_arithUsed && d_theoryBitvector->theoryUsed())) {
          *d_osdump << "unknown";
        }
        else {
          bool QF = false;
          bool A = false;
          bool UF = false;
          bool promote = d_theoryCore->getFlags()["promote"].getBool();

          if (!d_theoryQuant->theoryUsed()) {
            QF = true;
            *d_osdump << "QF_";
          }

          if (d_theoryArray->theoryUsed() && !d_convertArray) {
            A = true;
            *d_osdump << "A";
          }

          // Promote undefined subset logics
          else if (promote &&
                   !QF &&
                   !(d_arithUsed && d_realUsed && !d_intUsed && d_langUsed <= LINEAR) &&
                   !(d_arithUsed && !d_realUsed && d_intUsed && d_langUsed == NONLINEAR)) {
            A = true;
            *d_osdump << "A";
          }

          if (d_theoryUF->theoryUsed() ||
              (d_theoryArray->theoryUsed() && d_convertArray)) {
            UF = true;
            *d_osdump << "UF";
          }

          // Promote undefined subset logics
            else if (promote &&
                     !QF &&
                     !(d_arithUsed && d_realUsed && !d_intUsed && d_langUsed <= LINEAR)) {
              UF = true;
              *d_osdump << "UF";
            }

          if (d_arithUsed) {
            if (d_intUsed && d_realUsed) {
              if (d_langUsed < NONLINEAR) {
                *d_osdump << "LIRA";
              }
              else *d_osdump << "NIRA";
            }
            else if (d_realUsed) {
              if (d_langUsed <= DIFF_ONLY) {

                // Promote undefined subset logics
                 if (promote && !QF) {
                   *d_osdump << "LRA";
                 } else

                  *d_osdump << "RDL";
              }
              else if (d_langUsed <= LINEAR) {
                  *d_osdump << "LRA";
              }
              else {

                // Promote undefined subset logics
                 if (promote && !QF) {
                   *d_osdump << "NIRA";
                 } else

                  *d_osdump << "NRA";
              }
            }
            else {
              if (QF && !A && UF && d_langUsed <= LINEAR) {
                if (!d_realUsed && d_langUsed <= LINEAR && d_UFIDL_ok) {
                  *d_osdump << "IDL";
                }
                else {
                  *d_osdump << "LIA";
                }
              }
              else if (d_langUsed <= DIFF_ONLY) {

                // Promote undefined subset logics
                if (promote && !QF) {
                  *d_osdump << "LIA";
                }
                else if (A) {
                  if (!UF) {
                    UF = true;
                    *d_osdump << "UF";
                  }
                  *d_osdump << "LIA";
                } else

                  *d_osdump << "IDL";
              }
              else if (d_langUsed <= LINEAR) {

                // Promote undefined subset logics
                 if (promote && QF && A && !UF) {
                   UF = true;
                   *d_osdump << "UF";
                 }

                if (QF && !A && (!d_realUsed && d_langUsed <= LINEAR && d_UFIDL_ok)) {
                  *d_osdump << "UFIDL";
                }
                else {
                  *d_osdump << "LIA";
                }
              }
              else {
                  *d_osdump << "NIA";
              }
            }
          }
          else if (d_theoryBitvector->theoryUsed()) {

            // Promote undefined subset logics
            if (promote && A && QF && !UF) {
              UF = true;
              *d_osdump << "UF";
            }

            *d_osdump << "BV";
          }
          else {

            if (d_ax) {
              *d_osdump << "X";
            }

            // Promote undefined subset logics
            else if (promote && (!QF || (A && UF))) {
              *d_osdump << "LIA";
            } else {

              // Default logic
              if (!A && !UF) {
                UF = true;
                *d_osdump << "UF";
              }
              qf_uf = QF && UF && (!A);
            }
          }
        }
      }
      if (d_em->getOutputLang() == SMTLIB_V2_LANG) {
        *d_osdump << ")";
      }
      *d_osdump << endl;
    }

    if (d_em->getOutputLang() == SMTLIB_V2_LANG) {
      // Print the rest of the set-info commands

      if (source() != "") {
        *d_osdump << "(set-info :source "
                  << quoteAnnotation(source())
                  << ')' << endl;
      }

      *d_osdump << "(set-info :smt-lib-version 2.0)" << endl;

      // Remove leading and trailing spaces from category
      string c = category();
      size_t i = 0, j = c.size();
      while (c[i] == ' ') {
        ++i; --j;
      }
      while (j > 0 && c[i+j-1] == ' ') --j;
      if (j > 0) {
        c = c.substr(i,j);
        *d_osdump << "(set-info :category \"" << c << "\")" << endl;
      }
      
//       if (benchName() != "") {
//         *d_osdump << "(set-info :name \"" << benchName() << "\")" << endl;
//       }

      // Get status from expResult flag
      *d_osdump << "(set-info :status ";
      if (d_expResult == "invalid" ||
          d_expResult == "satisfiable")
        *d_osdump << "sat";
      else if (d_expResult == "valid" ||
               d_expResult == "unsatisfiable")
        *d_osdump << "unsat";
      else if (status() != "") {
        *d_osdump << status();
      }
      else *d_osdump << "unknown";
      *d_osdump << ")" << endl;

      // Create types for theory QF_AX if needed
      if (d_theoryCore->getFlags()["convert2array"].getBool()) {
        d_indexType = new Type(d_theoryCore->newTypeExpr("Index"));
        d_elementType = new Type(d_theoryCore->newTypeExpr("Element"));
        d_arrayType = new Type(arrayType(*d_indexType, *d_elementType));
      }
    }


    // Dump the actual expressions
    vector<Expr>::const_iterator i = d_dumpExprs.begin(), iend = d_dumpExprs.end();
    vector<Expr> assumps;
    bool skip_diff = d_theoryCore->getFlags()["trans-skip-difficulty"].getBool();
    for (; i != iend; ++i) {
      Expr e = *i;
      switch (e.getKind()) {
        case ASSERT: {
          if (d_combineAssump) {
            assumps.push_back(e[0]);
          }
          else {
            *d_osdump << e << endl;
          }
          break;
        }
        case QUERY: {
          if (!assumps.empty()) {
            assumps.push_back(e[0].negate());
            e = Expr(QUERY, Expr(NOT, Expr(AND, assumps)));
          }
          *d_osdump << e << endl;
          break;
        }
        default:
          if (d_em->getOutputLang() == SMTLIB_LANG &&
              qf_uf && e.getKind() == TYPE && e[0].getKind() == RAW_LIST &&
              e[0][0].getKind() == ID && e[0][0][0].getKind() == STRING_EXPR &&
              e[0][0][0].getString() == "U")
            break;
          if (skip_diff && e.getKind() == ANNOTATION && e[0].getKind() == STRING_EXPR &&
              e[0].getString() == "difficulty")
            break;
          *d_osdump << e << endl;
          break;
      }
    }
    if (d_em->getOutputLang() == SMTLIB_LANG) {
      *d_osdump << ")" << endl;
    }
    else if (d_em->getOutputLang() == SMTLIB_V2_LANG) {
      *d_osdump << "(exit)" << endl;
    }

    if (d_em->getOutputLang() == SPASS_LANG) {
      *d_osdump << "end_of_list." << endl;
      *d_osdump << endl;
      *d_osdump << "end_problem." << endl;
    }
  }

  if (d_dumpFileOpen) d_osdumpFile.close();
  if (d_zeroVar) delete d_zeroVar;
}


const string Translator::fixConstName(const string& s)
{
  if (d_em->getOutputLang() == SMTLIB_LANG) {
    if (s[0] == '_') {
      return "smt"+s;
    }
  }
  return s;
}


const string Translator::escapeSymbol(const string& s)
{
  if (d_em->getOutputLang() == SMTLIB_V2_LANG) {
    if (s.length() == 0 || isdigit(s[0]))
      return "|" + s + "|";
    // This is the legal set of SMTLIB v2 symbol characters from page
    // 20 of the SMT-LIB v2.0 spec.  If any character in the symbol
    // string falls outside this set, the symbol must be |-delimited.
    if(s.find_first_not_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789~!@$%^&*_-+=<>.?/") != string::npos)
      return "|" + s + "|";
  }
  return s;
}

const string Translator::quoteAnnotation(const string& s)
{
  if(s.find('|') == string::npos) {
    return "|" + s + "|";
  } else {
    stringstream sb;
    sb << '"';
    for(string::const_iterator i = s.begin(); i != s.end(); ++i) {
      char c = *i;
      if(c == '"')
        sb << "\\\"";
      else
        sb << *i;
    }
    sb << '"';
    return sb.str();
  }
}


bool Translator::printArrayExpr(ExprStream& os, const Expr& e)
{
  if (e.getKind() == ARRAY) {
    if (d_convertArray) {
      os << Expr(ARROW, e[0], e[1]);
      return true;
    }
    if (d_em->getOutputLang() == SMTLIB_V2_LANG) {
      DebugAssert( e.arity() == 2, "expected arity 2");
      os << push << "(Array" << space << nodag << e[0] << space << nodag << e[1] << ")" << pop;
      return true;
    }
    if (d_em->getOutputLang() != SMTLIB_LANG) return false;
    if (e[0].getKind() == TYPEDECL) {
      DebugAssert(e[0].arity() == 1, "expected arity 1");
      if (e[0][0].getString() == "Index") {
        if (e[1].getKind() == TYPEDECL) {
          DebugAssert(e[1].arity() == 1, "expected arity 1");
          if (e[1][0].getString() == "Element") {
            os << "Array";
            return true;
          }
        }
      }
    }
    else if (isInt(Type(e[0]))) {
      if (isInt(Type(e[1]))) {
        d_intIntArray = true;
        os << "Array";
        return true;
      }
      else if (isReal(Type(e[1]))) {
        d_intRealArray = true;
        os << "Array1";
        return true;
      }
      else if (isArray(Type(e[1])) &&
               isInt(Type(e[1][0])) &&
               isReal(Type(e[1][1]))) {
        d_intIntRealArray = true;
        os << "Array2";
        return true;
      }
    }
    else if (e[0].getKind() == BITVECTOR &&
             e[1].getKind() == BITVECTOR) {
      os << "Array[";
      os << d_theoryBitvector->getBitvectorTypeParam(Type(e[0]));
      os << ":";
      os << d_theoryBitvector->getBitvectorTypeParam(Type(e[1]));
      os << "]";
      return true;
    }
    os << "UnknownArray";
    d_unknown = true;
    return true;
  }

  switch (e.getKind()) {
    case READ:
      if (d_convertArray) {
        if (e[0].getKind() == UCONST) {
          os << Expr(d_em->newSymbolExpr(e[0].getName(), UFUNC).mkOp(), e[1]);
          return true;
        }
        else if (e[0].getKind() == WRITE) {
          throw Exception("READ of WRITE not implemented yet for convertArray");
        }
        else {
          throw Exception("Unexpected case for convertArray");
        }
      }
      break;
    case WRITE:
      if (d_convertArray) {
        throw Exception("WRITE expression encountered while attempting "
                        "to convert arrays to uninterpreted functions");
      }
      break;
    case ARRAY_LITERAL:
      if (d_convertArray) {
        throw Exception("ARRAY_LITERAL expression encountered while attempting"
                        " to convert arrays to uninterpreted functions");
      }
      break;
    default:
      throw Exception("Unexpected case in printArrayExpr");
      break;
  }
  return false;
}


Expr Translator::zeroVar()
{
  if (!d_zeroVar) {
    d_zeroVar = new Expr();
    if (d_convertToDiff == "int") {
      *d_zeroVar = d_theoryCore->newVar("cvc3Zero", d_theoryArith->intType().getExpr());
    }
    else if (d_convertToDiff == "real") {
      *d_zeroVar = d_theoryCore->newVar("cvc3Zero", d_theoryArith->realType().getExpr());
    }
  }
  return *d_zeroVar;
}
