/*****************************************************************************/
/*!
 * \file expr_stream.cpp
 * 
 * Author: Sergey Berezin
 * 
 * Created: Mon Jun 16 13:57:29 2003
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

#include "pretty_printer.h"
#include "expr_stream.h"
#include "theory_core.h"

using namespace std;

namespace CVC3 {

  ExprStream::ExprStream(ExprManager *em)
    : d_em(em), d_os(&cout), d_depth(em->printDepth()), d_currDepth(0),
      d_lang(em->getOutputLang()),
      d_indent(em->withIndentation()), d_col(em->indent()),
      d_lineWidth(em->lineWidth()), d_indentReg(0), d_beginningOfLine(false),
      d_dag(em->dagPrinting()), d_dagBuilt(false), d_idCounter(0),
      d_nodag(false) {
    d_indentStack.push_back(d_em->indent());
    d_indentLast = d_indentStack.size();
    d_dagPtr.push_back(0);
    d_lastDagSize=d_dagPtr.size();
  }

  //! Generating unique names in DAG expr
  string ExprStream::newName() {
    ostringstream name;
    name << "v_" << d_idCounter++;
    return name.str();
  }

  static bool isTrivialExpr(const Expr& e) {
    return (e.arity()==0 && !e.isClosure());
  }

  //! Traverse the Expr, collect shared subexpressions in d_dagMap
  void ExprStream::collectShared(const Expr& e, ExprMap<bool>& cache) {
    // If seen before, and it's not something trivial, add to d_dagMap
    if(!isTrivialExpr(e) && cache.count(e) > 0) {
      if(d_dagMap.count(e) == 0) {
	string s(newName());
        if (d_lang == SMTLIB_LANG) {
          Type type(e.getType());
          if (type.isBool()) {
            s = "$" + s;
          }
          else {
            s = "?" + s;
          }
        }
        else if (d_lang == SMTLIB_V2_LANG) {
          s = "?" + s;
        }
        if (d_lang == TPTP_LANG) {
	  
	  s = to_upper( s);
        }

	d_dagMap[e] = s;
	d_newDagMap[e] = s;
	d_dagStack.push_back(e);
      }
      return;
    }
    cache[e] = true;
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
      collectShared(*i, cache);
    d_dagBuilt = true;
  }

  //! Wrap e into the top-level LET ... IN header from the dagMap
  /*! 
   * We rely on the fact that d_dagMap is ordered by the Expr creation
   * order, so earlier expressions cannot depend on later ones.
   */
  Expr ExprStream::addLetHeader(const Expr& e) {
    ExprManager* em = e.getEM();
    if(d_newDagMap.size() == 0) return e;
    vector<Expr> decls;
    for(ExprMap<string>::iterator i=d_newDagMap.begin(),
	  iend=d_newDagMap.end(); i!=iend; ++i) {
      Expr var(em->newVarExpr((*i).second));
      if(((*i).first).isType())
	decls.push_back(Expr(LETDECL, var, em->newLeafExpr(TYPE),
                             (*i).first));
      else
	decls.push_back(Expr(LETDECL, var, (*i).first));
    }
    d_newDagMap.clear();
    return Expr(LET, Expr(LETDECLS, decls), e);
  }

  void ExprStream::popIndent() {
    DebugAssert(d_indentStack.size() > 0
		&& d_indentStack.size() > d_indentLast,
		"ExprStream::popIndent(): popped too much: "
		"stack size = "+int2string(d_indentStack.size())
		+", indentLast = "+int2string(d_indentLast));
    if(d_indentStack.size() > 0 && d_indentStack.size() > d_indentLast)
      d_indentStack.pop_back();
  }

  //! Reset indentation to what it was at this level
  void ExprStream::resetIndent() {
    while(d_indentStack.size() > d_indentLast)
      d_indentStack.pop_back();
  }


  void ExprStream::pushDag() {
    d_dagBuilt = false;
    d_dagPtr.push_back(d_dagStack.size());
  }

  void ExprStream::popDag() {
    DebugAssert(d_dagPtr.size() > d_lastDagSize,
		"ExprStream::popDag: popping more than pushed");
    DebugAssert(d_lastDagSize > 0, "ExprStream::popDag: this cannot happen!");
    if(d_dagPtr.size() > d_lastDagSize) {
      size_t size(d_dagPtr.back());
      d_dagPtr.pop_back();
      while(d_dagStack.size() > size) {
	d_dagMap.erase(d_dagStack.back());
	d_dagStack.pop_back();
      }
      d_newDagMap.clear();
    }
  }

  void ExprStream::resetDag() {
    while(d_dagPtr.size() > d_lastDagSize) popDag();
  }

  /*! \defgroup ExprStream_Op Overloaded operator<< 
   * \ingroup PrettyPrinting
   * @{
   */
  //! Use manipulators which are functions over ExprStream&
  ExprStream& operator<<(ExprStream& os,
			 ExprStream& (*manip)(ExprStream&)) {
    return (*manip)(os);
  }

  //! Print Expr
  ExprStream& operator<<(ExprStream& os, const Expr& e) {
    //os << "Printing in expr_stream";
    // If the max print depth is reached, print "..."
    if(os.d_depth >= 0 && os.d_currDepth > os.d_depth) return os << "...";
    Expr e2(e);
    // Don't LET-ify commands like ASSERT, QUERY, TRANSFORM
    switch(e.getKind()) {
    case QUERY:
    case ASSERT:
    case RESTART:
    case TRANSFORM:
    case TYPE:
    case CONST:
      os.d_nodag = true;
      break;
    default: break;
    }
    // Check cache for DAG printing
    if(os.d_dag && !os.d_nodag &&
       os.d_lang != SPASS_LANG) { // SPASS doesn't support LET
      if(os.d_dagBuilt) {
	ExprMap<string>::iterator i(os.d_dagMap.find(e));
	if(i != os.d_dagMap.end()) {
	  ostringstream ss;
	  ss << (*i).second;
	  return os << ss.str();
	}
      } else {
	// We are at the top level; build dagMap and print LET header
	ExprMap<bool> cache;
	os.collectShared(e, cache);
	e2 = os.addLetHeader(e);
      }
    }
    os.d_nodag=false;

    // Increase the depth before the (possibly) recursive call
    os.d_currDepth++;
    // Save the indentation stack position and register
    int indentLast = os.d_indentLast;
    int reg = os.d_indentReg;
    size_t lastDagSize = os.d_lastDagSize;

    os.d_indentLast = os.d_indentStack.size();
    os.d_lastDagSize = os.d_dagPtr.size();

    PrettyPrinter* pp = os.d_em->getPrinter();
    // If no pretty-printer, or the language is AST, print the AST
    if(pp == NULL || os.d_lang == AST_LANG) e2.printAST(os);
    // Otherwise simply call the pretty-printer
    else pp->print(os, e2);
    // Restore the depth after the (possibly) recursive call
    os.d_currDepth--;

    // Restore the indentation stack and register
    os.resetIndent();
    os.resetDag();
    os.d_indentLast = indentLast;
    os.d_indentReg = reg;
    os.d_lastDagSize = lastDagSize;
    return os;
  }

  //! Print Type
  ExprStream& operator<<(ExprStream& os, const Type& t) {
    return os << t.getExpr();
  }


  //! Print string
  /*! This is where all the indentation is happening.

  The algorithm for determining whether to go to the next line is the
  following:
  
  - If the new d_col does not exceed d_lineWidth/2 or current
    indentation, don't bother.
  
  - If the difference between the new d_col and the current
    indentation is less than d_lineWidth/4, don't bother either, so
    that we don't get lots of very short lines clumped to the right
    side.

  - Similarly, if the difference between the old d_col and the current
    indentation is less than d_lineWidth/6, keep the same line.
    Otherwise, for long atomic strings, we may get useless line breaks.
  
  - Otherwise, go to the next line.
  */
  ExprStream& operator<<(ExprStream& os, const string& s) {
    // Save the old position
    int oldCol(os.d_col);
    // The new position after printing s
    os.d_col += s.size();
    if(os.d_indent) {
      // Current indentation position
      int n(os.d_indentStack.size()? os.d_indentStack.back() : 0);
      // See if we need to go to the next line before printing.
      if(2*os.d_col > os.d_lineWidth && 4*(os.d_col - n) > os.d_lineWidth
	 && 6*(oldCol - n) > os.d_lineWidth) {
	os << endl;
	// Recompute the new column
	os.d_col += s.size();
      }
    }
    *os.d_os << s;
    os.d_beginningOfLine = false;
    return os;
  }

  //! Print char* string
  ExprStream& operator<<(ExprStream& os, const char* s) {
    return os << string(s);
  }

  //! Print Rational
  ExprStream& operator<<(ExprStream& os, const Rational& r) {
    ostringstream ss;
    ss << r;
    return os << ss.str();
  }

  //! Print int
  ExprStream& operator<<(ExprStream& os, int i) {
    ostringstream ss;
    ss << i;
    return os << ss.str();
  }
  /*! @} */ // End of group ExprStream_Op

  /*! \defgroup ExprStream_Manip Manipulators 
   * \ingroup PrettyPrinting
   * @{
   */

  //! Set the indentation to the current position
  ExprStream& push(ExprStream& os) { os.pushIndent(); return os; }

  //! Restore the indentation
  ExprStream& pop(ExprStream& os) { os.popIndent(); return os; }
  //! Remember the current indentation and pop to the previous position
  /*! There is only one register to save the previous position.  If
    you use popSave() more than once, only the latest position can be
    restored with pushRestore(). */
  ExprStream& popSave(ExprStream& os) {
    os.d_indentReg = os.d_indentStack.size() ? os.d_indentStack.back() : 0;
    os.popIndent();
    return os;
  }
  //! Set the indentation to the position saved by popSave()
  /*! There is only one register to save the previous position.  Using
    pushRestore() several times will set intendation to the same
    position. */
  ExprStream& pushRestore(ExprStream& os) {
    os.pushIndent(os.d_indentReg);
    return os;
  }
  //! Reset the indentation to the default at this level
  ExprStream& reset(ExprStream& os) { os.resetIndent(); return os; }
  //! Insert a single white space separator
  /*! It is preferred to use 'space' rather than a string of spaces
    (" ") because ExprStream needs to delete extra white space if it
    decides to end the line.  If you use strings for spaces, you'll
    mess up the indentation. */
  ExprStream& space(ExprStream& os) {
    // Prevent " " to carry to the next line
    if(!os.d_beginningOfLine) os << push << " " << pop;
    return os;
  }

  ExprStream& nodag(ExprStream& os) {
    os.d_nodag = true;
    return os;
  }

  ExprStream& pushdag(ExprStream& os) { os.pushDag(); return os; }

  ExprStream& popdag(ExprStream& os) { os.popDag(); return os; }

  /*! @} */ // End of group ExprStream_Manip

} // End of namespace CVC3

namespace std {

  //! Print the end-of-line
  /*! 
   * The new line will not necessarily start at column 0 because of
   * indentation.
   * \ingroup ExprStream_Manip 
   */
  CVC3::ExprStream& endl(CVC3::ExprStream& os) {
    if(os.d_indent) {
      // Current indentation
      int n(os.d_indentStack.size()? os.d_indentStack.back() : 0);
      // Create a string of n white spaces
      string spaces(n, ' ');
      (*os.d_os) << endl << spaces;
      os.d_col = n;
    } else {
      (*os.d_os) << endl;
      os.d_col = 0;
    }
    os.d_beginningOfLine = true;
    return os;
  }
}
