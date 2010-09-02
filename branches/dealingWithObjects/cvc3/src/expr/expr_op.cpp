/*****************************************************************************/
/*!
 * \file expr_op.cpp
 * 
 * Author: Sergey Berezin
 * 
 * Created: Fri Feb  7 15:29:42 2003
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

#include "expr_op.h"

using namespace std;

namespace CVC3 {

Op::Op(ExprManager* em, const Op& op) : d_kind(op.d_kind), d_expr() {
  if (!op.d_expr.isNull()) d_expr = em->rebuild(op.d_expr);
}

Op& Op::operator=(const Op& op) {
  if(&op == this) return *this; // Self-assignment
  d_kind = op.d_kind;
  d_expr = op.d_expr;
  return *this;
}

string Op::toString() const {
  ostringstream ss;
  ss << *this;
  return ss.str();
}

} // end of namespace CVC3
