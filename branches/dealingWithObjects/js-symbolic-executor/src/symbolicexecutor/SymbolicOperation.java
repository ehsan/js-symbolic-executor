/*
 * Copyright 2010 Google Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package symbolicexecutor;

import com.google.common.base.Joiner;

import cvc3.Expr;

import java.util.Formatter;

/**
 * A SymbolicExpression representing a symbolic operation, such as {@code x + 5}
 * or {@code x ? y : []}.
 * <p>
 * For now, constant expressions like {@code 5 * 3} are also encoded as
 * {@link SymbolicOperation}s, but we can do constant folding later, if desired.
 * Another thing we may eventually want to do is represent operations such as
 * {@code obj[x]} or {@code x.indexOf(y)}.
 * <p>
 * Each operation allowed in a {@link SymbolicOperation} must be encoded in the
 * solver.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
class SymbolicOperation implements SymbolicExpression {
  private final String opString;
  private final SymbolicExpression[] args;

  private SymbolicOperation(String opString, SymbolicExpression[] args) {
    this.args = args;
    this.opString = opString;
  }

  /* (non-Javadoc)
   * @see SymbolicExpression#toCVC3(Cvc3Context)
   */
  @Override
  public Expr toCvc3(Cvc3Context context) {
    return context.funExpr(opString, args);
  }

  /** Factory method */
  static SymbolicOperation create(String opString, SymbolicExpression[] args) {
    return new SymbolicOperation(opString, args);
  }

  @Override
  public String toString() {
    return new Formatter().format("(%s %s)",
        opString, Joiner.on(" ").join(args)).toString();
  }
}
