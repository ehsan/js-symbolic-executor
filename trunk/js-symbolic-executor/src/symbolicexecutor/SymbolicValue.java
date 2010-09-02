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

import cvc3.Expr;

/**
 * One type of basic {@link SymbolicExpression}: a symbolic input value
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
class SymbolicValue implements SymbolicExpression {
  private final String name;

  /** Create a SymbolicValue with the given name and expr */
  private SymbolicValue(String name) {
    this.name = name;
  }

  /**
   * @param name The name to give the symbolic value
   */
  public static SymbolicValue create(String name) {
    return new SymbolicValue(name);
  }

  /**
   * @see SymbolicExpression#toCvc3(Cvc3Context)
   * @throws RuntimeException if context does not have a symbolic value
   *         corresponding to this {@link SymbolicValue}'s name
   */
  @Override
  public Expr toCvc3(Cvc3Context context) {
    Expr expr = context.lookupVar(name);
    if (expr.isNull()) {
      throw new RuntimeException("No such symbolic value: " + name);
    }
    return expr;
  }
  
  @Override
  public String toString() {
    return name;
  }
}
