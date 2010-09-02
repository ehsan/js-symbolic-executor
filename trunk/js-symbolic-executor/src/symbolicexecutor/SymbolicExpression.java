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
 * The interface for a symbolic expression. This an intermediate form between
 * JavaScript objects and expressions suitable to be passed to the constraint
 * solver. The SymbolicExpression needs to contain all the information necessary
 * to be able to convert to a solver expression when supplied with a solver
 * context.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
interface SymbolicExpression {
  /**
   * @param context The solver environment in which to create the expression.
   * @return a representation in CVC3 of this symbolic expression
   */
  public Expr toCvc3(Cvc3Context context);
}
