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
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
public class JsBool implements JsValue {
  /** The encapsulated boolean value */
  private final boolean bool;

  private JsBool(boolean value) {
    this.bool = value;
  }

  public static JsBool create(boolean bool) {
    return new JsBool(bool);
  }

  /* (non-Javadoc)
   * @see SymbolicExpression#toCvc3(Cvc3Context)
   */
  @Override
  public Expr toCvc3(Cvc3Context context) {
    return context.construct(bool ? "js_true" : "js_false");
  }

  @Override
  public String toString() {
    return Boolean.toString(bool);
  }
}
