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
public class JsDouble implements JsValue {
  /** The encapsulated double value */
  private final double value;

  private JsDouble(double value) {
    this.value = value;
  }

  public static JsDouble create(double value) {
    return new JsDouble(value);
  }

  /* (non-Javadoc)
   * @see SymbolicExpression#toCvc3(Cvc3Context)
   */
  @Override
  public Expr toCvc3(Cvc3Context context) {
    if (Double.isNaN(value)) {
      return context.construct("js_NaN");
    } else if (value == (int) value) {
      return context.jsNum((int) value);
    }
    throw new IllegalArgumentException("Can't handle non-integers yet");
  }

  @Override
  public String toString() {
    return Double.toString(value);
  }
}
