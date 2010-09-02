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
public class JsString implements JsPrimitive {
  /** The encapsulated string value */
  private final String string;

  private JsString(String string) {
    this.string = string;
  }

  public static JsString create(String string) {
    assert string != null : "Cannot create a null JsString";
    return new JsString(string);
  }

  /* (non-Javadoc)
   * @see SymbolicExpression#toCvc3(Cvc3Context)
   */
  @Override
  public Expr toCvc3(Cvc3Context context) {
    return context.construct("js_string", context.stringConstant(string));
  }

  /**
   * Print the string out so that a JavaScript interpreter can understand it.
   * Specifically, enclose it in quotes and escape all backslashes and quotes.
   */
  @Override
  public String toString() {
    // Note that we have to escape backslashes before escaping quotes, because
    // otherwise we'd escape the backslashes that we had inserted to escape the
    // quotes.
    return String.format("'%s'",
        string.replaceAll("\\\\", "\\\\\\\\") // Replace \ with \\
        .replaceAll("'", "\\\\'")); // Replace ' with \'
  }
}
