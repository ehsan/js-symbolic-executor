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

import org.mozilla.javascript.Context;
import org.mozilla.javascript.ContextAction;
import org.mozilla.javascript.ScriptableObject;

/**
 * A helper class to make it easy to evaluate a string as JavaScript code.
 * @author elnatan@google.com (Elnatan Reisner)
 */
class ContextEval implements ContextAction {
  private final String code;

  /**
   * @param code The JavaScript to be evaluated
   */
  public ContextEval(final String code) {
    this.code = code;
  }

  @Override
  public Object run(final Context cx) {
    ScriptableObject scope = cx.initStandardObjects();
    return cx.evaluateString(scope, code, "<no path>", 0, null);
  }
}
