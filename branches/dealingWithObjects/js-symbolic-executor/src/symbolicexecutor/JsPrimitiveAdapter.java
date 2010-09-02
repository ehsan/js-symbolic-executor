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

import org.mozilla.javascript.Undefined;

/**
 * An adapter to transform JavaScript values to {@link JsPrimitive}s.
 * @author elnatan@google.com (Elnatan Reisner)
 */
final class JsPrimitiveAdapter implements SymbolicExpressionAdapter {
  // Singleton class
  private JsPrimitiveAdapter() {}
  public static final JsPrimitiveAdapter ADAPTER = new JsPrimitiveAdapter();

  /** Converts an Object to a JsPrimitive. */
  public JsPrimitive fromJS(Object obj) {
    if (obj instanceof Double) {
      return JsDouble.create((Double) obj);
    } else if (obj instanceof Integer) {
      return JsDouble.create((Integer) obj);
    } else if (obj instanceof Undefined) {
      return JsUndefined.INSTANCE;
    } else if (obj instanceof String) {
      return JsString.create((String) obj);
    }
    return null;
  }

  /* (non-Javadoc)
   * @see SymbolicExpressionAdapter#fromJS(Object, AdapterList)
   */
  @Override
  public JsPrimitive fromJS(Object obj, AdapterList ignored) {
    return fromJS(obj);
  }
}
