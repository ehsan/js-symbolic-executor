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

/**
 * A class to convert from JavaScript objects to {@link SymbolicExpression}s
 * using a sequence of {@link SymbolicExpressionAdapter}s.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
final class AdapterList {
  private final SymbolicExpressionAdapter[] adapters;

  /**
   * A default list of adapters: first, see if the object is a symbolic value;
   * if not, see if it is a symbolic operation; if not, it must be a normal
   * JavaScript value.
   */
  public static final AdapterList DEFAULT_ADAPTERS =
    new AdapterList(SymbolicValueAdapter.ADAPTER,
        SymbolicOperationAdapter.ADAPTER,
        JsObjectAdapter.ADAPTER,
        JsPrimitiveAdapter.ADAPTER);

  /**
   * @param adapters The adapters to use. They will be tried in the order in
   *        which they are passed to the constructor.
   */
  public AdapterList(SymbolicExpressionAdapter... adapters) {
    this.adapters = adapters;
  }

  /**
   * Iterate through the list of adapters until one successfully translates the
   * argument into a {@link SymbolicExpression}
   * @return the SymbolicExpression
   */
  SymbolicExpression toSymbolicExpression(Object jsObject) {
    for (SymbolicExpressionAdapter adapter : adapters) {
      SymbolicExpression exp = adapter.fromJS(jsObject, this);
      if (exp != null) {
        return exp;
      }
    }
    throw new IllegalArgumentException("Failed to convert " + jsObject);
  }
}
