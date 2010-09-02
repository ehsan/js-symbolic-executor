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

import org.mozilla.javascript.NativeObject;

/**
 * An adapter to transform symbolic values from JavaScript to
 * {@link SymbolicValue}s.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
final class SymbolicValueAdapter implements SymbolicExpressionAdapter {
  // Singleton class
  private SymbolicValueAdapter() {}
  public static final SymbolicValueAdapter ADAPTER = new SymbolicValueAdapter();

  /* (non-Javadoc)
   * @see SymbolicExpressionAdapter#fromJS(Object, AdapterList)
   */
  @Override
  public SymbolicValue fromJS(Object obj, AdapterList ignored) {
    return fromJs(obj);
  }

  /** Converts an Object to a SymbolicValue. */
  public SymbolicValue fromJs(Object obj) {
    if (obj instanceof NativeObject) {
      NativeObject nativeObj = (NativeObject) obj;
      // TODO(elnatan): Changing this test to be, essentially, {@code
      // nativeObj instanceof symbolicExecution.SymbolicValue} might be more
      // robust. As is, {@code {symbolicValue: 'foo'}} would (incorrectly) pass
      // this test.
      if (nativeObj.has("symbolicValue", nativeObj)) {
        return SymbolicValue.create(
            (String) nativeObj.get("symbolicValue", nativeObj));
      }
    }
    return null;
  }
}
