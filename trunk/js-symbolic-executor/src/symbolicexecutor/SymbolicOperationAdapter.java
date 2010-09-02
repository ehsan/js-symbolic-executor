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
import org.mozilla.javascript.ScriptableObject;

/**
 * An adapter to transform JavaScript symbolic expressions, arising from
 * symbolic execution, to {@link SymbolicOperation}s.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
final class SymbolicOperationAdapter implements SymbolicExpressionAdapter {
  // Singleton class
  private SymbolicOperationAdapter() {}
  public static final SymbolicOperationAdapter ADAPTER =
    new SymbolicOperationAdapter();

  /* (non-Javadoc)
   * @see SymbolicExpressionAdapter#fromJS(Object, AdapterList)
   */
  @Override
  public SymbolicOperation fromJS(Object obj, AdapterList adapters) {
    if (obj instanceof NativeObject) {
      NativeObject nativeObj = (NativeObject) obj;
      // TODO(elnatan): Changing this test to be, essentially, {@code
      // nativeObj instanceof symbolicExecution.Operation} might be more robust.
      // As is, an object such as {@code {getSymbol: 'foo'}} would (incorrectly)
      // pass this test.
      if (nativeObj.has("getSymbol", nativeObj)) {
        return create(nativeObj, adapters);
      }
    }
    return null;
  }

  /**
   * Convert a {@link NativeObject} into a {@link SymbolicExpression} by getting
   * the string representing the operation and using the given adapters to
   * transform the arguments.
   */
  private SymbolicOperation create(NativeObject nativeObj,
      AdapterList adapters) {
    String opString = (String) ScriptableObject.callMethod(
        nativeObj, "getSymbol", new Object[] {});
    Double arity =
      (Double) ScriptableObject.callMethod(nativeObj, "arity", new Object[] {});
    SymbolicExpression[] args = new SymbolicExpression[arity.intValue()];
    for (int i = 0; i < args.length; i++) {
      args[i] = adapters.toSymbolicExpression(getArg(nativeObj, i));
    }
    return SymbolicOperation.create(opString, args);
  }

  /**
   * Get the i-th argument of nativeObj
   * @param nativeObj a JavaScript symbolic operation expression
   * @param i the desired argument number
   */
  private Object getArg(NativeObject nativeObj, int i) {
    return ScriptableObject.callMethod(nativeObj, "getArg",
        new Object[] { new Double(i) });
  }
}
