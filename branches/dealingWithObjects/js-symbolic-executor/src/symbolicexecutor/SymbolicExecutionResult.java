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

import org.mozilla.javascript.NativeArray;
import org.mozilla.javascript.NativeObject;

/**
 * A wrapper for the JavaScript object returned by symbolic execution.
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
class SymbolicExecutionResult {
  private NativeObject jsObject;

  public SymbolicExecutionResult(NativeObject jsObject) {
    this.jsObject = jsObject;
  }

  /**
   * @param adapters The {@link AdapterList} to use to convert JavaScript
   *        objects to {@link SymbolicExpression}s
   * @return an array of {@link SymbolicExpression}s
   */
  public SymbolicExpression[] pathCondition(AdapterList adapters) {
    NativeArray array =
      (NativeArray) jsObject.get("pathCondition", jsObject);
    if (array.getLength() > Integer.MAX_VALUE) {
      throw new RuntimeException("Array length too long");
    }
    SymbolicExpression[] pathCondition =
      new SymbolicExpression[(int) array.getLength()];
    for (int i = 0; i < pathCondition.length; ++i) {
      pathCondition[i] = adapters.toSymbolicExpression(array.get(i, array));
    }
    return pathCondition;
  }

  /**
   * @return the JavaScript value returned by the call to the entry function
   */
  public Object result() {
    return jsObject.get("result", jsObject);
  }
}
