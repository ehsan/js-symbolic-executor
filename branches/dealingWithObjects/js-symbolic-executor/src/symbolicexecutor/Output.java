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

import java.util.Set;

/**
 * The result of taking one execution path through the program.
 * <p>
 * This includes the input that was used, the path condition that generalizes
 * this input but still guarantees executing the same path, and the JavaScript
 * object that was returned by the entry function. Later, we may also want to
 * include the concrete and symbolic states at the end of execution.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
class Output {
  final Input input;
  final Set<SymbolicExpression> pathCondition;
  final Object result;

  public Output(Input input, Set<SymbolicExpression> pathCondition,
      Object result) {
    this.input = input;
    this.pathCondition = pathCondition;
    this.result = result;
  }

  /* (non-Javadoc)
   * @see Object#toString()
   */
  @Override
  public String toString() {
    return String.format(
        "\nInput:\n  %s\nOutput:\n  %s\nGeneralized input:\n  %s\n",
        input.toString(), JsValueAdapter.ADAPTER.fromJS(result).toString(),
        pathCondition.toString());
  }
}
