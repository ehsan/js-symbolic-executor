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

import com.google.common.collect.Sets;

import cvc3.Expr;

import java.util.Collection;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * A class to generate new inputs for symbolic execution by using the API.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
public class ApiBasedInputGenerator implements NewInputGenerator {
  private final Cvc3Context cvc3Context;

  /**
   * @param cvc3Context queries will be solved within this context
   */
  public ApiBasedInputGenerator(Cvc3Context cvc3Context) {
    this.cvc3Context = cvc3Context;
  }

  /* (non-Javadoc)
   * @see NewInputGenerator#generateNewInputs(Input, SymbolicExecutionResult)
   */
  @Override
  public Collection<Input> generateNewInputs(Input oldInput,
      SymbolicExecutionResult result) {
    int conditionNumber = -1;
    TreeSet<Input> newInputs = Sets.newTreeSet();
    Set<Expr> assumptions = Sets.newHashSet();
    cvc3Context.push(); // Checkpoint the solver state
    for (SymbolicExpression constraint :
      result.pathCondition(AdapterList.DEFAULT_ADAPTERS)) {
      conditionNumber++;
      if (conditionNumber < oldInput.depthBeforeBranching) {
        cvc3Context.assume(constraint);
      } else {
        Map<String, JsPrimitive> model = cvc3Context.query(constraint);
        if (model != null) {
          String[] inputArgs = new String[oldInput.numArgs()];
          for (int argIndex = 0; argIndex < oldInput.numArgs(); argIndex++) {
            inputArgs[argIndex] = model.get("sym" + argIndex).toString();
          }
          newInputs.add(new Input(inputArgs, conditionNumber + 1));
          // Assume that the constraint holds so that later inputs follow the
          // same path as oldInput for one additional branch. Note that we only
          // have to do this for invalid constraints, because valid constraints
          // are implied by earlier constraints.
          cvc3Context.assume(constraint);
        }
      }
    }
    cvc3Context.pop(); // Restore the original solver state
    return newInputs;
  }
}
