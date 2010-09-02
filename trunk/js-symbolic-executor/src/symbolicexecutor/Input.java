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

import com.google.common.base.Joiner;

import org.mozilla.javascript.ContextFactory;
import org.mozilla.javascript.NativeArray;

/**
 * An input for symbolic execution. It holds both the input values themselves
 * and an integer, the <em>depth</em>, needed to employ the <em>generational
 * search</em> exploration strategy: The very first input has a depth of 0 and,
 * if an input i is meant to force execution to take the branches b1, ..., bn,
 * then i's depth is n. (Inputs generated based on i will not try to flip these
 * branches, but only later branches taken by i.)
 *
 * @author elnatan@google.com (Elnatan Reisner)
 */
class Input implements Comparable<Input> {
  private static int counter = Integer.MIN_VALUE; // Used to give unique ids
  private final String[] valueStrings;
  private final int id;
  final int depthBeforeBranching;

  /**
   * @param values Strings representing the input values
   * @param depth The number of branches to take with this input before trying
   * to generate new inputs that take the opposite branch.
   */
  Input(String[] values, int depth) {
    this.depthBeforeBranching = depth;
    this.valueStrings = values.clone();
    this.id = counter;
    counter++;
  }

  @Override
  public String toString() {
    return "[" + Joiner.on(",").join(valueStrings) + "]";
  }

  /**
   * @param contextFactory usually just the global {@link ContextFactory}
   * @return a Java array of the JavaScript input values
   */
  public Object[] toArray(ContextFactory contextFactory) {
    NativeArray values = toJSArray(contextFactory);
    Object[] result = new Object[valueStrings.length];
    for (int i = 0; i < valueStrings.length; i++) {
      result[i] = values.get(i, values);
    }
    return result;
  }

  /**
   * @param contextFactory usually just the global {@link ContextFactory}
   * @return a JavaScript array of the JavaScript input values
   */
  public NativeArray toJSArray(ContextFactory contextFactory) {
    return (NativeArray) contextFactory.call(new ContextEval(this.toString()));
  }

  // For now, order by id. Later, we may want to use heuristics to find a
  // 'good' next input to run.
  @Override
  public int compareTo(Input other) {
    if (this.id < other.id) {
      return -1;
    } else if (this.id > other.id) {
      return 1;
    }
    return 0;
  }

  /** Return the number of arguments this input provides. */
  public int numArgs() {
    return valueStrings.length;
  }
}
