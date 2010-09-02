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

import com.google.common.collect.Maps;

import org.mozilla.javascript.Context;
import org.mozilla.javascript.ContextFactory;
import org.mozilla.javascript.ScriptableObject;

import java.io.IOException;
import java.util.Map;
import java.util.Map.Entry;

/**
 * An object that runs symbolic execution on one program to generate a bunch of
 * tests and their outputs, runs a second program with these tests, compares
 * against the first set of outputs, and reports the differences.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
public class CompareFiles {
  /** The file names of the original and new programs */
  private final String originalProgram;
  private final String newProgram;

  /** The name of the function at which to start symbolic execution */
  private final String entryFunction;

  /** The arguments to pass to the entry function to start execution */
  private final String[] arguments;

  /**
   * @param originalProgram file name of the original version of the program
   * @param newProgram file name of the new version of the program
   * @param entryFunction the function at which to start symbolic execution
   * @param arguments the arguments to pass to the entry function
   */
  public CompareFiles(String originalProgram, String newProgram,
      String entryFunction, String... arguments) {
    this.originalProgram = originalProgram;
    this.newProgram = newProgram;
    this.entryFunction = entryFunction;
    this.arguments = arguments;
  }

  /**
   * @param maxTests the maximum number of tests to generate
   * @return the differences between the old and new programs, given as a map
   *         from Inputs to pairs (x, y), where x is the {@link Output} from the
   *         original program and y is the new program's result.
   * @throws IOException if one of the programs cannot be loaded.
   */
  public Map<Input, Pair<Output, Object>> compare(FileLoader loader,
      int maxTests)
  throws IOException {
    Cvc3Context cvc3Context = Cvc3Context.create(arguments.length, loader);
    NewInputGenerator inputGenerator = new ApiBasedInputGenerator(cvc3Context);
    SymbolicExecutor executor = SymbolicExecutor.create(
        originalProgram, loader, inputGenerator, maxTests, entryFunction,
        arguments);
    Context rhinoContext = Context.enter();
    Map<Input, Pair<Output, Object>> differences = Maps.newHashMap();
    // Run symbolic execution, and iterate through all generated inputs
    for (Entry<Input, Output> inputOutput : executor.run().entrySet()) {
      Input input = inputOutput.getKey();
      Output output = inputOutput.getValue();
      // Run the new program with the old arguments
      ScriptableObject scope = rhinoContext.initStandardObjects();
      rhinoContext.evaluateString(scope, loader.toString(newProgram),
          "new program", 0, null);
      Object result = ScriptableObject.callMethod(scope, entryFunction,
          input.toArray(ContextFactory.getGlobal()));
      // If the results differ, add them to the set of differences
      if (!output.result.equals(result)) {
        differences.put(input, new Pair<Output, Object>(output, result));
      }
    }
    return differences;
  }
}
