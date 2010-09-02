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

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.javascript.jscomp.Compiler;
import com.google.javascript.jscomp.CompilerOptions;
import com.google.javascript.jscomp.JSSourceFile;

import org.mozilla.javascript.Context;
import org.mozilla.javascript.ContextFactory;
import org.mozilla.javascript.NativeObject;
import org.mozilla.javascript.Script;
import org.mozilla.javascript.Scriptable;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Map;
import java.util.SortedSet;

/**
 * This class implements symbolic execution. The constructor takes the filename
 * of the JavaScript program to symbolically execute, which must have already
 * been instrumented by the symbolic execution instrumentation pass. The
 * constructor also takes a FileLoader and a NewInputGenerator, which it uses
 * during initialization and execution, respectively.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 */
public class SymbolicExecutor {
  /**
   * The filename of the JavaScript symbolic execution library. These are the
   * functions called by the instrumented JavaScript code.
   */
  private static final String SYMBOLIC_EXECUTION_OBJECT_SOURCE_FILE =
      "data/symbolicExecutionObject.js";

  /** The JavaScript source code to symbolically execute */
  private final String jsSource;

  /** The object that will generate new inputs after each execution */
  private final NewInputGenerator newInputGenerator;

  /** An object to help with loading files */
  private final FileLoader loader;

  /** Stop generating inputs after this many have been generated */
  private final int maxNumInputs;

  /** A set of inputs waiting to be run */
  private final SortedSet<Input> inputs;

  private SymbolicExecutor(String source, FileLoader loader,
      NewInputGenerator newInputGenerator, Input arguments,
      int maxNumInputs) {
    this.jsSource = source;
    this.loader = loader;
    this.newInputGenerator = newInputGenerator;
    this.maxNumInputs = maxNumInputs;
    this.inputs = Sets.newTreeSet();
    this.inputs.add(arguments);
  }

  /**
   * Creates a symbolic executor.
   *
   * @param code the (already instrumented) source code that will be
   *        symbolically executed
   * @param loader a FileLoader to help load files
   * @param newInputGenerator the object that will generate new inputs from old
   *        ones
   * @param inputs the values for the JavaScript variable named {@code inputs}
   * @param maxNumInputs symbolic execution will stop after this many inputs are
   *        generated. This isn't a strict maximum, though, because new inputs
   *        are generated in batches, and we stop after the first <em>batch</em>
   *        puts us at or past this limit.
   * @return the newly created {@link SymbolicExecutor}
   */
  public static SymbolicExecutor create(String code, FileLoader loader,
      NewInputGenerator newInputGenerator, String[] inputs,
      int maxNumInputs) {
    return new SymbolicExecutor(code, loader, newInputGenerator,
        new Input(inputs, 0), maxNumInputs);
  }

  /**
   * Creates a symbolic executor which will instrument the given file and then,
   * when run, symbolically execute starting by calling entryFunction with the
   * given inputs.
   *
   * @param filename a JavaScript file which will be instrumented and then
   *        symbolically executed
   * @param loader a FileLoader to help load files
   * @param newInputGenerator the object that will generate new inputs from old
   *        ones
   * @param maxNumInputs symbolic execution will stop after this many inputs are
   *        generated. This isn't a strict maximum, though, because new inputs
   *        are generated in batches, and we stop after the first <em>batch</em>
   *        puts us at or past this limit.
   * @param entryFunction the function at which symbolic execution will start
   * @param inputs the initial inputs to use when calling entryFunction
   */
  public static SymbolicExecutor create(String filename, FileLoader loader,
      NewInputGenerator newInputGenerator, int maxNumInputs,
      String entryFunction, String... inputs) {
    CompilerOptions options = new CompilerOptions();
    // Enable instrumentation
    options.symbolicExecutionInstrumentation = true;
    options.prettyPrint=true;
    // Compile the program; this is where the instrumentation happens.
    Compiler compiler = new Compiler();
    compiler.compile(new ArrayList<JSSourceFile>(),
        Lists.newArrayList(JSSourceFile.fromFile(loader.getPath(filename))),
        options);
    // Add the call to symbolicExecution.execute
    String code = String.format("%s;symbolicExecution.execute(this,%s,inputs)",
      compiler.toSource(), entryFunction);
    return create(code, loader, newInputGenerator, inputs, maxNumInputs);
  }

  /**
   * Starting with 'outputs' as the empty set, this method does executes the
   * following loop until {@link SymbolicExecutor#inputs} is empty.
   * <ul>
   * <li> Remove an input from 'inputs', and call the input X and the depth d.
   * <li> Run symbolic execution with X as the inputs
   * <li> This will output
   *   <ul>
   *   <li> the path condition that leads execution down the path that was taken
   *   <li> the symbolic state at the end of execution and
   *   <li> the concrete state at the end of execution.
   *   </ul>
   * <li> Add the pair X,(a) to 'outputs'.
   * <li> The path condition has the form (p1,...,pn), and d will always be less
   * than n. Let C = (p1 and ... and pd). For i in {d+1,...,n}, try to solve (C
   * and p{d+1} and ... and p{i-1} and !pi). If the constraint is solvable, it
   * gives a new input Y; add (Y,i) to 'inputs'. (If the constraint is
   * unsatisfiable, just skip it.)
   * </ul>
   *
   * @return a map from {@link Input}s to {@link Output}s generated by symbolic
   *    execution
   */
  public Map<Input, Output> run() throws IOException {
    String code = loader.toString(SYMBOLIC_EXECUTION_OBJECT_SOURCE_FILE) +
        this.jsSource;

    Context rhinoContext = Context.enter();

    // Compile the code. We can run it by executing it in a scope in which we
    // set "inputs" to a NativeArray of the arguments
    Script script = rhinoContext.compileString(code, "no file", 0, null);

    Map<Input, Output> inputOutputMap = Maps.newTreeMap();

    int numInputs = 1;
    while (!inputs.isEmpty()) {
      Input input = inputs.first();
      inputs.remove(input);

      SymbolicExecutionResult result = execute(rhinoContext, script, input);
      Output output = new Output(input,
          Sets.newHashSet(result.pathCondition(AdapterList.DEFAULT_ADAPTERS)),
          result.result());
      Output oldValue = inputOutputMap.put(input, output);
      // Stop generating new inputs once we reach the limit.
      if (numInputs < maxNumInputs) {
        Collection<Input> newInputs =
          newInputGenerator.generateNewInputs(input, result);
        numInputs += newInputs.size();
        inputs.addAll(newInputs);
        System.out.println(input + " generated " + newInputs);
      }
    }

    return inputOutputMap;
  }

  /**
   * Symbolically executes one path through the compiled program.
   *
   * @param rhinoContext the JavaScript scope containing the symbolic execution
   *        library functions
   * @param script the compiled instrumented JavaScript
   * @param input the arguments to pass to the entry function for symbolic
   *        execution
   * @return the result of performing symbolic execution
   */
  private SymbolicExecutionResult execute(Context rhinoContext, Script script,
      Input input) {
    ContextFactory contextFactory = ContextFactory.getGlobal();
    Scriptable scope = rhinoContext.initStandardObjects();
    scope.put("inputs", scope, input.toJSArray(contextFactory));
    return new SymbolicExecutionResult(
        (NativeObject) script.exec(rhinoContext, scope));
  }

  public static void main(String[] args) throws IOException {
     if (args.length < 3) {
       System.out.println(
           "Usage:\n" +
           "java -jar <jarfile> filename entryFunction numTests [arg...]\n\n" +
           "filename is the file to instrument\n" +
           "entryFunction is the function at which symbolic execution will " +
           "start\n" +
           "numTests---Symbolic execution will stop after generating " +
           "(roughly) this many test inputs\n" +
           "[arg...] are the arguments that will be passed to entryFunction;" +
           "they are strings, parsed by the JavaScript interpreter\n\n" +
           "This will instrument the program, run symbolic execution, and " +
           "print out the generated inputs and the corresponding outputs.");
       System.exit(0);
     }
     String filename = args[0], entryFunction = args[1];
     int maxNumInputs = Integer.valueOf(args[2]);
     FileLoader loader = new FileLoader();
     Cvc3Context cvc3Context = Cvc3Context.create(args.length - 3, loader);
     System.out.println(create(filename, loader,
         new ApiBasedInputGenerator(cvc3Context), maxNumInputs,
         entryFunction, Arrays.copyOfRange(args, 3, args.length)).run());
  }
}
