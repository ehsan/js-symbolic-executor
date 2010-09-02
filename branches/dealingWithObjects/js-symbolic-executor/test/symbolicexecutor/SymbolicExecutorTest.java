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

import junit.framework.TestCase;

import java.io.IOException;
import java.util.Map;

/**
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
public class SymbolicExecutorTest extends TestCase {
  private FileLoader loader = new FileLoader();

  /** Test bounding the number of inputs */
  public void testMaxNumInputs() {
    String filename = "test/data/sample.js";
    String[] args = { "0", "5" };
    try {
      Map<Input, Output> output = test(filename, 5, args);
      assertEquals(5, output.size());
    } catch (IOException e) {
      e.printStackTrace();
      fail("Should not have thrown an exception");
    }
  }

  public void testrunWithArgs() {
    String filename = "test/data/generationalSearch.js";
    String[] args = { "0", "0", "0", "0" };
    try {
      Map<Input, Output> output = test(filename, 100, args);
      assertEquals(16, output.size());
    } catch (IOException e) {
      e.printStackTrace();
      fail("Should not have thrown an exception");
    }
  }

  public void testString() throws IOException {
    String filename = "test/data/stringTest.js";
    String[] args = { "5", "10" };
    Map<Input, Output> output = test(filename, 10, args);
    assertEquals(3, output.size());
  }

  private Map<Input, Output> test(String filename, int maxNumInputs,
      String... args) throws IOException {
    Cvc3Context context = Cvc3Context.create(args.length, loader);
    Map<Input, Output> o = SymbolicExecutor.create(filename, loader,
        new ApiBasedInputGenerator(context), maxNumInputs, "f", args).run();
    return o;
  }
}
