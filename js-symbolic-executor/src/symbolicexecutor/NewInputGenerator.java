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

import java.io.IOException;
import java.util.Collection;

/**
 * An interface for generating new inputs from the symbolic execution of a
 * single path.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
interface NewInputGenerator {
  /**
   * Generates a set of inputs that will explore new program paths.
   *
   * @param input the concrete input that was just executed
   * @param result the result of running input
   * @return a Collection of inputs which will explore new program paths
   * @throws IOException
   */
  Collection<Input> generateNewInputs(Input input,
      SymbolicExecutionResult result) throws IOException;
}
