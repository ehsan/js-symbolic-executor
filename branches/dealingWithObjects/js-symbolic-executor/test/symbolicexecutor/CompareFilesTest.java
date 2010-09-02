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
 * A TestCase for comparing two files using symbolic execution.
 * @author elnatan@google.com (Elnatan Reisner)
 */
public class CompareFilesTest extends TestCase {
  /**
   * Test that two files with identical behavior are reported as identical.
   * @throws IOException
   */
  public void testComparePass() throws IOException {
    String oldFile = "test/data/generationalSearch.js";
    String newFile = "test/data/generationalSearchRight.js";
    CompareFiles comparer = new CompareFiles(oldFile, newFile, "f",
        "0", "0", "0", "0");
    Map<Input, Pair<Output, Object>> diffs =
      comparer.compare(new FileLoader(), 1000);
    assertTrue(diffs.isEmpty());
  }

  /**
   * Test that two programs that differ are reported to differ.
   * @throws IOException
   */
  public void testCompareFail() throws IOException {
    String oldFile = "test/data/generationalSearch.js";
    String newFile = "test/data/generationalSearchWrong.js";
    CompareFiles comparer = new CompareFiles(oldFile, newFile, "f",
        "10", "0", "10", "0");
    Map<Input, Pair<Output, Object>> diffs =
      comparer.compare(new FileLoader(), 1000);
    assertEquals(7, diffs.size());
  }
}
