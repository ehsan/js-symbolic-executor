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

package com.google.javascript.jscomp;

import com.google.common.base.Supplier;

/**
 * Test converting loops to while(1).
 * @author elnatan@google.com (Elnatan Reisner)
 */
public class ConvertLoopsToWhileOneTest extends CompilerTestCase {
  /* (non-Javadoc)
   * @see CompilerTestCase#getProcessor(Compiler)
   */
  @Override
  protected CompilerPass getProcessor(Compiler compiler) {
    return new ConvertLoopsToWhileOne(new SimpleNameSupplier(), compiler);
  }

  public ConvertLoopsToWhileOneTest() {
    super.enableLineNumberCheck(false);
  }

  private class SimpleNameSupplier implements Supplier<String> {
    private int i = 0;

    @Override
    public String get() {
      return "temp" + i++;
    }
  }

  public void testWhile() {
    test("while (i < 10) { f(i++); }",
        "while(1) { if (!(i < 10)) break; f(i++); }");
  }

  public void testDoWhile() {
    test("do { f(); } while (0);",
        "while(1) { f(); if (!0) break; }");
  }

  public void testFor() {
    test("for (var i = 0; i < 10; i++) { a[i] = i; }",
        "{var i = 0;"
        + "while(1) {"
        + " if (!(i < 10)) break;"
        + " a[i] = i;"
        + " i++;"
        + "}}");
  }

  public void testForWithContinue() {
    test("for (var i = 0; i < 10; i++) { i++; continue; }",
        "{var i = 0;"
        + "var temp0 = false;"
        + "while(1) {"
        + " if (temp0) i++;"
        + " if (!(i < 10)) break;"
        + " temp0 = true;"
        + " i++;"
        + " continue;"
        + "}}");
  }

  public void testNestedLoop() {
    test("for (var i = 0; i < 10; i++) {"
        + "  for (var j = 3; j < 20; j++) {"
        + "    if (j === 5) continue;"
        + "    f(i,j);"
        + "  }"
        + "}",
        "{var i = 0;"
        + "var temp1 = false;"
        + "while (1) {"
        + "  if (temp1) i++;"
        + "  if (!(i < 10)) break;"
        + "  temp1 = true;"
        + "  {var j = 3;"
        + "  var temp0 = false;"
        + "  while (1) {"
        + "    if (temp0) j++;"
        + "    if (!(j < 20)) break;"
        + "    temp0 = true;"
        + "    if (j === 5) continue;"
        + "    f(i,j);"
        + "  }}"
        + "}}");
  }

  /** Make sure that FOR-IN loops are left alone. */
  public void testForIn() {
    testSame("for (x in y) { f(x,y); }");
  }

  /** Make sure that while(1) loops are left alone. */
  public void testWhile1() {
    testSame("while (1) { body }");
  }
}
