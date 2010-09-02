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

/**
 * Unit tests for SymbolicExecutionInstrumentation
 * @author elnatan@google.com (Elnatan Reisner)
 */
public class SymbolicExecutionInstrumentationTest extends CompilerTestCase {
  @Override
  protected int getNumRepetitions() {
    // The instrumentation pass is only run once.
    return 1;
  }

  @Override
  public CompilerPass getProcessor(final Compiler compiler) {
    return new SymbolicExecutionInstrumentation(compiler);
  }

  public SymbolicExecutionInstrumentationTest() {
    super.enableLineNumberCheck(false);
  }

  public void testinstrumentReturn0() {
    test("function () { return; }",
         "function () { return symbolicExecution.setReturnValue(); }");
  }

  public void testinstrumentReturn1() {
    test("function () { return []; }",
         "function () { return (symbolicExecution.setReturnValue([]), []); }");
    test("function () { return undefined; }",
         "function() {" +
         " return (symbolicExecution.setReturnValue(undefined), undefined); }");
  }

  public void testinstrumentReturn2() {
    test("function () { return -y ? 2*y : 8; }",
         "function () {" +
         " return (" +
         "  symbolicExecution.setReturnValue(" +
         "   symbolicExecution.HOOK(" +
         "    symbolicExecution.NEG(symbolicExecution.read('y'))," +
         "    symbolicExecution.MUL(2,symbolicExecution.read('y'))," +
         "    8))," +
         "  -y ? 2*y : 8);" +
         "}");
  }

  public void testinstrumentAssignment0() {
    test("x = 9", instrumentedAssign("x", "9"));
  }

  public void testinstrumentAssignment1() {
    test("x = x", instrumentedAssign("x", "x", "symbolicExecution.read('x')"));
  }

  public void testinstrumentIf0() {
    test(
        "if (x);",
        String.format("if (%s);",
            instrumentedCondition("x", "symbolicExecution.read('x')")));
  }

  public void testinstrumentIf1() {
    test(
        "if (1) { 0; }",
        String.format("if (%s) { 0 }", instrumentedCondition("1")));
  }

  public void testinstrumentIf2() {
    test(
        "if ('s'); else { 0; }",
        String.format("if (%s); else { 0; }", instrumentedCondition("'s'")));
  }

  public void testinstrumentIf3() {
    String symbolicCondition = "symbolicExecution.LE(" +
        "symbolicExecution.MUL(8,symbolicExecution.read('n'))," +
        "symbolicExecution.ADD(symbolicExecution.read('m'),12))";
    test(
        "if (8 * n <= m + 12) { n=''; } else { m=0; }",
        String.format("if (%s) { %s } else { %s }",
            instrumentedCondition("8 * n <= m + 12", symbolicCondition),
            instrumentedAssign("n", "''"),
            instrumentedAssign("m", "0")));
  }

  public void testFunction0() {
    test("function (a,b,c) {}",
         "function (a,b,c) {" +
         " symbolicExecution.write('c',symbolicExecution.read(2));" +
         " symbolicExecution.write('b',symbolicExecution.read(1));" +
         " symbolicExecution.write('a',symbolicExecution.read(0));" +
         " return symbolicExecution.setReturnValue();" +
         "}");
  }

  public void testCall0() {
    test("f(5,x + 1)",
        instrumentedCall("f", "5, x+1",
            "5, symbolicExecution.ADD(symbolicExecution.read('x'), 1)"));
  }

  public void testCall1() {
    test("y = f()", instrumentedAssignCall("y", "f", "", ""));
  }

  public void testFor() {
    test("for (x = 1; x < y; x = 2*x) { f(); }",
        String.format("for (%s; %s; %s) { %s }",
            instrumentedAssign("x", "1"),
            instrumentedCondition("x<y", "symbolicExecution.LT("
                + "symbolicExecution.read('x'),"
                + "symbolicExecution.read('y'))"),
            instrumentedAssign("x", "2*x",
                "symbolicExecution.MUL(2, symbolicExecution.read('x'))"),
            instrumentedCall("f", "", "")));
  }

  public void testWhile() {
    test("while (8 === x) {}", String.format("while (%s) {}",
        instrumentedCondition("8===x",
        "symbolicExecution.SHEQ(8, symbolicExecution.read('x'))")));
  }

  public void testDoWhile() {
    test("do {} while (8 === x)", String.format("do {} while (%s)",
        instrumentedCondition("8===x",
        "symbolicExecution.SHEQ(8, symbolicExecution.read('x'))")));
  }

  /**
   * @param lhs the variable being assigned to
   * @param rhs the value being assigned, which must be a literal
   * @return the String representing an instrumented assignment
   */
  private String instrumentedAssign(String lhs, String rhs) {
    return instrumentedAssign(lhs, rhs, rhs);
  }
 
  /**
   * @param lhs the variable being assigned to
   * @param rhs the value being assigned
   * @param rhsSymbolic the symbolic value of rhs
   * @return the instrumented assignment
   */
  private String instrumentedAssign(String lhs, String rhs, String rhsSymbolic) {
    return String.format("%s = (symbolicExecution.write('%s', %s), %s)",
        lhs, lhs, rhsSymbolic, rhs);
  }

  /**
   * @param condition the condition, which must be a literal
   * @return the instrumented condition
   */
  private String instrumentedCondition(String condition) {
    return instrumentedCondition(condition, condition);
  }

  /**
   * @param condition the condition
   * @param symbolicCondition the symbolic value of condition
   * @return the instrumented condition
   */
  private String instrumentedCondition(String condition,
      String symbolicCondition) {
    return String.format("symbolicExecution.temp = %s,"
        + "symbolicExecution.temp2 = %s,"
        + "symbolicExecution.temp || (symbolicExecution.temp2 ="
        + " symbolicExecution.NOT(symbolicExecution.temp2)),"
        + "symbolicExecution.addCondition(symbolicExecution.temp2),"
        + "symbolicExecution.temp", condition, symbolicCondition);
  }

  private String instrumentedCall(String function, String args,
      String symbolicArgs) {
    return String.format("symbolicExecution.push([%s]),"
        + "symbolicExecution.temp = %s(%s),"
        + "symbolicExecution.pop(),"
        + "symbolicExecution.temp",
        symbolicArgs, function, args);
  }

  private String instrumentedAssignCall(String lhs, String function,
      String args, String symbolicArgs) {
    return String.format("symbolicExecution.push([%s]),"
        + "%s = %s(%s),"
        + "symbolicExecution.pop(),"
        + "symbolicExecution.write('%s', symbolicExecution.getReturnValue()),"
        + "%s",
        symbolicArgs, lhs, function, args, lhs, lhs);
  }

  /** Make sure assignment unfolding happens before instrumentation */
  public void testIncrement() {
    test("x *= 7",
        "x = (symbolicExecution.write('x',"
        + " symbolicExecution.MUL(symbolicExecution.read('x'), 7)), x * 7)");
  }

  public void testObjectLiteral0() {
    test("x = {};",
        "x = (symbolicExecution.write('x', symbolicExecution.createObject()),"
        + "{});");
  }

  public void testObjectLiteral1() {
    test("y = {0:x, 'a b':'a'};",
        "y = (symbolicExecution.write('y',"
        + "symbolicExecution.createObject(0, symbolicExecution.read('x'),"
        + "'a b', 'a')),"
        + "{0:x, 'a b':'a'});");
  }
}
