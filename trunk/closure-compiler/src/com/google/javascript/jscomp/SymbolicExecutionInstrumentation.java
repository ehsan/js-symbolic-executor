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

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.javascript.jscomp.NodeTraversal.Callback;
import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;

import java.util.Arrays;
import java.util.List;

/**
 * This is a pass to instrument the code to enable symbolic execution. All
 * assignments and function calls will have code added to maintain a symbolic
 * state in addition to the actual state. Also, branching statements will have
 * code added to track what conditions (in terms of the symbolic state) would
 * cause the code to execute the particular path being run.
 *
 * For example,
 *   {@code if (x) { x += 2; } else { y = x; }}
 * would be instrumented to become
 *   <pre>
 *   if (x) {
 *     symbolicState.addCondition(symbolicState.read('x'));
 *     x += 2;
 *     symbolicState.write('x',symbolicAdd(symbolicState.read('x'),2));
 *   } else {
 *     symbolicState.addCondition(symbolicNot(symbolicState.read('x')));
 *     y = x;
 *     symbolicState.write('y',symbolicState.read('x'));
 *   }
 *   </pre>
 *
 * In addition to tracking the conditions that lead to this path being executed,
 * each call to symbolicState.addCondition() will also output a condition which
 * would lead to execution taking the *other* branch. We will eventually pass
 * these conditions to a constraint solver to find inputs that will lead us down
 * different paths.
 *
 * This pass make heavy use of the comma operator. There are, of course, other
 * ways of instrumenting, some of which might be more intuitive, but using the
 * comma operator makes it easier to instrument a node without changing any of
 * its ancestors. This is useful because it doesn't confuse the postorder
 * traversal.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 */
class SymbolicExecutionInstrumentation implements Callback, CompilerPass {

  private final AbstractCompiler compiler;

  static final DiagnosticType UNIMPLEMENTED_FOR_SYMBOLIC_EXECUTION =
    DiagnosticType.warning(
        "JSC_UNIMPLEMENTED_FOR_SYMBOLIC_EXECUTION",
        "symbolic execution instrumentation cannot handle this: {0}");

  static final DiagnosticType INVALID_FOR_SYMBOLIC_EXECUTION =
    DiagnosticType.error(
        "JSC_INVALID_FOR_SYMBOLIC_EXECUTION",
        "this should have been eliminated before instrumentation for symbolic "
        + "execution: {0}");

  SymbolicExecutionInstrumentation(AbstractCompiler compiler) {
    this.compiler = compiler;
  }

  /**
   * Issue a warning or error when hitting something that
   * SymbolicExecutionInstrumentation can't handle.
   *
   * @param t The NodeTraversal that we need to construct the warning. This,
   *        unfortunately, needs to be passed to several functions just for the
   *        purposes of reporting warnings.
   * @param node The Node at which the problem occurred
   * @param msg The warning message
   * @param diagnostic the actual error or warning
   */
  private void makeError(NodeTraversal t, Node node, String msg,
      DiagnosticType diagnostic) {
    compiler.report(t.makeError(node, diagnostic, msg));
  }

  /** Raise an warning */
  private void warn(NodeTraversal t, Node node, String msg) {
    makeError(t, node, msg, UNIMPLEMENTED_FOR_SYMBOLIC_EXECUTION);
  }

  /** Raise an error */
  private void error(NodeTraversal t, Node node, String msg) {
    makeError(t, node, msg, INVALID_FOR_SYMBOLIC_EXECUTION);
  }

  @Override
  public void process(Node externs, Node root) {
    NodeTraversal.traverse(compiler, root,
        new UnfoldCompoundAssignments(compiler));
    NodeTraversal.traverse(compiler, root, this);
  }

  /** Creates the call funcName(args_0, ..., args_n). */
  static Node newCallNode(String funcName, List<Node> args) {
    Node call = new Node(Token.CALL,
                         NodeUtil.newQualifiedNameNode(funcName, -1, -1));
    for (Node arg : args) {
      call.addChildToBack(arg);
    }
    return call;
  }

  /** Creates the call funcName(args_0, ..., args_n). */
  static Node newCallNode(String funcName, Node... args) {
    return newCallNode(funcName, Arrays.asList(args));
  }

  /**
   * Create a 'left-leaning' nested COMMA node.
   * <p>
   * {@code seq(a,b)} creates {@code COMMA(a, b)},
   * <p>
   * {@code seq(a,b,c)} creates {@code COMMA(COMMA(a,b),c)},
   * <p>
   * {@code seq(a,b,c,d)} creates {@code COMMA(COMMA(COMMA(a,b),c),d)},
   * <p>
   * and so on.
   */
  static Node comma(Node a, Node b, Node... nodes) {
    Node result = new Node(Token.COMMA, a, b);
    for (Node node : nodes) {
      result = new Node(Token.COMMA, result, node);
    }
    return result;
  }

  /**
   * Return the symbolic value representing a node which has no side effects and
   * contains no control flow (although hooks with no side effects are allowed).
   * To get a node's symbolic value, we first get the symbolic values of its
   * children, then construct the symbolic expression involving those
   * arguments. The base cases are literals, whose symbolic values are
   * themselves, and variables, whose symbolic values are the values stored in
   * the symbolic memory.
   *
   * @param node
   * @return A node representing the symbolic value of the input node
   */
  Node getSymbolicValue(NodeTraversal t, Node node) {
    if (NodeUtil.isLiteralValue(node, true)) {
      // We need to clone node to detach it from its parent; other than that, a
      // literal is just itself. Note: 'isLiteralValue' returns true for
      // 'undefined', 'Infinity', and 'NaN' even though (I think) the compiler
      // doesn't check that these names never have values assigned to them.
      return node.cloneTree();
    }
    if (node.getType() == Token.NAME) {
      // Read the symbolic value of variables
      return newCallNode("symbolicExecution.read",
                         Node.newString(node.getString()));
    }
    if (NodeUtil.mayEffectMutableState(node)) {
      warn(t, node,
           "The argument to getSymbolicValue should not have side effects");
    }
    // If we've reached here, node must be an operator, so we need to get the
    // symbolic values of its children and construct the symbolic expression.
    return newCallNode("symbolicExecution." + Token.name(node.getType()),
                       getSymbolicValues(t, node.children()));
  }

  /**
   * Get the symbolic values representing each node in an Iterable of nodes.
   */
  List<Node> getSymbolicValues(NodeTraversal t, Iterable<Node> nodes) {
    List<Node> result = Lists.newLinkedList();
    for (Node node : nodes) {
      result.add(getSymbolicValue(t, node));
    }
    return result;
  }

  /** Don't visit CALL nodes on the right-hand sides of assignments. */
  @Override
  public boolean shouldTraverse(NodeTraversal t, Node node, Node parent) {
    return !(node.getType() == Token.CALL && parent.getType() == Token.ASSIGN);
  }

  @Override
  public void visit(NodeTraversal t, Node node, Node parent) {
    switch (node.getType()) {
      case Token.INC:
      case Token.DEC:
      case Token.ASSIGN_BITOR:  // |=
      case Token.ASSIGN_BITXOR: // ^=
      case Token.ASSIGN_BITAND: // &=
      case Token.ASSIGN_LSH:    // <<=
      case Token.ASSIGN_RSH:    // >>=
      case Token.ASSIGN_URSH:   // >>>=
      case Token.ASSIGN_ADD:    // +=
      case Token.ASSIGN_SUB:    // -=
      case Token.ASSIGN_MUL:    // *=
      case Token.ASSIGN_DIV:    // /=
      case Token.ASSIGN_MOD:    // %=
        error(t, node, Token.name(node.getType()));
        break;
      case Token.ASSIGN:        // simple assignment  (=)
        instrumentAssignment(t, node);
        break;
      case Token.RETURN:
        instrumentReturn(t, node);
        break;
      case Token.FOR:
        if (node.getChildCount() == 3) {
          warn(t, node, "for-in loops not yet implemented");
          break;
        }
        instrumentCondition(t, NodeUtil.getConditionExpression(node));
        break;
      case Token.IF:
      case Token.WHILE:
      case Token.DO:
        instrumentCondition(t, NodeUtil.getConditionExpression(node));
        break;
      case Token.CALL:
        // This only instruments calls that are not within an assignment (due to
        // shouldTraverse). Those within assignments will be instrumented when
        // the assignment is visited.
        instrumentCall(t, node);
        break;
      case Token.FUNCTION:
        instrumentFunction(t, node);
        break;
    }
  }

  /**
   * @param inputNode A Node representing {@code f(a1,...,an)} or {@code
   *        x=f(a1,...,an)}
   * @return A new node representing {@code (push([a1',...,an']), call, pop())},
   *         where the {@code ai'} are the symbolic values of the arguments, and
   *         {@code call} is the input node.
   */
  Node wrapCall(NodeTraversal t, Node inputNode) {
    Node callNode = inputNode;
    if (inputNode.getType() == Token.ASSIGN) {
      callNode = inputNode.getLastChild();
    }
    if (!NodeUtil.isCall(callNode)) {
      throw new IllegalStateException(
          "wrapCall expected a CALL Node but got\n" + callNode.toStringTree());
    }
    Node symbolicArgArray = new Node(Token.ARRAYLIT);
    for (Node arg = callNode.getFirstChild().getNext();
         arg != null;
         arg = arg.getNext()) {
      symbolicArgArray.addChildToBack(getSymbolicValue(t, arg));
    }
    Node push = newCallNode("symbolicExecution.push", symbolicArgArray);
    return comma(push, inputNode.cloneTree(),
                 newCallNode("symbolicExecution.pop"));
  }

  Node getSymbolicLHSForAssignment(NodeTraversal t, Node concreteLHS) {
    if (concreteLHS.getType() == Token.NAME) {
      return Node.newString(concreteLHS.getString());
    }
    if (!(concreteLHS.getType() == Token.GETPROP ||
          concreteLHS.getType() == Token.GETELEM)) {
      throw new IllegalStateException(
          "LHS of assignment must be NAME, GETPROP, or GETELEM, but it is " +
          Token.name(concreteLHS.getType()));
    }
    warn(t, concreteLHS.getParent(),
         "LHS of assignment is GETPROP or GETELEM---not yet implemented");
    return concreteLHS.cloneTree();
  }

  /**
   * Convert {@code x = f(...);} to
   * {@code (push(...), x = f(...), pop(), write('x',returnValue), x)}.
   *
   * This can't simply be done as the composition of instrumentCall and
   * instrumentAssign because instrumentCall would make the right-hand side a
   * weird COMMA node, which instrumentAssign wouldn't be able to handle.
   */
  void instrumentAssignCall(NodeTraversal t, Node assignStmt) {
    Node wrappedCall = wrapCall(t, assignStmt);
    Node lhs = assignStmt.getFirstChild();
    Node symbolicAssign =
        newCallNode("symbolicExecution.write",
                    getSymbolicLHSForAssignment(t, lhs),
                    newCallNode("symbolicExecution.getReturnValue"));
    Node result = comma(wrappedCall, symbolicAssign, lhs.cloneTree());
    assignStmt.getParent().replaceChild(assignStmt, result);
    compiler.reportCodeChange();
  }

  /**
   * Convert {@code f(...);} to
   * {@code (push(...), tmp = f(...), pop(), tmp)}
   */
  private void instrumentCall(NodeTraversal t, Node callStmt) {
    Node temp = NodeUtil.newQualifiedNameNode("symbolicExecution.temp", -1, -1);
    // Make the node: symbolicExecution.temp = f(...)
    Node assignCall = newAssign(temp, callStmt.cloneTree());
    // Wrap it to get: push(...), temp = f(...), pop()
    Node wrappedCall = wrapCall(t, assignCall);
    // Add the temporary variable to the end, so the call evaluates to the
    // return value
    wrappedCall = comma(wrappedCall, temp.cloneTree());
    // Replace the original call statement with the one we constructed
    callStmt.getParent().replaceChild(callStmt, wrappedCall);
    compiler.reportCodeChange();
  }

  /** Construct the Node {@code lhs = rhs} */
  private Node newAssign(Node lhs, Node rhs) {
    return new Node(Token.ASSIGN, lhs, rhs);
  }

  /**
   * There are three types of assignments that have to be dealt with specially:
   * <ul>
   * <li>{@code x = {};}
   * <li>{@code x = [];}
   * <li>{@code x = f(...);}
   * </ul>
   * Each of these right-hand sides have side-effects, and these have to be
   * taken care of along with the assignment itself.
   */
  void instrumentAssignment(NodeTraversal t, Node assignStmt) {
    Node rhs = assignStmt.getLastChild();
    if (NodeUtil.isCall(rhs)) {
      instrumentAssignCall(t, assignStmt);
    } else if (rhs.getType() == Token.OBJECTLIT) {
      instrumentCreateObject(t, assignStmt);
    } else if (rhs.getType() == Token.ARRAYLIT) {
      warn(t, assignStmt, "Array literals not yet implemented");
    } else {
      instrumentPlainAssignment(t, assignStmt);
    }
  }

  /**
   * {@code x = expr;} becomes {@code x = (write('x',...), expr)},
   * where the ellipsis is the symbolic value of {@code expr}
   */
  void instrumentPlainAssignment(NodeTraversal t, Node assignStmt) {
    Node lhs = assignStmt.getFirstChild();
    Node rhs = assignStmt.getLastChild();
    Node symbolicAssign =
        newCallNode("symbolicExecution.write",
                    getSymbolicLHSForAssignment(t, lhs),
                    getSymbolicValue(t, rhs));
    assignStmt.replaceChild(rhs, comma(symbolicAssign, rhs.cloneTree()));
    compiler.reportCodeChange();
  }

  /**
   * Replace {@code x = { p1:v1, ... }} with <pre>
   * {@code x = (write('x', createObj(p1, v1', ...)), { p1:v1, ... })},</pre>
   * where {@code v1'} is the symbolic value of {@code v1}.
   */
  private void instrumentCreateObject(NodeTraversal t, Node assignStmt) {
    Node lhs = assignStmt.getFirstChild();
    Node rhs = lhs.getNext();
    Preconditions.checkArgument(rhs.getType() == Token.OBJECTLIT,
        "instrumentCreateObject needs an object literal on the RHS");
    assignStmt.replaceChild(rhs,
        comma(
            newCallNode("symbolicExecution.write",
                getSymbolicLHSForAssignment(t, lhs),
                newCallNode("symbolicExecution.createObject",
                    getSymbolicValues(t, rhs.children()))),
            rhs.cloneTree()));
    compiler.reportCodeChange();
  }

  /**
   * Transform each return statement {@code return x} into
   * {@code return (setReturnValue(read('x')), x)} to symbolically track
   * the return value but then return the original value.
   */
  void instrumentReturn(NodeTraversal t, Node returnStmt) {
    // TODO(elnatan): This assumes the return value has no side effects. It
    // should be easy to ensure this by writing a pass to transform all return
    // statements to simply return a variable, or by building this
    // transformation into ExpressionDecomposer.
    //
    // This also doesn't currently handle the case where the function was
    // called with 'new'.
    Node call = newCallNode("symbolicExecution.setReturnValue");
    Node returnValue = returnStmt.getFirstChild();
    if (returnValue == null) {
      // returnStmt is {@code return;}. We change it to
      // {@code return setReturnValue();}.  By not providing any arguments to
      // setReturnValue, the value will default to {@code undefined}, and since
      // setReturnValue (implicitly) returns {@code undefined}, returnStmt
      // itself still returns undefined.
      returnStmt.addChildToFront(call);
    } else { // There is a return value
      // Make the symbolic return value the argument to setReturnValue
      call.addChildToBack(getSymbolicValue(t, returnValue));
      returnStmt.replaceChild(returnValue,
                              comma(call, returnValue.cloneTree()));
    }
    compiler.reportCodeChange();
  }

  /**
   * Instrument a node representing a branch condition; namely, the condition in
   * an if statement or a loop guard.
   * <p>
   * An expression {@code cond} becomes <pre>
   * {@code
   * temp = cond,
   * temp2 = cond',
   * temp || (temp2 = symbolicExecution.NOT(temp2)),
   * symbolicExecution.addCondition(temp2),
   * temp;}</pre>
   * where {@code cond'} is the symbolic encoding of the condition.
   * (N.B. {@code x || y} is equivalent to {@code if (!x) y;}.)
   */
  private void instrumentCondition(NodeTraversal t, Node condition) {
    Node temp = NodeUtil.newQualifiedNameNode("symbolicExecution.temp", -1, -1);
    Node temp2 =
      NodeUtil.newQualifiedNameNode("symbolicExecution.temp2", -1, -1);
    Node result =
      comma(newAssign(temp, condition.cloneTree()),
          newAssign(temp2, getSymbolicValue(t, condition)),
          new Node(Token.OR, temp.cloneTree(),
              newAssign(temp2.cloneTree(),
                  newCallNode("symbolicExecution.NOT", temp2.cloneTree()))),
          newCallNode("symbolicExecution.addCondition", temp2.cloneTree()),
          temp.cloneTree());
    condition.getParent().replaceChild(condition, result);
    compiler.reportCodeChange();
  }

  // TODO(elnatan): Handle {@code arguments}
  void instrumentFunction(NodeTraversal t, Node functionStmt) {
    Node paramList = NodeUtil.getFnParameters(functionStmt);
    Node funcBody = NodeUtil.getFunctionBody(functionStmt);
    // Add a final return statement, if there wasn't one
    if (funcBody.getLastChild() == null ||
        funcBody.getLastChild().getType() != Token.RETURN) {
      Node emptyReturn = new Node(Token.RETURN);
      instrumentReturn(t, emptyReturn);
      funcBody.addChildToBack(emptyReturn);
    }
    int i = 0;
    for (Node param : paramList.children()) {
      // Read the i-th argument and write it into the i-th parameter
      funcBody.addChildToFront(NodeUtil.newExpr(
          newCallNode("symbolicExecution.write",
                      Node.newString(param.getString()),
                      newCallNode("symbolicExecution.read",
                                  Node.newNumber(i)))));
      i++;
    }
    compiler.reportCodeChange();
  }
}
