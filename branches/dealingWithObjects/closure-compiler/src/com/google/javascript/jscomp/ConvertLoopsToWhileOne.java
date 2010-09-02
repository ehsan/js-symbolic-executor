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
import com.google.javascript.jscomp.NodeTraversal.Callback;
import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;

/**
 * A pass to transform loops into while(1).<p>
 * {@code while} loops are transformed from <pre>{@code
 * while(guard) {
 *   body;
 * }}</pre>
 * to <pre>{@code
 * while(1) {
 *   if (!guard) { break; }
 *   body;
 * }}</pre>.<p>
 * {@code do-while} loops <pre>{@code
 * do {
 *   body;
 * } while (guard)}</pre> become <pre>{@code
 * while(1) {
 *   body;
 *   if (!guard) { break; }
 * }}</pre>.<p>
 * {@code for} loops without {@code continue}s go from
 * <pre>{@code
 * for (init; guard; incr) {
 *   body
 * }}</pre>
 * to <pre>{@code
 * init;
 * while (1) {
 *   if (!guard) { break; }
 *   body;
 *   incr;
 * }}</pre>.<p>
 * {@code for} loops <em>with</em> {@code continue}s are transformed them to
 * <pre>{@code
 * init;
 * looping = false;
 * while (1) {
 *   if (looping) incr;
 *   if (!guard) { break; }
 *   looping = true;
 *   body;
 * }}</pre>, where {@code looping} is a fresh variable. This allows {@code
 * continue}s and normal iterations of the loop to execute the increment, but
 * prevents the initial entry to the loop from executing it.
 *
 * TODO(elnatan): Initializers for {@code for} loops have to be pulled to before
 * any labels on the loop. However, since {@code for} loops do not have
 * initializers in normalized code, we wouldn't have to worry about this, and we
 * could simplify this pass a little, by requiring that this pass always be run
 * on normalized code.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 */
class ConvertLoopsToWhileOne implements Callback, CompilerPass {
  private final AbstractCompiler compiler;

  /** A {@link Supplier} that provides unique variable names. */
  private final Supplier<String> varNameSupplier;

  public ConvertLoopsToWhileOne(Supplier<String> varNameSupplier,
      AbstractCompiler compiler) {
    this.varNameSupplier = varNameSupplier;
    this.compiler = compiler;
  }

  /* (non-Javadoc)
   * @see Callback#shouldTraverse(NodeTraversal, Node, Node)
   */
  @Override
  public boolean shouldTraverse(NodeTraversal nodeTraversal, Node n,
      Node parent) {
    return true;
  }

  /* (non-Javadoc)
   * @see Callback#visit(NodeTraversal, Node, Node)
   */
  @Override
  public void visit(NodeTraversal t, Node n, Node parent) {
    switch (n.getType()) {
      case Token.WHILE:
        // If the loop is already a while(1), leave it alone.
        if (Node.newNumber(1).isEquivalentTo(n.getFirstChild())) {
          break;
        }
        Node whileGuard = n.removeFirstChild();
        n.addChildToFront(Node.newNumber(1));
        // Add {@code if (!guard) break;} to the start of the body
        n.getLastChild().addChildToFront(breakIfNot(whileGuard));
        compiler.reportCodeChange();
        break;
      case Token.DO:
        n.setType(Token.WHILE);
        Node doGuard = n.getLastChild();
        doGuard.detachFromParent();
        // Add {@code if (!guard) break;} to the end of the body
        n.getFirstChild().addChildToBack(breakIfNot(doGuard));
        // Add the condition 1.
        n.addChildToFront(Node.newNumber(1));
        compiler.reportCodeChange();
        break;
      case Token.FOR:
        // Don't transform FOR-IN loops
        if (NodeUtil.isForIn(n)) {
          break;
        }
        // At first, n is FOR(init, guard, incr, BLOCK(body))
        n.setType(Token.BLOCK);
        // Now n is BLOCK(init, guard, incr, BLOCK(body))

        // We will pull off each child and rearrange things.
        // BLOCKs seem to only have as children VARs, EXPR_RESULTs, and control
        // structures, so we have to wrap init and incr in EXPR_RESULTs if they
        // aren't one of those.
        Node forInit = makeStmt(n.removeFirstChild());
        // n is BLOCK(guard, incr, BLOCK(body))
        Node forGuard = n.removeFirstChild();
        // n is BLOCK(incr, BLOCK(body))
        Node forIncr = makeStmt(n.removeFirstChild());
        // n is BLOCK(BLOCK(body))
        Node forBody = n.removeFirstChild();
        // n is BLOCK()
        n.addChildToFront(forInit);
        // n is BLOCK(init)
        n.addChildToBack(new Node(Token.WHILE, Node.newNumber(1), forBody));
        // n is BLOCK(init, WHILE(1, BLOCK(body))).
        forBody.addChildToFront(breakIfNot(forGuard));
        // n is BLOCK(init,
        //            WHILE(1, BLOCK(IF(NOT(guard), BLOCK(BREAK)), body)))

        // Right now, this will add the temporary variable even in loops which
        // have continue statements only within nested loops; this is fine,
        // albeit unnecessary. Detecting nested continues is not trivial,
        // though, so I'm not bothering.
        if (NodeUtil.containsType(n, Token.CONTINUE)) {
          String looping = varNameSupplier.get();
          n.addChildAfter(NodeUtil.newVarNode(looping, new Node(Token.FALSE)),
              forInit);
          // n is BLOCK(init,
          //            VAR(temp, FALSE),
          //            WHILE(1, BLOCK(IF(NOT(guard), BLOCK(BREAK)), body)))
          forBody.addChildAfter(
              NodeUtil.newExpr(
                  new Node(Token.ASSIGN, Node.newString(Token.NAME, looping),
                      new Node(Token.TRUE))),
                      forBody.getFirstChild());
          // n is BLOCK(init,
          //            VAR(temp, FALSE),
          //            WHILE(1, BLOCK(IF(NOT(guard), BLOCK(BREAK)),
          //                           ASSIGN(entering, TRUE),
          //                           body)))
          forBody.addChildToFront(
              new Node(Token.IF,
                  Node.newString(Token.NAME, looping),
                  new Node(Token.BLOCK, forIncr)));
          // n is BLOCK(init,
          //            VAR(entering, FALSE),
          //            WHILE(1, BLOCK(IF(entering, BLOCK(incr)),
          //                           IF(NOT(guard), BLOCK(BREAK)),
          //                           ASSIGN(entering, TRUE),
          //                           body)))
        } else {
          forBody.addChildToBack(forIncr);
          // n is BLOCK(init,
          //            WHILE(1, BLOCK(IF(NOT(guard), BLOCK(BREAK)),
          //                           body, incr)))
        }
        compiler.reportCodeChange();
        break;
      default: return;
    }
  }

  /**
   * Make a Node a standalone statement by wrapping it in an EXPR_RESULT, if
   * necessary
   *
   * @param node the Node to be made a standalone statement
   * @return node, if it is a VAR, EXPR_RESULT, IF, or WHILE; otherwise,
   *         EXPR_RESULT(node)
   */
  private Node makeStmt(Node node) {
    switch (node.getType()) {
      case Token.VAR:
      case Token.EXPR_RESULT:
      case Token.IF:
      case Token.WHILE:
        return node;
      default:
        return NodeUtil.newExpr(node);
    }
  }

  /**
   * @param guard a Node that must not be attached to a parent
   * @return a Node representing {@code if (!guard) break;}
   */
  private Node breakIfNot(Node guard) {
    return new Node(Token.IF, new Node(Token.NOT, guard),
        new Node(Token.BLOCK, new Node(Token.BREAK)));
  }

  /* (non-Javadoc)
   * @see CompilerPass#process(Node, Node)
   */
  @Override
  public void process(Node externs, Node root) {
    NodeTraversal.traverse(compiler, root, this);
  }
}
