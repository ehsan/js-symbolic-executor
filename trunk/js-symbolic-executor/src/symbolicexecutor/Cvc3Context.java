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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import cvc3.Expr;
import cvc3.Op;
import cvc3.QueryResult;
import cvc3.Type;
import cvc3.ValidityChecker;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A wrapper around CVC3's ValidityChecker class.
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
class Cvc3Context {
  /** The file containing the CVC3 definitions of JavaScript operators */
  private static final String CVC3_JS_FILE_NAME = "data/javascript.cvc";

  /** The file containing the CVC3 definitions of strings */
  private static final String CVC3_STRING_FILE_NAME = "data/string.cvc";

  private final ValidityChecker context;

  /** How many symbolic values there are */
  private int numSymbols;

  /** The CVC3 types INT, String, and JSType */
  private final Type intType;
  private final Type stringType;
  private final Type jsType;

  private Cvc3Context(int numSymbols, FileLoader loader) {
    this.numSymbols = numSymbols;
    context = ValidityChecker.create();
    context.loadFile(loader.getPath(CVC3_STRING_FILE_NAME));
    intType = context.intType();
    stringType = context.lookupType("String");
    // Create string constants JavaScript needs
    stringConstant("true");
    stringConstant("false");
    stringConstant("NaN");
    stringConstant("null");
    stringConstant("undefined");
    context.loadFile(loader.getPath(CVC3_JS_FILE_NAME));
    jsType = context.lookupType("JSType");
    for (int i = 0; i < numSymbols; i++) {
      createSymbolicInput(i);
    }
  }

  /**
   * Creates the i-th symbolic input value.
   * <p>
   * Ideally, only the first line would be needed, creating a variable with type
   * JSType. However, the code below restricts inputs to be strings or integers.
   * (The commented out lines would allow the inputs to also be boolean, null,
   * undefined, or NaN, but that isn't quite ready yet.)
   * <p>
   * Also, the helper variables symInt* and symStr* are there because CVC3 isn't
   * good at giving useful concrete values for inductive data types. Making the
   * actual integer or string explicit makes it easier to read values out of
   * CVC3's countermodels (but strings still cause problems).
   */
  private void createSymbolicInput(int i) {
    Expr symVar = varExpr("sym" + i, jsType);
    Expr symInt = varExpr("symInt" + i, intType);
    Expr symStr = varExpr("symStr" + i, stringType);
    context.assertFormula(
        context.orExpr(ImmutableList.of(
//              context.funExpr(lookupOp("is_js_true"), symVar),
//              context.funExpr(lookupOp("is_js_false"), symVar),
//              context.funExpr(lookupOp("is_js_null"), symVar),
//              context.funExpr(lookupOp("is_js_undefined"), symVar),
//              context.funExpr(lookupOp("is_js_NaN"), symVar),
            context.eqExpr(symVar, construct("js_num", symInt)),
            context.eqExpr(symVar, construct("js_string", symStr))
        )));
  }

  /** Make an Expr from a datatype constructor */
  public Expr construct(String constructor, Expr... args) {
    return context.datatypeConsExpr(constructor, ImmutableList.copyOf(args));
  }

  /**
   * @param numSymbols How many symbolic values to create
   * @param loader A FileLoader to use to locate the file containing the CVC3
   *        definitions of JavaScript operators
   * @return a wrapper around a new CVC3 ValidityChecker, initialized with the
   *         JavaScript operator definitions and symbolic arguments
   */
  public static Cvc3Context create(int numSymbols, FileLoader loader) {
    return new Cvc3Context(numSymbols, loader);
  }

  /** Return the CVC3 variable with the given name */
  public Expr lookupVar(String name) {
    return context.exprFromString(name);
  }

  /** Return the CVC3 operation with the given name */
  public Op lookupOp(String opString) {
    // ValidityChecker has a lookupOp method, but it only finds uninterpreted
    // functions, not defined functions, so we need to work around that.
    return context.exprFromString(opString).mkOp();
  }

  /** Create a variable with a given name and type. */
  public Expr varExpr(String name, Type type) {
    return context.varExpr(name, type);
  }

  /**
   * @param opString A string representing the operation
   * @param exprs The arguments to the operation
   * @return An Expr representing applying the operator to the arguments
   */
  public Expr funExpr(String opString, Expr... exprs) {
    return context.funExpr(lookupOp(opString), ImmutableList.copyOf(exprs));
  }

  /**
   * @param opString A string representing the operation
   * @param args The arguments to the operation
   * @return an {@link Expr} representing apply opString to args.
   * @throws RuntimeException if opString is not a defined function, or if any
   *         element of args contains an undefined symbol.
   */
  public Expr funExpr(String opString, SymbolicExpression[] args) {
    Op op = lookupOp(opString);
    List<Expr> argList = Lists.newArrayListWithCapacity(args.length);
    for (SymbolicExpression arg : args) {
      argList.add(arg.toCvc3(this));
    }
    return context.funExpr(op, argList);
  }

  /** Puts the fact that Boolean(constraint) is true into the current context */
  public void assume(SymbolicExpression constraint) {
    context.assertFormula(toBoolean(constraint));
  }

  /**
   * Returns a CVC3 expression representing the fact that Boolean(constraint) is
   * true.
   */
  private Expr toBoolean(SymbolicExpression constraint) {
    return context.funExpr(lookupOp("toBoolean"), constraint.toCvc3(this));
  }

  /**
   * Checks if the constraint is valid (i.e. if Boolean(constraint)
   * <em>must</em> be true) in the current context.
   *
   * @return null if the query is VALID; or, if the query is INVALID, a
   *         Map<String, JsValue> from variables to values that makes the query
   *         false.
   */
  public Map<String, JsValue> query(SymbolicExpression constraint) {
    context.push();
    QueryResult queryResult = context.query(toBoolean(constraint));
    if (queryResult == QueryResult.VALID) {
      context.pop();
      return null;
    } else if (queryResult == QueryResult.INVALID) {
      HashMap<Expr, Expr> model = getConcreteModel();
      HashMap<String, JsValue> myModel =
        Maps.newHashMapWithExpectedSize(numSymbols);
      for (int i = 0; i < numSymbols; ++i) {
        String varName = "sym" + i;
        myModel.put(varName, exprToJsValue(lookupVar(varName), model));
      }
      context.pop();
      return myModel;
    }
    // Throw an exception unless CVC3 returns VALID or INVALID.
    throw new RuntimeException("CVC3 returned " + queryResult);
  }

  /** Returns a map from Exprs to Exprs that falsify the current assumptions. */
  @SuppressWarnings("unchecked")
  private HashMap<Expr, Expr> getConcreteModel() {
    return context.getConcreteModel();
  }

  /** Returns the CVC3 Expr js_num(n):JSType */
  public Expr jsNum(int n) {
    return construct("js_num", context.ratExpr(n));
  }

  /** Return the CVC3 Expr n:INT */
  public Expr ratExpr(int n){
    return context.ratExpr(n);
  }

  /** Save the current state of the solver */
  public void push() {
    context.push();
  }

  /** Revert to the last state of the solver that was stored by push() */
  public void pop() {
    context.pop();
  }

  /** A hash table of all string constants that have been created. */
  private final HashMap<String, Expr> stringConstants = Maps.newHashMap();

  /** Gets/creates a CVC3 String constant whose value is the given string. */
  public Expr stringConstant(String string) {
    Expr stringVar = stringConstants.get(string);
    if (stringVar != null) {
      return stringVar;
    }
    assert !stringConstants.containsKey(string) :
      "Duplicate string constant: " + string;
    // Construct the CVC3 string value. We have to build up the string from the
    // end to the beginning.
    stringVar = construct("char_nil");
    for (int i = string.length(); i > 0;) {
      --i;
      stringVar = construct("char_cons",
          context.ratExpr(string.charAt(i)), stringVar);
    }
    stringVar = context.varExpr("strConst_" + string, stringType, stringVar);
    stringConstants.put(string, stringVar);
    return stringVar;
  }

  // TODO(elnatan): These next three methods are very similar. Can the common
  // pieces be refactored to avoid duplication?

  /**
   * Converts a CVC3 expression into a JsValue.
   *
   * @param variable the name of the CVC3 variable whose value we want
   * @param model the concrete model, which mapping variables to values
   * @return the JsValue representing the variable's concrete value in the model
   */
  private JsValue exprToJsValue(Expr variable, Map<Expr, Expr> model) {
    Expr value = model.get(variable);
    if (value == null) {
      throw new RuntimeException("Variable maps to null: " + variable);
    } else if (value.isRational()) {
      return JsDouble.create(constIntExprToInt(value));
    } else if (value.equals(lookupOp("js_true").getExpr())) {
      return JsBool.create(true);
    } else if (value.equals(lookupOp("js_false").getExpr())) {
      return JsBool.create(false);
    } else if (value.equals(lookupOp("js_null").getExpr())) {
      return JsNull.INSTANCE;
    } else if (value.equals(lookupOp("js_undefined").getExpr())) {
      return JsUndefined.INSTANCE;
    } else if (value.equals(lookupOp("js_NaN").getExpr())) {
      return JsDouble.create(Double.NaN);
    } else if (value.isApply()) {
      Op operator = value.getOp();
      if (operator.equals(lookupOp("js_num"))) {
        return JsDouble.create(exprToJsNum(value.getChild(0), model));
      } else if (operator.equals(lookupOp("js_string"))) {
        return JsString.create(exprToJsString(value.getChild(0), model));
      }
    } else if (value.isVar()) {
      throw new RuntimeException("Variable maps to variable: " + variable +
          " -> " + value);
    }
    throw new RuntimeException("Unexpected value: " + variable + " -> " +
        value);
  }

  /** Gets the int that a CVC3 Expr maps to in a model. */
  private int exprToJsNum(Expr expr, Map<Expr, Expr> model) {
    // Keep track of the variables we've seen to detect cycles (and prevent this
    // from being an infinite loop)
    List<Expr> varsAlreadySeen = Lists.newArrayList();
    while (true) {
      if (expr == null) {
        throw new RuntimeException("Variable maps to null: " + varsAlreadySeen);
      } else if (expr.isRational()) {
        return constIntExprToInt(expr);
      } else if (expr.isVar()) {
        if (varsAlreadySeen.contains(expr)) {
          throw new RuntimeException("cycle in model: " + varsAlreadySeen);
        }
        varsAlreadySeen.add(expr);
        expr = model.get(expr);
      } else {
        throw new RuntimeException(expr + " was supposed to be an int");
      }
    }
  }

  /** Gets the string that a CVC3 Expr maps to in a model. */
  private String exprToJsString(Expr expr, Map<Expr, Expr> model) {
    // Keep track of the variables we've seen to detect cycles (and prevent this
    // from being an infinite loop)
    List<Expr> varsAlreadySeen = Lists.newArrayList();
    StringBuilder result = new StringBuilder();
    Op charCons = lookupOp("char_cons");
    Expr charNil = lookupOp("char_nil").getExpr();
    while (true) {
      if (expr == null) {
        throw new RuntimeException("Variable maps to null: " + varsAlreadySeen);
      } else if (expr.equals(charNil)) {
        return result.toString();
      } else if (expr.getOp().equals(charCons)) {
        result.append((char) constIntExprToInt(expr.getChild(0)));
        expr = expr.getChild(1);
      } else if (expr.isVar()) {
        if (varsAlreadySeen.contains(expr)) {
          throw new RuntimeException("cycle in model: " + varsAlreadySeen);
        }
        varsAlreadySeen.add(expr);
        expr = model.get(expr);
      } else {
        throw new RuntimeException(expr + " was supposed to be a string");
      }
    }
  }

  /** Convert a constant integer Expr to an int */
  private int constIntExprToInt(Expr value) {
    if (!value.getRational().isInteger()) {
      throw new RuntimeException(value + " is not an integer in rationalToInt");
    }
    return value.getRational().getInteger();
  }
}
