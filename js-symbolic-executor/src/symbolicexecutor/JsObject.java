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

import cvc3.Expr;

import java.util.HashMap;

/**
 * A SymbolicExpression representing a JavaScript object.
 * @author elnatan@google.com (Elnatan Reisner)
 */
public class JsObject implements SymbolicExpression {
  /**
   * A hash table of all JsObjects that have been created. We will use this to
   * hash-cons all JsObjects.
   */
  private static final HashMap<Integer, JsObject> objects =
    new HashMap<Integer, JsObject>();

  /** Returns an object with the given id, creating one only if needed. */
  public static JsObject create(int id) {
    JsObject obj = objects.get(id);
    // We never put null into the table, so getting null means we need to create
    // an object with this id.
    if (obj == null) {
      obj = new JsObject(id);
      objects.put(id, obj);
    }
    return obj;
  }

  /** This object's ID number */
  private final int id;

  private JsObject(int id) {
    this.id = id;
  }

  /* (non-Javadoc)
   * @see SymbolicExpression#toCvc3(Cvc3Context)
   */
  @Override
  public Expr toCvc3(Cvc3Context context) {
    return context.construct("js_obj", context.ratExpr(id));
  }

  @Override
  public String toString() {
    return "obj" + id;
  }
}
