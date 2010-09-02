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

import org.mozilla.javascript.Context;
import org.mozilla.javascript.ContextAction;
import org.mozilla.javascript.ContextFactory;
import org.mozilla.javascript.ScriptableObject;
import org.mozilla.javascript.Wrapper;

/**
 * A test case to see what types Rhino considers various JavaScript objects to
 * have.
 *
 * @author corysmith@google.com (Cory Smith)
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
public class RhinoTest extends TestCase {
  private final class ContextEval implements ContextAction {
    private final String code;

    public ContextEval(String code) {
      this.code = code;
    }

    @Override
    public Object run(Context cx) {
      ScriptableObject scope = cx.initStandardObjects();
      return cx.evaluateString(scope, code, "<no path>", 0, null);
    }
  }

  public void testReturns() throws Exception {
    ContextFactory contextFactory = ContextFactory.getGlobal();
    
    
    evalJs(contextFactory, "'foo';");
    evalJs(contextFactory, "'\u0fff'");
    evalJs(contextFactory, "'\\u0fff'");
    evalJs(contextFactory, "new java.util.ArrayList();");
    evalJs(contextFactory, "[];");
    evalJs(contextFactory, "0");
    evalJs(contextFactory, "1;");
    evalJs(contextFactory, "2");
    evalJs(contextFactory, "0/0");
    evalJs(contextFactory, "1/0");
    evalJs(contextFactory, Integer.toString(Integer.MAX_VALUE));
    evalJs(contextFactory, Long.toString(Integer.MAX_VALUE + (long) 1));
    evalJs(contextFactory, "this.bar;");
    evalJs(contextFactory, "null;");
    evalJs(contextFactory, "zub = {};");
    evalJs(contextFactory, "reb = function (){};");
    evalJs(contextFactory, "new Error();");
    evalJs(contextFactory, "/.*/;");
    evalJs(contextFactory, "true");
    evalJs(contextFactory, "new Date();");
    evalJs(contextFactory, "this;");
    evalJs(contextFactory, "var foo = 1.0; this.foo;");
    evalJs(contextFactory,
        "var foo = {}; (function bar() {var f = 1;}).call(foo);");
  }

  private Object evalJs(ContextFactory contextFactory, String code) {
    Object result = contextFactory.call(new ContextEval(code));
    System.out.println(code);
    System.out.println("\t" + (result != null ? result.getClass() : null));
    System.out.println("\tis Wrapper: " + (result instanceof Wrapper));
    System.out.println("\t" + result);
    return result;
  }
}
