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

import org.mozilla.javascript.NativeObject;

/**
 * An adapter to transform JavaScript objects to {@link JsObject}s.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 */
final class JsObjectAdapter implements SymbolicExpressionAdapter {
  // Singleton class
  private JsObjectAdapter() {}
  public static final JsObjectAdapter ADAPTER =
    new JsObjectAdapter();

  /* (non-Javadoc)
   * @see SymbolicExpressionAdapter#fromJS(Object, AdapterList)
   */
  @Override
  public JsObject fromJS(Object obj, AdapterList adapters) {
    if (obj instanceof NativeObject) {
      final NativeObject nativeObj = (NativeObject) obj;
      if (nativeObj.has("location", nativeObj)) {
        assert nativeObj.getIds().length == 1 :
          "Object has fields other than location: " + nativeObj.getIds();
        int id = ((Double) nativeObj.get("location", nativeObj)).intValue();
        return JsObject.create(id);
      }
//      for (Object id : ((NativeObject) value).getIds()) {
//        
//      }
    }
    return null;
  }
}
