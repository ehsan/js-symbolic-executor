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

/**
 * Wrapper around a function that transforms JavaScript objects into
 * {@link SymbolicExpression}s. This includes not just JavaScript 'object's in
 * the strict sense, but also arrays, strings, numbers, etc.
 *
 * @author elnatan@google.com (Elnatan Reisner)
 *
 */
interface SymbolicExpressionAdapter {
  /**
   * @param obj A JavaScript object
   * @param adapters How to (recursively) transform components of obj into
   *        {@link SymbolicExpression}s. This argument is ignored by base
   *        values, but it is used by {@link SymbolicOperationAdapter}.
   * @return a {@link SymbolicExpression} representing the object, or null if
   *         the object could not be converted by the adapter
   */
  SymbolicExpression fromJS(Object obj, AdapterList adapters);
}
