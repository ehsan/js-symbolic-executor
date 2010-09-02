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

function add(x, y) {
  return x + y;
}

function sub(x, y) {
  return x - y;
}

function compare(x, y) {
  if (x > y) {
    return 1;
  }
  if (x < y) {
    return -1;
  }
  return 0;
}

function outOfRange(input, target, tolerance) {
  if (input > target + tolerance || input < target - tolerance) {
    return true;
  }
  return false;
}

function adjust(input, goal) {
  while (1) {
    var tmp;
    tmp = outOfRange(input, goal, 4);
    if (!tmp) { break; }
    var tmp0;
    tmp0 = compare(input, goal);
    if (tmp0 < 1) {
      input = add(input, 1);
    }
    else {
      input = sub(input, 1);
    }
  }
  return input;
}

var f = adjust;
