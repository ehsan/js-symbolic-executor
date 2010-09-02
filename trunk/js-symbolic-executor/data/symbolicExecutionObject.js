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

// This is a library of functions which are called by code instrumented by the
// symbolic execution instrumentation compiler pass.

var symbolicExecution =
(function() {
  var memory,
  memoryStack = [],
  pathCondition = [],
  returnValue,
  Operation = function(symbol, args) {
    return {
      getSymbol: function() {
        return symbol;
      },
      getArg: function(n) {
        return args[n];
      },
      arity: function() {
        return args.length;
      }
    };
  },
  SymbolicValue = function(a) {
    return {
      symbolicValue: 'sym' + a
    };
  },
  unop = function(symbol, a) {
    return new Operation(symbol, [a]);
  },
  binop = function(symbol, a, b) {
    return new Operation(symbol, [a, b]);
  },
  // Define push here so execute can call it.
  push = function(args) {
    memory = args;
    memoryStack.push(memory);
  };
  return {
    execute: function(obj, func, args) {
      var symbolicArgs = [];
      for (var i in args) {
        symbolicArgs[i] = new SymbolicValue(i);
      }
      push(symbolicArgs);
      var result = func.apply(obj, args);
      return { result: result,
               //memory: memory,
               pathCondition: pathCondition
             };
    },
    write: function(name, val) {
      memory[name] = val;
    },
    read: function(name) {
      return memory[name];
    },
    push: push,
    pop: function() {
      memoryStack.pop();
      memory = memoryStack[memoryStack.length - 1];
    },
    addCondition: function(condition) {
      pathCondition.push(condition);
    },
    setReturnValue: function(value) {
      returnValue = value;
    },
    getReturnValue: function() {
      return returnValue;
    },
    SHEQ: function(a, b) {
      return binop('jseq', a, b);
    },
    LE: function(a, b) {
      return binop('jsle', a, b);
    },
    LT: function(a, b) {
      return binop('jslt', a, b);
    },
    GE: function(a, b) {
      return binop('jsge', a, b);
    },
    GT: function(a, b) {
      return binop('jsgt', a, b);
    },
    ADD: function(a, b) {
      return binop('jsplus', a, b);
    },
    SUB: function(a, b) {
      return binop('jsminus', a, b);
    },
    NEG: function(a) {
      return unop('jsneg', a);
    },
    NOT: function(a) {
      return unop('jsnot', a);
    },
    OR: function(a, b) {
      return binop('jsor', a, b);
    },
    AND: function(a, b) {
      return binop('jsand', a, b);
    },
    HOOK: function(guard, trueExp, falseExp) {
      return new Operation('jsite', [guard, trueExp, falseExp]);
    }
  };
})();
