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
  memoryStack = [], // This currently only handles local variables (no scope chains or globals)
  pathCondition = [],
  emptyObject = {},
  heap = [],
  returnValue,
  locationId = 0,
  SymbolicOperation = function(symbol, args) {
    this.getSymbol = function() {
      return symbol;
    };
    this.getArg = function(n) {
      return args[n];
    };
    this.arity = function() {
      return args.length;
    };
  },
  SymbolicValue = function(a) {
    this.symbolicValue = 'sym' + a;
  },
  Location = function(arguments) {
    this.location = locationId++;
  },
  op1 = function(symbol, a) {
    return new SymbolicOperation(symbol, [a]);
  },
  op2 = function(symbol, a, b) {
    return new SymbolicOperation(symbol, [a, b]);
  },
  op3 = function(symbol, a, b, c) {
    return new SymbolicOperation(symbol, [a, b, c]);
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
      pathCondition.push([condition, heap.length]);
    },
    setReturnValue: function(value) {
      returnValue = value;
    },
    getReturnValue: function() {
      return returnValue;
    },
    createObject: function() {
      var newLocation = new Location();
      var newObject = emptyObject;
      // Note that this for loop converts all property names to strings, and
      // overwrites duplicate property names with the last such value given.
      // This behavior is correct; see ECMA-262, Ed. 3, 11.1.5.
      for (var i = 0; i < arguments.length; i += 2) {
        newObject = op3('jssetProp', newObject, String(arguments[i]),
                              arguments[i+1]);
      }
      heap.push([newLocation, newObject]);
      return newLocation;
    },
    SHEQ: function(a, b) {
      return op2('jseq', a, b);
    },
    LE: function(a, b) {
      return op2('jsle', a, b);
    },
    LT: function(a, b) {
      return op2('jslt', a, b);
    },
    GE: function(a, b) {
      return op2('jsge', a, b);
    },
    GT: function(a, b) {
      return op2('jsgt', a, b);
    },
    ADD: function(a, b) {
      return op2('jsplus', a, b);
    },
    SUB: function(a, b) {
      return op2('jsminus', a, b);
    },
    NEG: function(a) {
      return op1('jsneg', a);
    },
    NOT: function(a) {
      return op1('jsnot', a);
    },
    OR: function(a, b) {
      return op2('jsor', a, b);
    },
    AND: function(a, b) {
      return op2('jsand', a, b);
    },
    HOOK: function(guard, trueExp, falseExp) {
      return op3('jsite', guard, trueExp, falseExp);
    },
    GETPROP: function(base, property) {
      return op2('jsgetProp', base, property);
    }
  };
})();
