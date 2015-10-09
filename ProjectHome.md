js-symbolic-executor is a symbolic executor for JavaScript. It's primary use is to automatically generate test inputs for JavaScript programs.

js-symbolic-executor makes use of [Closure Compiler](http://code.google.com/closure/compiler) to instrument JavaScript code so that running the code also gathers constraints that describe why the program took the particular path it did on that input. Then, js-symbolic-executor translates these constraints into a form that can be digested by [CVC3](http://www.cs.nyu.edu/acsys/cvc3/), an SMT solver. CVC3 responds with a result that js-symbolic-executor uses to generate a new set of inputs that will cause the JavaScript program to exercise new paths. This can be repeated until all paths are explored, or until some given number of tests have been generated.

For more information, see the [README](http://code.google.com/p/js-symbolic-executor/source/browse/trunk/README).

Also, here is a short [presentation](https://docs.google.com/present/view?id=dc3xj967_5hqfknfd5) which illustrates how js-symbolic-executor works.