# Nat and Fibonacci

Atli v0.1.0's implemented values are unary `Nat`s surfaced as decimal literals. The tutorial Fibonacci program is a real source file, not copied prose:

```zig
{{#include ../../../examples/fib.atli:4:}}
```

The important lesson is the `measure n` annotation. The strict structural rule only accepts direct recursion on the predecessor bound by `case`; `fib(m - 1)` is a library call, not the peeled predecessor. Real Fibonacci therefore uses the trusted measure rung in v0.1.0.
