# Owning things: `^`, `inplace`, and your second type error

Atli v0.2.0 spends the `Q = {0,1,ω}` semiring on unique array handles. A `^Array` may be consumed once by `move`, by `inplace`, by passing to a unique parameter, or by being forgotten at shared type. The payoff is visible native code: an accepted `inplace set` lowers to a store, not an allocation.

The original pitch shape is now a real example:

```zig
{{#include ../../../examples/render.atli:2:}}
```

The functional and in-place versions compute the same value, but native allocation counters differ:

```zig
{{#include ../../../examples/copy_vs_inplace.atli:2:}}
```

Misusing ownership is a type error with two source locations. `use_after_move.atli` consumes `a` at the `move`, then points at the later reuse:

```zig
{{#include ../../../examples/use_after_move.atli:2:}}
```

The checker rejects shared in-place mutation too:

```zig
{{#include ../../../examples/inplace_on_shared.atli:2:}}
```

The oracle always uses copy semantics for arrays. The native backend may mutate only after the surface uniqueness pass has made the aliasing bug unrepresentable for checked programs.
