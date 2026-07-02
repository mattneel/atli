# Generics, and threading what you own

Atli v0.5.0 adds type parameters and the `^u` uniqueness-preservation marker. Generic functions compile once because tier-1 values are uniform i64 slots: a `Nat` immediate, an array handle, a record handle, a variant handle, or a task handle all occupy one slot.

The simple generic option example is a real test-covered source file:

```zig
{{#include ../../../examples/option.atli}}
```

The list example uses the same `map` symbol at more than one element type in one program. The current tier-1 higher-order fragment is pure and erased; effect-row variables remain a roadmap item.

```zig
{{#include ../../../examples/list_map.atli}}
```

The ownership lesson is the `through` helper. `^u A` means "preserve whatever grade the caller supplied." It lets a unique array flow through a helper and remain eligible for `inplace` afterwards:

```zig
{{#include ../../../examples/preserve.atli}}
```

Bare parameters are shared (`ω`). Passing a unique value to a bare helper forgets uniqueness, so a later `inplace` is rejected:

```zig
{{#include ../../../examples/forget.atli}}
```

And `^u` does not grant privileges inside the helper. A preserving parameter may be threaded or returned, but it cannot be mutated unless the signature demands definite uniqueness (`^A`):

```zig
{{#include ../../../examples/inplace_on_preserving.atli}}
```
