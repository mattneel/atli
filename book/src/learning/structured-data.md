# Structured data: records, variants, and taking things apart

Atli v0.3.0 adds nominal monomorphic records and variants. The flagship variant example
from the syntax document is a real checked and compiled program:

```zig
{{#include ../../../examples/shape_area.atli}}
```

Records can carry heap payloads. The safe way to take a unique heap payload out of a
record is **destructure-consume**: matching a unique aggregate consumes the aggregate
handle and transfers unique ownership of heap-typed fields to the pattern binders.
That is why this mailbox-shaped program can mutate the contained buffer and repack it:

```zig
{{#include ../../../examples/mailbox.atli}}
```

Functional record update copies the aggregate, while `inplace .{ r | field = e }` consumes
a unique record and lowers to one store:

```zig
{{#include ../../../examples/record_update_inplace.atli}}
```

Variants also give structural recursion its natural source of strict descent. `sum` over a
recursive list uses the tail bound by the `Cons` pattern, so it needs no `measure` annotation:

```zig
{{#include ../../../examples/natlist.atli}}
```

Misuses are rejected at the source. A unique record cannot expose a heap-typed field by
projection; destructure it instead:

```zig
{{#include ../../../examples/field_from_unique.atli}}
```

And once a unique aggregate is destructured, using the old aggregate handle again is the same
kind of error as use-after-move:

```zig
{{#include ../../../examples/use_after_destructure.atli}}
```
