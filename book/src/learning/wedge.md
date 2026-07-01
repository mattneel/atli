# The wedge: your first type error

This program mentions the continuation `k` without resuming it:

```zig
{{#include ../../../examples/wedge.atli:3:}}
```

`atli check examples/wedge.atli` rejects it with a `Handle §4.7` extra-mention diagnostic. That error protects the lazy-capture theorem: on well-typed clauses, mentioning `k` is equivalent to exactly one direct resume.
