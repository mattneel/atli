# Effects and handlers

Handlers have two idioms. A resuming handler spends the one-shot continuation:

```zig
{{#include ../../../examples/counter.atli:3:}}
```

A dropped handler abandons the continuation and behaves like an exception/default path:

```zig
{{#include ../../../examples/default_handler.atli:3:}}
```

The native backend compiles both through the runtime handler-scope stack. The drop path allocates no continuation frame; the resume path restores exactly one continuation.
