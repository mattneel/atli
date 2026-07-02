# Tasks: the tree of arenas

Atli v0.4.0 turns `scope`, `spawn`, and `await` on. A `scope` owns a task group and a region; every `spawn` inside attaches to the nearest scope, and scope exit joins any dropped handles before freeing the region.

The small fan-out example is a real checked sample:

```zig
{{#include ../../../examples/fanout.atli}}
```

Native execution may use OS threads, but accepted programs remain schedule-independent: a task receives only values consumed at the spawn site, and unique heap data can cross the boundary only by `move`. Racing requires two aliases to mutable data; that is exactly what the checker rejects.

The courier example pays `move`'s IOU. A unique mailbox is moved into a task, destructured there, mutated in place, and awaited:

```zig
{{#include ../../../examples/courier.atli}}
```

The spawn boundary performs no functional copy of the mailbox. The child receives a handle into an enclosing region, and `await` copies heap results back only when a task returns heap data. Primitive `Nat` results return directly.

Your third task-shaped type error is using one unique value as if two tasks could own it:

```zig
{{#include ../../../examples/unique_to_two_spawns.atli}}
```

The diagnostic names the second spawn-site use after the first consumed the value. The race falsifier in the test suite bypasses that check and shows why the rule exists: native execution diverges from the copy oracle and produces nondeterministic outputs across repeated runs.
