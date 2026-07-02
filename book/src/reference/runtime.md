# Runtime contracts

Native execution reports `ATLI_HIGH_WATER=<n> ATLI_BETA=<m> ATLI_DATA_ALLOCS=<k>` on stderr. Trap exit 86 means certified arena overflow. Trap exit 87 means a debug one-shot violation. Trap exit 88 means `ATLI BOUNDS` for array bounds or runtime scope bounds. `ATLI_DATA_ALLOCS` counts data-region array creations/copies; accepted `inplace set` sites do not increment it. `ATLI_TASKS_SPAWNED` counts task spawns in native execution, and debug `ATLI_TASK_TIDS` reports the distinct pthread IDs observed by the runtime. `ATLI_MAX_ITERS` bounds the growable `div` path in tests. `ATLI_FORCE_DYNAMIC_DISPATCH=1` disables lexical handler fast paths and forces the runtime handler-scope stack.


## v0.3.0 structured data

Records and variants are implemented in v0.3.0. Normative syntax and lowering remain in `docs/syntax.md`, `docs/elaboration.md`, and `docs/calculus.md`; this Book chapter links the live examples rather than restating the rules.


## v0.4.1 tasks

`scope` owns a task group and joins children at exit. `spawn f(args)` records a task creation and evaluates arguments in the parent before transfer. `await h` consumes an affine task handle. Normative region-tree rules live in `docs/calculus.md §9.3`; examples are covered by `atli test examples/`.
