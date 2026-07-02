# Surface subset

The implemented surface is specified in [`docs/syntax.md`](../../docs/syntax.md). The Book narrates; `docs/` specifies. v0.4.0 includes `Nat`, `Unit`, `Array`, records, variants, `^` uniqueness, `move`/`inplace`/`freeze`, functions, `case`, `measure`/`div`, multi-label effects, handlers, arithmetic prelude operators, mutual top-level recursion, and `scope`/`spawn`/`await`.


## v0.3.0 structured data

Records and variants are implemented in v0.3.0. Normative syntax and lowering remain in `docs/syntax.md`, `docs/elaboration.md`, and `docs/calculus.md`; this Book chapter links the live examples rather than restating the rules.


## v0.4.0 tasks

Structured concurrency is implemented with `scope { ... }`, `spawn f(args)`, and `await h`. The callee must be a declared top-level function and effect-closed; task handles are affine and scope-local. See `docs/syntax.md §9` and `docs/elaboration.md` for normative details.
