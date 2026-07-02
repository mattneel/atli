# Elaboration mapping

The surface-to-core mapping is specified in [`docs/elaboration.md`](../../docs/elaboration.md). Important mappings include decimal `Nat` to unary core constructors, arithmetic operators to injected prelude recursion, top-level SCCs to `fix*`, and handlers to the amended core handler rule.


## v0.3.0 structured data

Records and variants are implemented in v0.3.0. Normative syntax and lowering remain in `docs/syntax.md`, `docs/elaboration.md`, and `docs/calculus.md`; this Book chapter links the live examples rather than restating the rules.


## v0.4.1 tasks

Structured concurrency is implemented with `scope { ... }`, `spawn f(args)`, and `await h`. The callee must be a declared top-level function and effect-closed; task handles are affine and scope-local. See `docs/syntax.md §9` and `docs/elaboration.md` for normative details.
