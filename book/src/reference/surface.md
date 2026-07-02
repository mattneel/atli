# Surface subset

The implemented surface is specified in [`docs/syntax.md`](../../docs/syntax.md). The Book narrates; `docs/` specifies. v0.5.1 includes `Nat`, `Unit`, `Array`, records, variants, `^` uniqueness, `move`/`inplace`/`freeze`, functions, `case`, `measure`/`div`, multi-label effects, handlers, arithmetic prelude operators, mutual top-level recursion, `scope`/`spawn`/`await`, type parameters, generic `Array[A]`/records/variants/functions, and `^u` preservation.


## v0.3.0 structured data

Records and variants are implemented in v0.3.0. Normative syntax and lowering remain in `docs/syntax.md`, `docs/elaboration.md`, and `docs/calculus.md`; this Book chapter links the live examples rather than restating the rules.


## v0.4.1 tasks

Structured concurrency is implemented with `scope { ... }`, `spawn f(args)`, and `await h`. The callee must be a declared top-level function and effect-closed; task handles are affine and scope-local. See `docs/syntax.md §9` and `docs/elaboration.md` for normative details.


## v0.5.1 generics

`fn f[A](...)`, `type Option[A] = ...`, `Array[A]`, `Task[T]`, and `^u A` are implemented. `^u` preserves a caller-supplied uniqueness grade but grants no mutation privilege inside the generic body. Effect-row variables stay open; see ROADMAP for `map[A, B](xs: List[A], f: A -> B ! e) -> List[B] ! e`.
