# Surface-to-core elaboration (Sprint 05)

This document records the implemented subset mapping from `docs/syntax.md` to the reduced
core in `docs/calculus.md §10`.

- Top-level functions are elaborated into nested core `let` bindings ending in `main`'s
  body. Earlier declarations are available to later declarations; the core has no global
  namespace, so the file is closed by lexical `let` nesting.
- Surface functions with multiple parameters are curried: `f(a, b)` elaborates uniformly
  as `(f a) b`, matching `syntax.md §5`'s pipe rule and the unary core arrow.
- Recursive unary `Nat -> ...` functions elaborate to core `fix`; the boundedness slot
  chooses `Structural` (absent), `Measure` (`measure e`, parsed and conservatively
  accepted only when `e` is a Nat literal or parameter name), or `Div` (`div`) per
  `syntax.md §8`.
- Decimal Nat literals elaborate to unary `zero`/`succ` chains (`docs/calculus.md §3.2`).
- `case n { 0 -> e0 ; p -> e1 }` is the surface Nat eliminator: the second arm's name
  binds the predecessor, so it elaborates to `TCaseNat n e0 p e1`. This is the concrete
  Sprint 05 reading of `syntax.md §5` for the reduced core.
- The only supported effect declaration is `effect L { op(x: Nat) -> Nat }`, which fixes
  the single reduced-core label `ℓ` (`docs/calculus.md §10`). `L.op(e)` elaborates to
  `perform ℓ e`.
- Handlers map directly to deep core handlers. `L.op(p), k -> k(v)` elaborates `k(v)` to
  core `resume`; `L.op(p), _ -> e` drops the continuation. Mention-without-resume is
  intentionally allowed through parsing/elaboration and rejected by `check::check` under
  `docs/calculus.md §4.7`.
- Pipe desugaring follows `syntax.md §5`: `x |> f(a)` becomes `f(x, a)`, then currying
  maps that to `(f x) a`.
- Unsupported settled-but-out-of-reduced-core constructs (`^`, records, variants,
  `inplace`, `move`, `freeze`, `spawn`, `scope`, `if`, type parameters, strings/chars/
  floats, `use`/modules, multiple effect labels) diagnose as "not yet in the reduced
  surface" rather than silently elaborating.
