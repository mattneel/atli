# Atli spec gaps surfaced by executable sprints

This file records `SPEC-GAP:` findings exposed while turning the calculus into executable
Rust. The implementation chooses conservative interpretations and does not silently expand
semantics.

- SPEC-GAP(frame-metric-byte-accuracy): `docs/calculus.md §8.4` states that finite `β`
  bounds continuation-frame bytes, but Sprint 01/Sprint 02 have no byte layout, ABI, or
  frame-field sizing rules. The interpreter therefore uses an executable proxy metric:
  the number of captured evaluation-context frames in a handled operation continuation.
  Property tests check that this realized frame count never exceeds generated witness `β`;
  this is an empirical conformance check, not a byte-accurate backend allocation proof.
  Sprint 04's Rocq scaffold deliberately does not state `L7` as a theorem yet: the
  instrumented frame-counting step relation is missing. When added, it should target this
  same frame-count proxy; a byte-accurate theorem remains a future backend/layout
  refinement.

- SPEC-GAP(measure-tag-trusted-reduced-core): Sprint 03 accepts `Measure`-tagged `fix`
  terms as the annotated recursion rung but does not verify an actual well-founded
  measure. This is intentional for the reduced core: `docs/calculus.md §4.8/§7` keeps the
  solver architecture real while deferring real measure obligations to the future surface
  checker/elaborator. Sprint 04's `Typing.v` mirrors that trust boundary with a rule comment
  rather than adding an unproven measure checker to the mechanized core.

- SPEC-GAP(frame-metric-recursion-blindspot): the substitution-based reference interpreter
  reifies continuation frames only when a handler captures an operation context
  (`interp::decompose` → `alloc_continuation`). Pure recursion does not allocate an
  observable frame in `max_frame`, even though `docs/calculus.md §8.4` is about all
  continuation frames. Sprint 02 therefore checks handler-capture boundedness with
  `max_frame ≤ β` and checks the recursion half through the separate termination split:
  derived `Terminates` terms must reach `Value` within budget, while derived `Div` terms
  must exhaust the budget. This is honest differential coverage, not a complete frame
  layout model for recursion.

## Resolved gaps

- RESOLVED(handler-k-usage-discipline): `docs/calculus.md §4.7` now makes option (i)
  explicit: a handler clause may drop `k` only by not mentioning it, and if `k` appears
  free then the clause must contain exactly one direct `resume k v` and no other free
  occurrence of `k`. Thus `k ∈ FV(eᵢ) ⇔ eᵢ` resumes `k` for well-typed clauses, licensing
  the interpreter's lazy-capture FV dispatch while requiring the future checker to reject
  mention-without-resume wedges such as `let z = k in e`.

- RESOLVED(handler-drop-captured-frame-accounting): `docs/calculus.md §4.7` and §5 now use
  lazy continuation capture. A dropped operation clause (`k ∉ FV(eᵢ)`) reduces by
  `H-op-drop` without materializing the delimited continuation frame, so its effective
  `β̂ᵢ` is exactly the clause body's `βᵢ`. A resuming clause uses `H-op-resume`,
  materializes the one-shot continuation, and pays `βᵢ ⊕ β`. This preserves the
  exception/default-handler idiom where dropping is frame-free.

- RESOLVED(nat-structural-recursion-core): `docs/calculus.md` now includes unary `zero` /
  `succ e` naturals and `case e { zero => e₀ ; succ x => e₁ }`. The predecessor `x` in
  the `succ` branch is the strict subterm used by structural `Fix`; `gen.rs` derives
  finite `β` for recursive calls on that predecessor and `ω` for non-strict structural
  recursion.

- SPEC-GAP(surface-arithmetic-reduced-core-gap): `docs/syntax.md §1/§4/§5` includes
  arithmetic operators and uses real Fibonacci-style arithmetic in examples, but the
  Sprint 05 reduced core has only unary `Nat`, `succ`, and `case` and no primitive
  addition/subtraction/multiplication. The Sprint 05 parser diagnoses arithmetic tokens
  as not yet in the reduced surface; `examples/fib.atli` is therefore a structural Nat
  recursion seed (`fib(0) = 0`) rather than a full Fibonacci implementation. A later
  surface/core extension must decide whether arithmetic is primitive, elaborated to
  library recursion, or introduced through a standard prelude.

- SPEC-GAP(surface-measure-typecheck-without-surface-checker): `docs/syntax.md §8` says
  the `measure e` expression should be meaningful at type `Nat`, but Sprint 05 still has
  no surface type checker. The elaborator conservatively accepts only a Nat literal or the
  unary Nat parameter as a measure expression before trusting the existing reduced-core
  `Measure` tag (`SPEC-GAP(measure-tag-trusted-reduced-core)`).
