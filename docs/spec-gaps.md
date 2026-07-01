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
