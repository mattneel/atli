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

- SPEC-GAP(handler-drop-captured-frame-accounting): `docs/calculus.md §4.7` defines a
  dropped handler clause's effective `β̂ᵢ` as the clause body `βᵢ`, while `docs/calculus.md
  §5` still captures the delimited context in `H-op` before the clause drops `k`. The
  Sprint 02 executable frame metric observes that capture allocation even for early-return
  handlers. The derived witness therefore conservatively includes the handled body's
  frame bound whenever a handled operation may be introduced, including dropped clauses.

## Resolved gaps

- RESOLVED(nat-structural-recursion-core): `docs/calculus.md` now includes unary `zero` /
  `succ e` naturals and `case e { zero => e₀ ; succ x => e₁ }`. The predecessor `x` in
  the `succ` branch is the strict subterm used by structural `Fix`; `gen.rs` derives
  finite `β` for recursive calls on that predecessor and `ω` for non-strict structural
  recursion.
