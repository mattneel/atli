# Atli spec gaps surfaced by Sprint 01

This file records `SPEC-GAP:` findings exposed while turning the calculus into executable
Rust. The implementation chooses conservative interpretations and does not silently expand
semantics.

- SPEC-GAP(frame-metric-byte-accuracy): `docs/calculus.md §8.4` states that finite `β`
  bounds continuation-frame bytes, but Sprint 01 has no byte layout, ABI, or frame-field
  sizing rules. The interpreter therefore uses an executable proxy metric: the number of
  captured evaluation-context frames in a handled operation continuation. Property tests
  check that this realized frame count never exceeds generated witness `β`; this is an
  empirical conformance check, not a byte-accurate backend allocation proof.

## Resolved gaps

- RESOLVED(nat-structural-recursion-core): `docs/calculus.md` now includes unary `zero` /
  `succ e` naturals and `case e { zero => e₀ ; succ x => e₁ }`. The predecessor `x` in
  the `succ` branch is the strict subterm used by structural `Fix`; `gen.rs` derives
  finite `β` for recursive calls on that predecessor and `ω` for non-strict structural
  recursion.
