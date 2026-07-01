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

- SPEC-GAP(nat-structural-recursion-core): `docs/calculus.md §10` includes `Nat` and
  `Fix`, but the reduced term grammar in `docs/calculus.md §3.2` has no eliminator such
  as `if0`/case/predecessor/arithmetic for expressing genuine structural recursion on
  `Nat`. Sprint 01 golden/generated “structural fix” cases therefore exercise the `Fix`
  unfolding rule with terminating bodies and tag the witness as structural; real
  structural descent needs a future core eliminator or an explicit generation rule.
