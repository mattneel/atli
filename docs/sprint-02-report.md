# Sprint 02 report: compositional generator and differential boundedness harness

## Plan and design

- Replaced the Sprint 01 eight-shape catalog with a type-directed recursive generator over
  explicit choice bytes. Shrinking shrinks the choices; every shrunk choice sequence
  regenerates a closed term and re-runs `gen::derive_witness`, so witness metadata is
  never stale.
- Generation invariant: every generated safe term is closed, well-typed at its target type
  according to the reduced `docs/calculus.md §4` rules, and every continuation variable is
  used at most once. Negative top-level `perform ℓ` cases are explicitly tagged as
  detection fixtures rather than safe terms.
- Witnesses are derived-only: `gen::derive_witness` is the sole source of `β`, effects,
  divergence, continuation-use facts, and coverage tags.
- Extended distribution evidence beyond form coverage: depth histogram, nested-handler
  count, frame-positive count, tight boundedness hits, and strict/non-strict recursive
  call counts.
- Preserved Sprint 01 golden tests as fixed regression anchors.

## Implementation summary

- `src/gen.rs`: rewritten around compositional generation from choice sequences, with
  explicit `MAX_DEPTH = 5`, `MAX_CHOICES = 80`, `SAMPLE_SIZE = 1024`, and fixed seed
  `0xa7110002`.
- `src/props.rs`: rewritten as a differential harness: derive witness structurally,
  evaluate independently, compare progress/one-shot/determinism/discharge/boundedness and
  divergence behavior.
- `src/core.rs`: added generation metadata for expected negative outcomes and distribution
  facts.
- `docs/spec-gaps.md`: recorded the recursion-frame blind spot and the handler-drop
  captured-frame accounting tension.

## Acceptance table

Fixed seed: `0xa7110002`; sample size: `1024`; step budget: `96`.

| # | Criterion | Result | Evidence |
|---|---|---:|---|
| 1 | Progress (§8.1) | PASS | Safe generated terms are asserted `Value` or `Stepable` before evaluation. |
| 2 | One-shot soundness (§8.3) | PASS | Zero `StuckDoubleResume` outcomes across the sample. |
| 3 | Handler discharge + negative detection | PASS | Safe handled terms had zero `StuckUnhandledOperation`; 85 tagged top-level `perform ℓ` negatives did stick. |
| 4 | Determinism | PASS | Double evaluation normalized reports matched for every generated term. |
| 5 | Differential boundedness (§8.4) | PASS | All finite-`β` terms satisfied `max_frame ≤ β`; 305 cases had `max_frame > 0`. |
| 6 | Termination split | PASS | 758 evaluations reached `Value`; 181 derived-`Div` evaluations exhausted budget; zero misclassifications. |
| 7 | Tightness | PASS | 335 finite-bound cases had `max_frame == β`. |
| 8 | Coverage + distribution | PASS | All required form counters and distribution counters were nonzero; details below. |
| 9 | Regression | PASS | `cargo test --quiet` and `cargo test --test golden --quiet` pass. |

## Coverage and distribution

Form coverage counters over the fixed-seed sample:

- `LambdaApp`: 398
- `Let`: 554
- `FixStructural`: 292
- `FixMeasure`: 257
- `Perform`: 592
- `HandleResuming`: 360
- `HandleDropped`: 198

Distribution counters:

- Depth histogram: `{1: 34, 2: 32, 3: 38, 4: 136, 5: 184, 6: 135, 7: 101, 8: 113, 9: 123, 10: 85, 11: 30, 12: 12, 13: 1}`
- Nested handlers: 191
- Perform under captured context / `max_frame > 0`: 305
- Tight hits / `max_frame == β`: 335
- Strict recursive calls: 409
- Non-strict recursive calls: 544
- Negative unhandled-operation fixtures: 85

## Amendment note

After the lazy-capture calculus amendment, dropped handler clauses no longer materialize
the captured continuation frame. The fixed-seed distribution above was regenerated under
that amended `H-op-drop` / `H-op-resume` semantics; frame-positive cases remain well above
the ≥100 non-vacuity threshold.

## §8.4 interpretation note

Per `SPEC-GAP(frame-metric-recursion-blindspot)`, the interpreter's current `max_frame`
proxy observes handler-captured continuation frames, not pure recursion frames. Sprint 02
therefore witnesses the two halves separately: handler-capture boundedness through
`max_frame ≤ β`, and recursion boundedness through the derived termination split
(`Terminates` reaches `Value`, `Div` exhausts budget). This is explicit harness evidence,
not byte-accurate frame-layout proof.

## Verification commands

- `cargo fmt`
- `cargo test --quiet`

Final verification also ran through `just verify` and `just audit` before commit.
