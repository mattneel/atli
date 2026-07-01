# Sprint 01 report: executable core calculus

## Built

- Rust/Cargo scaffold with CI and `Justfile` command surface.
- `grade` module implementing `docs/calculus.md §2`:
  - uniqueness semiring `Q = {0,1,ω}`;
  - effect join-semilattice over the reduced one-operation label `ℓ`;
  - boundedness `Bound = ℕ ∪ {ω}` with `⊕` and `⊔`;
  - single-arena `Region` for `docs/calculus.md §10`.
- `core` module implementing the reduced AST/type/witness surface from `docs/calculus.md §3`/`§10`.
- `interp` module implementing a small-step CBV reference interpreter with comments tied to `docs/calculus.md §5` rules:
  - β, let, unfold;
  - deep `H-return` and `H-op`;
  - one-shot `resume` with detected double-resume stuck state;
  - step budget, rule trace, deterministic continuation-ID normalization, and max-frame instrumentation.
- `gen` module producing closed, well-typed-by-construction reduced-core terms with witness metadata.
- `props` module checking generated terms under a fixed seed.
- `docs/decisions/0001-host-language.md` selecting Rust.
- `docs/spec-gaps.md` recording executable-spec gaps.

## Out of scope preserved

No parser, type checker, MLIR/codegen, Rocq/Iris mechanization, or surface syntax implementation was added.

Audit command:

```text
just audit
Audit passed: no parser/typechecker/MLIR/surface changes detected.
```

## Generator run

- Fixed seed: `0xa7110001` (`gen::FIXED_SEED`).
- Sample size: `128` (`gen::SAMPLE_SIZE`).
- Step budget: `64` (`gen::STEP_BUDGET`).
- Shrinking: proptest shrinks the selector and regenerates the term+witness from the shrunk selector, so witness metadata stays aligned with the shrunk term.

Coverage counters from the fixed-seed sample:

| Required form | Count |
| --- | ---: |
| `λ`/app | 14 |
| `let` | 33 |
| `fix` structural | 11 |
| `fix` measure-tagged | 13 |
| `perform` | 35 |
| `handle` resuming clause | 18 |
| `handle` dropped clause | 17 |

All required counts are `> 0`.

## Acceptance criteria

| Criterion | Result | Evidence |
| --- | --- | --- |
| 1. Progress (`docs/calculus.md §8.1`) | PASS | `props::generated_terms_satisfy_acceptance_properties_with_fixed_seed` checks each generated closed term is a value or step-able before evaluation. |
| 2. One-shot soundness (`§8.3`) | PASS | Generated terms never produce `StuckDoubleResume`; golden negative `double_resume_is_detected_as_stuck` proves detection exists. |
| 3. Determinism | PASS | Property evaluates each generated term twice and compares normalized classification, final term/value, trace, and max frame. |
| 4. Boundedness soundness instrumentation (`§8.4`) | PASS for executable frame metric | For finite-β witnesses, property checks `max_frame <= β`. `SPEC-GAP(frame-metric-byte-accuracy)` records that this is a frame-count proxy, not byte layout. |
| 5. Handler discharge | PASS | Generated handled operations never end in `StuckUnhandledOperation`; golden unhandled fixture proves the stuck state remains detectable for negative cases. |
| 6. Termination of bounded generated subset | PASS | Finite-β generated terms are required to end in `Value` within budget; `div` terms are classified as `BudgetExhaustedDiv` and exempt. |
| 7. Generator coverage | PASS | Fixed-seed counters above cover every required reduced-core form. |

## Verification evidence

```text
just verify
cargo fmt --check
cargo clippy --all-targets -- -D warnings
cargo test

unit tests: 9 passed
integration golden tests: 9 passed
doc tests: 0 passed
```

The full `just verify` command completed successfully.

## Spec gaps surfaced

See `docs/spec-gaps.md`:

- `SPEC-GAP(frame-metric-byte-accuracy)` — no byte-level frame layout exists yet, so Sprint 01 checks an executable captured-context-frame count.
- `SPEC-GAP(nat-structural-recursion-core)` — reduced core has `Nat` and `Fix` but no Nat eliminator for genuine structural recursion; Sprint 01 exercises `Fix` unfolding and tags generator witnesses conservatively.
