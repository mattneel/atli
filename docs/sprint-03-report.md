# Sprint 03 report: checker and boundedness solver

## Plan and architecture

- Added a `check` module with a visible checker/solver split:
  - `src/check/error.rs`: blame-carrying `TypeError` with rule and spec-section citation.
  - `src/check/solve.rs`: boundedness constraint graph, Tarjan SCC decomposition,
    precise iteration to `SOLVER_THRESHOLD_K = 6`, upward widening to `ω`, and solver
    statistics.
  - `src/check/mod.rs`: reduced-core graded checker for `docs/calculus.md §4`, emitting
    pending boundedness expressions and constructing public witnesses only after solver
    certification.
- Implemented the §7.3 phase gate with `PendingGrade<T>` and `CertifiedGrade`. The
  `CheckedWitness` constructor is private and consumes only `CertifiedGrade`; a
  `compile_fail` doctest demonstrates that pending grades cannot construct a witness.
- Implemented the amended §4.7 handler rule: lazy drop (`k` absent) has `β̂ᵢ = βᵢ`,
  resume (`exactly one direct resume k v`) has `β̂ᵢ = βᵢ ⊕ β`, and mention-without-resume
  is rejected.
- Implemented `Structural` strict-descent rejection and trusted `Measure` tags for the
  reduced core. The `Measure` trust boundary is recorded in `docs/spec-gaps.md`.

## Acceptance table

Fixed seed: `0xa7110002`; generated sample: `1024`; safe generated terms: `939`.

| # | Criterion | Result | Evidence |
|---|---|---:|---|
| 1 | Safe generated terms accepted | PASS | 939 accepted, 0 rejected. |
| 2 | Checker/derive witness agreement | PASS | 0 disagreements on type, effects, divergence, and `β`. |
| 3 | Operational soundness composition | PASS | 758 finite-`β` frame checks passed; 758 terminating terms reached `Value`; 181 `Div` terms exhausted budget. |
| 4 | Rejection soundness | PASS | Targeted rejections are discipline/type errors; generated safe terms had zero checker rejections. |
| 5 | Wedge flips | PASS | `checker_rejects_mention_without_resume_wedge` rejects with `Handle §4.7` / `extra-mention`; old interpreter/derive documentation remains. |
| 6 | Structural-tag honesty | PASS | `checker_rejects_non_strict_structural_recursion` rejects non-strict `Structural`; report notes derive asymmetry. |
| 7 | Phase gate structural | PASS | `src/check/mod.rs` compile-fail doctest proves `PendingGrade` cannot build `CheckedWitness`. |
| 8 | Solver behavior evidenced | PASS | Solver SCC/iteration/widening stats below; isolated multi-node-SCC and widening goldens pass. |
| 9 | Error quality | PASS | Three real error printouts below include rule, section, and blamed subterm. |
| 10 | Regression | PASS | Prior tests remained green; suite is now 13 library/property + 19 golden + 1 compile-fail doctest. |

## Solver statistics over fixed-seed safe sample

- SCC count distribution per checked term: `{0: 369, 1: 380, 2: 93, 3: 41, 4: 32, 5: 17, 6: 2, 7: 2, 8: 2, 9: 1}`
- SCC size histogram: `{1: 953}`
- Iterations-to-certification histogram: `{2: 757, 7: 196}` (`7` = threshold `K=6` plus widening step)
- Widening fires: `196`

Targeted solver evidence:

- `solver_golden_multi_node_scc_converges`: hand-built two-node SCC converges to finite `β = 2`.
- `solver_golden_widening_fires_for_growing_cycle`: hand-built growing cycle widens to `ω`.
- `checker_div_fix_exercises_widening_and_classifies_div`: `Div`-tagged recursive term is accepted, widens, and is classified `Div`.

## Error samples

```text
Handle §4.7 rejected `(let z = k in succ(succ(succ(succ(succ(succ(succ(succ(succ(zero))))))))))`: extra-mention: `k` appears free but is never directly resumed
```

```text
Fix-Structural §4.8/§7.1 rejected `(f x)`: recursive call argument is not the peeled predecessor
```

```text
Succ §4.2 rejected `succ(())`: expected Nat, found Unit
```

## Asymmetries and gaps

- `derive_witness` is an analyzer, not a judge: for non-strict `Structural` recursion it
  assigns `ω`/`Div`, while the checker rejects the term. Differential witness agreement is
  therefore scoped to checker-accepted terms.
- `SPEC-GAP(measure-tag-trusted-reduced-core)` records that `Measure`-tagged recursion is
  trusted in this reduced core; a real measure proof belongs to a later surface checker.
- The two open frame-metric gaps remain interpreter/backend-fidelity gaps, not checker
  rule gaps.

## Verification commands

- `cargo fmt --check`
- `cargo clippy --all-targets -- -D warnings`
- `cargo test`
- `just audit`
