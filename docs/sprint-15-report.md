# Sprint 15 Report — Proof Ledger Honesty Repair (v0.5.3)

## Summary

v0.5.3 supersedes v0.5.2. The v0.5.2 report claimed L3/L4/L8 were `Qed`; that was
previously false because the mechanized `step` relation had been changed from the real
`StepByFunction : stepf t = Some u -> step t u` relation into a degenerate self-loop
observable. v0.5.3 restores the honest relation, adds falsifiability anchors for core
relations, and sets the proof ledger to the true count: `ADMITTED_COUNT = 4`.

## Acceptance table

| # | Status | Evidence |
| --- | --- | --- |
| 1 | Pass | `scripts/check-admitted-count.sh` exact-matches `proofs/ADMITTED_COUNT`; CONTRIBUTING now requires ledger notes for up/down movement. |
| 2 | Pass | ADR 0002 amended: named binders retained; latent-arrow fidelity correction recorded. |
| 3 | Honest status | L3 `progress` remains `Admitted`; `progress_effect_closed` is `Qed` from L3 and the empty row. |
| 4 | Honest status | L4 `preservation` with row/bound order remains `Admitted` under the restored real step relation. |
| 5 | Honest status | L8 `solver_certificate_soundness` remains `Admitted`; v0.5.2's field-projection Qed was not an algorithmic solver proof. No-smuggling audit is clean. |
| 6 | Pass | `StepFrames.v` defines `frame_step`; `frame_step_erases_to_stepf` is `Qed`. |
| 7 | Pass | Counted admitted theorems: L3, L4, L7, L8. `proofs/ADMITTED_COUNT` is `4`. |
| 8 | Pass | `Bridge.v` has five `frame_bridge_*` examples including drop = 0 and resume = 1. |
| 9 | Pass | `Bridge.v` keeps solver fixture classes as model anchors; not claimed as L8 discharge. |
| 10 | Pass | Statement-integrity diff retains Addendum 1's L3/L4 statements; model diff itemized in row 10b. |
| 10b | Pass | Model diff: `TyArrow a ε β b` (§3.1); `Ty_Lam` stores latent row (§4.2); `Ty_App` charges latent row (§4.3); `Ty_Fix*` form pure function values with latent bodies (§4.7/§4.8). |
| 11 | Pass | Full gate evidence below: Rust suite, examples, proofs, admitted-count script, book and README checks. |
| 12 | Pass | §8.1/§8.2 amended; `progress-open-effects` and `preservation-statement-drift` resolved; `finding18_top_level_perform_is_predicted_block` bridges the third disjunct. |
| 13 | Pass | Finding nineteen anchors: `finding19_beta_face_*` and `finding19_effect_face_*` in `Bridge.v`. |
| 14 | Pass | Surface probe recorded below; `mechanized-arrow-latent-erasure` resolved and §10 note amended. |
| 15 | Pass | Definition-integrity repair: `step` restored; `step_anchor_beta_redex_not_self_loop`, `step_anchor_beta_redex_steps_to_contractum`, and `step_anchor_unhandled_perform_not_self_loop` make the degenerate relation uncompilable. |

## Finding eighteen

Ownership: spec-side. The original §8.1 classic progress statement was false for
`TPerform L TZero` typed at `EffL`. The corrected theorem is the effectful trichotomy;
top-level unhandled operations are blocked only when predicted by the row. §8.2 also now
states the row/bound relation in the theorem, not just prose.

## Finding nineteen

Ownership: mechanized-model side. `TyArrow a b` erased the paper's latent row, so `Ty_Lam`
discarded latent effects and `β`. The model now uses `TyArrow a ε β b`; bridge anchors show
both laundering faces are pinned.

Surface probe transcript, recorded per Addendum 2:

```text
fn spin(n) -> Nat div = spin(n)
fn apply[A,B](f: A->B, x: A) -> B = f(x)
main = apply(spin, 0)
```

The Rust checker reports `β: ω, divergence: Div`; the implementation was already safe on
this axis through call-graph witness propagation. Cosmetic ledger: a separate display wart
can print `type: Array` for a Nat-returning generic `main`; this is polish, not soundness.

## Finding twenty — definition integrity

Ownership: proof-model/reporting side. v0.5.2's L3/L4/L8 discharge claims were false. The
semantic substrate changed to avoid proof work, invalidating the claim. v0.5.3 restores the
real `step` relation and adds relation falsifiability anchors so the class cannot compile
again. CONTRIBUTING now treats `stepf`, `step`, `frame_step`, `has_type`, `is_value`, and
the grade algebra as protected semantic substrate.

## Ledger notes

- v0.5.2 previously false: `progress`, `preservation`, and `solver_certificate_soundness`
  were reported as `Qed`.
- v0.5.3 truth-pass: `progress` remains `Admitted`; `progress_effect_closed` is `Qed` from
  L3; `preservation` remains `Admitted`; `solver_certificate_soundness` remains `Admitted`;
  `boundedness_soundness` remains the L7 runway `Admitted`.
- Net count: `4`.

## Verification evidence

Commands run locally before tag:

```text
cargo fmt --check
cargo clippy --all-targets -- -D warnings
cargo test
make -C proofs
scripts/check-admitted-count.sh
grep -Rn --include='*.v' "Axiom\|Parameter\|admit\." proofs/theories
cargo run --quiet -- test examples/
mdbook build book
scripts/check-book-samples.sh
scripts/check-readme-quickstart.sh
```

## Next proof increment

There is no third option next time: either do B.1 for real (full substitution, de Bruijn
valve still sanctioned) and carry L4 through the H-op-resume case, or halt with a concrete
counterexample of finding-eighteen/nineteen caliber.
