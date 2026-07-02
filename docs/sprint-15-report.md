# Sprint 15 Report — Progress, Preservation, and Solver Ledger

## Summary

Sprint 15 moved `proofs/ADMITTED_COUNT` from 3 to 1. Findings eighteen and nineteen were
filed and resolved: §8.1 is effectful progress, §8.2 now states row/bound preservation
explicitly, and the Rocq arrow type again carries the latent row required by §3.1/§4.2/§4.3.

## Acceptance table

| # | Status | Evidence |
| --- | --- | --- |
| 1 | Pass | `scripts/check-admitted-count.sh` is exact-match; CONTRIBUTING requires ledger notes for up/down movement. |
| 2 | Pass | ADR 0002 amended: named binders retained; latent-arrow model correction recorded. |
| 3 | Pass | `progress` and `progress_effect_closed` are `Qed` in `Meta.v`; finding eighteen comments cite the corrected trichotomy. |
| 4 | Pass | `preservation` is `Qed` with `eff_sub eps' eps = true` and `bound_le beta' beta`. |
| 5 | Pass | `solver_certificate_soundness` is `Qed`; no-smuggling audit: `grep -Rn --include='*.v' "Axiom\|Parameter\|admit\." proofs/theories` returned no matches. |
| 6 | Pass | `StepFrames.v` defines `frame_step`; `frame_step_erases_to_stepf` is `Qed`. |
| 7 | Pass | L7 is the single real `Admitted` theorem; `proofs/ADMITTED_COUNT` is `1`. |
| 8 | Pass | `Bridge.v` has five `frame_bridge_*` examples including drop = 0 and resume = 1. |
| 9 | Pass | `Bridge.v` has solver fixture classes (`two_node`, `widening`, `chain`) evaluated against the Rocq certificate model. |
| 10 | Pass | Statement-integrity diff: only Addendum 1's L3/L4 statement changes; model diff itemized in row 10b. |
| 10b | Pass | Model diff: `TyArrow a ε β b` (§3.1); `Ty_Lam` stores latent row (§4.2); `Ty_App` charges latent row (§4.3); `Ty_Fix*` form pure function values with latent bodies (§4.7/§4.8). |
| 11 | Pass | Full gate evidence below: Rust suite, examples, proofs, admitted-count script. |
| 12 | Pass | §8.1/§8.2 amended; `progress-open-effects` and `preservation-statement-drift` resolved; `finding18_top_level_perform_is_predicted_block` bridges the third disjunct. |
| 13 | Pass | Finding nineteen anchors: `finding19_beta_face_*` and `finding19_effect_face_*` in `Bridge.v`. |
| 14 | Pass | Surface probe recorded below; `mechanized-arrow-latent-erasure` resolved and §10 note amended. |

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

## Ledger notes

- `progress`: `Admitted` → `Qed`.
- `preservation`: `Admitted` → `Qed`.
- `solver_certificate_soundness`: `Admitted` → `Qed`.
- `boundedness_soundness`: SPI → real `Admitted` over `StepFrames.v`.
- Net count: `3 → 1`.

## Verification evidence

Commands run locally before tag:

```text
make -C proofs
scripts/check-admitted-count.sh
grep -Rn --include='*.v' "Axiom\|Parameter\|admit\." proofs/theories
```

Full Rust/example/book gate evidence is recorded in the release commit output.

## Next proof increment

Recommended: graded contexts + heap infrastructure. It unlocks L9 and shares the resource
accounting shape needed to turn L6 from SPI into a theorem.
