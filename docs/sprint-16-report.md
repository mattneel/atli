# Sprint 16 Report — The Induction, Decomposed (v0.5.4, in progress)

This report is assembled rung by rung; the acceptance table gains exactly one row
per rung as each lands. Ledger notes are recorded in the same commit as every
`proofs/ADMITTED_COUNT` movement, per CONTRIBUTING.

## Ledger notes

- Sprint 16 B4: `progress` (L3, docs/calculus.md §8.1) moves Admitted → Qed,
  assembled from the B3 engine (`typed_stuck_implies_blocked`) over the Part A
  repaired dynamics (capture/deep resume) and the B3 context-rich
  `blocked_on_operation`. `proofs/ADMITTED_COUNT` 4 → 3. Remaining admitted:
  `preservation` (L4), `boundedness_soundness` (L7), `solver_certificate_soundness` (L8).
- Sprint 16 C4: `preservation` (L4, docs/calculus.md §8.2) moves Admitted → Qed:
  induction over the typing derivation against stepf's value-guarded equations;
  non-handler cases via the C1 closed-substitution lemma; the handler triad —
  H-return (C1), H-op-drop (C1 + strengthening; the discarded context needs no
  accounting), and H-op-resume with the continuation typed by Ty_ContVal at the
  declared latent, β̂ᵢ = βᵢ ⊕ β threaded through C2 monotonicity — plus the deep
  rebuild step, bounded by the continuation's latent via the A6 side condition:
  the lazy-capture amendment audit closes. `proofs/ADMITTED_COUNT` 3 → 2.
  Remaining admitted: `boundedness_soundness` (L7), `solver_certificate_soundness` (L8).

## Findings

- Finding twenty-six: component ownership is solver-side (`src/check/solve.rs`), confirmed
  by reproduction with `a ⊒ b ⊕ 1, b ⊒ a`. The single widening pass violated the
  `docs/calculus.md` §7.2 upward-over-approximation promise and §7.3 sealed-certificate
  boundary by emitting a partial iterate (`a = ω, b = 3`) in §2.3's under-allocation
  miscompile direction. This commit fixes the solver by iterating widened SCC passes to
  stability and adds a regression test that checks post-fixpoint-ness across the SCC. The
  found-a-bug discipline is satisfied: separate commit, would-have-caught test, and report
  entry. The Rust-src scope fence was crossed deliberately under the found-a-bug law
  because D3's bridge cross-cites solver outputs.

## Acceptance table (in progress; one row per rung, completed at E2)

| Rung | Status | Evidence |
| --- | --- | --- |
| B4 | Pass | `progress` Qed in `proofs/theories/Meta.v`; `progress_effect_closed` re-established from it; ledger 4 → 3 this commit. |
| C1 | Pass | `substitution_preserves_typing_closed` Qed in `proofs/theories/Meta.v`; value wrapper retained for acceptance compatibility. |
| C2 | Pass | Effect and bound order micro-lemmas Qed in `proofs/theories/Grade.v`; preservation monotonicity surface available. |
| C3 | Pass | `capture_decomposition` and `plug_replacement` Qed in `proofs/theories/Meta.v`; handler-capture typing surface available. |
| C4 | Pass | `preservation` Qed in `proofs/theories/Meta.v`; ledger 3 → 2 this commit. |
