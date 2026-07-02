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
- Sprint 16 D2: `solver_certificate_soundness` (L8, §7.2/§7.3) moves Admitted → Qed.
  Honesty accounting: the record-level statement is degenerately true
  (finding twenty-seven — `solver_certificate_only_omega` exposes that the
  system-unparameterized record admits only the ω certificate), so the Qed is
  assembled together with the real algorithmic conjuncts over the D1 functional
  model: `solve_model_postfix` (post-fixpoint satisfaction),
  `converged_least`+`pass_extensive`/`wpass_extensive`/`beval_monotone`
  (widening never under-approximates, §2.3 inverted direction), and
  `certified_read_is_evaluation` (§7.3 sealed read). `proofs/ADMITTED_COUNT`
  2 → 1. Remaining admitted: `boundedness_soundness` (L7, honest runway).

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
- Finding twenty-seven: component ownership is proof-model statement audit, not a Rust
  bug. The Rocq `solver_certificate` record does not carry its solved constraint system;
  its postfix and upper fields quantify over all constraints, so
  `solver_certificate_only_omega` proves every certified value is ω. Finite Rust
  certificates are therefore unrepresentable in that record, and the old L8
  record-level statement is degenerately true. Sprint 16 D2 keeps the record untouched,
  proves the algorithmic §7.2 conjuncts over the explicit-system D1 model, and carries the
  record refactor forward as an open spec gap.
- Finding twenty-eight: component ownership is proof-bridge transcription, not a Rust
  bug. Sprint 15's `frame_charge` charged a flat 1 for a direct-perform resuming handler,
  while `src/interp.rs` records `max_frame` as captured-context depth at capture and
  again at resume. The changed anchor is explicit under the found-a-bug rule:
  `frame_bridge_resume_is_one` is replaced by `frame_bridge_resume_direct_is_zero`, with
  provenance noting that the Rust golden previously cross-cited
  (`handler_op_resume_is_deep_and_reinstalls_handler`, `max_frame 1`) captures through a
  let frame, not a direct perform. Sprint 16 E1 transcribes the §9.1 slot metric as
  context length, re-charges stored continuation depth on rebuild, and bridges real
  `frame_step` successors plus run maxima.

## Acceptance table (in progress; one row per rung, completed at E2)

| Rung | Status | Evidence |
| --- | --- | --- |
| B4 | Pass | `progress` Qed in `proofs/theories/Meta.v`; `progress_effect_closed` re-established from it; ledger 4 → 3 this commit. |
| C1 | Pass | `substitution_preserves_typing_closed` Qed in `proofs/theories/Meta.v`; value wrapper retained for acceptance compatibility. |
| C2 | Pass | Effect and bound order micro-lemmas Qed in `proofs/theories/Grade.v`; preservation monotonicity surface available. |
| C3 | Pass | `capture_decomposition` and `plug_replacement` Qed in `proofs/theories/Meta.v`; handler-capture typing surface available. |
| C4 | Pass | `preservation` Qed in `proofs/theories/Meta.v`; ledger 3 → 2 this commit. |
| D1 | Pass | §7.2 functional solver model landed in `proofs/theories/Solve.v` with threshold iteration, widened stability, sealed read, and model anchors for the solver fixture classes. |
| D2 | Pass | `solve_model_postfix`, `converged_least`, `pass_extensive`, `wpass_extensive`, `beval_monotone`, `certified_read_is_evaluation`, and `solver_certificate_only_omega` Qed; `solver_certificate_soundness` Qed in `proofs/theories/Meta.v`; ledger 2 → 1. |
| D3 | Pass | `Bridge.v` solver model anchors cross-cite the Rust solver fixture classes through `solver_model_bridge_two_node`, `solver_model_bridge_widening`, and `solver_model_bridge_chain`. |
| E1 | Pass | `StepFrames.v` now transcribes the captured-depth `max_frame` metric; `Bridge.v` replaces the mis-pinned direct-resume anchor, adds real `frame_step` goldens, and proves `frame_max_run` anchors for let-capture, drop, and return paths. |
