# Sprint 16 Report — The Induction, Decomposed (v0.5.4)

Progress and preservation are now theorems over a continuation semantics with real
captured contexts and deep `H-op-resume` per §5. The solver is proven sound against its
own §7.2 functional model. The ledger reads 1 (`boundedness_soundness`, L7) and means it:
the remaining admission is the honest boundedness runway. Sprint 16 recorded eight
findings (21-28); five of them were live L3/L4 counterexamples or unsound certificates
that the pre-decomposed ladder surfaced before the summit proofs were attempted.

## Acceptance table

| Rung | Status | Evidence | What was tricky |
| --- | --- | --- | --- |
| A1 | Pass | `TContVal h ctx`, `TUsedContVal h ctx`, `eframe`, and `plug` in `proofs/theories/Syntax.v`; commit `b92cd72` (`proofs: A1 continuation values carry handler and captured frames`). | Nested `list eframe` inside the mutual inductive weakens the auto Schemes (no IHs through the list); harmless because subst/counting stay payload-opaque under the closedness discipline. |
| A2 | Pass | `capture`, `capture_cons`, and `capture_plug` in `proofs/theories/Step.v`; capture anchors `capture_anchor_finding21_body`, `capture_anchor_nested_handler_stops`, `capture_anchor_innermost_perform_wins`, `capture_anchor_value_is_none`, and `capture_anchor_direct_perform_empty_ctx` in `proofs/theories/Bridge.v`. | `TResume`'s capture dispatch must mirror `stepf`'s pattern ORDER (`TContVal`/`TUsedContVal` before the catch-all); `capture_plug` pins decomposition + head-outermost orientation mechanically. |
| A3 | Pass | `stepf`'s `H-op-drop`, `H-op-resume`, and resume-rebuild cases in `proofs/theories/Step.v`; `finding21_now_steps`, `resume_rebuild_anchor`, `drop_discards_context_anchor`, and `used_cont_resume_still_stuck` in `proofs/theories/Bridge.v`. | Anchors landed in the same commit as the dynamics per the definition-integrity law; bonus fidelity: perform-with-non-value-argument under a handler was stuck pre-repair. |
| A4 | Pass | Extended dynamics anchors `capture_through_two_frames_anchor`, `perform_arg_congruence_unstuck_anchor`, `capture_beats_argument_congruence_anchor`, `nested_same_label_inner_owns_anchor`, `finding21_rebuilt_body_steps`, and `finding21_completes` in `proofs/theories/Bridge.v`. | Capture-first dispatch priority over the old argument-fallback is exactly §5's `E e` grammar; pinned. |
| A5 | Pass | `closed_term`, `handler_closed`, `ctx_closed`, `plug_mentions`, `subst_closed_op_drop`, `subst_closed_op_resume`, `ctx_payloads_closed_plug`, and `step_preserves_closedness` in `proofs/theories/Meta.v`; payload-opaque `mentions_var`/`free_var_count`/`direct_resume_count`/`subst` cases in `proofs/theories/Syntax.v`. | Handler/context closedness reified through `mentions_var` on wrapper terms (frames never bind over the hole); the `H-op-drop` case NEEDS the dispatch condition `mentions_var k op_body = false` to cover the k-shadow position. |
| A6 | Pass | `TyCont` in `proofs/theories/Syntax.v`; `Ty_HandleResume`, `Ty_Resume`, `Ty_ContVal`, and `ctx_types` in `proofs/theories/Typing.v`; anchors `contval_types_at_declared_latent`, `resuming_handle_types_finite`, `finding22_aliased_resuming_handle_untypable`, and `contval_finite_latent_refuses_divergent_clause` in `proofs/theories/Bridge.v`. | The design was adversarially verified before landing (three independent lenses); the prompt's literal no-bound sketch admits a preservation countermodel at the rebuild step, so `TyCont` carries §3.1's latent bound (the finding-19 pattern at `Cont`), with the §6.2 recursive side condition stated in-rule; finding-22 freshness lands here. |
| B1 | Pass | `canonical_nat`, `canonical_arrow`, `canonical_cont`, and `value_rows_trivial` in `proofs/theories/Meta.v`. | `value_rows_trivial` (values type at exactly `(EffEmpty, BFinite 0)`) is load-bearing across C4. |
| B2 | Pass | `typing_lookup_monotone`, `typing_context_ext`, and `closed_typing_weakening` in `proofs/theories/Meta.v`. | One lookup-monotone induction yields weakening and context extensionality. |
| B3 | Pass | Context-rich `blocked_on_operation`, `blocked_iff_capture`, and `typed_stuck_implies_blocked` in `proofs/theories/Meta.v`; anchors `blocked_anchor_finding21_body_is_blocked`, `blocked_anchor_handled_term_is_not_blocked`, and finding-23 dispatch anchors in `proofs/theories/Bridge.v`. | The `THandle` case of typed-stuck-implies-blocked is the payoff — blocked meets handler ⇒ capture succeeds ⇒ steps; resume/perform stuck cases are vacuous through `EffEmpty` premise rows. Landed after finding 23's `stepf` repair, without which L3 is false. |
| B4 | Pass | `progress` and `progress_effect_closed` Qed in `proofs/theories/Meta.v`; ledger note records `proofs/ADMITTED_COUNT` 4 → 3. | Assembly only — value / stepf-Some / engine; ledger 4→3 with same-commit report note. |
| C1 | Pass | `subst_free_var_count_other`, `subst_direct_resume_count_other`, `handler_clause_ok_subst_stable`, `substitution_preserves_typing_general`, `substitution_preserves_typing_closed`, and `substitution_preserves_typing_closed_value` in `proofs/theories/Meta.v`. | Two commits (count-stability infra; the substitution theorem via lookup-characterized contexts); the general lemma deliberately omits `is_value` — fix-unfold substitutes a closed pure non-value; ADR 0002's named-binder bet vindicated. |
| C2 | Pass | `eff_sub_trans`, `eff_sub_join_mono`, `eff_sub_join_upper_l`, `eff_sub_join_upper_r`, `eff_sub_empty`, `bound_le_trans`, `bound_seq_mono`, `bound_join_mono`, `bound_join_lub`, `bound_le_omega`, `bound_seq_upper_l`, `bound_seq_upper_r`, and `bound_le_zero` in `proofs/theories/Grade.v`. | Driven by exactly what C4 demanded. |
| C3 | Pass | `capture_decomposition` and `plug_replacement` in `proofs/theories/Meta.v`; `ctx_types` in `proofs/theories/Typing.v`; capture/plug bridge anchors in `proofs/theories/Bridge.v`. | Two commits; decomposition preserves the bound index EXACTLY (both hole fillers are bound-0) while the effect index is existential (the perform contributes `EffL`); the row-prediction conjunct falls out. |
| C4 | Pass | `typing_strengthen`, `preservation_stepf`, and `preservation` in `proofs/theories/Meta.v`; `finding24_aliased_fix_untypable`, `finding25_pure_body_div_untypable`, and `finding25_structural_unfold_preserves_type` in `proofs/theories/Bridge.v`; ledger note records `proofs/ADMITTED_COUNT` 3 → 2. | Two commits (strengthening; the theorem). The handler triad closed affirmatively: `H-op-resume` types the minted `TContVal` at the DECLARED latent because capture's `beta_p` equals `body_beta`, making `Ty_ContVal`'s side condition literally the rule's own; the rebuild step is bounded by the continuation latent. Findings 24/25 were surfaced by this rung's pre-proof audit and repaired first. |
| D1 | Pass | `valuation`, `vbot`, `bound_eqb`, `bound_grows`, `domain`, `rhs_join`, `pass`, `wpass`, `iterate_model`, `widen_model`, `solver_threshold_k`, `solve_model`, `certified_read`, and vm-compute anchors `model_anchor_two_node_converges`, `model_anchor_self_seq_widens`, `model_anchor_finding26_postfix`, and `model_anchor_chain_default_zero` in `proofs/theories/Solve.v`. | Joint fuel-based model of the CORRECTED (finding-26) algorithm; `vm_compute` anchors cross-cite the Rust unit tests. |
| D2 | Pass | `solve_model_postfix`, `converged_least`, `pass_extensive`, `wpass_extensive`, `beval_monotone`, `certified_read_is_evaluation`, and `solver_certificate_only_omega` in `proofs/theories/Solve.v`; `solver_certificate_soundness` in `proofs/theories/Meta.v`; ledger note records `proofs/ADMITTED_COUNT` 2 → 1. | The honest discharge — the record-level statement is degenerately true (finding 27), so the Qed is assembled together with the real conjunct lemmas over the model; ledger 2→1. |
| D3 | Pass | `solver_model_bridge_two_node`, `solver_model_bridge_widening`, `solver_model_bridge_chain`, and `solver_model_bridge_two_node_postfix` in `proofs/theories/Bridge.v`; old record-path anchors `solver_bridge_two_node_model_value`, `solver_bridge_widening_model_value`, and `solver_bridge_chain_model_value` remain explicitly ω-degenerate. | Fixture values equal the corrected Rust solver's outputs; post-fixpoint anchor distinguishes the model path from the ω-degenerate record path. |
| E1 | Pass | `frame_charge`, `frame_step`, `frame_step_erases_to_stepf`, and `frame_max_run` in `proofs/theories/StepFrames.v`; `frame_bridge_resume_direct_is_zero`, `frame_golden_resume_through_let`, `frame_golden_rebuild_recharges`, `frame_golden_dropped_handler_zero`, `frame_golden_resume_direct_zero`, `frame_golden_two_frames`, `frame_run_finding21_is_one`, `frame_run_dropped_is_zero`, and `frame_run_pure_return_is_zero` in `proofs/theories/Bridge.v`. | The metric itself was the finding (28); run-maxima via `frame_max_run` equal the Rust goldens' reported `max_frame`. |
| E2 | Pass | This report: `docs/sprint-16-report.md`, with exactly one top-level row per rung per CONTRIBUTING's row law. | This report; one row per rung per the row law. |
| E3 | Pass | tag `v0.5.4` is the sprint's final commit, applied after this report lands. | Release tagging is documentation/order bookkeeping after E2 lands; no proof or source semantics move here. |

## Findings

### Finding twenty-one — continuation payload erasure

Ownership: mechanized dynamics. Lineage: Sprint 04's token continuation model erased the
handler and captured context, so `H-op-resume` could not model §5's deep reinstallation.
Repair: `TContVal h ctx` and `TUsedContVal h ctx` now carry the installed handler plus the
handler-free evaluation context; `capture` decomposes to the innermost unhandled
`perform`, and `stepf` resumes by rebuilding `THandle (plug ctx v) h`. Anchors:
`capture_anchor_finding21_body`, `finding21_now_steps`, `resume_rebuild_anchor`,
`finding21_rebuilt_body_steps`, and `finding21_completes`.

### Finding twenty-two — handler p/k binder aliasing

Ownership: spec/mechanization/Rust alignment. Lineage: §4.7 uses distinct metavariables
`pᵢ`/`kᵢ` but did not state the named-binder freshness condition. With `op_param = op_k`,
typing bound `k` innermost while `subst2` substituted the parameter first, producing the
static/dynamic split recorded in `docs/spec-gaps.md`. Repair: the mechanized resuming
rules require `String.eqb op_param op_k = false`; the Rust checker rejection remains
carried-forward work. Anchors: `finding22_aliased_clause_passes_clause_ok`,
`finding22_param_wins_dynamically`, `finding22_successor_is_stuck`, and
`finding22_aliased_resuming_handle_untypable`.

### Finding twenty-three — `stepf` pattern absorption

Ownership: mechanized dynamics. Lineage: beta and case-succ patterns absorbed their
congruence cases, and App/Resume included off-grammar stuck-function argument fallbacks,
contradicting §5's `E e` / `v E` / `case E` grammar and the Rust oracle's value-guarded
dispatch. Repair: `stepf` now dispatches App, CaseNat, and Resume by value guards matching
`src/interp.rs`. Anchors: `finding23_beta_arg_congruence_now_steps`,
`finding23_case_succ_congruence_now_steps`, `finding23_stuck_fun_no_longer_steps_arg`,
and `finding23_blocked_fun_captured_under_handler`.

### Finding twenty-four — fix f/x binder aliasing

Ownership: mechanized typing/dynamics. Lineage: §4.8 writes distinct `f` and `x`
metavariables, but the model allowed aliasing; static lookup put the parameter innermost
while unfold substituted the function name. Repair: every fix typing rule now carries
`String.eqb f x = false`; Rust surface probing is carried forward. Anchors:
`finding24_unfold_substitutes_function_name` and `finding24_aliased_fix_untypable`.

### Finding twenty-five — fix rule mistranscription

Ownership: mechanized typing. Lineage: §4.8 binds `f` at the declared arrow, but the model
bound structural/measure recursion at a hardwired pure arrow and let Div drift under an
ω conclusion. Repair: fix rules now bind `f` at the declared arrow and take the equality
slice of `β ⊒ Fix_β`; §4.9 subsumption/§8.6 principality carry the slack forward.
Anchors: `finding25_pure_body_div_untypable` and
`finding25_structural_unfold_preserves_type`.

### Finding twenty-six — solver widening partial-iterate escape

Ownership: solver-side (`src/check/solve.rs`), confirmed by reproduction with
`a ⊒ b ⊕ 1, b ⊒ a`. Lineage: the single widening pass violated the `docs/calculus.md`
§7.2 upward-over-approximation promise and §7.3 sealed-certificate boundary by emitting a
partial iterate (`a = ω, b = 3`) in §2.3's under-allocation miscompile direction. Repair:
the solver iterates widened SCC passes to stability and has a regression test checking
post-fixpoint-ness across the SCC. Anchors: `model_anchor_finding26_postfix` and the Rust
test `widened_certificate_is_a_postfixpoint_across_the_scc`. The Rust-src scope fence was
crossed deliberately under the found-a-bug law because D3's bridge cross-cites solver
outputs.

### Finding twenty-seven — solver_certificate record ω-degeneracy

Ownership: proof-model statement audit, not a Rust bug. Lineage: the Rocq
`solver_certificate` record does not carry its solved constraint system; its postfix and
upper fields quantify over all constraints, so `solver_certificate_only_omega` proves
every certified value is ω. Finite Rust certificates are therefore unrepresentable in that
record, and the old L8 record-level statement is degenerately true. Repair: Sprint 16 D2
keeps the record untouched, proves the algorithmic §7.2 conjuncts over the explicit-system
D1 model, and carries the record refactor forward as an open spec gap. Anchors:
`solve_model_postfix`, `converged_least`, `pass_extensive`, `wpass_extensive`,
`beval_monotone`, `certified_read_is_evaluation`, `solver_certificate_only_omega`, and
`solver_certificate_soundness`.

### Finding twenty-eight — frame_charge metric transcription divergence

Ownership: proof-bridge transcription, not a Rust bug. Lineage: Sprint 15's
`frame_charge` charged a flat 1 for a direct-perform resuming handler, while
`src/interp.rs` records `max_frame` as captured-context depth at capture and again at
resume. Repair: `frame_bridge_resume_is_one` is replaced by
`frame_bridge_resume_direct_is_zero`, with provenance noting that the Rust golden
previously cross-cited (`handler_op_resume_is_deep_and_reinstalls_handler`, `max_frame 1`)
captures through a let frame, not a direct perform. Sprint 16 E1 transcribes the §9.1
slot metric as context length, re-charges stored continuation depth on rebuild, and bridges
real `frame_step` successors plus run maxima. Anchors: `frame_charge`,
`frame_golden_resume_through_let`, `frame_golden_rebuild_recharges`,
`frame_golden_resume_direct_zero`, and `frame_run_finding21_is_one`.

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

## Spec-gap movements

Filed/open:

- `SPEC-GAP(handler-binder-aliasing-static-dynamic-split)` — open; Rust repair carried.
- `SPEC-GAP(fix-binder-aliasing-static-dynamic-split)` — open; Rust probe carried.
- `SPEC-GAP(deep-handler-resume-accounting-recursive)` — open; Rust checker alignment carried.
- `SPEC-GAP(solver-certificate-record-system-unparameterized)` — open; record refactor carried.

Resolved:

- `RESOLVED(mechanized-token-continuation-erasure)`.
- `RESOLVED(stepf-pattern-absorption-congruence-loss)`.
- `RESOLVED(solver-widening-partial-iterate-escape)`.
- `RESOLVED(frame-charge-metric-transcription-divergence)`.

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

## Carried-forward work

- L7 discharge: the next proofs sprint's headline is the strengthened preservation
  invariant that finite certified β bounds every `frame_max_run` prefix over the now
  Rust-parity metric.
- Rust checker: deep-resume accounting alignment (bound-blind `Cont`), aliased
  handler-clause rejection, and aliased fix-binder rejection/probing.
- `solver_certificate` record refactor: parameterize the record by the solved system.
- §4.9 subsumption slice / §8.6 principality.
- §7.2 step 4 narrowing remains unimplemented on both sides.
