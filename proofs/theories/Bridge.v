From Coq Require Import Bool.Bool Strings.String Lists.List.
Import ListNotations.
Import StringSyntax.
Open Scope string_scope.

Require Import Atli.Grade.
Require Import Atli.Syntax.
Require Import Atli.Typing.
Require Import Atli.Step.

(** Golden-term transcription bridge, per Sprint 04 B.5. *)

Definition wedge_body : term := TLet "z" (TVar "k") TZero.
Definition dropped_clause_body : term := TZero.
Definition resuming_clause_body : term := TResume (TVar "k") TZero.
Definition extra_resume_body : term := TLet "a" (TResume (TVar "k") TZero) (TResume (TVar "k") TZero).
Definition nested_drop_body : term :=
  THandle TZero (Handler "r" (TVar "r") L "p" "j" TZero).
Definition structural_fix_golden : term :=
  TFix "f" "x" TyNat
    (TCaseNat (TVar "x") TZero "p" (TApp (TVar "f") (TVar "p"))) Structural.
Definition div_fix_golden : term :=
  TFix "f" "x" TyNat (TApp (TVar "f") (TVar "x")) Div.

Example wedge_rejected_like_rust_checker : handler_clause_ok "k" wedge_body = false.
Proof. reflexivity. Qed.

Example dropped_handler_clause_accepted_like_rust_checker : handler_clause_ok "k" dropped_clause_body = true.
Proof. reflexivity. Qed.

Example resuming_handler_clause_accepted_like_rust_checker : handler_clause_ok "k" resuming_clause_body = true.
Proof. reflexivity. Qed.

Example extra_resume_rejected_like_rust_checker : handler_clause_ok "k" extra_resume_body = false.
Proof. reflexivity. Qed.

Example nested_dropped_handler_clause_accepted_like_rust_checker : handler_clause_ok "k" nested_drop_body = true.
Proof. reflexivity. Qed.

Example structural_fix_typable_like_rust_checker : exists beta lat_eps lat_beta,
  has_type [] structural_fix_golden (TyArrow TyNat lat_eps lat_beta TyNat) EffEmpty beta.
Proof.
  eexists. eexists. eexists. unfold structural_fix_golden.
  eapply Ty_FixStructural with (eps := EffEmpty) (beta := BFinite 0).
  - reflexivity.
  - change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
    change (BFinite 0) with (bound_seq (BFinite 0) (bound_join (BFinite 0) (BFinite 0))).
    eapply Ty_CaseNat.
    + apply Ty_Var. reflexivity.
    + apply Ty_Zero.
    + change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
      change (BFinite 0) with (bound_seq (BFinite 0) (bound_seq (BFinite 0) (BFinite 0))).
      eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BFinite 0).
      * apply Ty_Var. reflexivity.
      * apply Ty_Var. reflexivity.
Qed.

Example div_fix_typable_like_rust_checker :
  has_type [] div_fix_golden (TyArrow TyNat EffEmpty BOmega TyNat) EffEmpty (BFinite 0).
Proof.
  unfold div_fix_golden.
  eapply Ty_FixDiv with (eps := EffEmpty).
  - reflexivity.
  - change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
    change BOmega with (bound_seq (BFinite 0) (bound_seq (BFinite 0) BOmega)).
    eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BOmega).
    + apply Ty_Var. reflexivity.
    + apply Ty_Var. reflexivity.
Qed.


(** Finding nineteen bridge anchors: latent arrows prevent higher-order laundering.
    Cross-cites Rust probe described in docs/sprint-15-report.md. *)
Definition latent_div_body : term := TApp div_fix_golden TZero.
Definition latent_beta_launder : term := TApp (TLam "x" TyNat latent_div_body) TZero.
Definition latent_effect_launder : term := TApp (TLam "x" TyNat (TPerform L TZero)) TZero.

Example finding19_beta_face_typed_at_omega :
  has_type [] latent_beta_launder TyNat EffEmpty BOmega.
Proof.
  unfold latent_beta_launder, latent_div_body.
  change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
  change BOmega with (bound_seq (BFinite 0) (bound_seq (BFinite 0) BOmega)).
  eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BOmega).
  - eapply Ty_Lam.
    unfold div_fix_golden.
    change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
    change BOmega with (bound_seq (BFinite 0) (bound_seq (BFinite 0) BOmega)).
    eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BOmega).
    + eapply Ty_FixDiv with (eps := EffEmpty).
      * reflexivity.
      * change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
        change BOmega with (bound_seq (BFinite 0) (bound_seq (BFinite 0) BOmega)).
        eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BOmega).
        -- apply Ty_Var. reflexivity.
        -- apply Ty_Var. reflexivity.
    + apply Ty_Zero.
  - apply Ty_Zero.
Qed.

Example finding19_beta_face_step_preserves_latent_charge :
  stepf latent_beta_launder = Some latent_div_body /\
  has_type [] latent_div_body TyNat EffEmpty BOmega.
Proof.
  split.
  - reflexivity.
  - unfold latent_div_body, div_fix_golden.
    change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
    change BOmega with (bound_seq (BFinite 0) (bound_seq (BFinite 0) BOmega)).
    eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BOmega).
    + eapply Ty_FixDiv with (eps := EffEmpty).
      * reflexivity.
      * change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
        change BOmega with (bound_seq (BFinite 0) (bound_seq (BFinite 0) BOmega)).
        eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BOmega).
        -- apply Ty_Var. reflexivity.
        -- apply Ty_Var. reflexivity.
    + apply Ty_Zero.
Qed.

Example finding19_effect_face_typed_at_effl :
  has_type [] latent_effect_launder TyNat EffL (BFinite 0).
Proof.
  unfold latent_effect_launder.
  change EffL with (eff_join EffEmpty (eff_join EffEmpty EffL)).
  change (BFinite 0) with (bound_seq (BFinite 0) (bound_seq (BFinite 0) (BFinite 0))).
  eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffL) (lat_beta := BFinite 0).
  - eapply Ty_Lam. apply Ty_Perform. apply Ty_Zero.
  - apply Ty_Zero.
Qed.

Example finding19_effect_face_step_preserves_row :
  stepf latent_effect_launder = Some (TPerform L TZero) /\
  has_type [] (TPerform L TZero) TyNat EffL (BFinite 0).
Proof.
  split; [reflexivity|]. apply Ty_Perform. apply Ty_Zero.
Qed.

Require Import Atli.Meta.
Require Import Atli.StepFrames.
Require Import Atli.Solve.

(** Finding eighteen bridge: the old top-level-perform negative fixture is the positive
    witness of effectful progress's third disjunct. Cross-cites the Rust top-level perform
    stuck golden in tests/golden.rs. *)
Definition top_level_perform_golden : term := TPerform L TZero.

Example finding18_top_level_perform_is_predicted_block :
  has_type [] top_level_perform_golden TyNat EffL (BFinite 0) /\
  blocked_on_operation L top_level_perform_golden /\
  stepf top_level_perform_golden = None.
Proof.
  split.
  - apply Ty_Perform. apply Ty_Zero.
  - split.
    + apply Blocked_Here. reflexivity.
    + reflexivity.
Qed.

(** L7 runway frame bridge: duplicated constants cross-cite Rust max_frame goldens. *)
Definition frame_drop_direct : term :=
  THandle (TPerform L TZero) (Handler "r" (TVar "r") L "p" "k" TZero).
Definition frame_resume_direct : term :=
  THandle (TPerform L TZero) (Handler "r" (TVar "r") L "p" "k" (TResume (TVar "k") TZero)).
Definition frame_pure_return : term :=
  THandle TZero (Handler "r" (TVar "r") L "p" "k" TZero).
Definition frame_plain_perform : term := TPerform L TZero.
Definition frame_succ_drop : term := TSucc frame_drop_direct.

Example frame_bridge_drop_is_zero : frame_max_one frame_drop_direct = 0.
Proof. reflexivity. Qed.

Example frame_bridge_resume_is_one : frame_max_one frame_resume_direct = 1.
Proof. reflexivity. Qed.

Example frame_bridge_return_is_zero : frame_max_one frame_pure_return = 0.
Proof. reflexivity. Qed.

Example frame_bridge_unhandled_is_zero : frame_max_one frame_plain_perform = 0.
Proof. reflexivity. Qed.

Example frame_bridge_context_drop_one_step_zero : frame_max_one frame_succ_drop = 0.
Proof. reflexivity. Qed.

(** Solver bridge: Sprint 03 fixture shapes evaluated by the Rocq certificate model. *)
Definition omega_rho (_ : unknown) : bound := BOmega.

Lemma bound_le_any_omega : forall b, bound_le b BOmega.
Proof. destruct b; simpl; auto. Qed.

Lemma omega_cert_postfix : forall c, satisfies omega_rho c.
Proof.
  intros [x e]. unfold satisfies, omega_rho. apply bound_le_any_omega.
Qed.

Lemma omega_cert_upper : forall rho c,
  (forall c', satisfies rho c') -> bound_le (rho (target c)) (omega_rho (target c)).
Proof. intros rho [x e] _. unfold omega_rho. apply bound_le_any_omega. Qed.

Definition omega_cert : solver_certificate :=
  SolverCertificate omega_rho omega_cert_postfix omega_cert_upper.

Definition solver_fixture_two_node_a : constraint := Constraint 0 (BJoin (BUnknown 1) (BConst (BFinite 1))).
Definition solver_fixture_two_node_b : constraint := Constraint 1 (BJoin (BUnknown 0) (BConst (BFinite 1))).
Definition solver_fixture_widening : constraint := Constraint 0 (BSeq (BUnknown 0) (BConst (BFinite 1))).
Definition solver_fixture_chain : constraint := Constraint 2 (BUnknown 1).

Example solver_bridge_two_node_model_value :
  certified_value omega_cert (target solver_fixture_two_node_a) = BOmega /\
  certified_value omega_cert (target solver_fixture_two_node_b) = BOmega.
Proof. split; reflexivity. Qed.

Example solver_bridge_widening_model_value :
  certified_value omega_cert (target solver_fixture_widening) = BOmega.
Proof. reflexivity. Qed.

Example solver_bridge_chain_model_value :
  certified_value omega_cert (target solver_fixture_chain) = BOmega.
Proof. reflexivity. Qed.

(** Relation falsifiability anchors, finding twenty: these fail under a degenerate
    self-loop step relation and pin the semantic substrate of docs/calculus.md §5. *)
Definition beta_id_redex : term := TApp (TLam "x" TyNat (TVar "x")) TZero.
Definition beta_id_contractum : term := TZero.

Example step_anchor_beta_redex_steps_to_contractum :
  step beta_id_redex beta_id_contractum.
Proof. unfold beta_id_redex, beta_id_contractum. apply StepByFunction. reflexivity. Qed.

Example step_anchor_beta_redex_not_self_loop :
  ~ step beta_id_redex beta_id_redex.
Proof.
  intro H. inversion H; subst. unfold beta_id_redex in H0. discriminate H0.
Qed.

Example step_anchor_unhandled_perform_not_self_loop :
  ~ step top_level_perform_golden top_level_perform_golden.
Proof.
  intro H. inversion H; subst. unfold top_level_perform_golden in H0. discriminate H0.
Qed.

Example frame_step_anchor_beta_redex_steps_to_contractum :
  frame_step beta_id_redex 0 beta_id_contractum.
Proof. unfold beta_id_redex, beta_id_contractum. apply FrameStep. reflexivity. Qed.

Example frame_step_anchor_beta_redex_not_self_loop :
  ~ frame_step beta_id_redex 0 beta_id_redex.
Proof.
  intro H. inversion H; subst. unfold beta_id_redex in H0. discriminate H0.
Qed.

Example typing_anchor_perform_has_effl_not_empty :
  has_type [] top_level_perform_golden TyNat EffL (BFinite 0).
Proof. apply Ty_Perform. apply Ty_Zero. Qed.

Example value_anchor_beta_redex_is_not_value :
  is_value beta_id_redex = false.
Proof. reflexivity. Qed.

Example grade_anchor_omega_not_le_finite_zero :
  ~ bound_le BOmega (BFinite 0).
Proof. simpl. exact (fun x => x). Qed.

(** Capture decomposition anchors, Sprint 16 A2: falsifiability witnesses for
    docs/calculus.md §5 handler-free lazy capture. *)

Example capture_anchor_finding21_body :
  capture (TLet "x" (TPerform L TZero) (TVar "x"))
  = Some ([FLet "x" (TVar "x")], TZero).
Proof. reflexivity. Qed.

Example capture_anchor_nested_handler_stops :
  capture (THandle (TPerform L TZero) (Handler "r" (TVar "r") L "p" "k" TZero)) = None.
Proof. reflexivity. Qed.

Example capture_anchor_innermost_perform_wins :
  capture (TPerform L (TPerform L TZero)) = Some ([FPerformArg L], TZero).
Proof. reflexivity. Qed.

Example capture_anchor_value_is_none : capture TZero = None.
Proof. reflexivity. Qed.

Example capture_anchor_direct_perform_empty_ctx :
  capture (TPerform L TZero) = Some ([], TZero).
Proof. reflexivity. Qed.

(** Finding twenty-one dynamics anchors, Sprint 16 A3: captured handler
    contexts are resumed deeply and dropped frame-free. *)
Definition resuming_handler : handler :=
  Handler "r" (TVar "r") L "p" "k" (TResume (TVar "k") TZero).
Definition dropping_handler : handler :=
  Handler "r" (TVar "r") L "p" "k" TZero.

(** B3 anchors: context-rich blocked operations mirror handler-free capture. *)

Example blocked_anchor_finding21_body_is_blocked :
  blocked_on_operation L (TLet "x" (TPerform L TZero) (TVar "x")).
Proof. apply Blocked_Let. apply Blocked_Here. reflexivity. Qed.

Example blocked_anchor_handled_term_is_not_blocked :
  ~ blocked_on_operation L (THandle (TPerform L TZero) dropping_handler).
Proof. intro H. inversion H. Qed.

Definition finding21_term : term :=
  THandle (TLet "x" (TPerform L TZero) (TVar "x")) resuming_handler.

Example finding21_now_steps :
  step finding21_term (TResume (TContVal resuming_handler [FLet "x" (TVar "x")]) TZero).
Proof. apply StepByFunction. reflexivity. Qed.

Example resume_rebuild_anchor :
  step (TResume (TContVal resuming_handler [FLet "x" (TVar "x")]) TZero)
       (THandle (TLet "x" TZero (TVar "x")) resuming_handler).
Proof. apply StepByFunction. reflexivity. Qed.

Example drop_discards_context_anchor :
  step (THandle (TLet "x" (TPerform L TZero) (TVar "x")) dropping_handler) TZero.
Proof. apply StepByFunction. reflexivity. Qed.

Example used_cont_resume_still_stuck :
  stepf (TResume (TUsedContVal resuming_handler []) TZero) = None.
Proof. reflexivity. Qed.

(** Extended dynamics anchors, Sprint 16 A4: multi-frame capture, congruence fidelity, dispatch priority, nested ownership. *)

Example capture_through_two_frames_anchor :
  step (THandle (TSucc (TLet "x" (TPerform L TZero) (TVar "x"))) resuming_handler)
       (TResume (TContVal resuming_handler [FSucc; FLet "x" (TVar "x")]) TZero).
Proof. apply StepByFunction. reflexivity. Qed.

Example perform_arg_congruence_unstuck_anchor :
  step (THandle (TPerform L (THandle TZero dropping_handler)) resuming_handler)
       (THandle (TPerform L TZero) resuming_handler).
Proof. apply StepByFunction. reflexivity. Qed.

Definition steppable_arg : term := TApp (TLam "y" TyNat (TVar "y")) TZero.

Example capture_beats_argument_congruence_anchor :
  step (THandle (TApp (TPerform L TZero) steppable_arg) resuming_handler)
       (TResume (TContVal resuming_handler [FAppFun steppable_arg]) TZero).
Proof. apply StepByFunction. reflexivity. Qed.

Example nested_same_label_inner_owns_anchor :
  step (THandle (THandle (TPerform L TZero) dropping_handler) resuming_handler)
       (THandle TZero resuming_handler).
Proof. apply StepByFunction. reflexivity. Qed.

Example finding21_rebuilt_body_steps :
  step (THandle (TLet "x" TZero (TVar "x")) resuming_handler)
       (THandle TZero resuming_handler).
Proof. apply StepByFunction. reflexivity. Qed.

Example finding21_completes :
  step (THandle TZero resuming_handler) TZero.
Proof. apply StepByFunction. reflexivity. Qed.

(** Finding twenty-three anchors, Sprint 16: value-guarded congruence restored.
    App, case, and resume dispatch now mirrors docs/calculus.md §5 and the Rust
    oracle instead of absorbing congruence cases or falling back to the argument
    after a stuck non-value function/kont. *)
Definition inner_redex : term := TApp (TLam "y" TyNat (TVar "y")) TZero.

Example finding23_beta_arg_congruence_now_steps :
  step (TApp (TLam "x" TyNat (TVar "x")) inner_redex)
       (TApp (TLam "x" TyNat (TVar "x")) TZero).
Proof. apply StepByFunction. reflexivity. Qed.

Example finding23_case_succ_congruence_now_steps :
  step (TCaseNat (TSucc inner_redex) TZero "p" TZero)
       (TCaseNat (TSucc TZero) TZero "p" TZero).
Proof. apply StepByFunction. reflexivity. Qed.

(* Off-grammar fallback removed: a stuck non-value function position no longer
   licenses stepping the argument (§5: E e | v E). Under a handler the same term
   is captured -- the blocked function position is the redex. *)
Example finding23_stuck_fun_no_longer_steps_arg :
  stepf (TApp (TPerform L TZero) inner_redex) = None.
Proof. reflexivity. Qed.

Example finding23_blocked_fun_captured_under_handler :
  step (THandle (TApp (TPerform L TZero) inner_redex) resuming_handler)
       (TResume (TContVal resuming_handler [FAppFun inner_redex]) TZero).
Proof. apply StepByFunction. reflexivity. Qed.

(** Finding twenty-two anchors, Sprint 16: handler binder aliasing.
    With op_param = op_k, typing's context order lets the continuation binding
    shadow (k wins statically) while subst2 substitutes the operation parameter
    first (param wins dynamically). The aliased resuming handler therefore
    steps to an untypable stuck term -- a live L4 counterexample under the
    pre-A6 placeholder rules. A6 adds the freshness premise §4.7 implicitly
    assumes with its distinct p_i/k_i metavariables. The Rust implementation
    shares the disagreement faithfully (src/check/mod.rs op-clause binding
    order vs src/interp.rs substitution order); the Rust-side repair is
    carried-forward work. *)
Definition aliased_handler : handler :=
  Handler "r" (TVar "r") L "k" "k" (TResume (TVar "k") TZero).

Example finding22_aliased_clause_passes_clause_ok :
  handler_clause_ok "k" (TResume (TVar "k") TZero) = true.
Proof. reflexivity. Qed.

Example finding22_param_wins_dynamically :
  step (THandle (TPerform L TZero) aliased_handler) (TResume TZero TZero).
Proof. apply StepByFunction. reflexivity. Qed.

Example finding22_successor_is_stuck :
  stepf (TResume TZero TZero) = None.
Proof. reflexivity. Qed.

(** Continuation typing anchors, Sprint 16 A6: captured continuations carry their
    declared latent boundedness, and resuming clauses must satisfy the deep
    reinstallation accounting side condition. *)

Example contval_types_at_declared_latent :
  has_type [] (TContVal resuming_handler []) (TyCont TyNat (BFinite 0) TyNat)
    EffEmpty (BFinite 0).
Proof.
  unfold resuming_handler.
  eapply Ty_ContVal.
  - apply Ctx_Nil.
  - apply Ty_Var. reflexivity.
  - eapply Ty_Resume.
    + apply Ty_Var. reflexivity.
    + apply Ty_Zero.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. auto.
Qed.

Example resuming_handle_types_finite :
  has_type [] (THandle (TPerform L TZero) resuming_handler) TyNat EffEmpty (BFinite 0).
Proof.
  unfold resuming_handler.
  eapply Ty_HandleResume with
    (eps_body := EffL) (body_beta := BFinite 0) (ret_beta := BFinite 0)
    (op_beta := BFinite 0) (bk := BFinite 0).
  - apply Ty_Perform. apply Ty_Zero.
  - apply Ty_Var. reflexivity.
  - change (BFinite 0) with (bound_seq (BFinite 0) (BFinite 0)).
    eapply Ty_Resume.
    + apply Ty_Var. reflexivity.
    + apply Ty_Zero.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. auto.
Qed.

Example finding22_aliased_resuming_handle_untypable :
  forall t eps beta, ~ has_type [] (THandle (TPerform L TZero) aliased_handler) t eps beta.
Proof.
  intros t eps beta Hty.
  inversion Hty; subst; simpl in *; discriminate.
Qed.

(** Finding twenty-four anchors, Sprint 16: fix binder aliasing. *)
Definition aliased_fix : term := TFix "f" "f" TyNat (TVar "f") Structural.

Example finding24_unfold_substitutes_function_name :
  step aliased_fix (TLam "f" TyNat aliased_fix).
Proof. apply StepByFunction. reflexivity. Qed.

Example finding24_aliased_fix_untypable :
  forall ty eps beta, ~ has_type [] aliased_fix ty eps beta.
Proof.
  intros ty eps beta Hty. inversion Hty; subst; simpl in *; discriminate.
Qed.

(** Finding twenty-five anchors, Sprint 16: fix binds f at the declared arrow. *)

Example finding25_pure_body_div_untypable :
  forall ty eps beta, ~ has_type [] (TFix "f" "x" TyNat TZero Div) ty eps beta.
Proof.
  intros ty eps beta Hty. inversion Hty; subst.
  (* the premise forces TZero at row (eps0, BOmega); invert it *)
  match goal with
  | H : has_type _ TZero _ _ _ |- _ => inversion H
  end.
Qed.

Example finding25_structural_unfold_preserves_type :
  step structural_fix_golden
       (TLam "x" TyNat
          (TCaseNat (TVar "x") TZero "p" (TApp structural_fix_golden (TVar "p")))) /\
  has_type []
    (TLam "x" TyNat
       (TCaseNat (TVar "x") TZero "p" (TApp structural_fix_golden (TVar "p"))))
    (TyArrow TyNat EffEmpty (BFinite 0) TyNat) EffEmpty (BFinite 0).
Proof.
  split.
  - apply StepByFunction. reflexivity.
  - apply Ty_Lam.
    change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
    change (BFinite 0) with (bound_seq (BFinite 0) (bound_join (BFinite 0) (BFinite 0))).
    eapply Ty_CaseNat.
    + apply Ty_Var. reflexivity.
    + apply Ty_Zero.
    + change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
      change (BFinite 0) with (bound_seq (BFinite 0) (bound_seq (BFinite 0) (BFinite 0))).
      eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BFinite 0).
      * unfold structural_fix_golden.
        eapply Ty_FixStructural with (eps := EffEmpty) (beta := BFinite 0).
        -- reflexivity.
        -- change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
           change (BFinite 0) with (bound_seq (BFinite 0) (bound_join (BFinite 0) (BFinite 0))).
           eapply Ty_CaseNat.
           ++ apply Ty_Var. reflexivity.
           ++ apply Ty_Zero.
           ++ change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
              change (BFinite 0) with (bound_seq (BFinite 0) (bound_seq (BFinite 0) (BFinite 0))).
              eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BFinite 0).
              ** apply Ty_Var. reflexivity.
              ** apply Ty_Var. reflexivity.
      * apply Ty_Var. reflexivity.
Qed.

Definition div_cost_handler : handler :=
  Handler "r" (TVar "r") L "p" "k"
    (TLet "z" (TResume (TVar "k") TZero) (TApp div_fix_golden (TVar "z"))).

Example contval_finite_latent_refuses_divergent_clause :
  ~ has_type [] (TContVal div_cost_handler []) (TyCont TyNat (BFinite 0) TyNat)
      EffEmpty (BFinite 0).
Proof.
  intro Hty.
  unfold div_cost_handler in Hty.
  inversion Hty; subst; clear Hty.
  match goal with
  | Hctx : ctx_types [] [] TyNat _ _ _ |- _ =>
      inversion Hctx; subst; clear Hctx
  end.
  match goal with
  | Hret : has_type [("r", TyNat)] (TVar "r") _ _ _ |- _ =>
      inversion Hret; subst; clear Hret
  end.
  match goal with
  | Hclause : has_type _ (TLet "z" _ _) _ _ _ |- _ =>
      inversion Hclause; subst; clear Hclause
  end.
  match goal with
  | Happ : has_type _ (TApp div_fix_golden (TVar "z")) _ _ _ |- _ =>
      inversion Happ; subst; clear Happ
  end.
  unfold div_fix_golden in *.
  match goal with
  | Hfix : has_type _ (TFix "f" "x" TyNat (TApp (TVar "f") (TVar "x")) Div) _ _ _ |- _ =>
      inversion Hfix; subst; clear Hfix
  end.
  repeat rewrite bound_seq_omega_r in *.
  simpl in *.
  contradiction.
Qed.
