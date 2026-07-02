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
  eapply Ty_FixStructural.
  eapply Ty_CaseNat.
  - apply Ty_Var. reflexivity.
  - apply Ty_Zero.
  - eapply Ty_App.
    + apply Ty_Var. reflexivity.
    + apply Ty_Var. reflexivity.
Qed.

Example div_fix_typable_like_rust_checker :
  has_type [] div_fix_golden (TyArrow TyNat EffEmpty BOmega TyNat) EffEmpty (BFinite 0).
Proof.
  unfold div_fix_golden.
  eapply Ty_FixDiv with (eps := EffEmpty) (beta := BOmega).
  change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
  change BOmega with (bound_seq (BFinite 0) (bound_seq (BFinite 0) BOmega)).
  eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BOmega).
  - apply Ty_Var. reflexivity.
  - apply Ty_Var. reflexivity.
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
    + eapply Ty_FixDiv with (eps := EffEmpty) (beta := BOmega).
      change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
      change BOmega with (bound_seq (BFinite 0) (bound_seq (BFinite 0) BOmega)).
      eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BOmega).
      * apply Ty_Var. reflexivity.
      * apply Ty_Var. reflexivity.
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
    + eapply Ty_FixDiv with (eps := EffEmpty) (beta := BOmega).
      change EffEmpty with (eff_join EffEmpty (eff_join EffEmpty EffEmpty)).
      change BOmega with (bound_seq (BFinite 0) (bound_seq (BFinite 0) BOmega)).
      eapply Ty_App with (arg_ty := TyNat) (lat_eps := EffEmpty) (lat_beta := BOmega).
      * apply Ty_Var. reflexivity.
      * apply Ty_Var. reflexivity.
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
    + exists TZero. split; reflexivity.
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
