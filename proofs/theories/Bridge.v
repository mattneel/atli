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
