From Coq Require Import Bool.Bool Strings.String Lists.List.
Import ListNotations.
Import StringSyntax.
Open Scope string_scope.

Require Import Atli.Grade.
Require Import Atli.Syntax.
Require Import Atli.Typing.

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

Example structural_fix_typable_like_rust_checker : exists beta,
  has_type [] structural_fix_golden (TyArrow TyNat TyNat) EffEmpty beta.
Proof.
  eexists. unfold structural_fix_golden.
  eapply Ty_FixStructural.
  eapply Ty_CaseNat.
  - apply Ty_Var. reflexivity.
  - apply Ty_Zero.
  - eapply Ty_App.
    + apply Ty_Var. reflexivity.
    + apply Ty_Var. reflexivity.
Qed.

Example div_fix_typable_like_rust_checker :
  has_type [] div_fix_golden (TyArrow TyNat TyNat) EffEmpty BOmega.
Proof.
  unfold div_fix_golden. eapply Ty_FixDiv.
  eapply Ty_App.
  - apply Ty_Var. reflexivity.
  - apply Ty_Var. reflexivity.
Qed.
