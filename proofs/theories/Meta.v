From Coq Require Import Bool.Bool Lists.List.
Import ListNotations.

Require Import Atli.Grade.
Require Import Atli.Syntax.
Require Import Atli.Typing.
Require Import Atli.Step.
Require Import Atli.Solve.

(** Proof ladder for [docs/calculus.md §8] and mechanization target §10. *)

Theorem L2_substitution_nonhandler_min : forall g t ty eps beta x replacement,
  has_type g t ty eps beta ->
  mentions_var x t = false ->
  subst x replacement t = t ->
  has_type g (subst x replacement t) ty eps beta.
Proof. apply substitution_preserves_unmentioned_typing. Qed.

Theorem L5_mentions_iff_resume : forall k body,
  handler_clause_ok k body = true ->
  (mentions_var k body = true <-> direct_resume_count k body = 1).
Proof. apply handler_clause_ok_mentions_iff_resumes. Qed.

Theorem step_is_deterministic : forall t u v,
  step t u -> step t v -> u = v.
Proof. apply step_deterministic. Qed.

(* L3 sketch, owner: future metatheory sprint. Induct on the typing derivation after the
   full substitution/weakening library is in place; use L5 to show the split H-op rules are
   exclusive and the one-shot-stuck state is unreachable for well-typed closed terms. *)
Theorem progress : forall t ty eps beta,
  has_type [] t ty eps beta -> is_value t = true \/ exists u, step t u.
Admitted.

(* L4 sketch, owner: future metatheory sprint. Prove substitution preserves full typing,
   then case-analyze each §5 reduction. Handler cases use row discharge from §4.7 and L5
   to align FV dispatch with typed resume usage. *)
Theorem preservation : forall t u ty eps beta,
  has_type [] t ty eps beta -> step t u -> exists eps' beta', has_type [] u ty eps' beta'.
Admitted.

(* L6 status: Stated-Pending-Infrastructure, owner: future Iris/resource sprint.
   This is deliberately not a theorem yet: the scaffold has no continuation resource/usage
   transition model to quantify over. The intended statement is that well-typed closed
   programs cannot reach the §5 resume-after-use stuck state. L5 supplies the syntactic
   exactly-one direct resume premise; the missing infrastructure is the dynamic one-shot
   resource model. *)

(* L7 status: Stated-Pending-Infrastructure, owner: future boundedness sprint.
   This is deliberately not a theorem yet: the scaffold has no instrumented frame-slot
   step relation. Once that relation exists, the statement should quantify over reductions
   from a term typed with finite beta and prove that every realized frame-slot prefix is <=
   beta. The metric is the docs/calculus.md §9.1 slot model (tier-1 i64 slots); byte
   layout remains the refinement tracked by SPEC-GAP(frame-metric-byte-accuracy). *)

Theorem solver_certificate_postfix_field : forall cert c,
  satisfies (certified_value cert) c.
Proof. intros cert c. exact (certificate_postfix cert c). Qed.

(* L8 sketch, owner: future solver-proof sprint. Prove SCC iteration/widening returns a
   post-fixpoint and widening only moves upward, then connect [solver_certificate] to Rust
   Part A's sealed [SolverCertificate] invariant. *)
Theorem solver_certificate_soundness : forall rho cert c,
  (forall c', satisfies rho c') ->
  satisfies (certified_value cert) c /\ bound_le (rho (target c)) (certified_value cert (target c)).
Admitted.
