From Coq Require Import Bool.Bool Lists.List.
Import ListNotations.

Require Import Atli.Grade.
Require Import Atli.Syntax.
Require Import Atli.Typing.
Require Import Atli.Step.
Require Import Atli.StepFrames.
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

(** Finding eighteen / SPEC-GAP(progress-open-effects): the third progress disjunct is
    an unhandled top-level operation predicted by its row. The executable bridge pins the
    top-level-perform golden; future context-rich mechanization widens this predicate to
    the full handler-free-for-label evaluation-context grammar of docs/calculus.md §5. *)
Definition blocked_on_operation (l : label) (t : term) : Prop :=
  match l with
  | L => exists v, is_value v = true /\ t = TPerform L v
  end.

Theorem progress : forall t ty eps beta,
  has_type [] t ty eps beta ->
  is_value t = true \/ (exists u, step t u) \/
  (exists l, eff_mem eps = true /\ blocked_on_operation l t).
Admitted.

(** Effect-closed progress corollary, consumed by the Sprint 13 spawn rule: spawned task
    bodies require the empty row, so the unhandled-operation disjunct is uninhabited. *)
Theorem progress_effect_closed : forall t ty beta,
  has_type [] t ty EffEmpty beta -> is_value t = true \/ exists u, step t u.
Proof.
  intros t ty beta Ht.
  destruct (progress t ty EffEmpty beta Ht) as [Hv|[[u Hu]|[l [Hm Hb]]]].
  - left; exact Hv.
  - right; exists u; exact Hu.
  - simpl in Hm. discriminate Hm.
Qed.

(** Finding eighteen / SPEC-GAP(preservation-statement-drift): preservation carries the
    explicit row and boundedness order components claimed by docs/calculus.md §8.2. *)
Theorem preservation : forall t u ty eps beta,
  has_type [] t ty eps beta -> step t u ->
  exists eps' beta', has_type [] u ty eps' beta' /\ eff_sub eps' eps = true /\ bound_le beta' beta.
Admitted.

(* L6 status: Stated-Pending-Infrastructure, owner: future Iris/resource sprint.
   This is deliberately not a theorem yet: the scaffold has no continuation resource/usage
   transition model to quantify over. The intended statement is that well-typed closed
   programs cannot reach the §5 resume-after-use stuck state. L5 supplies the syntactic
   exactly-one direct resume premise; the missing infrastructure is the dynamic one-shot
   resource model. *)

(** L7: boundedness soundness over the docs/calculus.md §9.1 slot metric. Sprint 15 builds
    [frame_step] and proves erasure; the strengthened preservation invariant that finite
    certified beta bounds every frame-counting prefix is the next proofs sprint's owner. *)
Theorem boundedness_soundness : forall t ty n,
  has_type [] t ty EffEmpty (BFinite n) ->
  forall u frames, frame_step t frames u -> frames <= n.
Admitted.

Theorem solver_certificate_postfix_field : forall cert c,
  satisfies (certified_value cert) c.
Proof. intros cert c. exact (certificate_postfix cert c). Qed.

Theorem solver_certificate_soundness : forall rho cert c,
  (forall c', satisfies rho c') ->
  satisfies (certified_value cert) c /\ bound_le (rho (target c)) (certified_value cert (target c)).
Admitted.

(* L9 status: Stated-Pending-Infrastructure, owner: future heap/graded-context sprint.
   Sprint 11 extends the executable compiler with docs/calculus.md §4 data affinity and
   §9.2 arrays, but this Rocq scaffold deliberately does not yet model heap arrays or
   Q-graded data contexts. The intended theorem states that, under the affine discipline,
   [inplace set] is observationally equivalent to functional [set]. It is not represented
   as an [Admitted] theorem until those missing definitions exist. *)

(* L10 status: Stated-Pending-Infrastructure, owner: future concurrent-semantics sprint.
   Sprint 13 extends the executable compiler with docs/calculus.md §5 task oracle semantics
   and §9.3 region-tree native tasks. The intended theorem states schedule independence:
   every fair native task interleaving of a well-typed program has the same observables as
   the deterministic sequential oracle. It needs a concurrent small-step relation over task
   pools and region-tree ownership, so it is not represented as an [Admitted] theorem yet. *)
