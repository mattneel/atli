From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import Atli.Grade.

(** Constraint shapes for [docs/calculus.md §7.1] and the sealed certificate invariant. *)

Definition unknown := nat.

Inductive bexpr : Type :=
| BConst (b : bound)
| BUnknown (u : unknown)
| BSeq (a b : bexpr)
| BJoin (a b : bexpr).

Fixpoint beval (rho : unknown -> bound) (e : bexpr) : bound :=
  match e with
  | BConst b => b
  | BUnknown u => rho u
  | BSeq a b => bound_seq (beval rho a) (beval rho b)
  | BJoin a b => bound_join (beval rho a) (beval rho b)
  end.

Record constraint : Type := Constraint { target : unknown; rhs : bexpr }.

Definition satisfies (rho : unknown -> bound) (c : constraint) : Prop :=
  bound_le (beval rho (rhs c)) (rho (target c)).

Record solver_certificate : Type := SolverCertificate {
  certified_value : unknown -> bound;
  certificate_postfix : forall c, satisfies certified_value c;
  certificate_upper : forall rho c,
    (forall c', satisfies rho c') -> bound_le (rho (target c)) (certified_value (target c))
}.

(** Functional model of docs/calculus.md §7.2 at the certificate boundary: a completed
    solve returns a post-fixpoint plus the upward/no-under-approximation field. *)
Definition solver_model_returns (cert : solver_certificate) : Prop :=
  forall c, satisfies (certified_value cert) c.

(** This mirrors Part A's sealed Rust [SolverCertificate]: per §7.3/§2.3, consumers read
    certified grades only through a post-fixpoint certificate, never through partial SCC
    iterates. The full solver proof is L8 in [Meta.v]. *)

(** Sprint 16 D1: the §7.2 functional solver model (rule names cited per step).
    Mirrors src/check/solve.rs post finding twenty-six: joint fuel-based iteration from
    ⊥ (§7.2 step 2, threshold k), widening to ω on still-growing unknowns iterated to
    stability (§7.2 step 3; §2.3 upward-only), certification on convergence (§7.3 phase
    gate). SCC decomposition (§7.2 step 1) is an evaluation-order optimization the joint
    model does not need; narrowing (§7.2 step 4) is not implemented on either side. *)

Definition valuation := unknown -> bound.
Definition vbot : valuation := fun _ => BFinite 0.

Definition bound_eqb (a b : bound) : bool :=
  match a, b with
  | BFinite m, BFinite n => Nat.eqb m n
  | BOmega, BOmega => true
  | _, _ => false
  end.

Lemma bound_eqb_eq : forall a b, bound_eqb a b = true <-> a = b.
Proof.
  destruct a as [m|], b as [n|]; simpl; split; intro H; try discriminate; try reflexivity.
  - apply Nat.eqb_eq in H. now subst.
  - inversion H; subst. now rewrite Nat.eqb_refl.
Qed.

(* Rust grows(): ω on either side is not 'growing'; finite strictly-increasing is. *)
Definition bound_grows (current next : bound) : bool :=
  match current, next with
  | BOmega, _ | _, BOmega => false
  | BFinite a, BFinite b => Nat.ltb a b
  end.

Fixpoint bexpr_unknowns (e : bexpr) : list unknown :=
  match e with
  | BConst _ => []
  | BUnknown u => [u]
  | BSeq a b | BJoin a b => bexpr_unknowns a ++ bexpr_unknowns b
  end.

Definition domain (cs : list constraint) : list unknown :=
  flat_map (fun c => target c :: bexpr_unknowns (rhs c)) cs.

(* join of all rhs evaluations targeting u — Rust apply_scc's per-unknown rhs. *)
Definition rhs_join (cs : list constraint) (rho : valuation) (u : unknown) : bound :=
  fold_right (fun c acc =>
      if Nat.eqb (target c) u then bound_join (beval rho (rhs c)) acc else acc)
    (BFinite 0) cs.

(* one joint monotone pass — Rust's candidate = current.join(rhs). *)
Definition pass (cs : list constraint) (rho : valuation) : valuation :=
  fun u => bound_join (rho u) (rhs_join cs rho u).

(* the widened pass: still-growing unknowns jump to ω (§7.2 step 3, canonical ∇). *)
Definition wpass (cs : list constraint) (rho : valuation) : valuation :=
  fun u => let cand := bound_join (rho u) (rhs_join cs rho u) in
           if bound_grows (rho u) cand then BOmega else cand.

Definition vals_equal_on (dom : list unknown) (r1 r2 : valuation) : bool :=
  forallb (fun u => bound_eqb (r1 u) (r2 u)) dom.

Fixpoint iterate_model (cs : list constraint) (fuel : nat) (rho : valuation)
  : valuation * bool :=
  match fuel with
  | 0 => (rho, false)
  | S f => let rho' := pass cs rho in
           if vals_equal_on (domain cs) rho rho' then (rho, true)
           else iterate_model cs f rho'
  end.

(* finding twenty-six on the model side: the widened pass iterates to stability. *)
Fixpoint widen_model (cs : list constraint) (fuel : nat) (rho : valuation)
  : valuation * bool :=
  match fuel with
  | 0 => (rho, false)
  | S f => let rho' := wpass cs rho in
           if vals_equal_on (domain cs) rho rho' then (rho, true)
           else widen_model cs f rho'
  end.

Definition solver_threshold_k : nat := 6. (* src/check/solve.rs SOLVER_THRESHOLD_K *)

Definition solve_model (cs : list constraint) : valuation * bool :=
  match iterate_model cs solver_threshold_k vbot with
  | (rho, true) => (rho, true)
  | (rho, false) => widen_model cs (S (length (domain cs))) rho
  end.

(* §7.3's sealed-read boundary: a certified grade is read by evaluating at the
   certified map — nothing else (certificate-equals-evaluation, D2 conjunct 3). *)
Definition certified_read (rho : valuation) (e : bexpr) : bound := beval rho e.

(* Sprint 03 two-node join class: converges to the finite lfp (1,1). *)
Example model_anchor_two_node_converges :
  let cs := [Constraint 0 (BJoin (BUnknown 1) (BConst (BFinite 1)));
             Constraint 1 (BJoin (BUnknown 0) (BConst (BFinite 1)))] in
  (fst (solve_model cs) 0, fst (solve_model cs) 1, snd (solve_model cs))
  = (BFinite 1, BFinite 1, true).
Proof. vm_compute. reflexivity. Qed.

(* Sprint 03 widening class: the self-seq loop widens to ω. *)
Example model_anchor_self_seq_widens :
  let cs := [Constraint 0 (BSeq (BUnknown 0) (BConst (BFinite 1)))] in
  (fst (solve_model cs) 0, snd (solve_model cs)) = (BOmega, true).
Proof. vm_compute. reflexivity. Qed.

(* Finding twenty-six shape: the widen loop reaches a post-fixpoint — both ω,
   cross-citing src/check/solve.rs widened_certificate_is_a_postfixpoint_across_the_scc. *)
Example model_anchor_finding26_postfix :
  let cs := [Constraint 0 (BSeq (BUnknown 1) (BConst (BFinite 1)));
             Constraint 1 (BUnknown 0)] in
  (fst (solve_model cs) 0, fst (solve_model cs) 1, snd (solve_model cs))
  = (BOmega, BOmega, true).
Proof. vm_compute. reflexivity. Qed.

(* Unconstrained unknowns stay at ⊥ (Rust certificate.value default ZERO). *)
Example model_anchor_chain_default_zero :
  let cs := [Constraint 2 (BUnknown 1)] in
  (fst (solve_model cs) 2, snd (solve_model cs)) = (BFinite 0, true).
Proof. vm_compute. reflexivity. Qed.

(** Sprint 16 D2: the three §7.2 soundness conjuncts over the functional model. *)

Lemma target_in_domain : forall cs c,
  In c cs -> In (target c) (domain cs).
Proof.
  intros cs c Hin.
  unfold domain.
  apply in_flat_map.
  exists c. split; [exact Hin|].
  simpl. left. reflexivity.
Qed.

Lemma vals_equal_on_member_eq : forall dom r1 r2 u,
  vals_equal_on dom r1 r2 = true ->
  In u dom ->
  r1 u = r2 u.
Proof.
  intros dom r1 r2 u Heq Hin.
  unfold vals_equal_on in Heq.
  apply forallb_forall with (x := u) in Heq; [|exact Hin].
  apply bound_eqb_eq. exact Heq.
Qed.

Lemma iterate_model_true_stable : forall cs fuel rho0 rho,
  iterate_model cs fuel rho0 = (rho, true) ->
  vals_equal_on (domain cs) rho (pass cs rho) = true.
Proof.
  intros cs fuel.
  induction fuel as [|fuel IH]; intros rho0 rho Hiter; simpl in Hiter.
  - discriminate.
  - destruct (vals_equal_on (domain cs) rho0 (pass cs rho0)) eqn:Hstable.
    + inversion Hiter. subst. exact Hstable.
    + eapply IH. exact Hiter.
Qed.

Lemma widen_model_true_stable : forall cs fuel rho0 rho,
  widen_model cs fuel rho0 = (rho, true) ->
  vals_equal_on (domain cs) rho (wpass cs rho) = true.
Proof.
  intros cs fuel.
  induction fuel as [|fuel IH]; intros rho0 rho Hiter; simpl in Hiter.
  - discriminate.
  - destruct (vals_equal_on (domain cs) rho0 (wpass cs rho0)) eqn:Hstable.
    + inversion Hiter. subst. exact Hstable.
    + eapply IH. exact Hiter.
Qed.

Lemma rhs_join_member_le : forall cs rho c u,
  In c cs -> target c = u -> bound_le (beval rho (rhs c)) (rhs_join cs rho u).
Proof.
  induction cs as [|d rest IH]; intros rho c u Hin Htarget.
  - contradiction.
  - simpl in Hin.
    unfold rhs_join. simpl.
    fold (rhs_join rest rho u).
    destruct Hin as [Hc|Hin].
    + subst d. rewrite Htarget, Nat.eqb_refl.
      apply bound_join_upper_l.
    + destruct (Nat.eqb (target d) u) eqn:Hdu.
      * eapply bound_le_trans.
        -- eapply IH; eauto.
        -- apply bound_join_upper_r.
      * eapply IH; eauto.
Qed.

Lemma bound_join_absorb_le : forall a b,
  bound_join a b = a -> bound_le b a.
Proof.
  destruct a as [m|], b as [n|]; simpl; intro H; try discriminate; auto.
  injection H as Hmax.
  rewrite <- Hmax.
  apply Nat.le_max_r.
Qed.

Lemma pass_stable_postfix : forall cs rho,
  vals_equal_on (domain cs) rho (pass cs rho) = true ->
  forall c, In c cs -> satisfies rho c.
Proof.
  intros cs rho Hstable c Hin.
  unfold satisfies.
  pose proof (target_in_domain cs c Hin) as Hdom.
  pose proof (vals_equal_on_member_eq (domain cs) rho (pass cs rho) (target c)
    Hstable Hdom) as Heq.
  unfold pass in Heq.
  eapply bound_le_trans.
  - eapply rhs_join_member_le; [exact Hin|reflexivity].
  - apply bound_join_absorb_le. symmetry. exact Heq.
Qed.

Lemma wpass_stable_postfix : forall cs rho,
  vals_equal_on (domain cs) rho (wpass cs rho) = true ->
  forall c, In c cs -> satisfies rho c.
Proof.
  intros cs rho Hstable c Hin.
  unfold satisfies.
  pose proof (target_in_domain cs c Hin) as Hdom.
  pose proof (vals_equal_on_member_eq (domain cs) rho (wpass cs rho) (target c)
    Hstable Hdom) as Heq.
  unfold wpass in Heq.
  set (u := target c) in *.
  set (cand := bound_join (rho u) (rhs_join cs rho u)) in *.
  destruct (bound_grows (rho u) cand) eqn:Hgrows.
  - destruct (rho u) as [n|] eqn:Hrho.
    + discriminate.
    + simpl in Hgrows. discriminate.
  - eapply bound_le_trans.
    + eapply rhs_join_member_le; [exact Hin|reflexivity].
    + apply bound_join_absorb_le.
      unfold cand.
      symmetry. exact Heq.
Qed.

(* -------- Conjunct 1: post-fixpoint satisfaction (§7.2/§7.3). -------- *)
Theorem solve_model_postfix : forall cs rho,
  solve_model cs = (rho, true) ->
  forall c, In c cs -> satisfies rho c.
Proof.
  intros cs rho Hsolve.
  unfold solve_model in Hsolve.
  destruct (iterate_model cs solver_threshold_k vbot) as [rho_iter ok_iter] eqn:Hiter.
  destruct ok_iter.
  - inversion Hsolve. subst.
    apply pass_stable_postfix.
    eapply iterate_model_true_stable. exact Hiter.
  - destruct (widen_model cs (S (length (domain cs))) rho_iter) as [rho_w ok_w] eqn:Hwiden.
    destruct ok_w; [|discriminate].
    inversion Hsolve. subst.
    apply wpass_stable_postfix.
    eapply widen_model_true_stable. exact Hwiden.
Qed.

(* -------- Conjunct 2: widening never under-approximates (§8.5, the §2.3
   inverted-soundness direction: the goal predicate is >= true size, not a safe
   set. The model iterates up from bottom, so the convergent branch returns a
   lower bound of every solution; both passes are extensive, so widening only
   moves up from those iterates. -------- *)
Theorem pass_extensive : forall cs rho u, bound_le (rho u) (pass cs rho u).
Proof.
  intros cs rho u.
  unfold pass.
  apply bound_join_upper_l.
Qed.

Theorem wpass_extensive : forall cs rho u, bound_le (rho u) (wpass cs rho u).
Proof.
  intros cs rho u.
  unfold wpass.
  destruct (bound_grows (rho u) (bound_join (rho u) (rhs_join cs rho u))).
  - apply bound_le_omega.
  - apply bound_join_upper_l.
Qed.

Theorem beval_monotone : forall e r1 r2,
  (forall u, bound_le (r1 u) (r2 u)) -> bound_le (beval r1 e) (beval r2 e).
Proof.
  induction e as [b|u|a IHa b IHb|a IHa b IHb]; intros r1 r2 Hle; simpl.
  - apply bound_le_refl.
  - apply Hle.
  - apply bound_seq_mono; auto.
  - apply bound_join_mono; auto.
Qed.

Lemma rhs_join_below_solution : forall cs rho rho_sol u,
  (forall x, bound_le (rho x) (rho_sol x)) ->
  (forall c, In c cs -> satisfies rho_sol c) ->
  bound_le (rhs_join cs rho u) (rho_sol u).
Proof.
  induction cs as [|c rest IH]; intros rho rho_sol u Hrho Hsol.
  - simpl. apply bound_le_zero.
  - unfold rhs_join. simpl.
    fold (rhs_join rest rho u).
    destruct (Nat.eqb (target c) u) eqn:Htarget.
    + apply Nat.eqb_eq in Htarget.
      apply bound_join_lub.
      * eapply bound_le_trans.
        -- apply beval_monotone. exact Hrho.
        -- pose proof (Hsol c (or_introl eq_refl)) as Hsat.
           unfold satisfies in Hsat.
           rewrite Htarget in Hsat. exact Hsat.
      * apply IH.
        -- exact Hrho.
        -- intros c' Hin. apply Hsol. right. exact Hin.
    + apply IH.
      * exact Hrho.
      * intros c' Hin. apply Hsol. right. exact Hin.
Qed.

Lemma pass_below_solution : forall cs rho rho_sol,
  (forall u, bound_le (rho u) (rho_sol u)) ->
  (forall c, In c cs -> satisfies rho_sol c) ->
  forall u, bound_le (pass cs rho u) (rho_sol u).
Proof.
  intros cs rho rho_sol Hrho Hsol u.
  unfold pass.
  apply bound_join_lub.
  - apply Hrho.
  - apply rhs_join_below_solution; assumption.
Qed.

Lemma iterate_model_below_solution : forall cs fuel rho0 rho rho_sol,
  (forall u, bound_le (rho0 u) (rho_sol u)) ->
  (forall c, In c cs -> satisfies rho_sol c) ->
  iterate_model cs fuel rho0 = (rho, true) ->
  forall u, bound_le (rho u) (rho_sol u).
Proof.
  intros cs fuel.
  induction fuel as [|fuel IH]; intros rho0 rho rho_sol Hrho Hsol Hiter u; simpl in Hiter.
  - discriminate.
  - destruct (vals_equal_on (domain cs) rho0 (pass cs rho0)) eqn:Hstable.
    + inversion Hiter. subst. apply Hrho.
    + eapply IH.
      * exact (pass_below_solution cs rho0 rho_sol Hrho Hsol).
      * exact Hsol.
      * exact Hiter.
Qed.

Theorem converged_least : forall cs rho,
  iterate_model cs solver_threshold_k vbot = (rho, true) ->
  forall rho_sol, (forall c, In c cs -> satisfies rho_sol c) ->
  forall u, bound_le (rho u) (rho_sol u).
Proof.
  intros cs rho Hiter rho_sol Hsol u.
  eapply iterate_model_below_solution.
  - intros x. unfold vbot. apply bound_le_zero.
  - exact Hsol.
  - exact Hiter.
Qed.

(* -------- Conjunct 3: certificate-equals-evaluation (§7.3's sealed read). ---- *)
Theorem certified_read_is_evaluation : forall rho e,
  certified_read rho e = beval rho e.
Proof. reflexivity. Qed.

(* -------- Finding twenty-seven: the v0.5.x sealed-record statement audit. ----
   [solver_certificate]'s field quantifications range over all constraints; the record is
   not indexed by the solved system. Its postfix field already forces every certified
   value to omega: the record admits exactly the omega certificate, and finite Rust
   certificates are unrepresentable in it. The L8 statement over this record is therefore
   true but degenerate; the algorithmic content of §7.2 soundness lives in the model
   lemmas above. Refactoring the record to carry its constraint system is carried-forward
   work. -------- *)
Theorem solver_certificate_only_omega : forall (cert : solver_certificate) u,
  certified_value cert u = BOmega.
Proof.
  intros cert u.
  pose proof (certificate_postfix cert (Constraint u (BConst BOmega))) as Hpost.
  unfold satisfies in Hpost. simpl in Hpost.
  destruct (certified_value cert u); [contradiction|reflexivity].
Qed.
