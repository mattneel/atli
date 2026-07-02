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
