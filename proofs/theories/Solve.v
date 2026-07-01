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
  certificate_postfix : forall c, satisfies certified_value c
}.

(** This mirrors Part A's sealed Rust [SolverCertificate]: per §7.3/§2.3, consumers read
    certified grades only through a post-fixpoint certificate, never through partial SCC
    iterates. The full solver proof is L8 in [Meta.v]. *)
