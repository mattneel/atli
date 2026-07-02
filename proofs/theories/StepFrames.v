From Coq Require Import Arith.PeanoNat.

Require Import Atli.Syntax.
Require Import Atli.Step.

(** Instrumented frame-step scaffold for docs/calculus.md §9.1 / §8.4 (L7 runway).
    The slot metric mirrors the executable bridge at one-step granularity: dropped
    clauses allocate 0 slots; resuming clauses allocate one captured-continuation slot. *)

Definition frame_charge (t : term) : nat :=
  match t with
  | THandle (TPerform L arg) (Handler _ _ _ _ k op_body) =>
      if is_value arg then if mentions_var k op_body then 1 else 0 else 0
  | _ => 0
  end.

Inductive frame_step : term -> nat -> term -> Prop :=
| FrameStep : forall t u,
    stepf t = Some u -> frame_step t (frame_charge t) u.

Theorem frame_step_erases_to_stepf : forall t n u,
  frame_step t n u -> stepf t = Some u.
Proof. intros t n u H. inversion H; subst; assumption. Qed.

Definition frame_max_one (t : term) : nat :=
  match stepf t with
  | Some _ => frame_charge t
  | None => 0
  end.
