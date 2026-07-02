From Coq Require Import Arith.PeanoNat.

Require Import Atli.Syntax.
Require Import Atli.Step.

(** Instrumented frame-step scaffold for docs/calculus.md §9.1 / §8.4 (L7 runway). *)

(** §9.1 slot metric, transcribed from the oracle (finding twenty-eight): a
    resuming capture charges the captured context's DEPTH (interp.rs
    step_handle: max_frame.max(frames.len())); the deep rebuild re-charges the
    stored context's depth (interp.rs resume_continuation:
    max_frame.max(cont.frame_size)). Drops are frame-free (§5 H-op-drop). *)
Definition frame_charge (t : term) : nat :=
  match t with
  | THandle body (Handler _ _ _ _ k op_body) =>
      if is_value body then 0
      else match capture body with
           | Some (ctx, _) => if mentions_var k op_body then length ctx else 0
           | None => 0
           end
  | TResume (TContVal _ ctx) v => if is_value v then length ctx else 0
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

Fixpoint frame_max_run (fuel : nat) (t : term) : nat :=
  match fuel with
  | 0 => 0
  | S f => match stepf t with
           | None => 0
           | Some u => Nat.max (frame_charge t) (frame_max_run f u)
           end
  end.
