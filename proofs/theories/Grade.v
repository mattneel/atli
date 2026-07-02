From Coq Require Import Arith Lia.

(** Grade algebra for the reduced core, mirroring [docs/calculus.md §2]. *)

Inductive qgrade : Type := Q0 | Q1 | QOmega.

Definition q_plus (a b : qgrade) : qgrade :=
  match a, b with
  | Q0, x | x, Q0 => x
  | Q1, Q1 => QOmega
  | QOmega, _ | _, QOmega => QOmega
  end.

Definition q_mul (a b : qgrade) : qgrade :=
  match a, b with
  | Q0, _ | _, Q0 => Q0
  | Q1, x | x, Q1 => x
  | QOmega, QOmega => QOmega
  end.

Theorem q_plus_assoc : forall a b c, q_plus (q_plus a b) c = q_plus a (q_plus b c).
Proof. destruct a, b, c; reflexivity. Qed.

Theorem q_plus_comm : forall a b, q_plus a b = q_plus b a.
Proof. destruct a, b; reflexivity. Qed.

Theorem q_plus_zero_l : forall a, q_plus Q0 a = a.
Proof. destruct a; reflexivity. Qed.

Theorem q_mul_assoc : forall a b c, q_mul (q_mul a b) c = q_mul a (q_mul b c).
Proof. destruct a, b, c; reflexivity. Qed.

Theorem q_mul_one_l : forall a, q_mul Q1 a = a.
Proof. destruct a; reflexivity. Qed.

Theorem q_one_plus_one : q_plus Q1 Q1 = QOmega.
Proof. reflexivity. Qed.

Inductive eff : Type := EffEmpty | EffL.

Definition eff_mem (e : eff) : bool :=
  match e with EffEmpty => false | EffL => true end.

Definition eff_sub (a b : eff) : bool :=
  match a, b with
  | EffEmpty, _ => true
  | EffL, EffL => true
  | EffL, EffEmpty => false
  end.

Definition eff_join (a b : eff) : eff :=
  match a, b with
  | EffEmpty, x | x, EffEmpty => x
  | EffL, EffL => EffL
  end.

Theorem eff_join_assoc : forall a b c, eff_join (eff_join a b) c = eff_join a (eff_join b c).
Proof. destruct a, b, c; reflexivity. Qed.

Theorem eff_join_comm : forall a b, eff_join a b = eff_join b a.
Proof. destruct a, b; reflexivity. Qed.

Theorem eff_join_idem : forall a, eff_join a a = a.
Proof. destruct a; reflexivity. Qed.

Theorem eff_join_empty_l : forall a, eff_join EffEmpty a = a.
Proof. destruct a; reflexivity. Qed.

Theorem eff_sub_refl : forall a, eff_sub a a = true.
Proof. destruct a; reflexivity. Qed.

Inductive bound : Type := BFinite (n : nat) | BOmega.

Definition bound_seq (a b : bound) : bound :=
  match a, b with
  | BFinite m, BFinite n => BFinite (m + n)
  | BOmega, _ | _, BOmega => BOmega
  end.

Definition bound_join (a b : bound) : bound :=
  match a, b with
  | BFinite m, BFinite n => BFinite (Nat.max m n)
  | BOmega, _ | _, BOmega => BOmega
  end.

Definition bound_le (a b : bound) : Prop :=
  match a, b with
  | BFinite m, BFinite n => m <= n
  | BFinite _, BOmega => True
  | BOmega, BOmega => True
  | BOmega, BFinite _ => False
  end.

Theorem bound_seq_assoc : forall a b c,
  bound_seq (bound_seq a b) c = bound_seq a (bound_seq b c).
Proof.
  destruct a, b, c; simpl; try reflexivity.
  now rewrite Nat.add_assoc.
Qed.

Theorem bound_seq_zero_l : forall a, bound_seq (BFinite 0) a = a.
Proof. destruct a; reflexivity. Qed.

Theorem bound_seq_zero_r : forall a, bound_seq a (BFinite 0) = a.
Proof. destruct a; simpl; now rewrite ?Nat.add_0_r. Qed.

Theorem bound_seq_omega_l : forall a, bound_seq BOmega a = BOmega.
Proof. destruct a; reflexivity. Qed.

Theorem bound_seq_omega_r : forall a, bound_seq a BOmega = BOmega.
Proof. destruct a; reflexivity. Qed.

Theorem bound_join_assoc : forall a b c,
  bound_join (bound_join a b) c = bound_join a (bound_join b c).
Proof.
  destruct a, b, c; simpl; try reflexivity.
  now rewrite Nat.max_assoc.
Qed.

Theorem bound_join_comm : forall a b, bound_join a b = bound_join b a.
Proof.
  destruct a, b; simpl; try reflexivity.
  now rewrite Nat.max_comm.
Qed.

Theorem bound_join_idem : forall a, bound_join a a = a.
Proof.
  destruct a; simpl; try reflexivity.
  now rewrite Nat.max_idempotent.
Qed.

Theorem bound_le_refl : forall a, bound_le a a.
Proof. destruct a; simpl; auto. Qed.

Theorem bound_join_upper_l : forall a b, bound_le a (bound_join a b).
Proof. destruct a, b; simpl; auto; lia. Qed.

Theorem bound_join_upper_r : forall a b, bound_le b (bound_join a b).
Proof. destruct a, b; simpl; auto; lia. Qed.
