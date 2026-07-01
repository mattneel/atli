From Coq Require Import Bool.Bool Strings.String Arith.PeanoNat.
Import StringSyntax.
Open Scope string_scope.

Require Import Atli.Grade.

(** Reduced core syntax, [docs/calculus.md §3] and mechanization target §10. *)

Inductive ty : Type :=
| TyUnit
| TyNat
| TyArrow (a b : ty)
| TyCont (a b : ty).

Inductive rec_tag : Type := Structural | Measure | Div.
Inductive label : Type := L.

Inductive term : Type :=
| TVar (x : string)
| TUnit
| TZero
| TSucc (t : term)
| TCaseNat (scrut zero_body : term) (succ_var : string) (succ_body : term)
| TLam (param : string) (param_ty : ty) (body : term)
| TApp (f a : term)
| TLet (x : string) (expr body : term)
| TFix (func param : string) (param_ty : ty) (body : term) (tag : rec_tag)
| TPerform (op : label) (arg : term)
| THandle (body : term) (h : handler)
| TResume (kont arg : term)
| TContVal (id : nat)
| TUsedContVal (id : nat)
with handler : Type :=
| Handler (return_var : string) (return_body : term)
          (op_label : label) (op_param op_k : string) (op_body : term).

Scheme term_ind' := Induction for term Sort Prop
with handler_ind' := Induction for handler Sort Prop.
Combined Scheme syntax_ind from term_ind', handler_ind'.

Fixpoint is_value (t : term) : bool :=
  match t with
  | TUnit | TZero | TLam _ _ _ | TContVal _ => true
  | TUsedContVal _ => false
  | TSucc inner => is_value inner
  | _ => false
  end.

Fixpoint mentions_var (x : string) (t : term) : bool :=
  match t with
  | TVar y => String.eqb x y
  | TUnit | TZero | TContVal _ | TUsedContVal _ => false
  | TSucc inner => mentions_var x inner
  | TCaseNat scrut zero_body succ_var succ_body =>
      mentions_var x scrut || mentions_var x zero_body ||
      if String.eqb x succ_var then false else mentions_var x succ_body
  | TLam param _ body => if String.eqb x param then false else mentions_var x body
  | TApp f a => mentions_var x f || mentions_var x a
  | TLet y expr body =>
      mentions_var x expr || if String.eqb x y then false else mentions_var x body
  | TFix func param _ body _ =>
      if String.eqb x func || String.eqb x param then false else mentions_var x body
  | TPerform _ arg => mentions_var x arg
  | THandle body (Handler return_var return_body _ op_param op_k op_body) =>
      mentions_var x body ||
      (if String.eqb x return_var then false else mentions_var x return_body) ||
      (if String.eqb x op_param || String.eqb x op_k then false else mentions_var x op_body)
  | TResume kont arg => mentions_var x kont || mentions_var x arg
  end.

Fixpoint free_var_count (x : string) (t : term) : nat :=
  match t with
  | TVar y => if String.eqb x y then 1 else 0
  | TUnit | TZero | TContVal _ | TUsedContVal _ => 0
  | TSucc inner => free_var_count x inner
  | TCaseNat scrut zero_body succ_var succ_body =>
      free_var_count x scrut + free_var_count x zero_body +
      if String.eqb x succ_var then 0 else free_var_count x succ_body
  | TLam param _ body => if String.eqb x param then 0 else free_var_count x body
  | TApp f a => free_var_count x f + free_var_count x a
  | TLet y expr body =>
      free_var_count x expr + if String.eqb x y then 0 else free_var_count x body
  | TFix func param _ body _ =>
      if String.eqb x func || String.eqb x param then 0 else free_var_count x body
  | TPerform _ arg => free_var_count x arg
  | THandle body (Handler return_var return_body _ op_param op_k op_body) =>
      free_var_count x body +
      (if String.eqb x return_var then 0 else free_var_count x return_body) +
      (if String.eqb x op_param || String.eqb x op_k then 0 else free_var_count x op_body)
  | TResume kont arg => free_var_count x kont + free_var_count x arg
  end.

Fixpoint direct_resume_count (k : string) (t : term) : nat :=
  match t with
  | TVar _ | TUnit | TZero | TContVal _ | TUsedContVal _ => 0
  | TSucc inner => direct_resume_count k inner
  | TCaseNat scrut zero_body succ_var succ_body =>
      direct_resume_count k scrut + direct_resume_count k zero_body +
      if String.eqb k succ_var then 0 else direct_resume_count k succ_body
  | TLam param _ body => if String.eqb k param then 0 else direct_resume_count k body
  | TApp f a => direct_resume_count k f + direct_resume_count k a
  | TLet y expr body =>
      direct_resume_count k expr + if String.eqb k y then 0 else direct_resume_count k body
  | TFix func param _ body _ =>
      if String.eqb k func || String.eqb k param then 0 else direct_resume_count k body
  | TPerform _ arg => direct_resume_count k arg
  | THandle body (Handler return_var return_body _ op_param op_k op_body) =>
      direct_resume_count k body +
      (if String.eqb k return_var then 0 else direct_resume_count k return_body) +
      (if String.eqb k op_param || String.eqb k op_k then 0 else direct_resume_count k op_body)
  | TResume (TVar y) arg =>
      (if String.eqb k y then 1 else 0) + direct_resume_count k arg
  | TResume kont arg => direct_resume_count k kont + direct_resume_count k arg
  end.

Fixpoint subst (x : string) (replacement t : term) : term :=
  match t with
  | TVar y => if String.eqb x y then replacement else TVar y
  | TUnit => TUnit
  | TZero => TZero
  | TSucc inner => TSucc (subst x replacement inner)
  | TCaseNat scrut zero_body succ_var succ_body =>
      TCaseNat (subst x replacement scrut) (subst x replacement zero_body) succ_var
        (if String.eqb x succ_var then succ_body else subst x replacement succ_body)
  | TLam param param_ty body =>
      TLam param param_ty (if String.eqb x param then body else subst x replacement body)
  | TApp f a => TApp (subst x replacement f) (subst x replacement a)
  | TLet y expr body =>
      TLet y (subst x replacement expr) (if String.eqb x y then body else subst x replacement body)
  | TFix func param param_ty body tag =>
      TFix func param param_ty
        (if String.eqb x func || String.eqb x param then body else subst x replacement body) tag
  | TPerform op arg => TPerform op (subst x replacement arg)
  | THandle body (Handler return_var return_body op_label op_param op_k op_body) =>
      THandle (subst x replacement body)
        (Handler return_var
          (if String.eqb x return_var then return_body else subst x replacement return_body)
          op_label op_param op_k
          (if String.eqb x op_param || String.eqb x op_k then op_body else subst x replacement op_body))
  | TResume kont arg => TResume (subst x replacement kont) (subst x replacement arg)
  | TContVal id => TContVal id
  | TUsedContVal id => TUsedContVal id
  end.

Definition handler_clause_ok (k : string) (body : term) : bool :=
  if mentions_var k body then
    Nat.eqb (direct_resume_count k body) 1 && Nat.eqb (free_var_count k body) 1
  else Nat.eqb (direct_resume_count k body) 0.

Theorem handler_clause_ok_mentions_iff_resumes : forall k body,
  handler_clause_ok k body = true ->
  (mentions_var k body = true <-> direct_resume_count k body = 1).
Proof.
  intros k body H.
  unfold handler_clause_ok in H.
  destruct (mentions_var k body) eqn:Hm.
  - apply andb_true_iff in H as [Hr _].
    apply Nat.eqb_eq in Hr. split; intros; auto.
  - apply Nat.eqb_eq in H. split; intros C.
    + discriminate C.
    + rewrite H in C. discriminate C.
Qed.
