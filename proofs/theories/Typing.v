From Coq Require Import Bool.Bool Lists.List Strings.String Arith.PeanoNat.
Import ListNotations StringSyntax.
Open Scope string_scope.

Require Import Atli.Grade.
Require Import Atli.Syntax.

(** Typing skeleton for [docs/calculus.md §4], including amended Handle §4.7. *)

Definition ctx := list (string * ty).

Fixpoint lookup (x : string) (g : ctx) : option ty :=
  match g with
  | [] => None
  | (y, t) :: rest => if String.eqb x y then Some t else lookup x rest
  end.

Inductive has_type : ctx -> term -> ty -> eff -> bound -> Prop :=
| Ty_Var : forall g x t,
    lookup x g = Some t ->
    has_type g (TVar x) t EffEmpty (BFinite 0)
| Ty_Unit : forall g,
    has_type g TUnit TyUnit EffEmpty (BFinite 0)
| Ty_Zero : forall g,
    has_type g TZero TyNat EffEmpty (BFinite 0)
| Ty_Succ : forall g e eps beta,
    has_type g e TyNat eps beta ->
    has_type g (TSucc e) TyNat eps beta
| Ty_CaseNat : forall g scrut e0 x e1 t eps_s eps0 eps1 beta_s beta0 beta1,
    has_type g scrut TyNat eps_s beta_s ->
    has_type g e0 t eps0 beta0 ->
    has_type ((x, TyNat) :: g) e1 t eps1 beta1 ->
    has_type g (TCaseNat scrut e0 x e1) t
      (eff_join eps_s (eff_join eps0 eps1))
      (bound_seq beta_s (bound_join beta0 beta1))
| Ty_Lam : forall g x a body b eps beta,
    has_type ((x, a) :: g) body b eps beta ->
    (* docs/calculus.md §4.2 Abs: the body row is latent on the arrow; the lambda value is pure. *)
    has_type g (TLam x a body) (TyArrow a eps beta b) EffEmpty (BFinite 0)
| Ty_App : forall g f a arg_ty ret_ty lat_eps lat_beta epsf epsa betaf betaa,
    (* docs/calculus.md §4.3 App: operands plus the arrow's latent row are charged. *)
    has_type g f (TyArrow arg_ty lat_eps lat_beta ret_ty) epsf betaf ->
    has_type g a arg_ty epsa betaa ->
    has_type g (TApp f a) ret_ty (eff_join epsf (eff_join epsa lat_eps))
      (bound_seq betaf (bound_seq betaa lat_beta))
| Ty_Let : forall g x e body a b epse epsb betae betab,
    has_type g e a epse betae ->
    has_type ((x, a) :: g) body b epsb betab ->
    has_type g (TLet x e body) b (eff_join epse epsb) (bound_seq betae betab)
| Ty_FixStructural : forall g f x body eps beta,
    (* docs/calculus.md §4.8/§7: structural tag trusts strict-descent premises stated elsewhere. *)
    has_type ((x, TyNat) :: (f, TyArrow TyNat EffEmpty (BFinite 0) TyNat) :: g) body TyNat eps beta ->
    has_type g (TFix f x TyNat body Structural) (TyArrow TyNat eps beta TyNat) EffEmpty (BFinite 0)
| Ty_FixMeasure : forall g f x body eps beta,
    (* SPEC-GAP(measure-tag-trusted-reduced-core): reduced core trusts the measure tag. *)
    has_type ((x, TyNat) :: (f, TyArrow TyNat EffEmpty (BFinite 0) TyNat) :: g) body TyNat eps beta ->
    has_type g (TFix f x TyNat body Measure) (TyArrow TyNat eps beta TyNat) EffEmpty (BFinite 0)
| Ty_FixDiv : forall g f x body eps beta,
    has_type ((x, TyNat) :: (f, TyArrow TyNat eps BOmega TyNat) :: g) body TyNat eps beta ->
    has_type g (TFix f x TyNat body Div) (TyArrow TyNat eps BOmega TyNat) EffEmpty (BFinite 0)
| Ty_Perform : forall g arg beta,
    has_type g arg TyNat EffEmpty beta ->
    has_type g (TPerform L arg) TyNat EffL beta
| Ty_HandleDrop : forall g body rv rbody op_param op_k op_body t eps_body body_beta ret_beta op_beta,
    has_type g body t eps_body body_beta ->
    has_type ((rv, t) :: g) rbody t EffEmpty ret_beta ->
    has_type ((op_k, TyCont TyNat TyNat) :: (op_param, TyNat) :: g) op_body t EffEmpty op_beta ->
    handler_clause_ok op_k op_body = true ->
    mentions_var op_k op_body = false ->
    (* docs/calculus.md §4.7 Handle/drop: beta-hat_i = beta_i under lazy capture. *)
    has_type g (THandle body (Handler rv rbody L op_param op_k op_body)) t EffEmpty
      (bound_seq body_beta (bound_join ret_beta op_beta))
| Ty_HandleResume : forall g body rv rbody op_param op_k op_body t eps_body body_beta ret_beta op_beta,
    has_type g body t eps_body body_beta ->
    has_type ((rv, t) :: g) rbody t EffEmpty ret_beta ->
    has_type ((op_k, TyCont TyNat TyNat) :: (op_param, TyNat) :: g) op_body t EffEmpty op_beta ->
    handler_clause_ok op_k op_body = true ->
    mentions_var op_k op_body = true ->
    (* docs/calculus.md §4.7 Handle/resume: beta-hat_i = beta_i ⊕ beta. *)
    has_type g (THandle body (Handler rv rbody L op_param op_k op_body)) t EffEmpty
      (bound_seq body_beta (bound_join ret_beta (bound_seq op_beta body_beta)))
| Ty_Resume : forall g k arg beta,
    has_type g k (TyCont TyNat TyNat) EffEmpty (BFinite 0) ->
    has_type g arg TyNat EffEmpty beta ->
    has_type g (TResume k arg) TyNat EffEmpty beta
| Ty_ContVal : forall g id,
    has_type g (TContVal id) (TyCont TyNat TyNat) EffEmpty (BFinite 0).

Theorem substitution_preserves_unmentioned_typing : forall g t ty eps beta x replacement,
  has_type g t ty eps beta ->
  mentions_var x t = false ->
  subst x replacement t = t ->
  has_type g (subst x replacement t) ty eps beta.
Proof.
  intros. rewrite H1. assumption.
Qed.
