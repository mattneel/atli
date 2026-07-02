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
| Ty_HandleDrop : forall g body rv rbody op_param op_k op_body t eps_body body_beta ret_beta op_beta bk,
    has_type g body t eps_body body_beta ->
    has_type ((rv, t) :: g) rbody t EffEmpty ret_beta ->
    has_type ((op_k, TyCont TyNat bk t) :: (op_param, TyNat) :: g) op_body t EffEmpty op_beta ->
    handler_clause_ok op_k op_body = true ->
    mentions_var op_k op_body = false ->
    (* No freshness premise here: with an aliased dropping clause the shared name is
       unmentioned, so the split is harmless. *)
    (* docs/calculus.md §4.7 Handle/drop: beta-hat_i = beta_i under lazy capture. *)
    has_type g (THandle body (Handler rv rbody L op_param op_k op_body)) t EffEmpty
      (bound_seq body_beta (bound_join ret_beta op_beta))
| Ty_HandleResume : forall g body rv rbody op_param op_k op_body t eps_body body_beta ret_beta op_beta bk,
    has_type g body t eps_body body_beta ->
    has_type ((rv, t) :: g) rbody t EffEmpty ret_beta ->
    has_type ((op_k, TyCont TyNat bk t) :: (op_param, TyNat) :: g) op_body t EffEmpty op_beta ->
    handler_clause_ok op_k op_body = true ->
    mentions_var op_k op_body = true ->
    (* finding twenty-two: §4.7's distinct p_i/k_i metavariables, made explicit *)
    String.eqb op_param op_k = false ->
    (* §4.7/§6.2 under deep reinstallation (§5 H-op-resume): the continuation's
       latent bound must cover the rebuilt handle — the recursive constraint β ⊒
       c ⊕ β_rec stated in-rule. ω is always admissible (§2.3:
       over-approximation is the safe direction); finite bk exists exactly when
       the residual costs ground at zero. *)
    bound_le (bound_seq body_beta (bound_join ret_beta (bound_seq op_beta body_beta))) bk ->
    has_type g (THandle body (Handler rv rbody L op_param op_k op_body)) t EffEmpty
      (bound_seq body_beta (bound_join ret_beta (bound_seq op_beta body_beta)))
| Ty_Resume : forall g k arg t bk beta,
    has_type g k (TyCont TyNat bk t) EffEmpty (BFinite 0) ->
    has_type g arg TyNat EffEmpty beta ->
    (* §4.6/§3.1: resume charges the continuation's latent bound; the rebuilt
       handle (§5 H-op-resume) is paid for here. *)
    has_type g (TResume k arg) t EffEmpty (bound_seq beta bk)
| Ty_ContVal : forall g ctx rv rbody op_param op_k op_body t eps_p beta_p ret_beta op_beta bk,
    ctx_types [] ctx TyNat t eps_p beta_p ->
    has_type ((rv, t) :: []) rbody t EffEmpty ret_beta ->
    has_type ((op_k, TyCont TyNat bk t) :: (op_param, TyNat) :: []) op_body t EffEmpty op_beta ->
    handler_clause_ok op_k op_body = true ->
    mentions_var op_k op_body = true ->
    String.eqb op_param op_k = false ->
    bound_le (bound_seq beta_p (bound_join ret_beta (bound_seq op_beta beta_p))) bk ->
    (* §4.6: a continuation value stores the captured context and the installed
       handler's clause typings, []-pinned by the A5 closedness invariant; its
       latent bound covers the deep rebuild THandle (plug ctx v) h (§5). Only
       resuming handlers mint TContVal (stepf H-op-resume), so the premises
       mirror Ty_HandleResume's shapes, finding-22 freshness included. *)
    has_type g (TContVal (Handler rv rbody L op_param op_k op_body) ctx)
      (TyCont TyNat bk t) EffEmpty (BFinite 0)
(** [ctx_types g E a c eps beta] says that plugging a closed value of type [a]
    at row [EffEmpty]/[BFinite 0] into [E] yields a term of type [c] at row
    [(eps, beta)]. docs/calculus.md §4.6 and §5: the head of [E] is the
    OUTERMOST frame, so each cons rule wraps the tail judgment with the head
    frame, mirroring the corresponding [has_type] rule with the hole in its
    evaluation position. *)
with ctx_types : ctx -> list eframe -> ty -> ty -> eff -> bound -> Prop :=
| Ctx_Nil : forall g a, ctx_types g [] a a EffEmpty (BFinite 0)
| Ctx_Succ : forall g rest a eps beta,
    ctx_types g rest a TyNat eps beta ->
    ctx_types g (FSucc :: rest) a TyNat eps beta
| Ctx_CaseScrut : forall g rest a e0 x e1 t eps_s eps0 eps1 beta_s beta0 beta1,
    ctx_types g rest a TyNat eps_s beta_s ->
    has_type g e0 t eps0 beta0 ->
    has_type ((x, TyNat) :: g) e1 t eps1 beta1 ->
    ctx_types g (FCaseScrut e0 x e1 :: rest) a t
      (eff_join eps_s (eff_join eps0 eps1))
      (bound_seq beta_s (bound_join beta0 beta1))
| Ctx_AppFun : forall g rest a pending arg_ty ret_ty lat_eps lat_beta epsf epsa betaf betaa,
    ctx_types g rest a (TyArrow arg_ty lat_eps lat_beta ret_ty) epsf betaf ->
    has_type g pending arg_ty epsa betaa ->
    ctx_types g (FAppFun pending :: rest) a ret_ty
      (eff_join epsf (eff_join epsa lat_eps))
      (bound_seq betaf (bound_seq betaa lat_beta))
| Ctx_AppArg : forall g rest a fn arg_ty ret_ty lat_eps lat_beta epsf epsa betaf betaa,
    has_type g fn (TyArrow arg_ty lat_eps lat_beta ret_ty) epsf betaf ->
    ctx_types g rest a arg_ty epsa betaa ->
    ctx_types g (FAppArg fn :: rest) a ret_ty
      (eff_join epsf (eff_join epsa lat_eps))
      (bound_seq betaf (bound_seq betaa lat_beta))
| Ctx_Let : forall g rest a x body a' b epse epsb betae betab,
    ctx_types g rest a a' epse betae ->
    has_type ((x, a') :: g) body b epsb betab ->
    ctx_types g (FLet x body :: rest) a b (eff_join epse epsb) (bound_seq betae betab)
| Ctx_PerformArg : forall g rest a beta,
    ctx_types g rest a TyNat EffEmpty beta ->
    ctx_types g (FPerformArg L :: rest) a TyNat EffL beta
| Ctx_ResumeK : forall g rest a arg t bk beta,
    ctx_types g rest a (TyCont TyNat bk t) EffEmpty (BFinite 0) ->
    has_type g arg TyNat EffEmpty beta ->
    ctx_types g (FResumeK arg :: rest) a t EffEmpty (bound_seq beta bk)
| Ctx_ResumeArg : forall g rest a kont t bk beta,
    has_type g kont (TyCont TyNat bk t) EffEmpty (BFinite 0) ->
    ctx_types g rest a TyNat EffEmpty beta ->
    ctx_types g (FResumeArg kont :: rest) a t EffEmpty (bound_seq beta bk)
(* Deliberately no rule for [FHandleBody]: [capture] never emits it. A nested
   handler owns every perform beneath it in the one-label core. *).

Scheme has_type_mut := Minimality for has_type Sort Prop
with ctx_types_mut := Minimality for ctx_types Sort Prop.
Combined Scheme typing_mut from has_type_mut, ctx_types_mut.

Theorem substitution_preserves_unmentioned_typing : forall g t ty eps beta x replacement,
  has_type g t ty eps beta ->
  mentions_var x t = false ->
  subst x replacement t = t ->
  has_type g (subst x replacement t) ty eps beta.
Proof.
  intros. rewrite H1. assumption.
Qed.
