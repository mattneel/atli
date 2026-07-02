From Coq Require Import Bool.Bool Strings.String.
Import StringSyntax.
Open Scope string_scope.

Require Import Atli.Syntax.

(** Small-step skeleton for [docs/calculus.md §5], including split lazy-capture H-op. *)

Definition subst2 (x : string) (v : term) (y : string) (w : term) (body : term) : term :=
  subst y w (subst x v body).

Fixpoint stepf (t : term) : option term :=
  match t with
  | TApp (TLam x _ body) v =>
      if is_value v then Some (subst x v body) else None (* β, §5 *)
  | TApp f a =>
      match stepf f with
      | Some f' => Some (TApp f' a)
      | None => match stepf a with Some a' => Some (TApp f a') | None => None end
      end
  | TLet x v body =>
      if is_value v then Some (subst x v body) (* let, §5 *)
      else match stepf v with Some v' => Some (TLet x v' body) | None => None end
  | TSucc e => match stepf e with Some e' => Some (TSucc e') | None => None end
  | TCaseNat TZero e0 _ _ => Some e0 (* case-zero, §5 *)
  | TCaseNat (TSucc v) _ x e1 =>
      if is_value v then Some (subst x v e1) else None (* case-succ, §5 *)
  | TCaseNat scrut e0 x e1 =>
      match stepf scrut with Some scrut' => Some (TCaseNat scrut' e0 x e1) | None => None end
  | TFix f x a body tag =>
      Some (TLam x a (subst f (TFix f x a body tag) body)) (* unfold, §5 *)
  | TPerform op arg =>
      match stepf arg with Some arg' => Some (TPerform op arg') | None => None end
  | THandle v (Handler rv rbody op op_param op_k op_body) =>
      if is_value v then Some (subst rv v rbody) (* H-return, §5 *)
      else match v with
      | TPerform L arg =>
          if is_value arg then
            if mentions_var op_k op_body then
              Some (subst2 op_param arg op_k (TContVal 0) op_body) (* H-op-resume, §5 *)
            else Some (subst op_param arg op_body) (* H-op-drop, §5 *)
          else None
      | _ => match stepf v with Some v' => Some (THandle v' (Handler rv rbody op op_param op_k op_body)) | None => None end
      end
  | TResume (TContVal _) v =>
      if is_value v then Some v else match stepf v with Some v' => Some (TResume (TContVal 0) v') | None => None end
  | TResume (TUsedContVal _) _ => None (* resume-after-use is the retained stuck state, §5/§8.3 *)
  | TResume k arg =>
      match stepf k with
      | Some k' => Some (TResume k' arg)
      | None => match stepf arg with Some arg' => Some (TResume k arg') | None => None end
      end
  | _ => None
  end.

Inductive step : term -> term -> Prop :=
| StepByFunction : forall t u, stepf t = Some u -> step t u.

Theorem step_deterministic : forall t u v,
  step t u -> step t v -> u = v.
Proof.
  intros t u v Hu Hv. inversion Hu; inversion Hv; subst. congruence.
Qed.
