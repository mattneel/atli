From Coq Require Import Bool.Bool Lists.List Strings.String.
Import ListNotations StringSyntax.
Open Scope string_scope.

Require Import Atli.Syntax.

(** Small-step skeleton for [docs/calculus.md §5], including split lazy-capture H-op. *)

Definition subst2 (x : string) (v : term) (y : string) (w : term) (body : term) : term :=
  subst y w (subst x v body).

Definition capture_cons (f : eframe) (r : option (list eframe * term)) :
    option (list eframe * term) :=
  match r with
  | Some (ctx, v) => Some (f :: ctx, v)
  | None => None
  end.

(* docs/calculus.md §5: decompose a handler body to the innermost unhandled
   [perform L v] (value argument) under handler-free evaluation-context frames
   E ::= [·] | succ E | case E {...} | E e | v E | let x = E in e
       | perform L E | resume E e | resume v E.
   Returns the context OUTSIDE-IN (head = outermost frame), or None when the
   body is a value, steps internally, or is stuck for a non-operation reason.
   The subtle constructor is THandle: with one label, a nested handler owns
   every perform beneath it ("E is handler-free for l", §5), so capture STOPS
   there and never emits an FHandleBody frame. *)
Fixpoint capture (t : term) : option (list eframe * term) :=
  match t with
  | TPerform L arg =>
      if is_value arg then Some ([], arg) else capture_cons (FPerformArg L) (capture arg)
  | TSucc e =>
      if is_value e then None else capture_cons FSucc (capture e)
  | TCaseNat scrut e0 x e1 =>
      if is_value scrut then None else capture_cons (FCaseScrut e0 x e1) (capture scrut)
  | TApp f a =>
      if is_value f then
        if is_value a then None else capture_cons (FAppArg f) (capture a)
      else capture_cons (FAppFun a) (capture f)
  | TLet x e body =>
      if is_value e then None else capture_cons (FLet x body) (capture e)
  | TResume (TContVal h c) arg =>
      if is_value arg then None else capture_cons (FResumeArg (TContVal h c)) (capture arg)
  | TResume (TUsedContVal _ _) _ =>
      None
  | TResume kont arg =>
      if is_value kont then
        if is_value arg then None else capture_cons (FResumeArg kont) (capture arg)
      else capture_cons (FResumeK arg) (capture kont)
  | THandle _ _ =>
      None (* A nested handler owns every perform beneath it; "E is handler-free for l", §5. *)
  | TFix _ _ _ _ _ => None
  | TVar _ => None
  | TUnit => None
  | TZero => None
  | TLam _ _ _ => None
  | TContVal _ _ => None
  | TUsedContVal _ _ => None
  end.

Lemma capture_value_none : forall t, is_value t = true -> capture t = None.
Proof.
  intros t Hv. destruct t; simpl in *; try discriminate; try reflexivity.
  rewrite Hv. reflexivity.
Qed.

Theorem capture_plug : forall t ctx v,
  capture t = Some (ctx, v) -> t = plug ctx (TPerform L v) /\ is_value v = true.
Proof.
  assert (Hcons : forall f sub ctx v,
    capture_cons f (capture sub) = Some (ctx, v) ->
    (forall ctx' v',
      capture sub = Some (ctx', v') ->
      sub = plug ctx' (TPerform L v') /\ is_value v' = true) ->
    plug1 f sub = plug ctx (TPerform L v) /\ is_value v = true).
  {
    intros f sub ctx v Hcapture IHsub.
    unfold capture_cons in Hcapture.
    destruct (capture sub) as [[ctx' v']|] eqn:Hsub; try discriminate.
    destruct (IHsub ctx' v' eq_refl) as [Hplug Hvalue].
    injection Hcapture as Hctx Hv.
    subst ctx v.
    split; [simpl; rewrite Hplug; reflexivity | exact Hvalue].
  }
  induction t as
    [x| | |e IHe|scrut IHscrut e0 IHe0 x e1 IHe1
    |param param_ty body IHbody|f IHf a IHa|x e IHe body IHbody
    |func param param_ty body IHbody tag|op arg IHarg|body IHbody h
    |kont IHkont arg IHarg|h ctx0|h ctx0];
    intros ctx v H; cbn [capture is_value] in H; try discriminate.
  - destruct (is_value e) eqn:He; try discriminate.
    exact (Hcons FSucc e ctx v H IHe).
  - destruct (is_value scrut) eqn:Hscrut; try discriminate.
    exact (Hcons (FCaseScrut e0 x e1) scrut ctx v H IHscrut).
  - destruct (is_value f) eqn:Hf.
    + destruct (is_value a) eqn:Ha; try discriminate.
      exact (Hcons (FAppArg f) a ctx v H IHa).
    + exact (Hcons (FAppFun a) f ctx v H IHf).
  - destruct (is_value e) eqn:He; try discriminate.
    exact (Hcons (FLet x body) e ctx v H IHe).
  - destruct op.
    cbn [capture is_value] in H.
    destruct (is_value arg) eqn:Harg.
    + inversion H; subst. split; [reflexivity | exact Harg].
    + exact (Hcons (FPerformArg L) arg ctx v H IHarg).
  - destruct kont as
      [kx| | |ke|kscrut ke0 kx ke1|kparam kparam_ty kbody|kf ka
      |kx ke kbody|kfunc kparam kparam_ty kbody ktag|kop karg|kbody kh
      |kkont karg|kh kctx|kh kctx];
      cbn [capture is_value] in H.
    + discriminate.
    + destruct (is_value arg) eqn:Harg; try discriminate.
      exact (Hcons (FResumeArg TUnit) arg ctx v H IHarg).
    + destruct (is_value arg) eqn:Harg; try discriminate.
      exact (Hcons (FResumeArg TZero) arg ctx v H IHarg).
    + destruct (is_value ke) eqn:Hke; try discriminate.
      * destruct (is_value arg) eqn:Harg; try discriminate.
        exact (Hcons (FResumeArg (TSucc ke)) arg ctx v H IHarg).
      * assert (Hcap : capture_cons (FResumeK arg) (capture (TSucc ke)) = Some (ctx, v)).
        { cbn [capture is_value]. rewrite Hke. exact H. }
        exact (Hcons (FResumeK arg) (TSucc ke) ctx v Hcap IHkont).
    + exact (Hcons (FResumeK arg) (TCaseNat kscrut ke0 kx ke1) ctx v H IHkont).
    + destruct (is_value arg) eqn:Harg; try discriminate.
      exact (Hcons (FResumeArg (TLam kparam kparam_ty kbody)) arg ctx v H IHarg).
    + exact (Hcons (FResumeK arg) (TApp kf ka) ctx v H IHkont).
    + exact (Hcons (FResumeK arg) (TLet kx ke kbody) ctx v H IHkont).
    + exact (Hcons (FResumeK arg) (TFix kfunc kparam kparam_ty kbody ktag) ctx v H IHkont).
    + exact (Hcons (FResumeK arg) (TPerform kop karg) ctx v H IHkont).
    + exact (Hcons (FResumeK arg) (THandle kbody kh) ctx v H IHkont).
    + exact (Hcons (FResumeK arg) (TResume kkont karg) ctx v H IHkont).
    + destruct (is_value arg) eqn:Harg; try discriminate.
      exact (Hcons (FResumeArg (TContVal kh kctx)) arg ctx v H IHarg).
    + discriminate.
Qed.

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
      else match capture v with
      | Some (ctx, arg) =>
          if mentions_var op_k op_body then
            (* H-op-resume, §5: the continuation value carries the installed
               handler and the captured context. *)
            Some (subst2 op_param arg op_k
                    (TContVal (Handler rv rbody op op_param op_k op_body) ctx) op_body)
          else
            (* H-op-drop, §5: frame-free abandonment - the captured context is
               DISCARDED, never materialized. *)
            Some (subst op_param arg op_body)
      | None =>
          match stepf v with
          | Some v' => Some (THandle v' (Handler rv rbody op op_param op_k op_body))
          | None => None
          end
      end
  | TResume (TContVal h ctx) v =>
      if is_value v then
        Some (THandle (plug ctx v) h) (* H-op-resume completed: deep reinstallation of the handler, §5 *)
      else match stepf v with Some v' => Some (TResume (TContVal h ctx) v') | None => None end
  | TResume (TUsedContVal _ _) _ => None (* resume-after-use is the retained stuck state, §5/§8.3 *)
  | TResume k arg =>
      match stepf k with
      | Some k' => Some (TResume k' arg)
      | None => match stepf arg with Some arg' => Some (TResume k arg') | None => None end
      end
  | _ => None
  end.

Inductive step : term -> term -> Prop :=
| StepByFunction : forall t u, stepf t = Some u -> step t u.

(* Determinism is still by computation: [capture] is a function, so handler
   dispatch selects at most one successor. *)
Theorem step_deterministic : forall t u v,
  step t u -> step t v -> u = v.
Proof.
  intros t u v Hu Hv. inversion Hu; inversion Hv; subst. congruence.
Qed.
