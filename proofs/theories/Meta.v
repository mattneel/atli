From Coq Require Import Bool.Bool Lists.List Strings.String.
Import ListNotations StringSyntax.
Open Scope string_scope.

Require Import Atli.Grade.
Require Import Atli.Syntax.
Require Import Atli.Typing.
Require Import Atli.Step.
Require Import Atli.StepFrames.
Require Import Atli.Solve.

(** Sprint 16 A5: the closedness invariant licensing payload-opaque substitution. *)

Definition closed_term (t : term) : Prop := forall x, mentions_var x t = false.

(* Handler/context closedness is reified through [mentions_var] on wrapper terms.
   Evaluation-context frames never put the hole under a binder, so plugging a
   closed dummy reads off exactly the frames' own free variables. *)
Definition handler_closed (h : handler) : Prop := closed_term (THandle TZero h).
Definition ctx_closed (ctx : list eframe) : Prop := closed_term (plug ctx TZero).

Fixpoint payloads_closed (t : term) : Prop :=
  match t with
  | TVar _ | TUnit | TZero => True
  | TSucc inner => payloads_closed inner
  | TCaseNat scrut zero_body _ succ_body =>
      payloads_closed scrut /\ payloads_closed zero_body /\ payloads_closed succ_body
  | TLam _ _ body => payloads_closed body
  | TApp f a => payloads_closed f /\ payloads_closed a
  | TLet _ expr body => payloads_closed expr /\ payloads_closed body
  | TFix _ _ _ body _ => payloads_closed body
  | TPerform _ arg => payloads_closed arg
  | THandle body h => payloads_closed body /\ payloads_closed_handler h
  | TResume kont arg => payloads_closed kont /\ payloads_closed arg
  | TContVal h ctx | TUsedContVal h ctx =>
      handler_closed h /\ ctx_closed ctx /\ payloads_closed_handler h /\
      ((fix ctx_payloads_closed (ctx : list eframe) : Prop :=
          match ctx with
          | [] => True
          | f :: rest => payloads_closed_frame f /\ ctx_payloads_closed rest
          end) ctx)
  end
with payloads_closed_handler (h : handler) : Prop :=
  match h with
  | Handler _ return_body _ _ _ op_body =>
      payloads_closed return_body /\ payloads_closed op_body
  end
with payloads_closed_frame (f : eframe) : Prop :=
  match f with
  | FSucc | FPerformArg _ => True
  | FCaseScrut zero_body _ succ_body =>
      payloads_closed zero_body /\ payloads_closed succ_body
  | FAppFun pending_arg => payloads_closed pending_arg
  | FAppArg fn_value => payloads_closed fn_value
  | FLet _ body => payloads_closed body
  | FResumeK arg => payloads_closed arg
  | FResumeArg kont => payloads_closed kont
  | FHandleBody h => payloads_closed_handler h
  end.

Definition ctx_payloads_closed (ctx : list eframe) : Prop :=
  ((fix ctx_payloads_closed (ctx : list eframe) : Prop :=
      match ctx with
      | [] => True
      | f :: rest => payloads_closed_frame f /\ ctx_payloads_closed rest
      end) ctx).

Lemma plug_mentions : forall ctx s x,
  mentions_var x (plug ctx s) = orb (mentions_var x (plug ctx TZero)) (mentions_var x s).
Proof.
  induction ctx as [|f rest IH]; intros s x; simpl.
  - reflexivity.
  - destruct f; simpl; try destruct h; simpl; rewrite IH;
      repeat match goal with
      | |- context[String.eqb ?a ?b] => destruct (String.eqb a b) eqn:?
      | |- context[mentions_var ?a ?b] => destruct (mentions_var a b) eqn:?
      end; reflexivity.
Qed.

Lemma subst_mentions_other_mut :
  (forall e x v y,
    mentions_var y v = false -> y <> x ->
    mentions_var y (subst x v e) = mentions_var y e) /\
  (forall h x v y,
    mentions_var y v = false -> y <> x ->
    match h with
    | Handler rv rb op op_param op_k op_body =>
        ((if String.eqb y rv then false
          else mentions_var y (if String.eqb x rv then rb else subst x v rb)) ||
         (if String.eqb y op_param || String.eqb y op_k then false
          else mentions_var y
            (if String.eqb x op_param || String.eqb x op_k
             then op_body
             else subst x v op_body))) =
        ((if String.eqb y rv then false else mentions_var y rb) ||
         (if String.eqb y op_param || String.eqb y op_k
          then false
          else mentions_var y op_body))
    end) /\
  (forall f : eframe, True).
Proof.
  Ltac subst_mentions_other_crush :=
    repeat match goal with
    | |- context[String.eqb ?a ?b] =>
        destruct (String.eqb a b) eqn:?; simpl
    | IH : forall sx sv sy,
        mentions_var sy sv = false -> sy <> sx ->
        mentions_var sy (subst sx sv ?e) = mentions_var sy ?e
      |- context[mentions_var ?sy (subst ?sx ?sv ?e)] =>
        rewrite (IH sx sv sy ltac:(assumption) ltac:(assumption))
    | IH : forall sx sv sy,
        mentions_var sy sv = false -> sy <> sx -> ?lhs = ?rhs
      |- context[?lhs] =>
        rewrite (IH _ _ _ ltac:(assumption) ltac:(assumption))
    end; try reflexivity.
  apply syntax_ind; simpl; intros; try exact I; try reflexivity.
  - destruct (String.eqb x0 x) eqn:Heq.
    + apply String.eqb_eq in Heq. subst x0.
      assert (Hyx : (y =? x) = false) by (apply String.eqb_neq; exact H0).
      rewrite Hyx. exact H.
    + reflexivity.
  - rewrite (H x v y H0 H1). reflexivity.
  - rewrite (H x v y H2 H3).
    rewrite (H0 x v y H2 H3).
    destruct (String.eqb y succ_var); [reflexivity|].
    destruct (String.eqb x succ_var); [reflexivity|].
    rewrite (H1 x v y H2 H3). reflexivity.
  - destruct (String.eqb y param); [reflexivity|].
    destruct (String.eqb x param); [reflexivity|].
    rewrite (H x v y H0 H1). reflexivity.
  - rewrite (H x v y H1 H2).
    rewrite (H0 x v y H1 H2). reflexivity.
  - rewrite (H x0 v y H1 H2).
    destruct (String.eqb y x); [reflexivity|].
    destruct (String.eqb x0 x); [reflexivity|].
    rewrite (H0 x0 v y H1 H2). reflexivity.
  - destruct (String.eqb y func) eqn:?; simpl; [reflexivity|].
    destruct (String.eqb y param) eqn:?; simpl; [reflexivity|].
    destruct (String.eqb x func) eqn:?; simpl; [reflexivity|].
    destruct (String.eqb x param) eqn:?; simpl; [reflexivity|].
    rewrite (H x v y H0 H1). reflexivity.
  - rewrite (H x v y H0 H1). reflexivity.
  - pose proof (H0 x v y H1 H2) as Hh.
    destruct h; simpl in Hh |- *.
    rewrite (H x v y H1 H2).
    set (ret_sub :=
      if y =? return_var
      then false
      else mentions_var y (if x =? return_var then return_body else subst x v return_body)) in *.
    set (op_sub :=
      if (y =? op_param) || (y =? op_k)
      then false
      else mentions_var y
        (if (x =? op_param) || (x =? op_k) then op_body else subst x v op_body)) in *.
    set (ret_old :=
      if y =? return_var then false else mentions_var y return_body) in *.
    set (op_old :=
      if (y =? op_param) || (y =? op_k) then false else mentions_var y op_body) in *.
    destruct (mentions_var y body), ret_sub, op_sub, ret_old, op_old;
      simpl in Hh; try discriminate; reflexivity.
  - rewrite (H x v y H1 H2).
    rewrite (H0 x v y H1 H2). reflexivity.
  - destruct (String.eqb y return_var) eqn:?; simpl.
    + destruct (String.eqb y op_param || String.eqb y op_k) eqn:?; simpl; [reflexivity|].
      destruct (String.eqb x op_param || String.eqb x op_k) eqn:?; simpl; [reflexivity|].
      rewrite (H0 x v y H1 H2). reflexivity.
    + destruct (String.eqb x return_var) eqn:?; simpl.
      * destruct (String.eqb y op_param || String.eqb y op_k) eqn:?; simpl; [reflexivity|].
        destruct (String.eqb x op_param || String.eqb x op_k) eqn:?; simpl; [reflexivity|].
        rewrite (H0 x v y H1 H2). reflexivity.
      * rewrite (H x v y H1 H2).
        destruct (String.eqb y op_param || String.eqb y op_k) eqn:?; simpl; [reflexivity|].
        destruct (String.eqb x op_param || String.eqb x op_k) eqn:?; simpl; [reflexivity|].
        rewrite (H0 x v y H1 H2). reflexivity.
Qed.

Lemma subst_mentions_other : forall e x v y,
  mentions_var y v = false -> y <> x ->
  mentions_var y (subst x v e) = mentions_var y e.
Proof. exact (proj1 subst_mentions_other_mut). Qed.

Lemma subst_mentions_self_mut :
  (forall e x v,
    mentions_var x v = false ->
    mentions_var x (subst x v e) = false) /\
  (forall h x v,
    mentions_var x v = false ->
    match h with
    | Handler rv rb op op_param op_k op_body =>
        ((if String.eqb x rv then false
          else mentions_var x (if String.eqb x rv then rb else subst x v rb)) ||
         (if String.eqb x op_param || String.eqb x op_k then false
          else mentions_var x
            (if String.eqb x op_param || String.eqb x op_k
             then op_body
             else subst x v op_body))) = false
    end) /\
  (forall f : eframe, True).
Proof.
  apply syntax_ind; simpl; intros; try exact I; try reflexivity.
  - destruct (String.eqb x0 x) eqn:Heq; [exact H|exact Heq].
  - apply H. exact H0.
  - rewrite (H x v H2).
    rewrite (H0 x v H2).
    destruct (String.eqb x succ_var); [reflexivity|].
    rewrite (H1 x v H2). reflexivity.
  - destruct (String.eqb x param); [reflexivity|].
    apply H. exact H0.
  - rewrite (H x v H1). rewrite (H0 x v H1). reflexivity.
  - rewrite (H x0 v H1).
    destruct (String.eqb x0 x); [reflexivity|].
    rewrite (H0 x0 v H1). reflexivity.
  - destruct (String.eqb x func || String.eqb x param); [reflexivity|].
    apply H. exact H0.
  - apply H. exact H0.
  - pose proof (H0 x v H1) as Hh.
    destruct h; simpl in Hh |- *.
    rewrite (H x v H1).
    set (ret_sub :=
      if x =? return_var
      then false
      else mentions_var x (if x =? return_var then return_body else subst x v return_body)) in *.
    set (op_sub :=
      if (x =? op_param) || (x =? op_k)
      then false
      else mentions_var x
        (if (x =? op_param) || (x =? op_k) then op_body else subst x v op_body)) in *.
    destruct ret_sub, op_sub; simpl in Hh; try discriminate; reflexivity.
  - rewrite (H x v H1). rewrite (H0 x v H1). reflexivity.
  - destruct (String.eqb x return_var) eqn:?; simpl.
    + destruct (String.eqb x op_param || String.eqb x op_k) eqn:?; simpl; [reflexivity|].
      rewrite (H0 x v H1). reflexivity.
    + rewrite (H x v H1).
      destruct (String.eqb x op_param || String.eqb x op_k) eqn:?; simpl; [reflexivity|].
      rewrite (H0 x v H1). reflexivity.
Qed.

Lemma subst_mentions_self : forall e x v,
  mentions_var x v = false ->
  mentions_var x (subst x v e) = false.
Proof. exact (proj1 subst_mentions_self_mut). Qed.

Lemma subst_closes_one : forall body x v,
  (forall y, y <> x -> mentions_var y body = false) ->
  closed_term v ->
  closed_term (subst x v body).
Proof.
  intros body x v Hbody Hv y.
  destruct (String.eqb y x) eqn:Hyx.
  - apply String.eqb_eq in Hyx. subst y.
    apply subst_mentions_self. apply Hv.
  - apply String.eqb_neq in Hyx.
    rewrite subst_mentions_other; [|apply Hv|exact Hyx].
    apply Hbody. exact Hyx.
Qed.

Lemma subst2_closes_two : forall body x v y w,
  (forall z, z <> x -> z <> y -> mentions_var z body = false) ->
  closed_term v ->
  closed_term w ->
  closed_term (subst2 x v y w body).
Proof.
  intros body x v y w Hbody Hv Hw z.
  unfold subst2.
  destruct (String.eqb z y) eqn:Hzy.
  - apply String.eqb_eq in Hzy. subst z.
    apply subst_mentions_self. apply Hw.
  - apply String.eqb_neq in Hzy.
    rewrite subst_mentions_other; [|apply Hw|exact Hzy].
    destruct (String.eqb z x) eqn:Hzx.
    + apply String.eqb_eq in Hzx. subst z.
      apply subst_mentions_self. apply Hv.
    + apply String.eqb_neq in Hzx.
      rewrite subst_mentions_other; [|apply Hv|exact Hzx].
      apply Hbody; assumption.
Qed.

Lemma payloads_closed_subst_mut :
  (forall e x v,
    payloads_closed v -> payloads_closed e -> payloads_closed (subst x v e)) /\
  (forall h x v,
    payloads_closed v -> payloads_closed_handler h ->
    match h with
    | Handler rv rb op op_param op_k op_body =>
        payloads_closed_handler
          (Handler rv
            (if String.eqb x rv then rb else subst x v rb)
            op op_param op_k
            (if String.eqb x op_param || String.eqb x op_k
             then op_body
             else subst x v op_body))
    end) /\
  (forall f : eframe, True).
Proof.
  apply syntax_ind; simpl; intros; try exact I; try tauto.
  - destruct (String.eqb x0 x); [assumption|exact I].
  - eauto.
  - repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; eauto.
    destruct (String.eqb x succ_var); eauto.
  - destruct (String.eqb x param); eauto.
  - repeat match goal with H : _ /\ _ |- _ => destruct H end.
    split; eauto.
  - repeat match goal with H : _ /\ _ |- _ => destruct H end.
    split; eauto.
    destruct (String.eqb x0 x); eauto.
  - destruct (String.eqb x func || String.eqb x param); eauto.
  - eauto.
  - destruct h; simpl in *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    split; eauto.
  - repeat match goal with H : _ /\ _ |- _ => destruct H end.
    split; eauto.
  - destruct H2 as [Hret Hop].
    split.
    + destruct (String.eqb x return_var); [exact Hret|eauto].
    + destruct (String.eqb x op_param || String.eqb x op_k); [exact Hop|eauto].
Qed.

Lemma payloads_closed_subst : forall e x v,
  payloads_closed v -> payloads_closed e -> payloads_closed (subst x v e).
Proof. exact (proj1 payloads_closed_subst_mut). Qed.

Lemma plug1_payloads_closed : forall f s,
  payloads_closed (plug1 f s) <-> (payloads_closed_frame f /\ payloads_closed s).
Proof.
  destruct f; simpl; intros s; tauto.
Qed.

Lemma plug_ctx_payloads_closed : forall ctx,
  payloads_closed (plug ctx TZero) <-> ctx_payloads_closed ctx.
Proof.
  induction ctx as [|f rest IH]; simpl.
  - tauto.
  - rewrite plug1_payloads_closed. rewrite IH. unfold ctx_payloads_closed.
    simpl. fold ctx_payloads_closed. tauto.
Qed.

Lemma ctx_payloads_closed_plug : forall ctx s,
  ctx_payloads_closed ctx -> payloads_closed s -> payloads_closed (plug ctx s).
Proof.
  induction ctx as [|f rest IH]; intros s Hctx Hs; simpl in *.
  - exact Hs.
  - unfold ctx_payloads_closed in Hctx. simpl in Hctx. fold ctx_payloads_closed in Hctx.
    destruct Hctx as [Hf Hrest].
    apply plug1_payloads_closed. split; [exact Hf|].
    apply IH; assumption.
Qed.

Lemma plug_payloads_closed : forall ctx s,
  payloads_closed (plug ctx s) <-> (payloads_closed (plug ctx TZero) /\ payloads_closed s).
Proof.
  intros ctx s. split.
  - intro Hplug.
    split.
    + apply plug_ctx_payloads_closed.
      induction ctx as [|f rest IH]; simpl in *.
      * exact I.
      * apply plug1_payloads_closed in Hplug as [Hf Hrest].
        unfold ctx_payloads_closed. simpl. fold ctx_payloads_closed.
        split; [exact Hf|].
        apply IH. exact Hrest.
    + induction ctx as [|f rest IH]; simpl in *.
      * exact Hplug.
      * apply plug1_payloads_closed in Hplug as [_ Hrest].
        apply IH. exact Hrest.
  - intros [Hctx Hs].
    apply ctx_payloads_closed_plug.
    + apply plug_ctx_payloads_closed. exact Hctx.
    + exact Hs.
Qed.

Lemma plug_closed : forall ctx s,
  ctx_closed ctx -> closed_term s -> closed_term (plug ctx s).
Proof.
  intros ctx s Hctx Hs x.
  rewrite plug_mentions. rewrite Hctx, Hs. reflexivity.
Qed.

Lemma plug_closed_inv : forall ctx s,
  closed_term (plug ctx s) -> ctx_closed ctx /\ closed_term s.
Proof.
  intros ctx s Hplug. split; intros x; specialize (Hplug x);
    rewrite plug_mentions in Hplug; apply orb_false_iff in Hplug as [? ?]; assumption.
Qed.

Lemma closed_contval : forall h ctx, closed_term (TContVal h ctx).
Proof. intros h ctx x. reflexivity. Qed.

Lemma closed_handle_parts : forall body h,
  closed_term (THandle body h) -> closed_term body /\ handler_closed h.
Proof.
  intros body h Hclosed. split.
  - intros x. specialize (Hclosed x). destruct h; simpl in Hclosed.
    destruct (mentions_var x body) eqn:Hbody; [discriminate|reflexivity].
  - intros x. specialize (Hclosed x). destruct h; simpl in *.
    destruct (mentions_var x body); [discriminate|exact Hclosed].
Qed.

Lemma closed_handle_rebuild : forall body h,
  closed_term body -> handler_closed h -> closed_term (THandle body h).
Proof.
  intros body h Hbody Hhandler x. specialize (Hbody x). specialize (Hhandler x).
  destruct h; simpl in *. rewrite Hbody. exact Hhandler.
Qed.

Lemma handler_closed_return_except : forall rv rbody op op_param op_k op_body,
  handler_closed (Handler rv rbody op op_param op_k op_body) ->
  forall y, y <> rv -> mentions_var y rbody = false.
Proof.
  intros rv rbody op op_param op_k op_body Hclosed y Hneq.
  specialize (Hclosed y). simpl in Hclosed.
  assert (Hyret : (y =? rv) = false) by (apply String.eqb_neq; exact Hneq).
  rewrite Hyret in Hclosed.
  destruct (mentions_var y rbody) eqn:Hr; [destruct (mentions_var y op_body); discriminate|reflexivity].
Qed.

Lemma handler_closed_op_except_two : forall rv rbody op op_param op_k op_body,
  handler_closed (Handler rv rbody op op_param op_k op_body) ->
  forall y,
    y <> op_param -> y <> op_k -> mentions_var y op_body = false.
Proof.
  intros rv rbody op op_param op_k op_body Hclosed y Hparam Hk.
  specialize (Hclosed y). simpl in Hclosed.
  assert (Hyparam : (y =? op_param) = false) by (apply String.eqb_neq; exact Hparam).
  assert (Hyk : (y =? op_k) = false) by (apply String.eqb_neq; exact Hk).
  rewrite Hyparam in Hclosed.
  rewrite Hyk in Hclosed.
  simpl in Hclosed.
  destruct (if y =? rv then false else mentions_var y rbody);
    destruct (mentions_var y op_body) eqn:Hop; try discriminate; reflexivity.
Qed.

Lemma subst_closed_return_body : forall rv rbody op op_param op_k op_body v,
  handler_closed (Handler rv rbody op op_param op_k op_body) ->
  closed_term v ->
  closed_term (subst rv v rbody).
Proof.
  intros. apply subst_closes_one; auto.
  intros y Hy. eapply handler_closed_return_except; eauto.
Qed.

Lemma subst_closed_op_drop : forall rv rbody op_param op_k op_body arg,
  handler_closed (Handler rv rbody L op_param op_k op_body) ->
  closed_term arg ->
  mentions_var op_k op_body = false ->
  closed_term (subst op_param arg op_body).
Proof.
  intros rv rbody op_param op_k op_body arg Hhandler Harg Hdrop y.
  destruct (String.eqb y op_param) eqn:Hyparam.
  - apply String.eqb_eq in Hyparam. subst y.
    apply subst_mentions_self. apply Harg.
  - apply String.eqb_neq in Hyparam.
    rewrite subst_mentions_other; [|apply Harg|exact Hyparam].
    destruct (String.eqb y op_k) eqn:Hyk.
    + apply String.eqb_eq in Hyk. subst y. exact Hdrop.
    + apply String.eqb_neq in Hyk.
      eapply handler_closed_op_except_two; eauto.
Qed.

Lemma subst_closed_op_resume : forall rv rbody op_param op_k op_body arg h ctx,
  handler_closed (Handler rv rbody L op_param op_k op_body) ->
  closed_term arg ->
  closed_term
    (subst2 op_param arg op_k (TContVal h ctx) op_body).
Proof.
  intros rv rbody op_param op_k op_body arg h ctx Hhandler Harg.
  apply subst2_closes_two.
  - intros z Hzparam Hzk.
    eapply handler_closed_op_except_two; eauto.
  - exact Harg.
  - apply closed_contval.
Qed.

Lemma closed_lam_subst : forall x a body v,
  closed_term (TApp (TLam x a body) v) ->
  closed_term (subst x v body).
Proof.
  intros x a body v Hclosed.
  apply subst_closes_one.
  - intros y Hy.
    specialize (Hclosed y). simpl in Hclosed.
    assert (Hyx : (y =? x) = false) by (apply String.eqb_neq; exact Hy).
    rewrite Hyx in Hclosed.
    apply orb_false_iff in Hclosed as [Hbody _]. exact Hbody.
  - intros y. specialize (Hclosed y). simpl in Hclosed.
    apply orb_false_iff in Hclosed as [_ Hv]. exact Hv.
Qed.

Lemma closed_let_subst : forall x expr body,
  closed_term (TLet x expr body) ->
  closed_term expr ->
  closed_term (subst x expr body).
Proof.
  intros x expr body Hclosed Hexpr.
  apply subst_closes_one; auto.
  intros y Hy.
  specialize (Hclosed y). simpl in Hclosed.
  assert (Hyx : (y =? x) = false) by (apply String.eqb_neq; exact Hy).
  rewrite Hyx in Hclosed.
  apply orb_false_iff in Hclosed as [_ Hbody]. exact Hbody.
Qed.

Lemma closed_case_succ_subst : forall scrut zero_body x succ_body v,
  closed_term (TCaseNat scrut zero_body x succ_body) ->
  closed_term v ->
  closed_term (subst x v succ_body).
Proof.
  intros scrut zero_body x succ_body v Hclosed Hv.
  apply subst_closes_one; auto.
  intros y Hy.
  specialize (Hclosed y). simpl in Hclosed.
  assert (Hyx : (y =? x) = false) by (apply String.eqb_neq; exact Hy).
  rewrite Hyx in Hclosed.
  apply orb_false_iff in Hclosed as [_ Hbody]. exact Hbody.
Qed.

Lemma closed_fix_unfold : forall f x a body tag,
  closed_term (TFix f x a body tag) ->
  closed_term (TLam x a (subst f (TFix f x a body tag) body)).
Proof.
  intros f x a body tag Hclosed y. simpl.
  destruct (String.eqb y x) eqn:Hyx; [reflexivity|].
  apply String.eqb_neq in Hyx.
  destruct (String.eqb y f) eqn:Hyf.
  - apply String.eqb_eq in Hyf. subst y.
    apply subst_mentions_self. exact (Hclosed f).
  - apply String.eqb_neq in Hyf.
    rewrite subst_mentions_other; [|apply Hclosed|exact Hyf].
    specialize (Hclosed y). simpl in Hclosed.
    assert (Hyf_false : (y =? f) = false) by (apply String.eqb_neq; exact Hyf).
    assert (Hyx_false : (y =? x) = false) by (apply String.eqb_neq; exact Hyx).
    rewrite Hyf_false in Hclosed.
    rewrite Hyx_false in Hclosed.
    exact Hclosed.
Qed.

Lemma payloads_closed_contval : forall h ctx,
  handler_closed h -> ctx_closed ctx -> payloads_closed_handler h ->
  ctx_payloads_closed ctx -> payloads_closed (TContVal h ctx).
Proof.
  intros h ctx Hh Hctx Hph Hpctx. simpl.
  repeat split; auto.
Qed.

Lemma payloads_closed_contval_inv : forall h ctx,
  payloads_closed (TContVal h ctx) ->
  handler_closed h /\ ctx_closed ctx /\ payloads_closed_handler h /\ ctx_payloads_closed ctx.
Proof.
  intros h ctx H. simpl in H.
  destruct H as [Hh [Hctx [Hph Hpctx]]].
  repeat split; auto.
Qed.

Lemma plug_perform_closed_parts : forall ctx arg,
  closed_term (plug ctx (TPerform L arg)) -> ctx_closed ctx /\ closed_term arg.
Proof.
  intros ctx arg Hplug.
  apply plug_closed_inv in Hplug as [Hctx Hperform].
  split; [exact Hctx|].
  intros x. exact (Hperform x).
Qed.

Lemma plug_perform_payloads_parts : forall ctx arg,
  payloads_closed (plug ctx (TPerform L arg)) ->
  ctx_payloads_closed ctx /\ payloads_closed arg.
Proof.
  intros ctx arg Hplug.
  apply plug_payloads_closed in Hplug as [Hctx Harg].
  split.
  - apply plug_ctx_payloads_closed. exact Hctx.
  - exact Harg.
Qed.

Lemma typed_lookup_closed : forall g t ty eps beta,
  has_type g t ty eps beta ->
  forall x, lookup x g = None -> mentions_var x t = false.
Proof.
  intros g t ty eps beta Hty.
  induction Hty; intros y Hlookup; simpl.
  - destruct (String.eqb y x) eqn:Hyx.
    + apply String.eqb_eq in Hyx. subst y. rewrite H in Hlookup. discriminate.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IHHty. exact Hlookup.
  - rewrite (IHHty1 y Hlookup), (IHHty2 y Hlookup).
    simpl.
    destruct (String.eqb y x) eqn:Hyx; [reflexivity|].
    apply IHHty3. simpl. rewrite Hyx. exact Hlookup.
  - destruct (String.eqb y x) eqn:Hyx; [reflexivity|].
    apply IHHty. simpl. rewrite Hyx. exact Hlookup.
  - rewrite (IHHty1 y Hlookup), (IHHty2 y Hlookup). reflexivity.
  - rewrite (IHHty1 y Hlookup). simpl.
    destruct (String.eqb y x) eqn:Hyx; [reflexivity|].
    apply IHHty2. simpl. rewrite Hyx. exact Hlookup.
  - destruct (String.eqb y f) eqn:Hyf; [reflexivity|].
    destruct (String.eqb y x) eqn:Hyx; [reflexivity|].
    apply IHHty. simpl. rewrite Hyx. simpl. rewrite Hyf. exact Hlookup.
  - destruct (String.eqb y f) eqn:Hyf; [reflexivity|].
    destruct (String.eqb y x) eqn:Hyx; [reflexivity|].
    apply IHHty. simpl. rewrite Hyx. simpl. rewrite Hyf. exact Hlookup.
  - destruct (String.eqb y f) eqn:Hyf; [reflexivity|].
    destruct (String.eqb y x) eqn:Hyx; [reflexivity|].
    apply IHHty. simpl. rewrite Hyx. simpl. rewrite Hyf. exact Hlookup.
  - apply IHHty. exact Hlookup.
  - rewrite (IHHty1 y Hlookup). simpl.
    destruct (String.eqb y rv) eqn:Hyrv.
    + simpl.
      destruct (String.eqb y op_param) eqn:Hyp; [reflexivity|].
      destruct (String.eqb y op_k) eqn:Hyk; [reflexivity|].
      apply IHHty3. simpl. rewrite Hyk. simpl. rewrite Hyp. exact Hlookup.
    + rewrite (IHHty2 y). simpl.
      * destruct (String.eqb y op_param) eqn:Hyp; [reflexivity|].
        destruct (String.eqb y op_k) eqn:Hyk; [reflexivity|].
        apply IHHty3. simpl. rewrite Hyk. simpl. rewrite Hyp. exact Hlookup.
      * simpl. rewrite Hyrv. exact Hlookup.
  - rewrite (IHHty1 y Hlookup). simpl.
    destruct (String.eqb y rv) eqn:Hyrv.
    + simpl.
      destruct (String.eqb y op_param) eqn:Hyp; [reflexivity|].
      destruct (String.eqb y op_k) eqn:Hyk; [reflexivity|].
      apply IHHty3. simpl. rewrite Hyk. simpl. rewrite Hyp. exact Hlookup.
    + rewrite (IHHty2 y). simpl.
      * destruct (String.eqb y op_param) eqn:Hyp; [reflexivity|].
        destruct (String.eqb y op_k) eqn:Hyk; [reflexivity|].
        apply IHHty3. simpl. rewrite Hyk. simpl. rewrite Hyp. exact Hlookup.
      * simpl. rewrite Hyrv. exact Hlookup.
  - rewrite (IHHty1 y Hlookup), (IHHty2 y Hlookup). reflexivity.
  - reflexivity.
Qed.

Lemma typed_empty_closed : forall t ty eps beta,
  has_type [] t ty eps beta -> closed_term t.
Proof.
  intros t ty eps beta Hty x.
  eapply typed_lookup_closed; eauto.
Qed.

Lemma stepf_app_congruence_preserves : forall f a u,
  (forall u, closed_term f -> payloads_closed f ->
    stepf f = Some u -> closed_term u /\ payloads_closed u) ->
  (forall u, closed_term a -> payloads_closed a ->
    stepf a = Some u -> closed_term u /\ payloads_closed u) ->
  closed_term (TApp f a) -> payloads_closed (TApp f a) ->
  (match stepf f with
   | Some f' => Some (TApp f' a)
   | None => match stepf a with Some a' => Some (TApp f a') | None => None end
   end) = Some u ->
  closed_term u /\ payloads_closed u.
Proof.
  intros f a u IHf IHa Hclosed Hpayload Hstep.
  simpl in Hpayload. destruct Hpayload as [Hf_payload Ha_payload].
  assert (Hf_closed : closed_term f).
  { intros y. specialize (Hclosed y). simpl in Hclosed.
    apply orb_false_iff in Hclosed as [Hf_closed _]. exact Hf_closed. }
  assert (Ha_closed : closed_term a).
  { intros y. specialize (Hclosed y). simpl in Hclosed.
    apply orb_false_iff in Hclosed as [_ Ha_closed]. exact Ha_closed. }
  destruct (stepf f) eqn:Hsf.
  - inversion Hstep; subst.
    destruct (IHf t Hf_closed Hf_payload eq_refl) as [Hf' Hpf'].
    split.
    + intros y. simpl. rewrite Hf', Ha_closed. reflexivity.
    + simpl. split; assumption.
  - destruct (stepf a) eqn:Hsa; inversion Hstep; subst.
    destruct (IHa t Ha_closed Ha_payload eq_refl) as [Ha' Hpa'].
    split.
    + intros y. simpl. rewrite Hf_closed, Ha'. reflexivity.
    + simpl. split; assumption.
Qed.

Lemma stepf_resume_congruence_preserves : forall k a u,
  (forall u, closed_term k -> payloads_closed k ->
    stepf k = Some u -> closed_term u /\ payloads_closed u) ->
  (forall u, closed_term a -> payloads_closed a ->
    stepf a = Some u -> closed_term u /\ payloads_closed u) ->
  closed_term (TResume k a) -> payloads_closed (TResume k a) ->
  (match stepf k with
   | Some k' => Some (TResume k' a)
   | None => match stepf a with Some a' => Some (TResume k a') | None => None end
   end) = Some u ->
  closed_term u /\ payloads_closed u.
Proof.
  intros k a u IHk IHa Hclosed Hpayload Hstep.
  simpl in Hpayload. destruct Hpayload as [Hk_payload Ha_payload].
  assert (Hk_closed : closed_term k).
  { intros y. specialize (Hclosed y). simpl in Hclosed.
    apply orb_false_iff in Hclosed as [Hk_closed _]. exact Hk_closed. }
  assert (Ha_closed : closed_term a).
  { intros y. specialize (Hclosed y). simpl in Hclosed.
    apply orb_false_iff in Hclosed as [_ Ha_closed]. exact Ha_closed. }
  destruct (stepf k) eqn:Hsk.
  - inversion Hstep; subst.
    destruct (IHk t Hk_closed Hk_payload eq_refl) as [Hk' Hpk'].
    split.
    + intros y. simpl. rewrite Hk', Ha_closed. reflexivity.
    + simpl. split; assumption.
  - destruct (stepf a) eqn:Hsa; inversion Hstep; subst.
    destruct (IHa t Ha_closed Ha_payload eq_refl) as [Ha' Hpa'].
    split.
    + intros y. simpl. rewrite Hk_closed, Ha'. reflexivity.
    + simpl. split; assumption.
Qed.

Lemma stepf_preserves_closedness : forall t u,
  closed_term t -> payloads_closed t -> stepf t = Some u ->
  closed_term u /\ payloads_closed u.
Proof.
  induction t as
    [x| | |e IHe|scrut IHscrut zero_body IHzero succ_var succ_body IHsucc
    |param param_ty body IHbody|f IHf a IHa|x expr IHexpr body IHbody
    |func param param_ty body IHbody tag|op arg IHarg|body IHbody h
    |kont IHkont arg IHarg|h ctx|h ctx];
    intros u Hclosed Hpayload Hstep; simpl in Hstep; try discriminate.
  - destruct (stepf e) eqn:Hse; inversion Hstep; subst.
    destruct (IHe t Hclosed Hpayload eq_refl) as [Hc Hp].
    split; [intro x; simpl; apply Hc|exact Hp].
  - simpl in Hpayload. destruct Hpayload as [Hscrut_payload [Hzero_payload Hsucc_payload]].
    assert (Hscrut_closed : closed_term scrut).
    { intros y. specialize (Hclosed y). simpl in Hclosed.
      apply orb_false_iff in Hclosed as [Hleft _].
      apply orb_false_iff in Hleft as [Hscrut_closed _]. exact Hscrut_closed. }
    assert (Hzero_closed : closed_term zero_body).
    { intros y. specialize (Hclosed y). simpl in Hclosed.
      apply orb_false_iff in Hclosed as [Hleft _].
      apply orb_false_iff in Hleft as [_ Hzero_closed]. exact Hzero_closed. }
    destruct (is_value scrut) eqn:Hscrut_value.
    + destruct scrut as
        [sx| | |sv|sscrut sz sx ss|sparam sty sbody|sf sa
        |sx se sbody|sfunc sparam sty sbody stag|sop sarg|sbody sh
        |sk sa|sh sctx|sh sctx]; simpl in Hstep; try discriminate.
      * inversion Hstep; subst. split; [exact Hzero_closed|exact Hzero_payload].
      * inversion Hstep; subst.
        split.
        -- eapply closed_case_succ_subst; [exact Hclosed|].
           intros y. specialize (Hscrut_closed y). simpl in Hscrut_closed.
           exact Hscrut_closed.
        -- apply payloads_closed_subst; [exact Hscrut_payload|exact Hsucc_payload].
    + destruct (stepf scrut) as [scrut'|] eqn:Hsscrut; inversion Hstep; subst.
      destruct (IHscrut scrut' Hscrut_closed Hscrut_payload eq_refl)
        as [Hscrut' Hscrutp'].
      split.
      * intros y. simpl.
        specialize (Hclosed y). simpl in Hclosed.
        apply orb_false_iff in Hclosed as [Hleft Hsucc_closed].
        apply orb_false_iff in Hleft as [_ Hzero_closed_y].
        rewrite Hscrut', Hzero_closed_y.
        destruct (String.eqb y succ_var); [reflexivity|exact Hsucc_closed].
      * simpl. repeat split; assumption.
  - simpl in Hpayload. destruct Hpayload as [Hf_payload Ha_payload].
    assert (Hf_closed : closed_term f).
    { intros y. specialize (Hclosed y). simpl in Hclosed.
      apply orb_false_iff in Hclosed as [Hf_closed _]. exact Hf_closed. }
    assert (Ha_closed : closed_term a).
    { intros y. specialize (Hclosed y). simpl in Hclosed.
      apply orb_false_iff in Hclosed as [_ Ha_closed]. exact Ha_closed. }
    destruct (is_value f) eqn:Hf_value.
    + destruct (is_value a) eqn:Ha_value.
      * destruct f as
          [fx| | |fe|fscrut fz fx fs|fparam fty fbody|ff fa
          |fx fe fbody|ffunc fparam fty fbody ftag|fop farg|fbody fh
          |fk farg|fh fctx|fh fctx]; simpl in Hstep; try discriminate.
        inversion Hstep; subst.
        split.
        -- exact (closed_lam_subst fparam fty fbody a Hclosed).
        -- simpl in Hf_payload. apply payloads_closed_subst; assumption.
      * destruct (stepf a) as [a'|] eqn:Hsa; inversion Hstep; subst.
        destruct (IHa a' Ha_closed Ha_payload eq_refl) as [Ha' Hpa'].
        split.
        -- intros y. simpl. rewrite Hf_closed, Ha'. reflexivity.
        -- simpl. split; assumption.
    + destruct (stepf f) as [f'|] eqn:Hsf; inversion Hstep; subst.
      destruct (IHf f' Hf_closed Hf_payload eq_refl) as [Hf' Hpf'].
      split.
      * intros y. simpl. rewrite Hf', Ha_closed. reflexivity.
      * simpl. split; assumption.
  - destruct (is_value expr) eqn:Hexv.
    + inversion Hstep; subst.
      split.
      * apply closed_let_subst; [exact Hclosed|].
        intros y. specialize (Hclosed y). simpl in Hclosed.
        apply orb_false_iff in Hclosed as [Hexpr _]. exact Hexpr.
      * simpl in Hpayload. destruct Hpayload as [Hexpr Hbody].
        apply payloads_closed_subst; assumption.
    + destruct (stepf expr) eqn:Hse; inversion Hstep; subst.
      simpl in Hpayload. destruct Hpayload as [Hexpr Hbody].
      assert (Hexpr_closed : closed_term expr).
      { intros y. specialize (Hclosed y). simpl in Hclosed.
        apply orb_false_iff in Hclosed as [Hexpr_closed _]. exact Hexpr_closed. }
      destruct (IHexpr t Hexpr_closed Hexpr eq_refl) as [Hexpr' Hpexpr'].
      split.
      * intros y. simpl.
        specialize (Hclosed y). simpl in Hclosed.
        apply orb_false_iff in Hclosed as [_ Hbody_closed].
        rewrite Hexpr'.
        destruct (String.eqb y x); [reflexivity|exact Hbody_closed].
      * simpl. split; assumption.
  - inversion Hstep; subst.
    split.
    + apply closed_fix_unfold. exact Hclosed.
    + simpl. apply payloads_closed_subst; simpl; exact Hpayload.
  - destruct (stepf arg) eqn:Hsa; inversion Hstep; subst.
    destruct (IHarg t Hclosed Hpayload eq_refl) as [Harg' Hparg'].
    split; [exact Harg'|exact Hparg'].
  - destruct h as [rv rbody hop op_param op_k op_body].
    destruct (is_value body) eqn:Hbody_value.
    + inversion Hstep; subst.
      destruct (closed_handle_parts body (Handler rv rbody hop op_param op_k op_body) Hclosed)
        as [Hbody_closed Hhandler].
      split.
      * eapply (subst_closed_return_body rv rbody hop op_param op_k op_body body); eauto.
      * simpl in Hpayload. destruct Hpayload as [Hbody_payload [Hrbody_payload _]].
        apply payloads_closed_subst; assumption.
    + destruct (capture body) as [[cap_ctx cap_arg]|] eqn:Hcapture.
      * destruct (closed_handle_parts body (Handler rv rbody hop op_param op_k op_body) Hclosed)
          as [Hbody_closed Hhandler].
        destruct (capture_plug body cap_ctx cap_arg Hcapture) as [Hbody_eq _].
        subst body.
        destruct (plug_perform_closed_parts cap_ctx cap_arg Hbody_closed) as [Hcap_ctx_closed Harg_closed].
        simpl in Hpayload.
        destruct Hpayload as [Hbody_payload Hhandler_payload].
        destruct (plug_perform_payloads_parts cap_ctx cap_arg Hbody_payload)
          as [Hcap_payloads Harg_payload].
        destruct (mentions_var op_k op_body) eqn:Hopk.
        -- inversion Hstep; subst.
           split.
           ++ eapply subst_closed_op_resume; eauto.
           ++ unfold subst2.
              apply payloads_closed_subst.
              ** apply payloads_closed_contval; eauto.
              ** apply payloads_closed_subst; [exact Harg_payload|].
                 simpl in Hhandler_payload. tauto.
        -- inversion Hstep; subst.
           split.
           ++ eapply subst_closed_op_drop; eauto.
           ++ simpl in Hhandler_payload.
              apply payloads_closed_subst; [exact Harg_payload|tauto].
      * destruct (stepf body) eqn:Hsbody; inversion Hstep; subst.
        simpl in Hpayload. destruct Hpayload as [Hbody_payload Hhandler_payload].
        destruct (closed_handle_parts body (Handler rv rbody hop op_param op_k op_body) Hclosed)
          as [Hbody_closed Hhandler_closed].
        destruct (IHbody t Hbody_closed Hbody_payload eq_refl) as [Hbody' Hpayload'].
        split.
        -- apply closed_handle_rebuild; assumption.
        -- simpl. split; assumption.
  - simpl in Hpayload. destruct Hpayload as [Hkont_payload Harg_payload].
    assert (Hkont_closed : closed_term kont).
    { intros y. specialize (Hclosed y). simpl in Hclosed.
      apply orb_false_iff in Hclosed as [Hkont_closed _]. exact Hkont_closed. }
    assert (Harg_closed : closed_term arg).
    { intros y. specialize (Hclosed y). simpl in Hclosed.
      apply orb_false_iff in Hclosed as [_ Harg_closed]. exact Harg_closed. }
    assert (Hkont_step_preserves : forall kont',
      stepf kont = Some kont' ->
      closed_term (TResume kont' arg) /\ payloads_closed (TResume kont' arg)).
    { intros kont' Hskont.
      destruct (IHkont kont' Hkont_closed Hkont_payload Hskont) as [Hkont' Hpkont'].
      split.
      - intros y. simpl. rewrite Hkont', Harg_closed. reflexivity.
      - simpl. split; assumption. }
    assert (Harg_step_preserves : forall kont0 arg',
      closed_term kont0 -> payloads_closed kont0 -> stepf arg = Some arg' ->
      closed_term (TResume kont0 arg') /\ payloads_closed (TResume kont0 arg')).
    { intros kont0 arg' Hkont0_closed Hkont0_payload Hsarg.
      destruct (IHarg arg' Harg_closed Harg_payload Hsarg) as [Harg' Hparg'].
      split.
      - intros y. simpl. rewrite Hkont0_closed, Harg'. reflexivity.
      - simpl. split; assumption. }
    destruct kont as
      [kx| | |ke|kscrut kz kx ks|kparam kty kbody|kf ka
      |kx ke kbody|kfunc kparam kty kbody ktag|kop karg|kbody kh
      |kkont karg|kh kctx|kh kctx]; cbn [is_value] in Hstep.
    + discriminate.
    + destruct (is_value arg) eqn:Hargv; [discriminate|].
      destruct (stepf arg) as [arg'|] eqn:Hsarg; inversion Hstep; subst.
      eapply Harg_step_preserves; eauto.
    + destruct (is_value arg) eqn:Hargv; [discriminate|].
      destruct (stepf arg) as [arg'|] eqn:Hsarg; inversion Hstep; subst.
      eapply Harg_step_preserves; eauto.
    + destruct (is_value ke) eqn:Hke_value.
      * destruct (is_value arg) eqn:Hargv; [discriminate|].
        destruct (stepf arg) as [arg'|] eqn:Hsarg; inversion Hstep; subst.
        eapply Harg_step_preserves; eauto.
      * change (match stepf (TSucc ke) with
                | Some k' => Some (TResume k' arg)
                | None => None
                end = Some u) in Hstep.
        destruct (stepf (TSucc ke)) as [kont'|] eqn:Hskont;
          inversion Hstep; subst.
        apply Hkont_step_preserves. reflexivity.
    + change (match stepf (TCaseNat kscrut kz kx ks) with
              | Some k' => Some (TResume k' arg)
              | None => None
              end = Some u) in Hstep.
      destruct (stepf (TCaseNat kscrut kz kx ks)) as [kont'|] eqn:Hskont;
        inversion Hstep; subst.
      apply Hkont_step_preserves. reflexivity.
    + destruct (is_value arg) eqn:Hargv; [discriminate|].
      destruct (stepf arg) as [arg'|] eqn:Hsarg; inversion Hstep; subst.
      eapply Harg_step_preserves; eauto.
    + change (match stepf (TApp kf ka) with
              | Some k' => Some (TResume k' arg)
              | None => None
              end = Some u) in Hstep.
      destruct (stepf (TApp kf ka)) as [kont'|] eqn:Hskont;
        inversion Hstep; subst.
      apply Hkont_step_preserves. reflexivity.
    + change (match stepf (TLet kx ke kbody) with
              | Some k' => Some (TResume k' arg)
              | None => None
              end = Some u) in Hstep.
      destruct (stepf (TLet kx ke kbody)) as [kont'|] eqn:Hskont;
        inversion Hstep; subst.
      apply Hkont_step_preserves. reflexivity.
    + change (match stepf (TFix kfunc kparam kty kbody ktag) with
              | Some k' => Some (TResume k' arg)
              | None => None
              end = Some u) in Hstep.
      destruct (stepf (TFix kfunc kparam kty kbody ktag)) as [kont'|] eqn:Hskont;
        inversion Hstep; subst.
      apply Hkont_step_preserves. reflexivity.
    + change (match stepf (TPerform kop karg) with
              | Some k' => Some (TResume k' arg)
              | None => None
              end = Some u) in Hstep.
      destruct (stepf (TPerform kop karg)) as [kont'|] eqn:Hskont;
        inversion Hstep; subst.
      apply Hkont_step_preserves. reflexivity.
    + change (match stepf (THandle kbody kh) with
              | Some k' => Some (TResume k' arg)
              | None => None
              end = Some u) in Hstep.
      destruct (stepf (THandle kbody kh)) as [kont'|] eqn:Hskont;
        inversion Hstep; subst.
      apply Hkont_step_preserves. reflexivity.
    + change (match stepf (TResume kkont karg) with
              | Some k' => Some (TResume k' arg)
              | None => None
              end = Some u) in Hstep.
      destruct (stepf (TResume kkont karg)) as [kont'|] eqn:Hskont;
        inversion Hstep; subst.
      apply Hkont_step_preserves. reflexivity.
    + destruct (is_value arg) eqn:Hargv.
      * inversion Hstep; subst.
        apply payloads_closed_contval_inv in Hkont_payload as
          [Hhandler_closed [Hctx_closed [Hhandler_payload Hctx_payload]]].
        split.
        -- apply closed_handle_rebuild.
           ++ apply plug_closed; assumption.
           ++ exact Hhandler_closed.
        -- simpl. split.
           ++ apply ctx_payloads_closed_plug; assumption.
           ++ exact Hhandler_payload.
      * destruct (stepf arg) as [arg'|] eqn:Hsarg; inversion Hstep; subst.
        eapply Harg_step_preserves; eauto.
    + discriminate.
Qed.

Theorem step_preserves_closedness : forall t u,
  closed_term t -> payloads_closed t -> step t u ->
  closed_term u /\ payloads_closed u.
Proof.
  intros t u Hclosed Hpayload Hstep.
  inversion Hstep; subst.
  eapply stepf_preserves_closedness; eauto.
Qed.

(** Sprint 16 B1: canonical forms (docs/calculus.md §3.1/§4) and value-row canonicity. *)

Lemma canonical_nat : forall g v eps beta,
  is_value v = true -> has_type g v TyNat eps beta ->
  v = TZero \/ exists v', v = TSucc v' /\ is_value v' = true.
Proof.
  intros g v eps beta Hvalue Hty.
  destruct v as [x| | |v'|scrut zero_body succ_var succ_body
    |x param_ty body|f arg|x expr body|func param param_ty body tag
    |op arg|body h|kont arg|h ctx|h ctx];
    simpl in Hvalue; try discriminate; inversion Hty; subst.
  - left. reflexivity.
  - right. exists v'. split; [reflexivity|exact Hvalue].
Qed.

Lemma canonical_arrow : forall g v a lat_eps lat_beta b eps beta,
  is_value v = true -> has_type g v (TyArrow a lat_eps lat_beta b) eps beta ->
  exists x body, v = TLam x a body.
Proof.
  intros g v a lat_eps lat_beta b eps beta Hvalue Hty.
  destruct v as [y| | |v'|scrut zero_body succ_var succ_body
    |x param_ty body|f arg|y expr let_body|func param fix_ty fix_body tag
    |op arg|handle_body h|kont arg|h ctx|h ctx];
    simpl in Hvalue; try discriminate; inversion Hty; subst.
  eauto.
Qed.

Lemma canonical_cont : forall g v a bk b eps beta,
  is_value v = true -> has_type g v (TyCont a bk b) eps beta ->
  exists rv rbody op_param op_k op_body ctx,
    v = TContVal (Handler rv rbody L op_param op_k op_body) ctx.
Proof.
  intros g v a bk b eps beta Hvalue Hty.
  destruct v as [x| | |v'|scrut zero_body succ_var succ_body
    |x param_ty body|f arg|x expr let_body|func param fix_ty fix_body tag
    |op arg|handle_body h|kont arg|h ctx|h ctx];
    simpl in Hvalue; try discriminate; inversion Hty; subst.
  exists rv, rbody, op_param, op_k, op_body, ctx. reflexivity.
Qed.

Lemma value_rows_trivial : forall g v ty eps beta,
  is_value v = true -> has_type g v ty eps beta ->
  eps = EffEmpty /\ beta = BFinite 0.
Proof.
  intros g v ty eps beta Hvalue Hty.
  induction Hty; simpl in Hvalue; try discriminate; try (split; reflexivity).
  apply IHHty. exact Hvalue.
Qed.

(** Sprint 16 B2: context weakening — closed typings embed into any context. *)

Lemma typing_lookup_monotone : forall g1 t ty eps beta,
  has_type g1 t ty eps beta ->
  forall g2, (forall x tx, lookup x g1 = Some tx -> lookup x g2 = Some tx) ->
  has_type g2 t ty eps beta.
Proof.
  intros g1 t ty eps beta Hty.
  assert (lookup_preserve_cons :
    forall (g1 g2 : ctx) y ty0,
      (forall x tx, lookup x g1 = Some tx -> lookup x g2 = Some tx) ->
      forall x tx,
        lookup x ((y, ty0) :: g1) = Some tx ->
        lookup x ((y, ty0) :: g2) = Some tx).
  {
    intros ga gb y ty0 Hpres x tx Hlookup.
    simpl in Hlookup |- *.
    destruct (String.eqb x y); [exact Hlookup|].
    eapply Hpres. exact Hlookup.
  }
  induction Hty; intros g2 Hpres.
  - apply Ty_Var. eapply Hpres. exact H.
  - apply Ty_Unit.
  - apply Ty_Zero.
  - apply Ty_Succ. apply IHHty. exact Hpres.
  - eapply Ty_CaseNat.
    + apply IHHty1. exact Hpres.
    + apply IHHty2. exact Hpres.
    + apply IHHty3. apply lookup_preserve_cons. exact Hpres.
  - apply Ty_Lam. apply IHHty. apply lookup_preserve_cons. exact Hpres.
  - eapply Ty_App.
    + apply IHHty1. exact Hpres.
    + apply IHHty2. exact Hpres.
  - eapply Ty_Let.
    + apply IHHty1. exact Hpres.
    + apply IHHty2. apply lookup_preserve_cons. exact Hpres.
  - apply Ty_FixStructural. apply IHHty.
    apply lookup_preserve_cons. apply lookup_preserve_cons. exact Hpres.
  - apply Ty_FixMeasure. apply IHHty.
    apply lookup_preserve_cons. apply lookup_preserve_cons. exact Hpres.
  - eapply Ty_FixDiv. apply IHHty.
    apply lookup_preserve_cons. apply lookup_preserve_cons. exact Hpres.
  - apply Ty_Perform. apply IHHty. exact Hpres.
  - eapply Ty_HandleDrop.
    + apply IHHty1. exact Hpres.
    + apply IHHty2. apply lookup_preserve_cons. exact Hpres.
    + apply IHHty3. apply lookup_preserve_cons. apply lookup_preserve_cons. exact Hpres.
    + assumption.
    + assumption.
  - eapply Ty_HandleResume.
    + apply IHHty1. exact Hpres.
    + apply IHHty2. apply lookup_preserve_cons. exact Hpres.
    + apply IHHty3. apply lookup_preserve_cons. apply lookup_preserve_cons. exact Hpres.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
  - eapply Ty_Resume.
    + apply IHHty1. exact Hpres.
    + apply IHHty2. exact Hpres.
  - eapply Ty_ContVal; eauto.
Qed.

Lemma typing_context_ext : forall g1 g2 t ty eps beta,
  has_type g1 t ty eps beta ->
  (forall x, lookup x g1 = lookup x g2) ->
  has_type g2 t ty eps beta.
Proof.
  intros g1 g2 t ty eps beta Hty Heq.
  eapply typing_lookup_monotone; eauto.
  intros x tx Hlookup.
  rewrite <- Heq.
  exact Hlookup.
Qed.

Theorem closed_typing_weakening : forall t ty eps beta,
  has_type [] t ty eps beta -> forall g, has_type g t ty eps beta.
Proof.
  intros t ty eps beta Hty g.
  eapply typing_lookup_monotone; eauto.
  intros x tx Hlookup. discriminate Hlookup.
Qed.

(** Proof ladder for [docs/calculus.md §8] and mechanization target §10. *)

Theorem L2_substitution_nonhandler_min : forall g t ty eps beta x replacement,
  has_type g t ty eps beta ->
  mentions_var x t = false ->
  subst x replacement t = t ->
  has_type g (subst x replacement t) ty eps beta.
Proof. apply substitution_preserves_unmentioned_typing. Qed.

Theorem L5_mentions_iff_resume : forall k body,
  handler_clause_ok k body = true ->
  (mentions_var k body = true <-> direct_resume_count k body = 1).
Proof. apply handler_clause_ok_mentions_iff_resumes. Qed.

Theorem step_is_deterministic : forall t u v,
  step t u -> step t v -> u = v.
Proof. apply step_deterministic. Qed.

(** Sprint 16 B3: operation blocking, context-rich (docs/calculus.md §5/§8.1). *)

(* Mirrors capture's handler-free frame grammar: a blocked term is an unhandled
   [perform L v] under evaluation-context frames with NO enclosing handler
   (one label: every handler intercepts, so THandle never appears on the spine).
   Sprint 16 B3 replaces the Sprint 15 top-level-only predicate — finding
   twenty-one's counterexample was exactly a blocked-under-a-let term the old
   shape missed. *)
Inductive blocked_ind : term -> Prop :=
| Blocked_Here : forall v, is_value v = true -> blocked_ind (TPerform L v)
| Blocked_PerformArg : forall e, blocked_ind e -> blocked_ind (TPerform L e)
| Blocked_Succ : forall e, blocked_ind e -> blocked_ind (TSucc e)
| Blocked_Case : forall scrut e0 x e1,
    blocked_ind scrut -> blocked_ind (TCaseNat scrut e0 x e1)
| Blocked_AppFun : forall f a, blocked_ind f -> blocked_ind (TApp f a)
| Blocked_AppArg : forall f a,
    is_value f = true -> blocked_ind a -> blocked_ind (TApp f a)
| Blocked_Let : forall x e body, blocked_ind e -> blocked_ind (TLet x e body)
| Blocked_ResumeK : forall k arg, blocked_ind k -> blocked_ind (TResume k arg)
| Blocked_ResumeArg : forall k arg,
    is_value k = true -> blocked_ind arg -> blocked_ind (TResume k arg).

Definition blocked_on_operation (l : label) (t : term) : Prop :=
  match l with L => blocked_ind t end.

Lemma blocked_not_value : forall t, blocked_ind t -> is_value t = false.
Proof.
  intros t Hblocked. induction Hblocked; simpl; try reflexivity.
  exact IHHblocked.
Qed.

Lemma blocked_iff_capture : forall t,
  blocked_ind t <-> exists ctx v, capture t = Some (ctx, v).
Proof.
  split.
  - intros Hblocked. induction Hblocked.
    + exists [], v. simpl. rewrite H. reflexivity.
    + destruct IHHblocked as [ctx [v Hcapture]].
      pose proof (blocked_not_value e Hblocked) as Hnot_value.
      exists (FPerformArg L :: ctx), v.
      simpl. rewrite Hnot_value. unfold capture_cons. rewrite Hcapture. reflexivity.
    + destruct IHHblocked as [ctx [v Hcapture]].
      pose proof (blocked_not_value e Hblocked) as Hnot_value.
      exists (FSucc :: ctx), v.
      simpl. rewrite Hnot_value. unfold capture_cons. rewrite Hcapture. reflexivity.
    + destruct IHHblocked as [ctx [v Hcapture]].
      pose proof (blocked_not_value scrut Hblocked) as Hnot_value.
      exists (FCaseScrut e0 x e1 :: ctx), v.
      simpl. rewrite Hnot_value. unfold capture_cons. rewrite Hcapture. reflexivity.
    + destruct IHHblocked as [ctx [v Hcapture]].
      pose proof (blocked_not_value f Hblocked) as Hnot_value.
      exists (FAppFun a :: ctx), v.
      simpl. rewrite Hnot_value. unfold capture_cons. rewrite Hcapture. reflexivity.
    + destruct IHHblocked as [ctx [v Hcapture]].
      pose proof (blocked_not_value a Hblocked) as Harg_not_value.
      exists (FAppArg f :: ctx), v.
      simpl. rewrite H. rewrite Harg_not_value.
      unfold capture_cons. rewrite Hcapture. reflexivity.
    + destruct IHHblocked as [ctx [v Hcapture]].
      pose proof (blocked_not_value e Hblocked) as Hnot_value.
      exists (FLet x body :: ctx), v.
      simpl. rewrite Hnot_value. unfold capture_cons. rewrite Hcapture. reflexivity.
    + destruct IHHblocked as [ctx [v Hcapture]].
      pose proof (blocked_not_value k Hblocked) as Hkont_not_value.
      exists (FResumeK arg :: ctx), v.
      destruct k as
        [kx| | |ke|kscrut ke0 kx ke1|kparam kparam_ty kbody|kf ka
        |kx ke kbody|kfunc kparam kparam_ty kbody ktag|kop karg|kbody kh
        |kkont karg|kh kctx|kh kctx];
        cbn [capture is_value] in Hcapture, Hkont_not_value |- *;
        try discriminate Hcapture; try discriminate Hkont_not_value.
      * rewrite Hkont_not_value.
        rewrite Hkont_not_value in Hcapture.
        unfold capture_cons at 1. rewrite Hcapture. reflexivity.
      * unfold capture_cons at 1. rewrite Hcapture. reflexivity.
      * unfold capture_cons at 1. rewrite Hcapture. reflexivity.
      * unfold capture_cons at 1. rewrite Hcapture. reflexivity.
      * unfold capture_cons at 1. rewrite Hcapture. reflexivity.
      * unfold capture_cons at 1. rewrite Hcapture. reflexivity.
    + destruct IHHblocked as [ctx [v Hcapture]].
      pose proof (blocked_not_value arg Hblocked) as Harg_not_value.
      exists (FResumeArg k :: ctx), v.
      destruct k as
        [kx| | |ke|kscrut ke0 kx ke1|kparam kparam_ty kbody|kf ka
        |kx ke kbody|kfunc kparam kparam_ty kbody ktag|kop karg|kbody kh
        |kkont karg|kh kctx|kh kctx];
        cbn [capture is_value] in H, Harg_not_value |- *;
        try discriminate H;
        try (rewrite H; rewrite Harg_not_value;
             unfold capture_cons; rewrite Hcapture; reflexivity).
      * rewrite Harg_not_value. unfold capture_cons at 1. rewrite Hcapture. reflexivity.
      * rewrite Harg_not_value. unfold capture_cons at 1. rewrite Hcapture. reflexivity.
      * rewrite Harg_not_value. unfold capture_cons at 1. rewrite Hcapture. reflexivity.
      * rewrite Harg_not_value. unfold capture_cons at 1. rewrite Hcapture. reflexivity.
  - assert (Hcons_some : forall f sub ctx v,
      capture_cons f (capture sub) = Some (ctx, v) ->
      exists sub_ctx sub_v, capture sub = Some (sub_ctx, sub_v)).
    {
      intros f sub ctx v Hcapture.
      unfold capture_cons in Hcapture.
      destruct (capture sub) as [[sub_ctx sub_v]|] eqn:Hsub; try discriminate.
      exists sub_ctx, sub_v. reflexivity.
    }
    induction t as
      [x| | |e IHe|scrut IHscrut e0 IHe0 x e1 IHe1
      |param param_ty body IHbody|f IHf a IHa|x e IHe body IHbody
      |func param param_ty body IHbody tag|op arg IHarg|body IHbody h
      |kont IHkont arg IHarg|h ctx0|h ctx0];
      intros [ctx [v Hcapture]]; cbn [capture is_value] in Hcapture; try discriminate.
    + destruct (is_value e) eqn:He; try discriminate.
      apply Blocked_Succ. apply IHe. eapply Hcons_some. exact Hcapture.
    + destruct (is_value scrut) eqn:Hscrut; try discriminate.
      apply Blocked_Case. apply IHscrut. eapply Hcons_some. exact Hcapture.
    + destruct (is_value f) eqn:Hf.
      * destruct (is_value a) eqn:Ha; try discriminate.
        apply Blocked_AppArg; [exact Hf|].
        apply IHa. eapply Hcons_some. exact Hcapture.
      * apply Blocked_AppFun. apply IHf. eapply Hcons_some. exact Hcapture.
    + destruct (is_value e) eqn:He; try discriminate.
      apply Blocked_Let. apply IHe. eapply Hcons_some. exact Hcapture.
    + destruct op.
      destruct (is_value arg) eqn:Harg.
      * inversion Hcapture; subst. apply Blocked_Here. exact Harg.
      * apply Blocked_PerformArg. apply IHarg. eapply Hcons_some. exact Hcapture.
    + destruct kont as
        [kx| | |ke|kscrut ke0 kx ke1|kparam kparam_ty kbody|kf ka
        |kx ke kbody|kfunc kparam kparam_ty kbody ktag|kop karg|kbody kh
        |kkont karg|kh kctx|kh kctx];
        cbn [capture is_value] in Hcapture.
      * discriminate.
      * destruct (is_value arg) eqn:Harg; try discriminate.
        apply Blocked_ResumeArg; [reflexivity|].
        apply IHarg. eapply Hcons_some. exact Hcapture.
      * destruct (is_value arg) eqn:Harg; try discriminate.
        apply Blocked_ResumeArg; [reflexivity|].
        apply IHarg. eapply Hcons_some. exact Hcapture.
      * destruct (is_value (TSucc ke)) eqn:Hkont_value.
        -- change (is_value ke = true) in Hkont_value.
           rewrite Hkont_value in Hcapture.
           destruct (is_value arg) eqn:Harg; try discriminate.
           apply Blocked_ResumeArg; [exact Hkont_value|].
           apply IHarg. eapply Hcons_some. exact Hcapture.
        -- change (is_value ke = false) in Hkont_value.
           rewrite Hkont_value in Hcapture.
           apply Blocked_ResumeK. apply IHkont.
           unfold capture_cons at 1 in Hcapture.
           destruct (capture_cons FSucc (capture ke)) as [[sub_ctx sub_v]|] eqn:Hsub;
             [|discriminate Hcapture].
           exists sub_ctx, sub_v.
           cbn [capture is_value]. rewrite Hkont_value. rewrite Hsub. reflexivity.
      * apply Blocked_ResumeK. apply IHkont. eapply Hcons_some. exact Hcapture.
      * destruct (is_value arg) eqn:Harg; try discriminate.
        apply Blocked_ResumeArg; [reflexivity|].
        apply IHarg. eapply Hcons_some. exact Hcapture.
      * apply Blocked_ResumeK. apply IHkont. eapply Hcons_some. exact Hcapture.
      * apply Blocked_ResumeK. apply IHkont. eapply Hcons_some. exact Hcapture.
      * discriminate.
      * apply Blocked_ResumeK. apply IHkont. eapply Hcons_some. exact Hcapture.
      * discriminate.
      * apply Blocked_ResumeK. apply IHkont. eapply Hcons_some. exact Hcapture.
      * destruct (is_value arg) eqn:Harg; try discriminate.
        apply Blocked_ResumeArg; [reflexivity|].
        apply IHarg. eapply Hcons_some. exact Hcapture.
      * discriminate.
Qed.

Lemma eff_mem_join_l : forall a b, eff_mem a = true -> eff_mem (eff_join a b) = true.
Proof. destruct a, b; simpl; intros H; try discriminate; reflexivity. Qed.

Lemma eff_mem_join_r : forall a b, eff_mem b = true -> eff_mem (eff_join a b) = true.
Proof. destruct a, b; simpl; intros H; try discriminate; reflexivity. Qed.

Lemma typed_stuck_implies_blocked : forall g t ty eps beta,
  has_type g t ty eps beta -> g = [] ->
  is_value t = false -> stepf t = None ->
  blocked_ind t /\ eff_mem eps = true.
Proof.
  intros g t ty eps beta Hty.
  induction Hty; intros Hg Hnot_value Hstuck; subst; simpl in Hnot_value; try discriminate.
  - simpl in Hstuck.
    destruct (stepf e) eqn:Hestep; try discriminate.
    destruct (IHHty eq_refl Hnot_value eq_refl) as [Hblocked Hmem].
    split; [apply Blocked_Succ; exact Hblocked|exact Hmem].
  - simpl in Hstuck.
    destruct (is_value scrut) eqn:Hscrut_value.
    + match goal with
      | Hscrut_ty : has_type [] scrut TyNat ?eps_s ?beta_s |- _ =>
          destruct (canonical_nat [] scrut eps_s beta_s Hscrut_value Hscrut_ty)
            as [Hzero | [pred [Hsucc Hpred_value]]]
      end.
      * subst scrut. simpl in Hstuck. discriminate.
      * subst scrut. simpl in Hstuck. discriminate.
    + destruct (stepf scrut) eqn:Hscrut_step; try discriminate.
      destruct (IHHty1 eq_refl eq_refl eq_refl) as [Hblocked Hmem].
      split.
      * apply Blocked_Case. exact Hblocked.
      * apply eff_mem_join_l. exact Hmem.
  - simpl in Hstuck.
    destruct (is_value f) eqn:Hfun_value.
    + destruct (is_value a) eqn:Harg_value.
      * match goal with
        | Hfun_ty : has_type [] f (TyArrow ?arg_ty ?lat_eps ?lat_beta ?ret_ty) ?epsf ?betaf |- _ =>
            destruct (canonical_arrow [] f arg_ty lat_eps lat_beta ret_ty epsf betaf
              Hfun_value Hfun_ty) as [param [body Hfun_shape]]
        end.
        subst f. simpl in Hstuck. discriminate.
      * destruct (stepf a) eqn:Harg_step; try discriminate.
        destruct (IHHty2 eq_refl eq_refl eq_refl) as [Hblocked Hmem].
        split.
        -- apply Blocked_AppArg; [exact Hfun_value|exact Hblocked].
        -- apply eff_mem_join_r. apply eff_mem_join_l. exact Hmem.
    + destruct (stepf f) eqn:Hfun_step; try discriminate.
      destruct (IHHty1 eq_refl eq_refl eq_refl) as [Hblocked Hmem].
      split.
      * apply Blocked_AppFun. exact Hblocked.
      * apply eff_mem_join_l. exact Hmem.
  - simpl in Hstuck.
    destruct (is_value e) eqn:Hexpr_value; try discriminate.
    destruct (stepf e) eqn:Hexpr_step; try discriminate.
    destruct (IHHty1 eq_refl eq_refl eq_refl) as [Hblocked Hmem].
    split.
    + apply Blocked_Let. exact Hblocked.
    + apply eff_mem_join_l. exact Hmem.
  - simpl in Hstuck.
    destruct (is_value arg) eqn:Harg_value.
    + split.
      * apply Blocked_Here. exact Harg_value.
      * reflexivity.
    + destruct (stepf arg) eqn:Harg_step; try discriminate.
      destruct (IHHty eq_refl eq_refl eq_refl) as [_ Hmem].
      discriminate Hmem.
  - simpl in Hstuck.
    destruct (is_value body) eqn:Hbody_value; try discriminate.
    destruct (capture body) as [[cap_ctx cap_arg]|] eqn:Hcapture.
    + destruct (mentions_var op_k op_body); discriminate.
    + destruct (stepf body) eqn:Hbody_step; try discriminate.
      destruct (IHHty1 eq_refl eq_refl eq_refl) as [Hblocked _].
      (* A well-typed handle over a stuck body cannot be stuck — blocked meets handler ⇒ capture succeeds ⇒ steps. *)
      apply blocked_iff_capture in Hblocked.
      destruct Hblocked as [ctx [v Hsome]].
      rewrite Hcapture in Hsome. discriminate.
  - simpl in Hstuck.
    destruct (is_value body) eqn:Hbody_value; try discriminate.
    destruct (capture body) as [[cap_ctx cap_arg]|] eqn:Hcapture.
    + destruct (mentions_var op_k op_body); discriminate.
    + destruct (stepf body) eqn:Hbody_step; try discriminate.
      destruct (IHHty1 eq_refl eq_refl eq_refl) as [Hblocked _].
      (* A well-typed handle over a stuck body cannot be stuck — blocked meets handler ⇒ capture succeeds ⇒ steps. *)
      apply blocked_iff_capture in Hblocked.
      destruct Hblocked as [ctx [v Hsome]].
      rewrite Hcapture in Hsome. discriminate.
  - destruct (is_value k) eqn:Hkont_value.
    + match goal with
      | Hkont_ty : has_type [] k (TyCont TyNat ?bk ?ret_ty) EffEmpty (BFinite 0) |- _ =>
          destruct (canonical_cont [] k TyNat bk ret_ty EffEmpty (BFinite 0)
            Hkont_value Hkont_ty) as
            [rv [rbody [op_param [op_k [op_body [ctx Hkont_shape]]]]]]
      end.
      subst k. simpl in Hstuck.
      destruct (is_value arg) eqn:Harg_value; try discriminate.
      destruct (stepf arg) eqn:Harg_step; try discriminate.
      destruct (IHHty2 eq_refl eq_refl eq_refl) as [_ Hmem].
      discriminate Hmem.
    + assert (Hkont_step : stepf k = None).
      {
        destruct k as
          [kx| | |ke|kscrut ke0 kx ke1|kparam kparam_ty kbody|kf ka
          |kx ke kbody|kfunc kparam kparam_ty kbody ktag|kop karg|kbody kh
          |kkont karg|kh kctx|kh kctx];
          try discriminate Hkont_value; try reflexivity.
        - change ((if is_value (TSucc ke)
                   then if is_value arg
                        then None
                        else match stepf arg with
                             | Some arg' => Some (TResume (TSucc ke) arg')
                             | None => None
                             end
                   else match stepf (TSucc ke) with
                        | Some k' => Some (TResume k' arg)
                        | None => None
                        end) = None) in Hstuck.
          rewrite Hkont_value in Hstuck.
          destruct (stepf (TSucc ke)) eqn:Hke_step; [discriminate|reflexivity].
        - change (match stepf (TCaseNat kscrut ke0 kx ke1) with
                  | Some k' => Some (TResume k' arg)
                  | None => None
                  end = None) in Hstuck.
          destruct (stepf (TCaseNat kscrut ke0 kx ke1)) eqn:Hk_step;
            [discriminate|reflexivity].
        - change (match stepf (TApp kf ka) with
                  | Some k' => Some (TResume k' arg)
                  | None => None
                  end = None) in Hstuck.
          destruct (stepf (TApp kf ka)) eqn:Hk_step; [discriminate|reflexivity].
        - change (match stepf (TLet kx ke kbody) with
                  | Some k' => Some (TResume k' arg)
                  | None => None
                  end = None) in Hstuck.
          destruct (stepf (TLet kx ke kbody)) eqn:Hk_step; [discriminate|reflexivity].
        - simpl in Hstuck. discriminate.
        - change (match stepf (TPerform kop karg) with
                  | Some k' => Some (TResume k' arg)
                  | None => None
                  end = None) in Hstuck.
          destruct (stepf (TPerform kop karg)) eqn:Hk_step; [discriminate|reflexivity].
        - change (match stepf (THandle kbody kh) with
                  | Some k' => Some (TResume k' arg)
                  | None => None
                  end = None) in Hstuck.
          destruct (stepf (THandle kbody kh)) eqn:Hk_step; [discriminate|reflexivity].
        - change (match stepf (TResume kkont karg) with
                  | Some k' => Some (TResume k' arg)
                  | None => None
                  end = None) in Hstuck.
          destruct (stepf (TResume kkont karg)) eqn:Hk_step; [discriminate|reflexivity].
      }
      destruct (IHHty1 eq_refl eq_refl Hkont_step) as [_ Hmem].
      discriminate Hmem.
Qed.

Theorem progress : forall t ty eps beta,
  has_type [] t ty eps beta ->
  is_value t = true \/ (exists u, step t u) \/
  (exists l, eff_mem eps = true /\ blocked_on_operation l t).
Admitted.

(** Effect-closed progress corollary, consumed by the Sprint 13 spawn rule: spawned task
    bodies require the empty row, so the unhandled-operation disjunct is uninhabited. *)
Theorem progress_effect_closed : forall t ty beta,
  has_type [] t ty EffEmpty beta -> is_value t = true \/ exists u, step t u.
Proof.
  intros t ty beta Ht.
  destruct (progress t ty EffEmpty beta Ht) as [Hv|[[u Hu]|[l [Hm Hb]]]].
  - left; exact Hv.
  - right; exists u; exact Hu.
  - simpl in Hm. discriminate Hm.
Qed.

(** Finding eighteen / SPEC-GAP(preservation-statement-drift): preservation carries the
    explicit row and boundedness order components claimed by docs/calculus.md §8.2. *)
Theorem preservation : forall t u ty eps beta,
  has_type [] t ty eps beta -> step t u ->
  exists eps' beta', has_type [] u ty eps' beta' /\ eff_sub eps' eps = true /\ bound_le beta' beta.
Admitted.

(* L6 status: Stated-Pending-Infrastructure, owner: future Iris/resource sprint.
   This is deliberately not a theorem yet: the scaffold has no continuation resource/usage
   transition model to quantify over. The intended statement is that well-typed closed
   programs cannot reach the §5 resume-after-use stuck state. L5 supplies the syntactic
   exactly-one direct resume premise; the missing infrastructure is the dynamic one-shot
   resource model. *)

(** L7: boundedness soundness over the docs/calculus.md §9.1 slot metric. Sprint 15 builds
    [frame_step] and proves erasure; the strengthened preservation invariant that finite
    certified beta bounds every frame-counting prefix is the next proofs sprint's owner. *)
Theorem boundedness_soundness : forall t ty n,
  has_type [] t ty EffEmpty (BFinite n) ->
  forall u frames, frame_step t frames u -> frames <= n.
Admitted.

Theorem solver_certificate_postfix_field : forall cert c,
  satisfies (certified_value cert) c.
Proof. intros cert c. exact (certificate_postfix cert c). Qed.

Theorem solver_certificate_soundness : forall rho cert c,
  (forall c', satisfies rho c') ->
  satisfies (certified_value cert) c /\ bound_le (rho (target c)) (certified_value cert (target c)).
Admitted.

(* L9 status: Stated-Pending-Infrastructure, owner: future heap/graded-context sprint.
   Sprint 11 extends the executable compiler with docs/calculus.md §4 data affinity and
   §9.2 arrays, but this Rocq scaffold deliberately does not yet model heap arrays or
   Q-graded data contexts. The intended theorem states that, under the affine discipline,
   [inplace set] is observationally equivalent to functional [set]. It is not represented
   as an [Admitted] theorem until those missing definitions exist. *)

(* L10 status: Stated-Pending-Infrastructure, owner: future concurrent-semantics sprint.
   Sprint 13 extends the executable compiler with docs/calculus.md §5 task oracle semantics
   and §9.3 region-tree native tasks. The intended theorem states schedule independence:
   every fair native task interleaving of a well-typed program has the same observables as
   the deterministic sequential oracle. It needs a concurrent small-step relation over task
   pools and region-tree ownership, so it is not represented as an [Admitted] theorem yet. *)
