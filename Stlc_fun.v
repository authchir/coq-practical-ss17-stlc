Require Import Coq.Bool.Bool.

Require Export Stlc.

Definition is_value (e : expr) : bool :=
  match e with
  | eunit => true
  | eabs _ _ _ => true
  | _ => false
  end.

Theorem value_iff_is_value : forall e,
  value e <-> is_value e = true.
Proof.
  intros e.
  split; intros H.
  - induction H; reflexivity.
  - induction e; auto using value; inversion H.
Qed.

Fixpoint feval (e : expr) : option expr :=
  match e with
  | eapp (eabs x t e) e2 =>
      if is_value e2 then
        Some (subst x e2 e)
      else
        match feval e2 with
        | Some v2 => Some (eapp (eabs x t e) v2)
        | None => None
        end
  | eapp e1 e2 =>
      match feval e1 with
      | Some v1 => Some (eapp v1 e2)
      | None => None
      end
  | _ => None
  end.

Lemma not_value_if_eval : forall e1 e2, eval e1 e2 -> ~ value e1.
Proof.
  intros e1 e2 H.
  inversion H; rewrite value_iff_is_value; discriminate.
Qed.

Theorem feval_if_eval : forall c e1 e2 t,
  has_type c e1 t ->
  eval e1 e2 ->
  feval e1 = Some e2.
Proof.
  intros c e1 e2 t HAS_TYPE EVAL.
  generalize dependent t.
  generalize dependent c.
  induction EVAL; intros c ty HAS_TYPE.
  - simpl.
    destruct e1;
      inversion EVAL; inversion HAS_TYPE; subst;
      erewrite IHEVAL; eauto.
  - simpl.
    destruct v1.
    + inversion HAS_TYPE; subst.
      inversion H3.
    + inversion H.
    + inversion HAS_TYPE; subst.
      apply not_value_if_eval in EVAL.
      rewrite value_iff_is_value in EVAL.
      apply not_true_is_false in EVAL.
      rewrite EVAL.
      erewrite IHEVAL; eauto.
    + inversion H.
  - apply value_iff_is_value in H.
    simpl.
    rewrite H.
    reflexivity.
Qed.

Theorem eval_if_feval : forall c e1 e2 t,
  has_type c e1 t ->
  feval e1 = Some e2 ->
  eval e1 e2.
Proof.
  intros c e1.
  generalize dependent c.
  induction e1; intros c e2 ty HAS_TYPE H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion HAS_TYPE; clear HAS_TYPE; subst.
    destruct e1_1 eqn:Heqn.
    + discriminate.
    + discriminate.
    + simpl in H.
      destruct (is_value e1_2) eqn:Heqn2.
      * inversion H.
        apply eval_beta.
        apply value_iff_is_value.
        assumption.
      * destruct (feval e1_2);inversion H;
          eauto using eval_app2, vabs.
    + rewrite <- Heqn in *.
      simpl in H.
      destruct (feval e1_1) eqn:Heqn2.
      * rewrite Heqn in *.
        inversion H.
        eauto using eval_app1.
      * rewrite Heqn in *.
        discriminate.
Qed.

Theorem eval_iff_feval : forall c e1 e2 t,
  has_type c e1 t ->
  eval e1 e2 <->
  feval e1 = Some e2.
Proof.
  intros.
  split.
  - eauto using feval_if_eval.
  - eauto using eval_if_feval.
Qed.
