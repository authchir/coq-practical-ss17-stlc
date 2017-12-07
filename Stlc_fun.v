Require Import Coq.Bool.Bool.

Require Export Stlc.

Scheme Equality for type.

Lemma type_beq_refl : forall t,
  type_beq t t = true.
Proof.
  induction t.
  - reflexivity.
  - simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

Lemma type_beq_eq_iff : forall t1 t2,
  type_beq t1 t2 = true <-> t1 = t2.
Proof.
  intros t1 t2.
  split; intros H.
  - generalize dependent t2.
    induction t1; intros t2 H.
    + destruct t2; try discriminate; reflexivity.
    + destruct t2; try discriminate.
      simpl in H.
      apply andb_true_iff in H as [H1 H2].
      apply IHt1_1 in H1.
      apply IHt1_2 in H2.
      subst.
      reflexivity.
  - rewrite H.
    apply type_beq_refl.
Qed.


(******************************************************************************)
(* has_type                                                                   *)
(******************************************************************************)
Print has_type.

Fixpoint fhas_type (c : context) (e : expr) : option type :=
  match e with
  | eunit => Some tunit
  | evar x => Context.find x c
  | eabs x t1 e =>
      option_map (tfun t1) (fhas_type (Context.add x t1 c) e)
  | eapp e1 e2 =>
      match fhas_type c e1 with
      | Some (tfun t1 t2) =>
          match fhas_type c e2 with
          | Some t3 =>
              if type_beq t1 t3 then Some t2 else None
          | None => None
          end
      | Some _ => None
      | None => None
      end
  | elet x e1 e2 =>
      match fhas_type c e1 with
      | Some t1 => fhas_type (Context.add x t1 c) e2
      | None => None
      end
  end.

Theorem fhas_type_if_has_type : forall c e t,
  has_type c e t -> fhas_type c e = Some t.
Proof.
  intros c e t HAS_TYPE.
  induction HAS_TYPE.
  - reflexivity.
  - simpl.
    rewrite H.
    reflexivity.
  - simpl.
    rewrite IHHAS_TYPE.
    reflexivity.
  - simpl.
    rewrite IHHAS_TYPE1.
    rewrite IHHAS_TYPE2.
    rewrite type_beq_refl.
    reflexivity.
  - simpl.
    rewrite IHHAS_TYPE1.
    assumption.
Qed.

Theorem has_type_if_fhas_type : forall c e t,
  fhas_type c e = Some t -> has_type c e t.
Proof.
  intros c e.
  generalize dependent c.
  induction e; intros c ty H.
  - inversion H; clear H.
    apply has_type_unit.
  - inversion H; clear H.
    apply has_type_var.
    assumption.
  - inversion H; clear H.
    destruct (fhas_type (Context.add v t c) e) eqn:Heqn.
    + inversion H1; clear H1.
      apply has_type_abs.
      auto.
    + discriminate.
  - inversion H; clear H.
    destruct (fhas_type c e1) eqn:Heqn1.
    + destruct t eqn:Heqn2.
      * discriminate.
      * destruct (fhas_type c e2) eqn:Heqn3.
        { destruct (type_beq t0_1 t0) eqn:Heqn4.
          - apply type_beq_eq_iff in Heqn4; subst.
            inversion H1; clear H1; subst.
            eapply has_type_app; eauto.
          - discriminate.
        }
        { discriminate. }
    + discriminate.
  - inversion H; clear H.
    destruct (fhas_type c e1) eqn:Heqn1; try discriminate.
    destruct (fhas_type (Context.add v t c) e2) eqn:Heqn2; try discriminate.
    inversion H1; subst.
    eauto using has_type_let.
Qed.

Theorem has_type_iff_fhas_type : forall c e t,
  has_type c e t <-> fhas_type c e = Some t.
Proof.
  intros. split.
  - eauto 2 using fhas_type_if_has_type.
  - eauto 2 using has_type_if_fhas_type.
Qed.

(******************************************************************************)
(* value                                                                      *)
(******************************************************************************)

Definition is_value (e : expr) : bool :=
  match e with
  | eunit => true
  | eabs _ _ _ => true
  | _ => false
  end.

Theorem value_iff_is_value : forall e,
  value e <-> is_value e = true.
Proof.
  intros e. split; intros H.
  - induction H; reflexivity.
  - induction e; auto using value; inversion H.
Qed.

Theorem not_value_iff_is_value_false : forall e,
  ~ value e <-> is_value e = false.
Proof.
Admitted.

(******************************************************************************)
(* feval                                                                      *)
(******************************************************************************)

Print eval.

Fixpoint feval (h : heap) (e : expr) : option expr :=
  match e with
  | eunit => None
  | evar x => Heap.find x h
  | eabs _ _ _ => None
  | eapp (eabs x t e) e2 =>
      if is_value e2 then
        Some (subst x e2 e)
      else
        match feval h e2 with
        | Some v2 => Some (eapp (eabs x t e) v2)
        | None => None
        end
  | eapp e1 e2 =>
      match feval h e1 with
      | Some v1 => Some (eapp v1 e2)
      | None => None
      end
  | elet x e1 e2 =>
      if is_value e1 then
        Some (subst x e1 e2)
      else
        match feval h e1 with
        | Some v1 => Some (elet x v1 e2)
        | None => None
        end
  end.

Lemma not_value_if_eval : forall h e1 e2, eval h e1 e2 -> ~ value e1.
Proof.
  intros h e1 e2 H.
  inversion H; rewrite value_iff_is_value; try discriminate.
Qed.

Theorem feval_if_eval : forall c h e1 e2 t,
  has_type c e1 t ->
  eval h e1 e2 ->
  feval h e1 = Some e2.
Proof.
  intros c h e1 e2 t HAS_TYPE EVAL.
  generalize dependent t.
  generalize dependent c.
  induction EVAL; intros c ty HAS_TYPE.
  - assumption.
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
    + inversion H.
  - apply value_iff_is_value in H.
    simpl.
    rewrite H.
    reflexivity.
  - simpl.
    inversion HAS_TYPE; clear HAS_TYPE; subst.
    apply not_value_if_eval in EVAL.
    rewrite value_iff_is_value in EVAL.
    apply not_true_is_false in EVAL.
    destruct (is_value e1) eqn:Heqn.
    + discriminate.
    + erewrite IHEVAL; eauto 1.
  - simpl.
    apply value_iff_is_value in H.
    rewrite H.
    reflexivity.
Qed.

Lemma eval_if_not_value : forall e1,
  ~ value e1 -> exists h e2, eval h e1 e2.
Proof.
Admitted.

Theorem eval_if_feval : forall c h e1 e2 t,
  has_type c e1 t ->
  feval h e1 = Some e2 ->
  eval h e1 e2.
Proof.
  intros c h e1.
  generalize dependent h.
  generalize dependent c.
  induction e1; intros c h e2 ty HAS_TYPE H.
  - inversion H.
  - simpl in H.
    apply eval_var.
    assumption.
  - inversion H.
  - inversion HAS_TYPE; clear HAS_TYPE; subst.
    destruct e1_1 eqn:Heqn.
    + discriminate.
    + simpl in H.
      destruct (Heap.find (elt:=expr) v h) eqn:Heqn2.
      * inversion H.
        apply eval_app1.
        apply eval_var.
        assumption.
      * discriminate.
    + simpl in H.
      destruct (is_value e1_2) eqn:Heqn2.
      * inversion H.
        apply eval_beta.
        apply value_iff_is_value.
        assumption.
      * destruct (feval h e1_2) eqn:Heqn3;
          inversion H; clear H; subst;
          eauto using eval_app2, vabs.
    + rewrite <- Heqn in *.
      simpl in H.
      destruct (feval h e1_1) eqn:Heqn2.
      * rewrite Heqn in *.
        inversion H.
        eauto using eval_app1.
      * rewrite Heqn in *.
        discriminate.
    + rewrite <- Heqn in *.
      simpl in H.
      destruct (feval h e1_1) eqn:Heqn2.
      * rewrite Heqn in *.
        inversion H.
        eauto using eval_app1.
      * rewrite Heqn in *.
        discriminate.
  - inversion HAS_TYPE; clear HAS_TYPE; subst.
    simpl in H.
    destruct (is_value e1_1) eqn:Heqn1.
    + inversion H; clear H; subst.
      apply eval_let2.
      apply value_iff_is_value.
      assumption.
    + destruct (feval h e1_1) eqn:Heqn2;
        inversion H; clear H; subst;
        eauto using eval_let1.
Qed.

Theorem eval_iff_feval : forall c h e1 e2 t,
  has_type c e1 t ->
  eval h e1 e2 <-> feval h e1 = Some e2.
Proof.
  intros. split.
  - eauto 2 using feval_if_eval.
  - eauto 2 using eval_if_feval.
Qed.