Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Program.Basics.
Require Import Coq.FSets.FMaps.
Require Import Coq.MSets.MSets.
Require Import Coq.Structures.Equalities.

Module Var := Nat.
Definition var : Set := Var.t.
Module VarSet := MSetAVL.Make Var.
Module VarSetFacts := MSetFacts.Facts VarSet.
Module VarSetProps := MSetProperties.Properties VarSet.

Inductive type : Set :=
| tunit : type
| tfun : type -> type -> type.

Inductive expr : Set :=
| eunit : expr
| evar : var -> expr
| eabs : var -> type -> expr -> expr
| eapp : expr -> expr -> expr.

Fixpoint free_vars (e : expr) : VarSet.t :=
  match e with
  | eunit => VarSet.empty
  | evar y => VarSet.singleton y
  | eabs y _ e => VarSet.remove y (free_vars e)
  | eapp e1 e2 => VarSet.union (free_vars e1) (free_vars e2)
  end.

(* Type system *)

Module Context := FMapWeakList.Make Var.
Module ContextFacts := FMapFacts.Facts Context.
Module ContextProps := FMapFacts.Properties Context.
Definition context := Context.t type.
Definition context_empty : context := Context.empty type.

Inductive has_type : context -> expr -> type -> Prop :=
| has_type_unit : forall c,
    has_type c eunit tunit

| has_type_var : forall c x t,
    Context.find x c = Some t ->
    has_type c (evar x) t

| has_type_abs : forall c x t1 t2 e,
    has_type (Context.add x t1 c) e t2 ->
    has_type c (eabs x t1 e) (tfun t1 t2)

| has_type_app : forall c e1 e2 t1 t2,
    has_type c e1 (tfun t1 t2) ->
    has_type c e2 t1 ->
    has_type c (eapp e1 e2) t2.


(* Small-step semantics *)

Inductive value : expr -> Prop :=
| vunit : value eunit
| vabs : forall x t e, value (eabs x t e).

Fixpoint subst (x : var) (e1 e2 : expr) :=
  match e2 with
  | eunit => eunit
  | evar y => if Var.eqb x y then e1 else e2
  | eabs y t e => eabs y t
      (* Assuming y is not free in e1 *)
      (if Var.eqb x y then e else subst x e1 e)
  | eapp e3 e4 => eapp (subst x e1 e3) (subst x e1 e4)
  end.

Inductive eval : expr -> expr -> Prop :=
| eval_app1 : forall e1 e2 v1, 
    eval e1 v1 ->
    eval (eapp e1 e2) (eapp v1 e2)

| eval_app2 : forall e2 v1 v2, 
    value v1 ->
    eval e2 v2 ->
    eval (eapp v1 e2) (eapp v1 v2)

| eval_beta : forall x t e v2,
    value v2 ->
    eval (eapp (eabs x t e) v2) (subst x v2 e).

Inductive eval_star : expr -> expr -> Prop :=
| eval_star_refl : forall e,
    eval_star e e

| eval_star_step : forall e1 e2 e3,
    eval e1 e2 ->
    eval_star e2 e3 ->
    eval_star e1 e3.


(* Type safety *)

Theorem progress : forall e1 t,
  has_type context_empty e1 t ->
  value e1 \/ exists e2, eval e1 e2.
Proof.
  intros e1 t HAS_TYPE.
  remember context_empty as c eqn:CONTEXT.
  induction HAS_TYPE; subst c.
  - auto using value.
  - rewrite ContextFacts.empty_o in H. inversion H.
  - auto using value.
  - right.
    rename IHHAS_TYPE2 into IH2; specialize (IH2 eq_refl).
    rename IHHAS_TYPE1 into IH1; specialize (IH1 eq_refl).
    destruct IH1 as [IH1 | IH1];
      destruct IH2 as [IH2 | IH2].
    + inversion IH1; subst.
      * inversion HAS_TYPE1.
      * exists (subst x e2 e); auto using eval_beta.
    + inversion IH1; subst.
      * inversion HAS_TYPE1.
      * destruct IH2 as [e3 IH2].
        exists (eapp (eabs x t e) e3); auto using eval_app2.
    + destruct IH1 as [e1' IH1].
      exists (eapp e1' e2); auto using eval_app1.
    + destruct IH1 as [e1' IH1].
      exists (eapp e1' e2); auto using eval_app1.
Qed.

Lemma context_permutation : forall (c1 c2 : context) e t,
  has_type c1 e t ->
  Context.Equal c1 c2 ->
  has_type c2 e t.
Proof.
  intros c1 c2 e t H1.
  generalize dependent c2.
  induction H1; intros c2 H2.
  - apply has_type_unit.
  - apply has_type_var.
    rewrite <- H2.
    assumption.
  - apply has_type_abs.
    apply IHhas_type.
    unfold Context.Equal.
    intros y.
    destruct (Var.eqb x y) eqn:Heqn.
    + rewrite Var.eqb_eq in Heqn.
      repeat (rewrite ContextFacts.add_eq_o; try trivial).
    + rewrite Var.eqb_neq in Heqn.
      repeat (rewrite ContextFacts.add_neq_o; try trivial).
  - apply has_type_app with (t1:=t1); auto.
Qed.

Lemma context_add_add_eq : forall (c : context) x t1 t2,
  Context.Equal
    (Context.add x t1 c) (Context.add x t1 (Context.add x t2 c)).
Proof.
  intros c x t1 t2 y.
  destruct (Var.eqb x y) eqn:Heqn.
  - rewrite Var.eqb_eq in Heqn.
    repeat (rewrite ContextFacts.add_eq_o; try trivial).
  - rewrite Var.eqb_neq in Heqn.
    repeat (rewrite ContextFacts.add_neq_o; try trivial).
Qed.

Lemma context_add_add_neq : forall (c : context) x1 x2 t1 t2,
  x1 <> x2 ->
  Context.Equal
    (Context.add x1 t1 (Context.add x2 t2 c))
    (Context.add x2 t2 (Context.add x1 t1 c)).
Proof.
  intros c x1 x2 t1 t2 H y.
  destruct (Var.eqb x1 y) eqn:Heqn1;
  destruct (Var.eqb x2 y) eqn:Heqn2;
  try rewrite Var.eqb_eq in *;
  try rewrite Var.eqb_neq in *.
  - congruence.
  - rewrite ContextFacts.add_eq_o; try trivial.
    rewrite ContextFacts.add_neq_o; try trivial.
    rewrite ContextFacts.add_eq_o; try trivial.
  - rewrite ContextFacts.add_neq_o; try trivial.
    rewrite ContextFacts.add_eq_o; try trivial.
    rewrite ContextFacts.add_eq_o; try trivial.
  - repeat (rewrite ContextFacts.add_neq_o; try trivial).
Qed.

Lemma context_weakening : forall (c : context) e t t' x,
  has_type c e t ->
  ~ VarSet.In x (free_vars e) ->
  has_type (Context.add x t' c) e t.
Proof.
  intros c e t t' x H1.
  generalize dependent x.
  induction H1; intros ? H2.
  - apply has_type_unit.
  - apply has_type_var.
    rewrite ContextFacts.add_neq_o.
    + assumption.
    + simpl in H2.
      rewrite VarSetFacts.singleton_iff in H2.
      congruence.
  - apply has_type_abs.
    destruct (Var.eqb x0 x) eqn:Heqn.
    + rewrite Var.eqb_eq in Heqn; subst.
      eauto using context_permutation, context_add_add_eq.
    + rewrite Var.eqb_neq in Heqn.
      eapply context_permutation.
      * apply IHhas_type with (x0:=x0).
        intros contra.
        apply H2.
        apply VarSetFacts.remove_2; auto.
      * apply context_add_add_neq.
        assumption.
  - apply has_type_app with (t1:=t1);
      try apply IHhas_type1;
      try apply IHhas_type2;
      intros H3; apply H2; simpl;
      apply VarSet.union_spec;
      auto.
Qed.

Lemma has_type_free_vars_in_context : forall c e t,
  has_type c e t ->
  VarSet.For_all (fun x => Context.mem x c = true) (free_vars e).
Proof.
  intros c e t H.
  induction H; simpl.
  - intros x contra.
    apply VarSetFacts.empty_iff in contra.
    inversion contra.
  - intros y H2.
    apply Context.mem_1.
    apply ContextFacts.in_find_iff.
    apply VarSet.singleton_spec in H2.
    subst.
    rewrite H.
    discriminate.
  - intros y H2.
    unfold VarSet.For_all in *.
    apply VarSet.remove_spec in H2 as [H2 H3].
    specialize (IHhas_type y H2).
    rewrite ContextFacts.add_neq_b in IHhas_type; auto.
  - intros x H2.
    apply VarSet.union_spec in H2 as [H2 | H2]; auto.
Qed.

Lemma has_type_empty_context_free_vars : forall e t,
  has_type context_empty e t ->
  VarSet.Empty (free_vars e).
Proof.
  intros e t H.
  apply has_type_free_vars_in_context in H.
  induction (free_vars e) using VarSetProps.set_induction.
  - assumption.
  - rename t0_1 into s.
    rename t0_2 into s'.
    apply VarSetProps.Add_Equal in H1.
    unfold VarSet.For_all in *.
    specialize (H x).
    rewrite H1 in H.
    specialize (H (VarSetFacts.add_1 s eq_refl)).
    rewrite ContextFacts.empty_a in H.
    discriminate.
Qed.

Lemma context_empty_weakening : forall (c c' : context) e t,
  has_type c e t ->
  (forall x, VarSet.mem x (free_vars e) = true ->
    Context.find x c = Context.find x c') ->
  has_type c' e t.
Proof.
  intros.
  generalize dependent c'.
  induction H; intros.
  - apply has_type_unit.
  - apply has_type_var.
    destruct (VarSet.mem x (free_vars (evar x))) eqn:Heqn.
    + apply H0 in Heqn.
      rewrite <- Heqn.
      assumption.
    + simpl in Heqn.
      apply VarSetFacts.not_mem_iff in Heqn.
      rewrite VarSetFacts.singleton_iff in Heqn.
      congruence.
  - apply has_type_abs.
    apply IHhas_type.
    intros y FREE_VAR.
    destruct (Var.eqb x y) eqn:Heqn.
    + rewrite Var.eqb_eq in Heqn.
      repeat (rewrite ContextFacts.add_eq_o; try assumption).
      reflexivity.
    + rewrite Var.eqb_neq in Heqn.
      repeat (rewrite ContextFacts.add_neq_o; try assumption).
      apply H0.
      simpl.
      rewrite VarSetFacts.remove_neq_b; assumption.
  - apply has_type_app with t1.
    + apply IHhas_type1.
      intros x FREE_VAR.
      apply H1.
      simpl.
      rewrite VarSetFacts.union_b.
      rewrite FREE_VAR.
      reflexivity.
    + apply IHhas_type2.
      intros x FREE_VAR.
      apply H1.
      simpl.
      rewrite VarSetFacts.union_b.
      rewrite FREE_VAR.
      apply orb_true_r.
Qed.

Lemma has_type_subst : forall e1 e2 c x t1 t2 ,
  has_type (Context.add x t2 c) e1 t1 ->
  has_type context_empty e2 t2 ->
  has_type c (subst x e2 e1) t1.
Proof.
  induction e1; intros e2 c x t1 t2 H1 H2; inversion H1; subst.
  - apply has_type_unit.
  - simpl.
    destruct (Var.eqb x v) eqn:Heqn.
    + rewrite Var.eqb_eq in Heqn.
      rewrite ContextFacts.add_eq_o in H3; try assumption.
      inversion H3; subst.
      apply context_empty_weakening with context_empty.
      * assumption.
      * intros x FREE_VAR.
        apply has_type_empty_context_free_vars in H2.
        apply VarSetProps.empty_is_empty_1 in H2.
        rewrite H2 in FREE_VAR.
        rewrite VarSetFacts.empty_b in FREE_VAR.
        inversion FREE_VAR.
    + rewrite Var.eqb_neq in Heqn.
      rewrite ContextFacts.add_neq_o in H3; try assumption.
      apply has_type_var.
      assumption.
  - simpl.
    apply has_type_abs.
    destruct (Var.eqb x v) eqn:Heqn.
    + rewrite Var.eqb_eq in Heqn; subst.
      eauto using
        context_permutation, context_add_add_eq, ContextFacts.Equal_sym.
    + rewrite Var.eqb_neq in Heqn.
      eauto using context_permutation, context_add_add_neq.
  - apply has_type_app with t0; eauto.
Qed.

Theorem preservation : forall e1 e2 t,
  has_type context_empty e1 t ->
  eval e1 e2 ->
  has_type context_empty e2 t.
Proof.
  intros e1 e2 t HAS_TYPE.
  generalize dependent e2.
  remember context_empty as c.
  induction HAS_TYPE; intros e3 EVAL.
  - inversion EVAL.
  - inversion EVAL.
  - inversion EVAL.
  - inversion EVAL; subst.
    + eauto using has_type_app.
    + eauto using has_type_app.
    + clear IHHAS_TYPE1.
      clear IHHAS_TYPE2.
      inversion HAS_TYPE1; subst.
      eapply has_type_subst.
      * eassumption.
      * assumption.
Qed.

Theorem preservation_eval_star : forall e1 e2 t,
  has_type context_empty e1 t ->
  eval_star e1 e2 ->
  has_type context_empty e2 t.
Proof.
  intros e1 e2 t H1 H2.
  induction H2; eauto using preservation.
Qed.

Definition normal_form e := ~ exists e', eval e e'.
Definition stuck e := normal_form e /\ ~ value e.

Theorem soundness : forall e1 e2 t,
  has_type context_empty e1 t ->
  eval_star e1 e2 ->
  ~ stuck e2.
Proof.
  intros e1 e2 t H1 H2.
  unfold not, stuck, normal_form.
  intros [H3 H4].
  assert (H5 := preservation_eval_star e1 e2 t H1 H2).
  destruct (progress _ t H5); auto.
Qed.