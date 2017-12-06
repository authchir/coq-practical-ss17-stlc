Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Program.Basics.
Require Import Coq.FSets.FMaps.
Require Import Coq.MSets.MSets.
Require Import Coq.Structures.Equalities.

Lemma not_None_implies_Some : forall {A : Set} (o : option A),
  o <> None -> exists x, o = Some x.
Proof.
  intros A o H.
  destruct o.
  - exists a. reflexivity.
  - congruence.
Qed.

Module Var := Nat.
Definition var : Set := Var.t.
Module VarSet := MSetAVL.Make Var.
Module VarSetFacts := MSetFacts.Facts VarSet.
Module VarSetProps := MSetProperties.Properties VarSet.

Lemma VarSet_For_all_Empty : forall P s,
  VarSet.Empty s ->
  VarSet.For_all P s.
Proof.
  intros P s H1 x H2.
  apply VarSetProps.empty_is_empty_1 in H1.
  rewrite H1 in H2.
  apply VarSetFacts.empty_iff in H2.
  inversion H2.
Qed.

Lemma VarSet_For_all_union_spec : forall P s s',
  VarSet.For_all P (VarSet.union s s') ->
  VarSet.For_all P s /\ VarSet.For_all P s'.
Proof.
  intros P s s' H.
  induction s using VarSetProps.set_induction; subst.
  - apply VarSetProps.empty_is_empty_1 in H0.
    split.
    + intros x contra.
      rewrite H0 in contra.
      apply VarSetFacts.empty_iff in contra.
      inversion contra.
    + intros x H2.
      specialize (H x).
      apply VarSetFacts.union_3 with (s:=s) in H2.
      auto.
  - split.
    + intros y H2.
      specialize (H y).
      apply VarSetFacts.union_2 with (s':=s') in H2.
      auto.
    + intros y H2.
      unfold VarSet.For_all in H.
      apply VarSetFacts.union_3 with (s:=s2) in H2.
      auto.
Qed.

Inductive type : Set :=
| tunit : type
| tfun : type -> type -> type.

Inductive expr : Set :=
| eunit : expr
| evar : var -> expr
| eabs : var -> type -> expr -> expr
| eapp : expr -> expr -> expr
| elet : var -> expr -> expr -> expr.

Fixpoint free_vars (e : expr) : VarSet.t :=
  match e with
  | eunit => VarSet.empty
  | evar x => VarSet.singleton x
  | eabs x _ e => VarSet.remove x (free_vars e)
  | eapp e1 e2 => VarSet.union (free_vars e1) (free_vars e2)
  | elet x e1 e2 => VarSet.union (free_vars e1) (VarSet.remove x (free_vars e2))
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
    has_type c (eapp e1 e2) t2

| has_type_let : forall c x e1 e2 t1 t2,
    has_type c e1 t1 ->
    has_type (Context.add x t1 c) e2 t2 ->
    has_type c (elet x e1 e2) t2.


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
  | elet y e3 e4 => elet y (subst x e1 e3)
      (* Assuming y is not free in e1 *)
      (if Var.eqb x y then e4 else subst x e1 e4)
  end.

Module Heap := FMapWeakList.Make Var.
Module HeapFacts := FMapFacts.Facts Heap.
Module HeapProps := FMapFacts.Properties Heap.
Definition heap := Heap.t expr.
Definition heap_empty : heap := Heap.empty expr.

Inductive eval : heap -> expr -> expr -> Prop :=
| eval_var : forall h x e,
    Heap.find x h = Some e->
    eval h (evar x) e

| eval_app1 : forall h e1 e2 v1, 
    eval h e1 v1 ->
    eval h (eapp e1 e2) (eapp v1 e2)

| eval_app2 : forall h e2 v1 v2, 
    value v1 ->
    eval h e2 v2 ->
    eval h (eapp v1 e2) (eapp v1 v2)

| eval_beta : forall h x t e v2,
    value v2 ->
    eval h (eapp (eabs x t e) v2) (subst x v2 e)

| eval_let1 : forall h x e1 e2 e3,
    eval h e1 e3 ->
    eval h (elet x e1 e2) (elet x e3 e2)

| eval_let2 : forall h x v1 e2,
    value v1 ->
    eval h (elet x v1 e2) (subst x v1 e2).

Inductive eval_star : heap -> expr -> expr -> Prop :=
| eval_star_refl : forall h e,
    eval_star h e e

| eval_star_step : forall h e1 e2 e3,
    eval h e1 e2 ->
    eval_star h e2 e3 ->
    eval_star h e1 e3.


(* Type safety *)

Lemma VarSet_For_all_remove : forall x (h : heap) s e,
  VarSet.For_all (fun y => Heap.In y h) (VarSet.remove x s) ->
  VarSet.For_all (fun y => Heap.In y (Heap.add x e h)) s.
Proof.
  intros x h s e H1 z H2.
  destruct (Var.eqb x z) eqn:Heqn.
  - apply Var.eqb_eq in Heqn; subst.
    apply HeapFacts.add_in_iff.
    auto.
  - apply Var.eqb_neq in Heqn.
    specialize (H1 z).
    simpl in H1.
    apply VarSetFacts.remove_2 with (x:=x) in H2; try assumption.
    apply HeapFacts.add_in_iff.
    auto.
Qed.

Lemma progress0 : forall c e1 t (h : heap),
  has_type c e1 t ->
  VarSet.For_all (fun x => Heap.In x h) (free_vars e1) ->
  value e1 \/ exists e2, eval h e1 e2.
Proof.
  intros c e1 t h HAS_TYPE.
  generalize dependent h.
  induction HAS_TYPE; intros h HH.
  - auto using vunit.
  - right.
    unfold VarSet.For_all in HH.
    specialize (HH x (VarSetFacts.singleton_2 eq_refl)).
    apply HeapFacts.in_find_iff in HH.
    apply not_None_implies_Some in HH as [e3 HH].
    exists e3.
    auto using eval_var.
  - auto using vabs.
  - right.
    simpl in HH.
    apply VarSet_For_all_union_spec in HH as [H1 H2].
    specialize (IHHAS_TYPE1 _ H1) as [IH1 | [e3 IH1]]; clear H1.
    + specialize (IHHAS_TYPE2 _ H2) as [IH2 | [e4 IH2]]; clear H2.
      * destruct e1; inversion HAS_TYPE1; inversion IH1; subst.
        exists (subst v e2 e1). auto using eval_beta.
      * exists (eapp e1 e4). auto using eval_app2.
    + exists (eapp e3 e2). auto using eval_app1.
  - right.
    simpl in HH.
    apply VarSet_For_all_union_spec in HH as [H1 H2].
    specialize (IHHAS_TYPE1 h H1) as [IH1 | [e3 IH1]]; clear H1.
    + apply VarSet_For_all_remove with (e:=e1) in H2.
      exists (subst x e1 e2). auto using eval_let2.
    + exists (elet x e3 e2). auto using eval_let1.
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
  - intros y H1.
    apply VarSet.union_spec in H1 as [H1 | H1].
    + auto.
    + apply VarSet.remove_spec in H1 as [H1 H2].
      apply IHhas_type2 in H1.
      apply not_eq_sym in H2.
      rewrite ContextFacts.add_neq_b in H1; assumption.
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

Theorem progress : forall e1 t,
  has_type context_empty e1 t ->
  value e1 \/ exists e2, eval heap_empty e1 e2.
Proof.
  intros e1 t HAS_TYPE.
  apply progress0 with (c:=context_empty) (t:=t).
  - assumption.
  - apply has_type_empty_context_free_vars in HAS_TYPE.
    apply VarSet_For_all_Empty.
    assumption.
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
  - (* Why does rewriting not work here but works a few steps later? *)
    (* rewrite <- H2. *)
    apply has_type_let with (t1:=t1); auto.
    apply IHhas_type2.
    rewrite H2.
    apply ContextFacts.Equal_refl.
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

Lemma context_empty_weakening : forall (c c' : context) e t,
  has_type c e t ->
  VarSet.For_all (fun x => Context.find x c = Context.find x c')
    (free_vars e) ->
  has_type c' e t.
Proof.
  intros c c' e t H1.
  generalize dependent c'.
  induction H1; intros c' H2.
  - apply has_type_unit.
  - apply has_type_var.
    unfold VarSet.For_all in H2.
    specialize (H2 _ (VarSetFacts.singleton_2 eq_refl)).
    rewrite <- H2.
    assumption.
  - apply has_type_abs.
    apply IHhas_type.
    intros y FREE_VAR.
    simpl in H2.
    destruct (Var.eqb x y) eqn:Heqn.
    + apply Var.eqb_eq in Heqn.
      repeat (rewrite ContextFacts.add_eq_o; try assumption).
      reflexivity.
    + apply Var.eqb_neq in Heqn.
      repeat (rewrite ContextFacts.add_neq_o; try assumption).
      auto using VarSetFacts.remove_2.
  - apply has_type_app with t1.
    + apply IHhas_type1.
      intros x FREE_VAR.
      simpl in H2.
      auto using VarSetFacts.union_2.
    + apply IHhas_type2.
      intros x FREE_VAR.
      simpl in H2.
      auto using VarSetFacts.union_3.
  - eapply has_type_let with t1.
    + apply IHhas_type1.
      intros y FREE_VAR.
      simpl in H2.
      auto using VarSetFacts.union_2.
    + apply IHhas_type2.
      intros y FREE_VAR.
      destruct (Var.eqb x y) eqn:Heqn.
      * apply Var.eqb_eq in Heqn.
        repeat rewrite ContextFacts.add_eq_o; trivial.
      * apply Var.eqb_neq in Heqn.
        repeat rewrite ContextFacts.add_neq_o; trivial.
        simpl in H2.
        auto using VarSetFacts.union_3, VarSetFacts.remove_2.
Qed.

Lemma has_type_subst : forall e1 e2 c x t1 t2 ,
  has_type (Context.add x t2 c) e1 t1 ->
  has_type context_empty e2 t2 ->
  has_type c (subst x e2 e1) t1.
Proof.
  induction e1; intros e2 c x t1 t2 H1 H2; inversion H1; clear H1; subst.
  - apply has_type_unit.
  - simpl.
    destruct (Var.eqb x v) eqn:Heqn.
    + rewrite Var.eqb_eq in Heqn.
      rewrite ContextFacts.add_eq_o in H3; try assumption.
      inversion H3; subst.
      eauto using
        context_empty_weakening,
        VarSet_For_all_Empty,
        has_type_empty_context_free_vars.
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
      eapply IHe1.
      * eauto using context_permutation, context_add_add_neq.
      * assumption.
  - apply has_type_app with t0; eauto.
  - simpl.
    apply has_type_let with t0.
    + eauto.
    + destruct (x =? v) eqn:Heqn.
      * rewrite Var.eqb_eq in Heqn; subst.
        eauto using
          context_permutation, context_add_add_eq, ContextFacts.Equal_sym.
      * rewrite Var.eqb_neq in Heqn.
        eauto using context_permutation, context_add_add_neq, not_eq_sym.
Qed.

Theorem preservation : forall e1 e2 t,
  has_type context_empty e1 t ->
  eval heap_empty e1 e2 ->
  has_type context_empty e2 t.
Proof.
  intros e1.
  induction e1; intros e2 ty HAS_TYPE EVAL.
  - inversion EVAL.
  - inversion EVAL; clear EVAL; subst.
    inversion H1.
  - inversion EVAL.
  - inversion HAS_TYPE; clear HAS_TYPE; subst.
    inversion EVAL; clear EVAL; subst.
    + apply has_type_app with t1.
      * eauto.
      * eauto.
    + apply has_type_app with t1.
      * eauto.
      * eauto.
    + inversion H2; clear H2; subst.
      eauto using has_type_subst, has_type_empty_context_free_vars.
  - inversion HAS_TYPE; clear HAS_TYPE; subst.
    inversion EVAL; clear EVAL; subst.
    + apply has_type_let with t1.
      * eauto.
      * eauto.
    + eauto using has_type_subst, has_type_empty_context_free_vars.
Qed.

Theorem preservation_eval_star : forall e1 e2 t,
  has_type context_empty e1 t ->
  eval_star heap_empty e1 e2 ->
  has_type context_empty e2 t.
Proof.
  intros e1 e2 t H1 H2.
  remember heap_empty as h.
  induction H2; subst; eauto using preservation.
Qed.

Definition normal_form h e := ~ exists e', eval h e e'.
Definition stuck h e := normal_form h e /\ ~ value e.

Theorem soundness : forall e1 e2 t,
  has_type context_empty e1 t ->
  eval_star heap_empty e1 e2 ->
  ~ stuck heap_empty e2.
Proof.
  intros e1 e2 t H1 H2.
  unfold not, stuck, normal_form.
  intros [H3 H4].
  assert (H5 := preservation_eval_star e1 e2 t H1 H2).
  destruct (progress _ t H5); auto.
Qed.