Require Import models.logics.SeparationAlgebra.

Section FirstOrder.
    Context {model : Type}.

    Definition Assertion : Type := model -> Prop.
        
    Definition Conj (P Q : Assertion) : Assertion := fun s => P s /\ Q s.
    Definition Disj (P Q : Assertion) : Assertion := fun s => P s \/ Q s.
    Definition Imply (P Q : Assertion) : Assertion := fun s => P s -> Q s.
    Definition Neg P : Assertion := fun s => ~P s.
    Definition APure (P : Prop) : Assertion := fun _ => P.
    Definition FF : Assertion := fun _ => False.
End FirstOrder.

Delimit Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Assertion.

Notation "P //\\ Q" := (Conj P Q) (at level 40, left associativity) : assertion_scope.
Notation "P \\// Q" := (Disj P Q) (at level 50, left associativity) : assertion_scope.
Notation "P ==>> Q" := (Imply P Q) (at level 55, right associativity) : assertion_scope.
Notation "P <<==>> Q" := (Imply P Q //\\ Imply Q P)%Assertion (at level 60) : assertion_scope.
(* \ulcorner \urcorner *)
Notation "⌜ P ⌝" := (APure P) (at level 35, format "⌜ P ⌝") : assertion_scope.
Notation "!! P" := (Neg P) (at level 35) : assertion_scope.
Notation "⊨ P" := (forall s, P s) (at level 80, no associativity) : assertion_scope.

Section SeparationLogic.
  Context {model : Type}.
  Context {J : Join model}.
  Context {SA : SeparationAlgebra model}.

  Definition sepcon (P Q : Assertion) : Assertion :=
    fun s => exists s1 s2, join s1 s2 s /\ P s1 /\ Q s2.
  Definition emp : Assertion :=
    fun s => unit_element s.
  Definition wand (P Q : Assertion) : Assertion :=
    fun s => forall s1 s2, join s s1 s2 -> P s1 -> Q s2.
End SeparationLogic.

Notation "x * y" := (sepcon x y) (at level 40, left associativity) : assertion_scope.
Notation "x -* y" := (wand x y) (at level 55, right associativity) : assertion_scope.

Section SeparationLogicRules.
  Context {model : Type}.
  Context {J : Join model}.
  Context {SA : SeparationAlgebra model}.

  Open Scope assertion_scope.

  Lemma sepcon_comm_impp : forall x y, ⊨ x * y ==>> y * x.
  Proof.
    intros ? ? ? ?. destruct H as [? [? [? [? ?]]]].
    apply join_comm in H.
    do 2 eexists. eauto.
  Qed.
  
  Lemma sepcon_assoc1: forall x y z, ⊨ x * (y * z) ==>> (x * y) * z.
  Proof.
    intros x y z ? [? [? [? [? [? [? [? [? ?]]]]]]]].
    apply join_comm in H, H1.
    pose proof join_assoc _ _ _ _ _ H1 H as [? [? ?]].
    apply join_comm in H5, H4.
    do 2 eexists; do 2 (split; eauto).
    do 2 eexists. eauto.
  Qed.

  Lemma sepcon_assoc2: forall x y z, ⊨ (x * y) * z ==>> x * (y * z).
  Proof.
    intros. intros [? [? [? [[? [? [? [? ?]]]] ?]]]].
    pose proof join_assoc _ _ _ _ _ H0 H as [? [? ?]].
    do 2 eexists; do 2 (split; eauto).
    do 2 eexists; eauto.
  Qed.

  Lemma sepcon_mono: forall x1 x2 y1 y2, ⊨ x1 ==>> x2 -> ⊨ y1 ==>> y2 -> ⊨ (x1 * y1) ==>> (x2 * y2).
  Proof.
    intros. intros [? [? [? [? ?]]]].
    apply H in H2. apply H0 in H3.
    do 2 eexists; eauto.
  Qed.

  Lemma orp_sepcon_left: forall x y z,
    ⊨ (x \\// y) * z ==>> x * z \\// y * z.
  Proof.
    intros. intros [? [? [? [? ?]]]].
    destruct H0; [left | right];
    do 2 eexists; eauto.
  Qed.

  Lemma orp_sepcon_right: forall x y z,
    ⊨ x * z \\// y * z ==>> (x \\// y) * z.
  Proof.
    intros. intros [[? [? [? [? ?]]]] | [? [? [? [? ?]]]]];
    do 2 eexists; do 2 (split; eauto);
    [left | right]; auto.
  Qed.

  Lemma falsep_sepcon_left: forall x,
    ⊨ FF * x ==>> FF.
  Proof.
    intros. intros [? [? [? [? ?]]]].
    inversion H0.
  Qed.

  Lemma sepcon_emp1: forall x, ⊨ x * emp ==>> x.
  Proof.
    intros. intros [? [? [? [? ?]]]].
    apply join_comm, H1 in H; subst; auto.
  Qed.

  Lemma sepcon_emp2 {UE : SeparationAlgebraUnit model}: forall x, ⊨ x ==>> x * emp.
  Proof.
    intros. intros ?.
    exists s, ue. split.
    - apply unit_join.
    - split; auto. apply unit_spec.
  Qed.

  Lemma wand_sepcon_adjoint: forall x y z, ⊨ x * y ==>> z <-> ⊨ x ==>> (y -* z).
  Proof.
    split; intros.
    - intros ? ? ? ? ?.
      apply H. do 2 eexists; eauto.
    - intros [? [? [? [? ?]]]].
      apply H in H1. eapply H1 in H2; eauto.
  Qed.
    

End SeparationLogicRules.