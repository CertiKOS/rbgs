Require Import coqrel.LogicalRelations.
Require Import FunctionalExtensionality.
Require Import IntmDef.
Require Import IntmTactics.

Local Obligation Tactic := cbn; eauto.

Module Intm.
  Import IntmDef.Intm.
  Import IntmTactics.Intm.

  Section REPEAT.
    Context {M N A} (f : A -> t M N A).

    Fixpoint pow n a :=
      match n with O => ret a | S n => f a >>= pow n end.

    Definition star a :=
      sup (fun n => pow n a).

    Lemma pow_rotate n a :
      (pow n a >>= f) = (f a >>= pow n).
    Proof.
      revert a; induction n; intros; cbn; monad.
      f_equal. eauto using functional_extensionality.
    Qed.

    Lemma star_rotate a :
      (star a >>= f) = (f a >>= star).
    Proof.
      unfold star. mnorm.
      f_equal. apply functional_extensionality. intro n.
      apply pow_rotate.
    Qed.

    Lemma pow_plus n p a :
      pow (n + p) a = pow n a >>= pow p.
    Proof.
      revert a.
      induction n; cbn; intros.
      - mnorm. auto.
      - apply functional_extensionality in IHn.
        rewrite IHn. clear.
        rewrite <- !bind_bind. f_equal.
    Qed.

    Lemma star_unfold_l a :
      star a = join (ret a) (f a >>= star).
    Proof.
      apply antisymmetry.
      - apply sup_lub.
        intros [ | n].
        + apply join_ub_l.
        + etransitivity; [ | apply join_ub_r].
          unfold star. rewrite bind_sum by repeat constructor. cbn.
          apply (sup_ub (fun n => f a >>= pow n) n).
      - apply join_lub.
        + change (ret a) with ((fun i => pow i a) O). eapply sup_ub.
        + unfold star. rewrite bind_sum by repeat constructor. cbn.
          eapply sup_lub. intros i.
          eapply sup_at with (S i).
          reflexivity.
    Qed.

    Lemma star_unfold_r a :
      star a = join (ret a) (star a >>= f).
    Proof.
      rewrite star_rotate.
      apply star_unfold_l.
    Qed.

    Lemma star_ind_l {B} (g h : A -> t M N B) :
      (forall a, ref (f a >>= h) (h a)) ->
      (forall a, ref (g a) (h a)) ->
      (forall a, ref (star a >>= g) (h a)).
    Proof.
      intros Hf Hg a.
      setoid_rewrite bind_sup.
      eapply sup_lub. intro n.
      revert a.
      induction n; intro a; cbn.
      - mnorm. auto.
      - mnorm. setoid_rewrite IHn. auto.
    Qed.

    Lemma star_ind_r (x : t M N A) :
      ref (x >>= f) x ->
      ref (x >>= star) x.
    Proof.
      intros H.
      setoid_rewrite bind_sum; [ | repeat constructor].
      eapply sup_lub. intro n.
      induction n; cbn.
      - mnorm. reflexivity.
      - setoid_rewrite <- pow_rotate.
        rewrite <- bind_bind.
        rewrite IHn. auto.
    Qed.

    CoInductive diverges (a : A) : Prop :=
      | diverges_val a' :
          has (f a) (val a') ->
          diverges a' ->
          diverges a.
(*
      | diverges_undef :
          has (f a) undef ->
          diverges a.
*)
  End REPEAT.

  Program Definition divs {M N P Q A B} (f : A -> t M N A) (a : A) : t P Q B :=
    {|
      has t := t = div /\ diverges f a
    |}.
  Next Obligation.
    intros M N P Q A B f a s t [Ht Ha] Hst; subst.
    inversion Hst. auto.
  Qed.

  Lemma divs_bind {M N P Q A B} (f : A -> t M N A) (g : A -> t P Q B) (a : A) :
    divs f a >>= g = divs f a.
  Proof.
    apply antisymmetry.
    - intros t (s & [Hs Ha] & Hst). subst.
      inversion Hst; clear Hst; subst.
      constructor; auto.
    - intros t [Ht H]. subst.
      exists div. split; constructor; auto.
  Qed.

  Hint Rewrite @divs_bind : monad.

  Definition omega {M N A B} (f : A -> t M N A) (a : A) : t M N B :=
    star f a >>= divs f.

  Definition repeat {M N A} (f : A -> t M N A) (a : A) : t M N A :=
    star f a >>= fun a' => (ret a' \/ divs f a')%beh.

  Lemma repeat_unfold_l {M N A} (f : A -> t M N A) (a : A) :
    repeat f a = (ret a \/ divs f a \/ (f a >>= repeat f))%beh.
  Proof.
    unfold repeat. rewrite star_unfold_l. monad.
    rewrite bind_plus. monad.
  Qed.

  Lemma repeat_ind_l {M N A B} (f : A -> t M N A) (g h : A -> t M N B) :
    (forall a, ref (f a >>= h) (h a)) ->
    (forall a, ref (g a) (h a)) ->
    (forall a, ref (divs f a) (h a)) ->
    (forall a, ref (repeat f a >>= g) (h a)).
  Proof.
    intros Hf Hg Hd.
    unfold repeat.
    setoid_rewrite bind_bind.
    apply star_ind_l; monad.
  Qed.

  Global Instance pow_r :
    Monotonic
      (@pow)
      (forallr - @ M, forallr - @ N, forallr R,
        (R ++> r M N R) ++> - ==> R ++> r M N R) | 10.
  Proof.
    intros M N A B R f g Hfg n.
    induction n; simpl; intros; repeat rstep; eauto.
  Qed.

  Global Instance pow_ref :
    Monotonic
      (@pow)
      (forallr - @ M, forallr - @ N, forallr - @ A,
        (- ==> ref) ++> - ==> - ==> ref).
  Proof.
    rauto.
  Qed.

  Global Instance star_r :
    Monotonic
      (@star)
      (forallr -, forallr -, forallr R, (R ++> r _ _ R) ++> R ++> r _ _ R) | 10.
  Proof.
    intros M N A B R f g Hfg a b Hab.
    unfold star.
  Admitted.

  Global Instance star_ref :
    Monotonic
      (@star)
      (forallr -, forallr -, forallr -, (- ==> ref) ++> - ==> ref).
  Proof.
    rauto.
  Qed.

  Global Instance diverges_r :
    Monotonic
      (@diverges)
      (forallr - @ M, forallr - @ N, forallr R, (R ++> r M N R) ++> R ++> impl).
  Proof.
    intros M N A B R f g Hfg. cofix IH. intros a b Hab H.
    destruct H as [a' Ha' H].
    edestruct Hfg as (s & Hs & Has); eauto.
    inversion Has; clear Has; subst.
    - eapply diverges_val; eauto. eapply IH; eauto.
    - cofix IHb. exists b; eauto using closed.
  Qed.

  Global Instance divs_r :
    Monotonic
      (@divs)
      (forallr -, forallr -, forallr -, forallr -, forallr R, forallr S,
         (R ++> r _ _ R) ++> R ++> r _ _ S) | 10.
  Proof.
    intros M N P Q A1 A2 R B1 B2 S f g Hfg x y Hxy u (Hu & Ha). subst.
    exists div. cbn. intuition auto.
    eapply diverges_r; eauto.
  Qed.

  Global Instance divs_ref :
    Monotonic
      (@divs)
      (forallr -, forallr -, forallr -, forallr -, forallr -, forallr -,
         (- ==> ref) ++> eq ==> ref).
  Proof.
    rauto.
  Qed.

  Global Instance repeat_r :
    Monotonic
      (@repeat)
      (forallr -@M, forallr -@N, forallr R, (R ++> r M N R) ++> R ++> r M N R) | 10.
  Proof.
    intros M N A B R f g Hfg x y Hxy.
    unfold repeat. repeat rstep.
  Admitted.

  Global Instance repeat_ref :
    Monotonic
      (@repeat)
      (forallr -, forallr -, forallr -, (- ==> ref) ++> - ==> ref).
  Proof.
    rauto.
  Qed.

End Intm.

Notation "x '^*'" := (Intm.star x) (at level 30) : behavior_scope.
Notation "x '^ω'" := (Intm.omega x) (at level 30) : behavior_scope.
Notation "x '^∞'" := (Intm.repeat x) (at level 30) : behavior_scope.
