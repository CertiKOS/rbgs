Require Import coqrel.LogicalRelations.
Require Import FunctionalExtensionality.
Require Import List.
Require Import IntmDef.
Require Import IntmTactics.
Require Import IntmIter.
Require Import IntmDecomp.

Local Obligation Tactic := cbn; eauto.

Module Intm.
  Import IntmDef.Intm.
  Import IntmTactics.Intm.
  Import IntmIter.Intm.
  Import IntmDecomp.Intm.
  Local Open Scope behavior_scope.

  (** *** Substitution *)

  Definition subst_step {M N P Q A} (f : M -> t P Q N) (x : t M N A) :=
    mu x >>= fun m => f m >>= fun n => ret (delta x m n).

  Definition subst {M N P Q A} (f : M -> t P Q N) (x : t M N A) :=
    repeat (subst_step f) x >>= fun y => rho y.

  (** *** Resolution *)

  Definition uncons {M N A} (x : list A) : t M N (A * list A) :=
    choose (fun '(a, y) => a::y = x).

  Definition unnil {M N A} (x : list A) : t M N unit :=
    choose (fun 'tt => nil = x).

  Definition res_step {M N} (f : M -> t M N N) '(s, k) : t M N _ :=
    (mu s >>= fun m => interact m >>= fun n => ret (delta s m n, k)) \/
    (mu s >>= fun m => ret (f m, (fun n => delta s m n) :: k)) \/
    (rho s >>= fun n => uncons k >>= fun '(k0, k') => ret (k0 n, k')).

  Definition res {M N} (f : M -> t M N N) (m : M) :=
    repeat (res_step f) (interact m, nil) >>=
      fun '(s, k) => unnil k >>= fun _ => rho s.

  (** *** Properties *)

  Global Instance uncons_r :
    Monotonic
      (@uncons)
      (forallr - @ M, forallr - @ N, forallr R,
       list_rel R ++> r M N (R * list_rel R)).
  Proof.
    unfold uncons. repeat rstep.
    intros [a la] Ha. subst. inversion H; clear H; subst.
    eexists (_, _). split; rauto.
  Qed.

  Global Instance unnil_r :
    Monotonic
      (@unnil)
      (forallr - @ M, forallr - @ N, forallr R,
       list_rel R ++> ref).
  Proof.
    unfold unnil. repeat rstep.
    intros Ha. subst. inversion H; clear H; subst. auto.
  Qed.

  Global Instance res_step_ref :
    Monotonic
      (@res_step)
      (forallr - @ M, forallr - @ N, (- ==> ref) ++>
       ref * list_rel (- ==> ref) ++> r M N (ref * list_rel (- ==> ref))).
  Proof.
    unfold res_step. repeat rstep.
    - subst. reflexivity.
    - rauto.
  Qed.

  Global Instance res_ref :
    Monotonic
      (@res)
      (forallr -, forallr -, (eq ==> ref) ++> eq ==> ref).
  Proof.
    intros M N f g Hfg. rewrite ref_r in *.
    unfold res.
    rstep. subst.
    eapply bind_r.
    - instantiate (1 := (@ref M N N * list_rel (- ==> @ref M N N))%rel). rauto.
    - rauto.
  Qed.

  Lemma eta {A B} (f : A -> B) :
    (fun a => f a) = f.
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite @eta : monad.

  Lemma divs_flat {M N P Q A B} f :
    @divs M N P Q A B f = @divs M N P Q A B (fun a => nu (f a)).
  Proof.
    apply functional_extensionality. intro a.
    apply antisymmetry.
    - intros t [Ht Ha]. subst. split; auto. clear - Ha.
      revert a Ha. cofix IH.
      intros a [a' Ha' ?].
      eapply diverges_val; cbn; eauto.
    - intros t [Ht Ha]. subst. split; auto. clear - Ha.
      revert a Ha. cofix IH.
      intros a [a' Ha' ?].
      cbn in Ha'. destruct Ha' as [(v & Hfav & Hv) | Hu].
      + inversion Hv; clear Hv; subst. eapply diverges_val; cbn; eauto.
      + cofix IHa. exists a; eauto using closed.
  Qed.

  Global Instance bind_eq_proper {M N A B} :
    Proper
      (pointwise_relation A eq ==> eq ==> eq)
      (@bind M N A B).
  Proof.
    red. repeat rstep. subst. f_equal. eapply functional_extensionality; auto.
  Qed.

  Global Instance subrelation_eq_pointwise A B :
    subrelation (@eq (A -> B)) (pointwise_relation A eq).
  Proof.
    apply eq_subrelation. typeclasses eauto.
  Qed.

  Lemma subst_interact {M N A} (x : t M N A) :
    subst interact x = x.
  Proof.
    eapply antisymmetry.
    - unfold subst.
      change x with ((fun x => x) x) at 2. revert x.
      apply repeat_ind_l; intros.
      + unfold subst_step.
        rewrite (decompose a) at 2.
        monad.
      + monad.
      + unfold subst_step.
        rewrite divs_flat. mnorm.
        intros t Ht. destruct Ht as [Ht Hd]. subst.
        destruct Hd; cbn in *; eauto using closed.
    - intros t Ht. unfold subst, repeat.
      rewrite bind_bind. revert x Ht.
      induction t; intros; cbn.
      + exists (val x). split; eauto 20. exists 0; auto.
      + exists (val x). split; eauto 20. exists 0; auto.
      + exists (val x). split; eauto 20. exists 0; auto.
      + exists (move m). split; eauto 20. exists 1; eauto 20.
      + specialize (IHt (delta x m n)). simpl in IHt.
        destruct IHt as (s & (k & Hs) & Hst); auto.
        exists (tcons m n s). split; eauto.
        exists (S k). cbn [pow].
        exists (tcons m n (val (delta x m n))). split; eauto 10.
        exists (val m). eauto 20 using closed.
  Qed.

  Lemma div_subst_step_ret {K L M N P Q A B} (f : M -> t P Q N) (a : A) :
    divs (subst_step f) (ret a) = @bot K L B.
  Proof.
    apply antisymmetry; auto using bot_ref.
    intros t [Ht H]. subst. exfalso.
    destruct H as [a' Ha' H].
    cbn in Ha'. clear H. firstorder congruence.
  Qed.

  Lemma div_subst_step_interact {K L M N P Q B} (f : M -> t P Q N) m :
    ref (divs (subst_step f) (interact m)) (@phi _ _ K L _ B (f m)).
  Proof.
    intros t [Ht H]. subst. cbn.
    destruct H as [a' Ha' H].
    revert Ha'. unfold subst_step. repeat mnorm. cbn.
    intros (s & Hs & Hsa').
    inversion Hsa'; clear Hsa'; subst; auto.
    cbn in *. inversion H0; clear H0; subst.
    assert (has (divs (subst_step f) (ret a)) (@div M N B)) by (cbn; eauto).
    rewrite div_subst_step_ret in H0. elim H0.
  Qed.

  Lemma subst_step_ret {M N P Q A} (f : M -> t P Q N) (a : A) :
    repeat (subst_step f) (ret a) = ret (ret a).
  Proof.
    rewrite repeat_unfold_l.
    rewrite div_subst_step_ret.
    unfold subst_step at 2.
    monad.
  Qed.

  Hint Rewrite @subst_step_ret : monad.

  Lemma pow_star {M N A} (n : nat) (f : A -> t M N A) (a : A) :
    ref (pow f n a) (star f a).
  Proof.
    firstorder.
  Qed.

  Hint Resolve pow_star : monad.

  Lemma interact_subst {M N P Q} (f : M -> t P Q N) (m : M) :
    subst f (interact m) = f m.
  Proof.
    apply antisymmetry.
    - unfold subst.
      rewrite repeat_unfold_l.
      rewrite !bind_join.
      repeat apply join_lub.
      + monad.
      + rewrite div_subst_step_interact. monad.
      + unfold subst_step at 2. monad.
    - unfold subst, repeat.
      rewrite <- (pow_star 1). cbn.
      unfold subst_step. monad.
  Qed.

End Intm.
