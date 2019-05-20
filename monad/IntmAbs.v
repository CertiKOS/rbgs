Require Import coqrel.LogicalRelations.
Require Import coqrel.KLR.
Require Import IntmDef.
Require Import IntmTactics.
Require Import IntmDecomp.

Local Obligation Tactic := cbn; eauto.

Module Intm.
  Import IntmDef.Intm.
  Import IntmTactics.Intm.
  Import IntmDecomp.Intm.

  (** ** Abstraction (trace relation) *)

  Section ABS.
    Context {Ma Mc Na Nc Xa Xc} (gamma : rel (trace Ma Na Xa) (trace Mc Nc Xc)).

    Program Definition abs (x : t Mc Nc Xc) : t Ma Na Xa :=
      {|
        has t := forall ta tc, gamma ta tc -> prefix ta t -> has x tc
      |}.
    Next Obligation.
      intros y s t Ht Hst ta tc Htac Hsta.
      eapply Ht; eauto. etransitivity; eauto.
    Qed.

    Program Definition concr (y : t Ma Na Xa) : t Mc Nc Xc :=
      {|
        has t := exists ta tc, gamma ta tc /\ prefix t tc /\ has y ta;
      |}.
    Next Obligation.
      intros x s t (ta & tc & Htac & Ht & Hta) Hst.
      exists ta, tc. intuition auto. etransitivity; eauto.
    Qed.

    Lemma abs_concr_galois x y :
      ref (concr x) y <-> ref x (abs y).
    Proof.
      split.
      - intros Hxy t Ht ta tc Htac Htat.
        eapply Hxy.
        exists ta, tc. intuition eauto using closed. reflexivity.
      - intros Hxy t (ta & tc & Htac & Ht & Hta).
        rewrite Ht.
        eapply Hxy; eauto. reflexivity.
    Qed.

    Instance concr_ref :
      Monotonic concr (ref ++> ref).
    Proof.
      intros x y Hxy.
      apply abs_concr_galois.
      transitivity y; auto.
      apply abs_concr_galois.
      reflexivity.
    Qed.

    Lemma concr_join x y :
      concr (join x y) = join (concr x) (concr y).
    Proof.
      apply antisymmetry.
      - apply abs_concr_galois; apply join_lub; apply abs_concr_galois.
        + apply join_ub_l.
        + apply join_ub_r.
      - apply join_lub; rstep.
        + apply join_ub_l.
        + apply join_ub_r.
    Qed.
  End ABS.

  (** ** Abstraction (KLR) *)

  Lemma has_ret {M N A} (x : t M N A) (a : A) :
    has x (val a) -> ref (ret a) x.
  Proof.
    intros Ha t [ ]. auto.
  Qed.

  Section SIM.
    Context {W : Type}.
    Context {M1 M2} (RM : klr W M1 M2).
    Context {N1 N2} (RN : klr W N1 N2).
    Context {A B} (R : rel A B).

    Inductive pull_has (x2 : t M2 N2 B) : trace M1 N1 A -> Prop :=
      | pull_val a b :
          has x2 (val b) ->
          R a b ->
          pull_has x2 (val a)
      | pull_div :
          has x2 div ->
          pull_has x2 div
      | pull_undef t :
          has x2 undef ->
          pull_has x2 t
      | pull_move w m1 m2 :
          has x2 (move m2) ->
          RM w m1 m2 ->
          pull_has x2 (move m1)
      | pull_tcons w m1 m2 n1 t1 :
          has x2 (move m2) ->
          RM w m1 m2 ->
          (forall n2, RN w n1 n2 -> pull_has (delta x2 m2 n2) t1) ->
          pull_has x2 (tcons m1 n1 t1).

    Lemma pull_has_undef_inv y t :
      pull_has y undef -> has y t.
    Proof.
      inversion 1; eauto using closed.
    Qed.

    Hint Constructors pull_has.
    Hint Resolve pull_has_undef_inv.

    Program Definition pull (x2 : t M2 N2 B) :=
      {| has := pull_has x2 |}.
    Next Obligation.
      intros x2 s t Ht Hst. revert s Hst.
      induction Ht; intros; eauto;
      inversion Hst; clear Hst; subst; eauto.
    Qed.

    Global Instance pull_ref :
      Monotonic (@pull) (ref ++> ref).
    Proof.
      intros x y Hxy t Ht.
      revert y Hxy. cbn in *.
      induction Ht; intros; eauto.
      eapply pull_tcons; eauto.
      intros n2 Hn.
      eapply H2; eauto.
      eapply delta_ref; eauto.
    Qed.

    Lemma join_pull x y:
      ref (join (pull x) (pull y)) (pull (join x y)).
    Proof.
      eapply join_lub; rstep; auto using join_ub_l, join_ub_r.
    Qed.

    Lemma sup_pull {I} (x : I -> _) :
      ref (sup (fun i => pull (x i))) (pull (sup x)).
    Proof.
      eapply sup_lub; intro; rstep; auto using sup_ub.
    Qed.

    Lemma pull_top :
      pull top = top.
    Proof.
      apply antisymmetry; auto using top_ref.
      intros t _. simpl.
      apply pull_undef. firstorder.
    Qed.

    (*
      It would be satisfying to have a Galois adjoint for pull,
      but it's not clear to me how to define it at the moment.
      It's also possible that the asymmetry in non-determinism
      (we have P non-det but not O) prevents this. One step
      to ascertain this would be to try to show that pull
      preserves joins (which seems plausible), in which case
      an adjoint exists and can be defined implicitely.
      It would also be interesting thing to consider the behavior
      of pull(R^-1).

    Inductive push_has w (x1 : t M1 N1 A) : trace M2 N2 B -> Prop :=
      | push_val b :
          (forall a, R w a b -> has x1 (val a)) ->
          push_has w x1 (val b)
      | push_div :
          has x1 div ->
          push_has w x1 div
      | push_undef t :
          has x1 undef ->
          push_has w x1 t
      | push_move m2 :
          (forall w' m1, w ~> w' -> RM w' m1 m2 -> has x1 (move m1)) ->
          push_has w x1 (move m2)
      | push_tcons m2 n2 t2 :
          (forall w' m1, w  ~> w' -> RM w' m1 m2 ->
           has x1 (move m1) /\
           exists w'' n1, w' ~> w'' /\ RN w'' n1 n2 /\
           push_has w'' (delta x1 m1 n1) t2) ->
          push_has w x1 (tcons m2 n2 t2).

    Fixpoint push_has w (x1 : t M1 N1 A) (t2 : trace M2 N2 B) : Prop :=
      has x1 undef \/
      match t2 with
        | val b => forall a, R w a b -> has x1 (val a)
        | div => has x1 div
        | undef => False
        | move m2 =>
          forall w' m1, w ~> w' -> RM w' m1 m2 -> has x1 (move m1)
        | tcons m2 n2 t2 =>
          forall w' m1, w ~> w' -> RM w' m1 m2 -> has x1 (move m1) /\
          exists w'' n1, w ~> w'' /\ RN w'' n1 n2 /\ push_has w (delta x1 m1 n1) t2
      end.

    Lemma push_undef_has w x1 t2 :
      has x1 undef -> push_has w x1 t2.
    Proof.
      destruct t2; left; eauto.
    Qed.

    Hint Resolve push_undef_has.

    Program Definition push w (x1 : t M1 N1 A) :=
      {| has := push_has w x1 |}.
    Next Obligation.
      intros w x1 s t Ht Hst. revert x1 Ht.
      induction Hst; intros; eauto;
      destruct Ht as [? | Ht]; eauto.
      - destruct Ht.
      - right. intros.
        edestruct Ht as (Hm1 & w'' & n1 & Hw'' & Hn & Ht'); eauto 10.
      - right. intros.
        edestruct Ht as (Hm1 & _); eauto.
    Qed.

    Lemma pull_meet w x2 y2 :
      pull w (meet x2 y2) = meet (pull w x2) (pull w y2).
    Proof.
      apply antisymmetry.
      - apply meet_glb; rstep; auto using meet_lb_l, meet_lb_r.
      - intros t [Hxt Hyt]. cbn in Hxt, Hyt |- *.
        induction Hxt; inversion Hyt; clear Hyt; subst;
          try solve [eauto].
        eapply pull_val; simpl; eauto.


    Lemma pull_join w x2 y2 :
      pull w (join x2 y2) = join (pull w x2) (pull w y2).
    Proof.
      apply antisymmetry.
      - remember (join x2 y2) as z2.
        intros t Ht. cbn in Ht |- *. revert x2 y2 Heqz2.
        induction Ht; intros; subst; try solve [destruct H; eauto].
        destruct H as [H|H].
        + left. eapply pull_tcons; eauto.
          setoid_rewrite delta_join in H2. cbn in H2.
          intros. change (has (pull w'' (delta x0 m2 n2)) t1).
          erewrite join_ub_l.
        + subst x2. destruct H; eauto.
          *)

    Definition sim : rel (t M1 N1 A) (t M2 N2 B) :=
      fun x y => ref x (pull y).

    Lemma pull_ret b :
      pull (ret b) = choose (fun a => R a b).
    Proof.
      apply antisymmetry.
      - inversion 1; clear H; subst; inversion H0; clear H0; subst; eauto.
      - intros t (a & Ha & Ht); subst; eauto.
    Qed.
  End SIM.

  Global Instance pull_ref_params :
    Params (@pull) 1.

  Lemma pull_eq {M N A} (x : t M N A) :
    pull (W:=unit) (k eq) (k eq) eq x = x.
  Proof.
    apply antisymmetry.
    - intros t Ht. cbn in Ht.
      induction Ht; unfold k in *; subst; cbn in *; eauto using closed.
    - intros t. revert x.
      induction t; intros; unfold k in *; try solve [ econstructor; eauto ].
      + apply pull_move with tt m; cbn; auto.
      + apply pull_tcons with tt m; cbn; eauto using closed.
        intros; subst.
        apply IHt. cbn. auto.
  Qed.

    Hint Constructors pull_has.
    Hint Resolve pull_has_undef_inv.

  Lemma sim_r M N {A B} (R : rel A B) :
    eqrel (sim (W:=unit) (k eq) (k eq) R) (r M N R).
  Proof.
    split.
    - intros x y Hxy t Ht.
      apply Hxy in Ht; clear x Hxy.
      induction Ht; unfold k in *; subst; eauto.
      cbn in H2. edestruct H2 as (s & Hs & Hst); eauto.
    - intros x y Hxy t Ht.
      apply Hxy in Ht as (s & Hs & Hst); clear x Hxy. unfold k; cbn.
      revert y Hs.
      induction Hst; intros; eauto.
      + eapply pull_move; eauto. constructor.
      + eapply pull_tcons; eauto using closed. constructor.
        intros; subst. eauto.
  Qed.

  Section SIM_PROP.
    Context {W : Type}.

    Global Instance ret_sim :
      Monotonic
        (@ret)
        (forallr RM, forallr RN, forallr R, R ++> sim (W:=W) RM RN R) | 10.
    Proof.
      intros M1 M2 RM N1 N2 RN A B R a b Hab _ [ ].
      eapply pull_val; cbn; eauto.
    Qed.

    Global Instance bind_sim :
      Monotonic
        (@bind)
        (forallr RM, forallr RN, forallr RA, forallr RB,
           (RA ++> sim (W:=W) RM RN RB) ++> sim RM RN RA ++> sim RM RN RB) | 10.
    Proof.

(** Notes on debugging rewriting:
  To try out the resolution you can simply use the approach:

  assert (exists R S T,
            Proper (R ==> S) op1 /\
            ProperProxy R arg /\
            Proper (S ==> T) op2 /\
            ...)

then go "repeat eexists; repeat apply conj; red"
and step through each goal with "rstep" *)

      intros M1 M2 RM N1 N2 RN A1 A2 RA B1 B2 RB f1 f2 Hf x1 x2 Hx.
      intros t1 (s1 & Hs1 & Hst1). revert x1 x2 Hx Hs1.
      induction Hst1; intros; eauto.
      - apply Hx in Hs1. inversion Hs1; clear Hs1; subst.
        + apply has_ret in H1. rewrite <- H1, ret_bind.
          revert H. repeat rstep. eapply Hf; rauto.
        + repeat (econstructor; eauto).
      - apply Hx in Hs1. inversion Hs1; clear Hs1; subst.
        + repeat (econstructor; eauto).
        + eapply pull_div; eauto.
      - apply Hx in Hs1. inversion Hs1; clear Hs1; subst.
        repeat (econstructor; eauto).
      - apply Hx in Hs1. inversion Hs1; clear Hs1; subst.
        + repeat (econstructor; eauto).
        + eapply pull_move; eauto.
      - apply Hx in Hs1. inversion Hs1; clear Hs1; subst.
        + repeat (econstructor; eauto).
        + eapply pull_tcons; eauto.
          intros.
          change (has (pull RM RN RB (delta (x2 >>= f2) m2 n2)) t0).
          rewrite delta_bind. rewrite <- join_pull.
          apply H4 in H. change (has (pull RM RN RA (delta x2 m2 n2)) s) in H.
          rewrite <- join_ub_l.
          eapply IHHst1; eauto.
          red. reflexivity.
    Qed.

    Global Instance interact_sim :
      Monotonic
        (@interact)
        (forallr RM, forallr RN, |= RM ++> k1 (sim (W:=W) RM RN) RN) | 10.
    Proof.
      intros M1 M2 RM N1 N2 RN w m1 m2 Hm.
      intros t [Ht | [n1 Ht]]; subst; cbn.
      - eapply pull_move; cbn; eauto.
      - eapply pull_tcons; cbn; eauto.
    Qed.

    Global Instance join_sim :
      Monotonic
        (@join)
        (forallr RM : klr W, forallr RN : klr W, forallr RX : rel,
         sim RM RN RX ++> sim RM RN RX ++> sim RM RN RX) | 10.
    Proof.
      intros M1 M2 RM N1 N2 RN X1 X2 RX.
      intros x1 x2 Hx y1 y2 Hy. unfold sim in *.
      rewrite Hx, Hy. apply join_pull.
    Qed.

    Global Instance sup_sim :
      Monotonic
        (@sup)
        (forallr RM : klr W, forallr RN : klr W, forallr RX : rel, forallr -,
          (- ==> sim RM RN RX) ++> sim RM RN RX).
    Proof.
      intros M1 M2 RM N1 N2 RN X1 X2 RX I.
      intros f1 f2 Hf. unfold sim.
      apply sup_lub. intros i. specialize (Hf i). red in Hf. rewrite Hf.
      rstep. monad.
    Qed.

    Global Instance guard_sim :
      Monotonic
        (@guard)
        (forallr RM : klr W, forallr RN : klr W, impl ++> sim RM RN ⊤) | 10.
    Proof.
      intros M1 M2 RM N1 N2 RN P Q HPQ. unfold sim in *.
      intros t (H & Ht); subst.
      eapply pull_val. simpl. eauto. constructor.
    Qed.

    Global Instance choose_sim :
      Monotonic
        (@choose)
        (forallr RM : klr W, forallr RN : klr W, forallr RA,
         set_le RA ++> sim RM RN RA) | 10.
    Proof.
      intros M1 M2 RM N1 N2 RN A1 A2 RA P Q HPQ. unfold sim in *.
      intros t (a & Ha & Ht); subst.
      edestruct HPQ as (b & Hb & Hab); eauto.
      apply pull_val with b; eauto.
    Qed.

    Context {M1 M2} (RM : klr W M1 M2).
    Context {N1 N2} (RN : klr W N1 N2).
    Context {X1 X2} (RX : rel X1 X2).

    Global Instance sim_ref :
      Monotonic
        (@sim _ M1 M2 RM N1 N2 RN X1 X2 RX)
        (ref --> ref ++> impl).
    Proof.
      unfold sim. repeat rstep. intro.
      etransitivity; eauto.
      etransitivity; eauto.
      rauto.
    Qed.

    Global Instance sim_ref_params :
      Params (@sim) 2.

    Lemma join_lub_sim x y z :
      sim RM RN RX x z ->
      sim RM RN RX y z ->
      sim RM RN RX (join x y) z.
    Proof.
      apply join_lub.
    Qed.

  End SIM_PROP.

End Intm.
