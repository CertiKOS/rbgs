Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import Classical.
Require Import ClassicalChoice.
Require Import structures.Category.
Require Import structures.Lattice.
Require Import structures.Completion.
Require Import lattices.Upset.
Require Import lattices.FCD.

Module Lazy <: LatticeCategory.

  Section DEF.
    Context {L M : cdlattice} (f : L -> M).

    Class NSupMorphism :=
      mor_sup: forall {I} (x : I -> L), inhabited I -> f (lsup x) = lsup (f @ x).

    Class Morphism := mor : NSupMorphism /\ Inf.Morphism f.
    Global Instance cmor_sup : Morphism -> NSupMorphism := @proj1 _ _.
    Global Instance cmor_inf : Morphism -> Inf.Morphism f := @proj2 _ _.

    Global Instance mor_ref :
      Morphism -> PosetMorphism f.
    Proof.
      intros [_ H].
      apply Inf.mor_ref; auto.
    Qed.
  End DEF.

  Lemma id_mor (L : cdlattice) :
    Morphism (fun x:L => x).
  Proof.
    firstorder.
  Qed.

  Lemma compose_mor {A B C : cdlattice} (g : B -> C) (f : A -> B) :
    Morphism f ->
    Morphism g ->
    Morphism (fun a => g (f a)).
  Proof.
    split.
    - intros I x Hx. rewrite (mor_sup f), (mor_sup g); auto.
    - apply Inf.compose_mor; typeclasses eauto.
  Qed.

End Lazy.

Module LBot.

  (** We construct the extended the lattice with a new ⊥ by using sets
    with at most one element. *)

  Inductive opt {A} :=
    mkopt (s : A -> Prop) (Hs : forall a b, s a -> s b -> a = b).

  Arguments opt : clear implicits.
  Definition is {A} : opt A -> A -> Prop := fun '(mkopt a _) => a.

  Lemma is_unique {A} (x : opt A) (a b : A) :
    is x a -> is x b -> a = b.
  Proof.
    destruct x; auto.
  Qed.

  Lemma opt_eq {A} (x y : opt A) :
    (forall a, is x a <-> is y a) -> x = y.
  Proof.
    destruct x as [x Hx], y as [y Hy]. cbn. intros H.
    cut (x = y).
    - intro. subst. f_equal. apply proof_irrelevance.
    - apply functional_extensionality. intro.
      apply propositional_extensionality; auto.
  Qed.

  Section DEF.
    Context {L M : cdlattice}.

    (** ** Poset *)

    Program Definition Fposet : poset :=
      {|
        poset_carrier := opt L;
        ref x y := forall l, is x l -> exists m, is y m /\ ref l m;
      |}.

    Next Obligation.
      split.
      - intros x. eauto using (reflexivity (R:=ref)).
      - intros [x Hx] [y Hy] [z Hz] Hxy Hyz l Hl. cbn in *.
        destruct (Hxy l) as (m & Hm & Hlm); auto.
        destruct (Hyz m) as (n & Hn & Hmn); auto.
        exists n. split; auto. transitivity m; auto.
    Qed.

    Next Obligation.
      intros [x Hx] [y Hy] Hxy Hyx. cbn in *.
      apply opt_eq. intros l. split.
      - intros Hl.
        destruct (Hxy l) as (m & Hm & Hlm); auto.
        destruct (Hyx m) as (n & Hn & Hmn); auto.
        assert (n = l) by auto; subst.
        assert (m = l) by (apply antisymmetry; auto); subst.
        assumption.
      - intros Hl.
        destruct (Hyx l) as (m & Hm & Hlm); auto.
        destruct (Hxy m) as (n & Hn & Hmn); auto.
        assert (n = l) by auto; subst.
        assert (m = l) by (apply antisymmetry; auto); subst.
        assumption.
    Qed.

    (** ** Lattice structure *)

    Definition proj (x : opt L) : L :=
      sup {l | is x l}, l.

    Lemma proj_is x l :
      is x l -> proj x = l.
    Proof.
      intros Hl. apply antisymmetry.
      - apply fsup_lub. intros m Hm.
        assert (m = l) by eauto using is_unique. rauto.
      - eapply fsup_at; eauto. reflexivity.
    Qed.

    Definition sup_of {I} (x : I -> opt L) (l : L) :=
      (exists i, exists li, is (x i) li) /\
      sup i, proj (x i) = l.

    Definition inf_of {I} (x : I -> opt L) (l : L) :=
      (forall i, exists li, is (x i) li) /\
      inf i, proj (x i) = l.

    Definition sup_inf_of {I J} (x : forall i:I, J i -> opt L) (l : L) :=
      (exists i, forall j, exists li, is (x i j) li) /\
      sup i, inf j, proj (x i j) = l.

    Definition inf_sup_of {I J} (x : forall i:I, J i -> opt L) (l : L) :=
      (forall i, exists j, exists li, is (x i j) li) /\
      inf i, sup j, proj (x i j) = l.

    Lemma sup_inf_of_cd {I J} (x : forall i:I, J i -> opt L) (l : L) :
      sup_inf_of x l <->
      inf_sup_of (fun f i => x i (f i)) l.
    Proof.
      split.
      - intros [Hx Hl]. split.
        + firstorder.
        + subst. rewrite sup_inf. reflexivity.
      - intros [Hx Hl]. split.
        + destruct (classic (forall i, exists j, ~ exists li, is (x i j) li)).
          * exfalso.
            admit.
            (*
            apply choice in H as [f Hf].
            specialize (Hx f) as (i & li & Hli).
            apply (Hf i). eauto.
             *)
          * apply not_all_ex_not in H as (i & H). exists i. intro j.
            apply not_ex_not_all with _ _ j in H. auto.
        + subst. rewrite sup_inf. reflexivity.
    Admitted.

    Hint Unfold sup_of inf_of.

    Program Definition F : cdlattice :=
      {|
        cdl_poset := Fposet;
        lsup I x := mkopt (sup_of x) _;
        linf I x := mkopt (inf_of x) _;
      |}.

    (** [sup], [inf] are singletons. *)

    Next Obligation.
      firstorder congruence.
    Qed.
    Next Obligation.
      firstorder congruence.
    Qed.

    (** [sup] is the least upper bound *)

    Next Obligation.
      eexists; split; eauto.
      apply (sup_at i). cbn.
      erewrite proj_is by eauto. rauto.
    Qed.

    Next Obligation.
      destruct H0 as [(i & li & Hli) Hl]. subst. cbn.
      destruct (H i li Hli) as (m & Hm & _). clear i li Hli.
      exists m. split; auto.
      apply sup_lub. intros i.
      apply fsup_lub. intros li Hli.
      destruct (H i li Hli) as (m' & Hm' & LE).
      assert (m' = m) by eauto using is_unique. congruence.
    Qed.

    (** [inf] is the greatest lower bound *)

    Next Obligation.
      destruct H as [H Hl]. subst.
      destruct (H i) as (l & Hl).
      exists l; split; auto. cbn.
      apply (inf_at i). rewrite (proj_is (x i) l) by auto.
      reflexivity.
    Qed.

    Next Obligation.
      eexists; split.
      - split; [ | auto].
        intros i. destruct (H i l) as (m & Hm & Hlm); eauto.
      - apply inf_glb. intros i. cbn.
        edestruct (H i) as (m & Hm & Hlm); eauto.
        erewrite proj_is; eauto.
    Qed.

    (** Distributivity *)

    Next Obligation.
      apply opt_eq. intros l. cbn.
      transitivity (sup_inf_of x l).
      {
        unfold sup_of, inf_of, sup_inf_of, proj; cbn.
        split; intros [Hx Hl]; subst.
        - split.
          + firstorder.
          + apply antisymmetry.
            * apply sup_lub. intros i. apply (sup_at i).
              destruct (classic (forall j, exists lij, is (x i j) lij)).
              -- eapply fsup_at; eauto. reflexivity.
              -- apply not_all_ex_not in H as (j & Hj).
                 apply (inf_at j). apply fsup_lub. firstorder.
            * apply sup_lub. intros i. apply (sup_at i).
              apply fsup_lub. intros _ [H [ ]].
              reflexivity.
        - split.
          + destruct Hx as [i Hi]. eauto.
          + apply antisymmetry.
            * apply sup_lub. intros i. apply (sup_at i).
              apply fsup_lub. intros _ [Hi [ ]].
              reflexivity.
            * apply sup_lub. intros i. apply (sup_at i).
              destruct (classic (forall j, exists lij, is (x i j) lij)).
              -- eapply fsup_at; eauto. reflexivity.
              -- apply not_all_ex_not in H as (j & Hj).
                 apply (inf_at j). apply fsup_lub. firstorder.
      }
      rewrite sup_inf_of_cd.
      {
        unfold sup_of, inf_of, inf_sup_of, proj; cbn.
        split; intros [Hx Hl]; subst.
        - split.
          + intros f. destruct (Hx f) as (i & l & Hl). eauto.
          + f_equal. apply functional_extensionality. intros f.
            apply antisymmetry.
            * apply fsup_lub. intros _ [(i & l & Hl) [ ]]. reflexivity.
            * eapply fsup_at; eauto. reflexivity.
        - split.
          + intros f. destruct (Hx f) as (i & l & Hl). eauto.
          + f_equal. apply functional_extensionality. intros f.
            apply antisymmetry.
            * apply sup_lub. intros i. apply fsup_lub. intros l Hl.
              eapply fsup_at; eauto. eapply sup_at, fsup_at; eauto. reflexivity.
            * apply fsup_lub. intros _ [(i & l & Hl) [ ]]. reflexivity.
      }
    Qed.

    (** ** Adjunction *)

    Program Definition emb (l : L) : F := mkopt (eq l) _.

    Global Instance emb_mor :
      Lazy.Morphism emb.
    Proof.
      split.
      - red. intros I x [i]. apply antisymmetry.
        + intros l Hl. cbn in *. subst.
          eexists; split; [ | reflexivity]. red; cbn.
          split. exists i. eauto. unfold proj; cbn.
          apply antisymmetry.
          * apply sup_lub. intros j.
            apply fsup_lub. intros _ [ ].
            apply (sup_at j). reflexivity.
          * apply sup_lub. intros j. apply (sup_at j). cbn.
            eapply fsup_at; eauto. reflexivity.
        + apply sup_lub. cbn. intros j _ [ ].
          eexists; split; [reflexivity | ].
          apply sup_ub.
      - red. intros I x. apply antisymmetry.
        + cbn. intros _ [ ].
          eexists; split; [constructor; cbn; eauto | ].
          eapply inf_glb. intros i. apply (inf_at i).
          unfold proj; cbn. eapply fsup_at; eauto. reflexivity.
        + cbn. intros _ [? [ ]]. cbn in *.
          eexists; split; [reflexivity | ].
          eapply inf_glb. intros i. unfold proj; cbn.
          apply (inf_at i). apply fsup_lub. intros _ [ ]. reflexivity.
    Qed.

    (*
    Lemma emb_mor c1 c2 :
      emb c1 ⊑ emb c2 -> c1 ⊑ c2.
    Proof.
      unfold emb. cbn.
      split.
      - intros H. destruct (H c1) as (? & ? & ?); auto. congruence.
      - intros H l Hl. subst. eauto.
    Qed.
     *)

    Lemma cases x :
      x = bot \/ exists l, x = emb l.
    Proof.
      destruct (classic (ex (is x))) as [[l Hl] | H].
      - right. exists l.
        destruct x as [x Hx]; cbn in *.
        apply opt_eq. intros l'.
        cbn. split; auto. congruence.
      - left. apply antisymmetry.
        + intros l Hl. elim H; eauto.
        + apply bot_lb.
    Qed.

    Lemma sup_cases {I} (x : I -> F) :
      (lsup x = bot /\
       forall i, x i = bot) \/
      (lsup x = emb (sup {l | exists i, is (x i) l}, l) /\
       exists i l, is (x i) l).
    Proof.
      destruct (classic (forall i, x i = bot)).
      - left. split; auto.
        apply antisymmetry; auto using bot_lb.
        apply sup_lub. intros i.
        intros l Hl. rewrite H in Hl. elim Hl.
        intros ([ ] & _).
      - right. apply not_all_ex_not in H as (i & Hi).
        split.
        unfold fsup. rewrite (Lazy.mor_sup emb).
        + cbn. apply opt_eq. intros l. cbn. split.
          * intros [(j & m & Hm)].
            econstructor.
    Admitted.


    Definition ext (f : L -> M) (x : F) : M :=
      sup {l | is x l}, f l.

    Context {f : L -> M} `{Hf : !Lazy.Morphism f}.

    Lemma ext_bot :
      ext f bot = bot.
    Proof.
      apply antisymmetry; try apply bot_lb.
      unfold ext. apply fsup_lub. Local Transparent bot. cbn.
      intros i [? ?]. destruct H as [[ ]].
    Qed.

    Lemma ext_ana :
      (forall x, ext f (emb x) = f x).
    Proof.
      intros x. unfold ext, emb. cbn.
      apply antisymmetry.
      - apply fsup_lub. intros _ [ ]. reflexivity.
      - apply fsup_ub. reflexivity.
    Qed.

    Instance ext_mor :
      CDL.Morphism (ext f).
    Proof.
      split.
      - red. intros I x.
        destruct (sup_cases x) as [[Hsup H] | [Hsup H]]; rewrite Hsup.
        + rewrite ext_bot. transitivity (sup i:I, ext f bot).
          * apply antisymmetry; try apply bot_lb.
            apply sup_lub. intros _. rewrite ext_bot. reflexivity.
          * f_equal. apply functional_extensionality. intro. rewrite H. reflexivity.
        + rewrite ext_ana. unfold fsup. rewrite (Lazy.mor_sup f).
          * apply antisymmetry.
            -- apply sup_lub. intros (l & i & Hli). cbn.
               apply (sup_at i). eapply fsup_at; eauto. reflexivity.
            -- apply sup_lub. intros i. apply fsup_lub. intros l Hli. cbn.
               admit.
          * admit.
      - admit.
    Admitted.

    Lemma ext_unique (g : F -> M) `{Hg : !CDL.Morphism g} :
      (forall x, g (emb x) = f x) -> forall x, g x = ext f x.
    Proof.
      intros Hgf l. destruct (cases l) as [? | [y Hy]]; subst.
      - rewrite (Downset.Sup.mor_bot (f := g)).
        rewrite (Downset.Sup.mor_bot (f := ext f)).
        reflexivity.
      - rewrite ext_ana. auto.
    Qed.

  End DEF.

End LBot.
