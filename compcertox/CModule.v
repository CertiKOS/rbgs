From Coq Require Import
     Relations
     RelationClasses
     List.
From compcertox Require Import
     Lifting AbRel.
From compcert.lib Require Import
     Coqlib Maps.
From compcert.common Require Import
     LanguageInterface
     AST Events Globalenvs
     Smallstep Linking
     SmallstepLinking
     Memory Values
     CallconvAlgebra
     CategoricalComp
     FlatComp.
From compcert.cfrontend Require Import
     Clight Ctypes.
Require Coq.omega.Omega.

(* A module is a list of compilation units. Specifically, they are Clight
   programs at this time. Note that in the layer library the modules are
   organized as mapping from identifiers to vars or functions. A module like
   that is transformed into a Clight program by [make_program] because separate
   compilation is not supported. However, here a module is nothing but a list of
   programs and the semantics is given by the horizontal composition of the
   Clight programs *)
Notation cmodule := (list Clight.program).

Fixpoint pos (M: cmodule): Type :=
  match M with
  | nil => Empty_set
  | p :: ps => unit + pos ps
  end.

Definition ref (M: cmodule) (k: pos M): Smallstep.semantics li_c li_c.
Proof.
  induction M as [| p ps].
  - inv k.
  - destruct k.
    + refine (Clight.semantics2 p).
    + apply IHps. apply p0.
Defined.

Definition semantics (M: cmodule) sk: Smallstep.semantics li_c li_c :=
  SmallstepLinking.semantics' (ref M) sk.

Require Import FunctionalExtensionality.
Require Import FinFun.

Global Instance cmod_progrom_sem M sk: ProgramSem (semantics M sk).
Proof.
  split.
  - intros. inv H. destruct H0 as (?&?&?&?).
  split; eauto. eexists; split; eauto.
  cbn. eexists; eauto.
  - intros. inv H. intros [Hq [x [Hx1 Hx2]]].
    destruct Hx1 as [j1 Hj]. apply (H1 j1).
    split; auto. exists x; split; auto.
Qed.

Section APP.

  Context (M N: cmodule).
  Variable (sk: AST.program unit unit).
  (* TODO: maybe we could use different sk for M and N *)
  Let L := fun (b: bool) => match b with | true => (semantics M sk) | false => (semantics N sk) end.
  Let J := fun (b: bool) => match b with | true => pos M | false => pos N end.
  Definition Lij: forall (b: bool), J b -> Smallstep.semantics li_c li_c.
  Proof.
    intros [|] j.
    - refine (ref M j).
    - refine (ref N j).
  Defined.

  Lemma Leq: L = (fun i => semantics' (fun j => Lij i j) sk).
  Proof.
    apply functional_extensionality. intros [|]; reflexivity.
  Qed.

  Definition F: pos (M ++ N) -> {b : bool & J b}.
  Proof.
    intros x. induction M as [| p ps].
    - refine (existT _ false x).
    - cbn in *. destruct x.
      + refine (existT _ true (inl u)).
      + specialize (IHps p0) as [[|] pp].
        * refine (existT _ true (inr pp)).
        * refine (existT _ false pp).
  Defined.

  Definition G: {b : bool & J b} -> pos (M ++ N).
  Proof.
    intros [[|] j].
    - cbn in *. induction M as [| p ps].
      + inv j.
      + cbn. destruct j.
        * refine (inl u).
        * refine (inr (IHps p0)).
    - cbn in *. induction M as [| p ps].
      + refine j.
      + refine (inr IHps).
  Defined.

  Lemma FG_bij: Bijective F.
  Proof.
    exists G. split; intros x.
    - unfold F, G. cbn.
      induction M as [| p ps].
      + reflexivity.
      + cbn in *. destruct x.
        * reflexivity.
        * cbn in *. specialize (IHps p0).
          remember (list_rect (fun l : cmodule => pos (l ++ N) -> _) _ _ ps p0) as lr.
          destruct lr as [b pb]. destruct b.
          -- f_equal. apply IHps.
          -- f_equal. apply IHps.
    - unfold F, G. cbn. destruct x as [[|] j].
      + cbn in *. induction M as [| p ps].
        * cbn in *. inv j.
        * cbn in *. destruct j.
          -- constructor.
          -- specialize (IHps p0). cbn in *.
             rewrite IHps. constructor.
      + cbn in *. induction M as [| p ps].
        * cbn in *. constructor.
        * cbn in *. rewrite IHps. constructor.
  Qed.

  Lemma LFeq: (fun i : pos (M ++ N) => (fun p : {x : bool & J x} => Lij (projT1 p) (projT2 p)) (F i)) = ref (M ++ N).
  Proof.
    apply functional_extensionality. intros x.
    unfold F, Lij. induction M as [| p ps].
    - cbn in *. reflexivity.
    - cbn in *. destruct x.
      + reflexivity.
      + cbn in *. specialize (IHps p0).
        remember (list_rect (fun l : cmodule => pos (l ++ N) -> _) _ _ ps p0) as lr.
        destruct lr as [b pb]. destruct b.
        * cbn in *. apply IHps.
        * cbn in *. apply IHps.
  Qed.

  Lemma cmodule_app_simulation:
    SmallstepLinking.semantics' L sk ≤ semantics (M ++ N) sk.
  Proof.
    rewrite Leq.
    etransitivity. apply level_simulation1.
    etransitivity. eapply bijective_map_simulation1 with (F := F).
    apply FG_bij. unfold semantics. rewrite <- LFeq.
    reflexivity.
  Qed.

  Section CAT_APP.
    Context `{!CategoricalLinkable (semantics M sk) (semantics N sk)}.

    Lemma cmodule_categorical_comp_simulation:
      comp_semantics' (semantics M sk) (semantics N sk) sk ≤ semantics (M ++ N) sk.
    Proof.
      etransitivity.
      apply categorical_compose_approximation; typeclasses eauto.
      fold L. rewrite Leq.
      etransitivity. apply level_simulation1.
      etransitivity. eapply bijective_map_simulation1 with (F := F).
      apply FG_bij. unfold semantics. rewrite <- LFeq.
      reflexivity.
    Qed.
  End CAT_APP.

  Section FLAT_APP.
    Context `{!FlatLinkable L}.

    Lemma cmodule_flat_comp_simulation:
      flat_comp_semantics' L sk ≤ semantics (M ++ N) sk.
    Proof.
      etransitivity.
      apply flat_composition_approximation;
        [ intros [|]; typeclasses eauto
        | eauto | decide equality ].
      rewrite Leq.
      fold @SmallstepLinking.semantics.
      etransitivity. apply level_simulation1.
      etransitivity. eapply bijective_map_simulation1 with (F := F).
      apply FG_bij. unfold semantics. rewrite <- LFeq.
      reflexivity.
    Qed.
  End FLAT_APP.

End APP.

Lemma cmodule_app_simulation' M N sk sk':
  CategoricalLinkable (semantics M sk) (semantics N sk) -> linkorder sk' sk ->
  comp_semantics' (semantics M sk) (semantics N sk') sk ≤ semantics (M ++ N) sk.
Proof.
  intros Hsk.
  etransitivity. 2:{ apply cmodule_categorical_comp_simulation; auto. }
  etransitivity. 2:{ apply lift_comp_component2. }
  eapply categorical_compose_simulation';
                   [ reflexivity
                   | apply identity_forward_simulation
                   | apply linkorder_refl | auto ].
Qed.

Definition skel_module_compatible (M: cmodule) (sk: AST.program unit unit) :=
  Forall (fun (p: Clight.program) => linkorder (AST.erase_program p) sk) M.

Lemma cmodule_abrel {Ks Kf} (R: abrel Ks Kf) M sk:
  skel_module_compatible M sk ->
  forward_simulation R R (semantics M sk @ Ks) (semantics M sk @ Kf).
Proof.
  intros Hsk.

  eapply open_fsim_ccref. apply cc_compose_id_left.
  unfold flip. apply cc_compose_id_left.
  eapply compose_forward_simulations.
  apply lift_horizontal_comp1.

  eapply open_fsim_ccref. apply cc_compose_id_right.
  unfold flip. apply cc_compose_id_right.
  eapply compose_forward_simulations.
  2: { apply lift_horizontal_comp2. }

  apply semantics_simulation'.
  - intros. induction M as [| p ps]; try easy.
    destruct i.
    + cbn. apply clight_sim.
    + apply IHps.
      unfold skel_module_compatible in *.
      rewrite -> Forall_forall in *.
      intros x Hx. apply Hsk. right. auto.
  - intros. induction M as [| p ps]; try easy.
    destruct i.
    + cbn. unfold skel_module_compatible in *.
      rewrite -> Forall_forall in *. apply Hsk.
      left. auto.
    + apply IHps.
      unfold skel_module_compatible in *.
      rewrite -> Forall_forall in *.
      intros x Hx. apply Hsk. right. auto.
Qed.

Require Import Integers.

(* FIXME: move to Clight *)
Global Instance clight_program_sem p: ProgramSem (semantics2 p).
Proof.
  split.
  - intros. inv H. clear -H0. unfold valid_query; cbn.
    unfold Genv.find_funct in H0.
    destruct vf; try congruence.
    destruct Ptrofs.eq_dec; try congruence.
    split. intros X. discriminate X.
    subst. unfold Genv.find_funct_ptr in H0.
    destruct Genv.find_def eqn: Hdef; try congruence.
    destruct g; try congruence. inv H0.
    unfold globalenv in Hdef; cbn in *.
    rewrite Genv.find_def_spec in Hdef.
    destruct Genv.invert_symbol eqn: Hse; try congruence.
    exists i. split. unfold footprint_of_program.
    rewrite Hdef. auto.
    unfold Genv.symbol_address.
    apply Genv.invert_find_symbol in Hse.
    rewrite Hse. auto.
  - intros. inv H. unfold valid_query. cbn.
    intros [? (i & Hi & Hse)].
    unfold Genv.find_funct in H0.
    destruct vf; try congruence.
    destruct Ptrofs.eq_dec; try congruence.
    unfold Genv.find_funct_ptr in H0.
    destruct Genv.find_def eqn: Hdef; try congruence.
    destruct g eqn: Hg; try congruence. inv H0.
    unfold globalenv in Hdef. cbn in *.
    rewrite Genv.find_def_spec in Hdef.
    destruct Genv.invert_symbol eqn: Hs; try congruence.
    apply Genv.invert_find_symbol in Hs.
    unfold Genv.symbol_address in Hse.
    destruct (Genv.find_symbol se i) eqn: Hxe; try congruence.
    inv Hse. exploit Genv.find_symbol_injective.
    apply Hs. apply Hxe. intros ->.
    unfold footprint_of_program in Hi. rewrite Hdef in Hi.
    subst f. cbn in *. discriminate Hi.
Qed.

Section LINKABLE.
  Definition program_vertical_linkable (p1 p2: Clight.program) :=
    forall id f ef ts t cc,
      (prog_defmap p1) ! id = Some (Gfun (Internal f)) ->
      (prog_defmap p2) ! id = Some (Gfun (External ef ts t cc)) -> False.

  Definition cmodule_vertical_linkable (M N: cmodule) :=
    forall pm pn, In pm M -> In pn N -> program_vertical_linkable pm pn.

  Definition program_horizontal_linkable (p1 p2: Clight.program) :=
    program_vertical_linkable p1 p2 /\ program_vertical_linkable p2 p1.

  Definition cmodule_horizontal_linkable (M N: cmodule) :=
    forall pm pn, In pm M -> In pn N -> program_horizontal_linkable pm pn.

  Lemma cmodule_program M idx:
    exists p, In p M /\ ref M idx = Clight.semantics2 p.
  Proof.
    induction M; [ easy | ].
    destruct idx.
    - eexists; split. now left. easy.
    - specialize (IHM p) as (x & Hx & Hp).
      exists x. split. now right. apply Hp.
  Qed.

  Lemma cmodule_vertical_linkable_cond M N sk1 sk2:
    cmodule_vertical_linkable M N -> CategoricalLinkable (semantics M sk1) (semantics N sk2).
  Proof.
    intros H se s q Hext Hvq.
    destruct Hvq as [Hq (id & (i & Hfp) & Hsymbol)].
    destruct (cmodule_program M i) as (pm & Hpm & Hm). rewrite Hm in Hfp.
    inversion Hext as [j ? ? ? Hx Hvq]. subst. clear Hext Hvq.
    destruct (cmodule_program N j) as (pn & Hpn & Hn).
    remember (ref N j) as pref. clear Heqpref. subst pref.
    cbn in Hx. inv Hx. cbn -[prog_defmap] in *.
    unfold footprint_of_program in Hfp.
    destruct ((prog_defmap pm) ! id) eqn: Hp1; try easy.
    destruct g; try easy. destruct f0; try easy.
    specialize (H pm pn Hpm Hpn). eapply H. eauto.
    unfold Genv.symbol_address in Hsymbol.
    destruct Genv.find_symbol eqn:Hb; try congruence.
    unfold Genv.find_funct in H0. subst.
    destruct Ptrofs.eq_dec; try congruence.
    unfold Genv.find_funct_ptr in H0.
    destruct Genv.find_def eqn:Hf in H0; try congruence.
    destruct g; try congruence. inv H0.
    rewrite Genv.find_def_spec in Hf.
    destruct Genv.invert_symbol eqn:Hb'; try congruence.
    apply Genv.invert_find_symbol in Hb'.
    assert (id = i0) by (eapply Genv.genv_vars_inj; eauto).
    subst. rewrite Hf. subst f. reflexivity.
  Qed.

  Lemma program_categorical_linkable_cond (p1 p2: Clight.program) sk1 sk2:
    (forall id f ef ts t cc,
        (prog_defmap p1) ! id = Some (Gfun (Internal f)) ->
        (prog_defmap p2) ! id = Some (Gfun (External ef ts t cc)) ->
        False) ->
    CategoricalLinkable (semantics (p1::nil) sk1) (semantics (p2::nil) sk2).
  Proof.
    intros. apply cmodule_vertical_linkable_cond.
    unfold cmodule_vertical_linkable, program_vertical_linkable.
    intros. inv H0; try easy. inv H1; try easy.
    eapply H; eauto.
  Qed.

  Lemma cmodule_horizontal_linkable_cond M N sk1 sk2:
    cmodule_horizontal_linkable M N ->
    FlatLinkable (fun (i: bool) => if i then semantics M sk1 else semantics N sk2).
  Proof.
    intros H. unfold FlatLinkable.
    intros [|] [|] * Ht Hvq; auto; exfalso.
    - assert (Hl: CategoricalLinkable (semantics N sk2) (semantics M sk1)).
      { apply cmodule_vertical_linkable_cond. intros p1 p2 Hp1 Hp2. apply H; eauto. }
      exploit Hl; eauto.
    - assert (Hl: CategoricalLinkable (semantics M sk1) (semantics N sk2)).
      { apply cmodule_vertical_linkable_cond. intros p1 p2 Hp1 Hp2. specialize (H p1 p2). apply H; eauto. }
      exploit Hl; eauto.
  Qed.

End LINKABLE.
