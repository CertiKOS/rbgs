From Coq Require Import
     Relations RelationClasses List.
From compcertox Require Import
     Lifting AbstractStateRel.
From compcert.lib Require Import
     Coqlib.
From compcert.common Require Import
     LanguageInterface Events
     Globalenvs Smallstep
     Linking Memory Values.
From compcert.cklr Require Import
     CKLR Extends Clightrel.
From compcert.cfrontend Require Import
     SimplLocalsproof Clight.

Definition blocks (se: Genv.symtbl) (names: ident -> Prop) : block -> Z -> Prop :=
  fun b ofs => exists v, names v /\ Genv.find_symbol se v = Some b.
Definition no_perm_on (m: mem) (vars: block -> Z -> Prop): Prop :=
  forall b ofs, vars b ofs -> ~ Mem.perm m b ofs Max Nonempty.

(** The relation Rr is parametrized by the symbol table so that we do not have
    to bind the variables being abstracted to particular blocks *)
Record krel {Ks Kf: Type}: Type :=
  mk_krel {
      krel_pred (se: Genv.symtbl):> Ks -> mem * Kf -> Prop;
      (** the names of the static variables being abstracted *)
      krel_footprint : ident -> Prop;

      (** the abstraction relation is not affected by other variables *)
      krel_invar: forall se kf ks m m',
        krel_pred se ks (m, kf) ->
        Mem.unchanged_on (blocks se krel_footprint) m m' ->
        krel_pred se ks (m', kf);
      (** the abstraction relation only focuses on valid blocks, i.e. those have
          been allocated *)
      krel_valid: forall se kf ks m b ofs,
        krel_pred se ks (m, kf) ->
        blocks se krel_footprint b ofs ->
        Mem.valid_block m b;
    }.
Arguments krel: clear implicits.

Inductive krel_world :=
| mk_aw : Genv.symtbl -> mem -> mem -> krel_world.

Section KREL_CC.

  Context {Ks Kf} (R: krel Ks Kf).

  Inductive krel_cc_query: krel_world -> query (li_c @ Ks) -> query (li_c @ Kf) -> Prop :=
    krel_cc_query_intro se ms mf vfs vff sg vargss vargsf ks kf:
      Val.inject inject_id vfs vff -> vfs <> Vundef ->
      Val.inject_list inject_id vargss vargsf ->
      Mem.extends ms mf ->
      no_perm_on ms (blocks se (krel_footprint R)) ->
      R se ks (mf, kf) ->
      krel_cc_query (mk_aw se ms mf) (cq vfs sg vargss ms, ks) (cq vff sg vargsf mf, kf).
  Inductive krel_cc_reply: krel_world -> reply (li_c @ Ks) -> reply (li_c @ Kf) -> Prop :=
    krel_cc_reply_intro se vress ms vresf mf ks kf:
      Val.inject inject_id vress vresf ->
      Mem.extends ms mf ->
      no_perm_on ms (blocks se (krel_footprint R)) ->
      R se ks (mf, kf) ->
      krel_cc_reply (mk_aw se ms mf) (cr vress ms, ks) (cr vresf mf, kf).
  Instance krel_cc_kf: KripkeFrame unit krel_world :=
    {| acc _ '(mk_aw se ms mf) '(mk_aw _ _ mf') :=
      let P b ofs := loc_out_of_bounds ms b ofs /\ ~ blocks se (krel_footprint R) b ofs
      in Mem.unchanged_on P mf mf'; |}.

  Program Definition krel_cc: callconv (li_c @ Ks) (li_c @ Kf) :=
    {|
      ccworld := krel_world;
      match_senv '(mk_aw se _ _) := fun se1 se2 => se = se1 /\ se = se2;
      match_query := krel_cc_query;
      match_reply := (klr_diam tt) krel_cc_reply;
    |}.
  Next Obligation.
    destruct w. destruct H; subst. reflexivity.
  Qed.
  Next Obligation.
    destruct w. destruct H; subst. reflexivity.
  Qed.
  Next Obligation.
    destruct w. destruct H; subst.
    inv H0. cbn. apply val_inject_id in H7. inv H7; easy.
  Qed.
  Next Obligation.
    destruct w.
    inv H; cbn. apply val_inject_id in H7. inv H7; easy.
  Qed.

End KREL_CC.

Ltac unchanged_implies_solve:=
  eapply Mem.unchanged_on_implies; [eauto | intros b ofs [v [? ?]]; eexists; eauto].

Require Import CallconvAlgebra.
Require Import Lia.

Section COMP.

  Context {Ks Kn Kf} (R: krel Ks Kn) (S: krel Kn Kf).

  Local Obligation Tactic := cbn.

  Program Definition krel_comp: krel Ks Kf :=
    {|
      krel_pred se :=
        fun ks '(m, kf) => exists kn, R se ks (m, kn) /\ S se kn (m, kf);
      krel_footprint i := krel_footprint R i \/ krel_footprint S i;
    |}.
  Next Obligation.
    intros se kf ks m m' (kn & HS & HR) H.
    eexists kn. split.
    - eapply krel_invar; eauto.
      unchanged_implies_solve.
    - eapply krel_invar; eauto.
      unchanged_implies_solve.
  Qed.
  Next Obligation.
    intros se ks kf * (kn & HS & HR) Hb.
    unfold blocks in Hb. destruct Hb as (v & Hv & ?).
    destruct Hv.
    - eapply krel_valid. apply HS.
      exists v; split; auto.
    - eapply krel_valid. apply HR.
      exists v; split; auto.
      Unshelve. apply ofs. apply ofs.
  Qed.

  Lemma krel_comp_ref:
    ccref (krel_cc krel_comp) (krel_cc R @ krel_cc S)%cc.
  Proof.
    intros w. destruct w as [se ms mf].
    intros se1 se2 (q3 & k3) (q1 & k1) Hse Hq.
    inv Hse. inv Hq.
    exists (se2, mk_aw se2 ms mf, mk_aw se2 ms mf).
    repeat apply conj. split; easy.
    destruct H11 as (k2 & HR & HS).
    - exists ((cq vff sg vargsf mf), k2).
  Abort.

End COMP.

Module KCC.

  Section CKLR.

    Context {K1 K2} (R: @krel' K2 K1).

    Inductive kworld := kw (se: Genv.symtbl) (k1: K1) (k2: K2).

    Inductive krel_mm : kworld -> mem -> mem -> Prop :=
      match_intro: forall se k1 k2 m1 m2,
          Mem.extends m1 m2 -> krel_pred R se k1 (m2, k2) ->
          (* The source program would crash if it tries to manipulate data on blocks
             defined in the footprint *)
          no_perm_on m1 (blocks se (krel_footprint R)) ->
          krel_mm (kw se k1 k2) m1 m2.
    Inductive krel_match_se: kworld -> Genv.symtbl -> Genv.symtbl -> Prop :=
      match_se_intro: forall se k1 k2, krel_match_se (kw se k1 k2) se se.

    Program Definition krel_cklr: cklr :=
      {|
        world := kworld;
        wacc := eq;
        mi w := inject_id;
        match_mem := krel_mm;
        match_stbls := krel_match_se;
      |}.
    (* mi_acc *)
    Next Obligation. repeat rstep. apply inject_incr_refl. Qed.
    (* match_stbls_acc *)
    Next Obligation. rauto. Qed.
    (* match_stbls_proj *)
    Next Obligation.
      intros se1 se2 Hse. inv Hse. apply Genv.match_stbls_id.
    Qed.
    (* match_stbls_nextblock *)
    Next Obligation.
      inv H. inv H0. erewrite <- Mem.mext_next; eauto.
    Qed.
    (* cklr_alloc *)
    Next Obligation.
      intros [ ] m1 m2 Hm lo hi. inv Hm.
      destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn: Hm1.
      edestruct Mem.alloc_extends as (m2' & Hm2' & Hm'); eauto; try reflexivity.
      rewrite Hm2'.
      eexists; split; repeat rstep.
      constructor; auto.
      - eapply krel_invar; eauto.
        eapply Mem.alloc_unchanged_on; eauto.
      - unfold no_perm_on in *. intros.
        specialize (H6 _ _ H). intros Hp. apply H6.
        eapply Mem.perm_alloc_4 in Hp; eauto.
        eapply Mem.alloc_result in Hm1. subst.
        eapply krel_valid in H5; eauto.
        erewrite Mem.mext_next; eauto.
    Qed.
    (* cklr_free *)
    Next Obligation.
      intros [ ] m1 m2 Hm [[b lo] hi] r2 Hr. inv Hm.
      apply coreflexivity in Hr. subst. simpl. red.
      destruct (Mem.free m1 b lo hi) as [m1'|] eqn:Hm1'; [|constructor].
      edestruct Mem.free_parallel_extends as (m2' & Hm2' & Hm'); eauto.
      rewrite Hm2'. constructor.
      eexists; split; repeat rstep.
      constructor; auto.
      - eapply krel_invar; eauto.
        eapply Mem.free_unchanged_on; eauto.
        intros ofs Hofs Hv. specialize (H6 _ _ Hv). apply H6.
        exploit Mem.free_range_perm. apply Hm1'. eauto.
        intros Hp. eapply Mem.perm_cur_max.
        eapply Mem.perm_implies. apply Hp. constructor.
      - unfold no_perm_on in *. intros.
        specialize (H6 _ _ H). intros Hp. apply H6.
        eapply Mem.perm_free_3; eauto.
    Qed.
    (* cklr_load *)
    Next Obligation.
      intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp. inv Hm.
      apply coreflexivity in Hp; subst. simpl. red.
      destruct (Mem.load chunk m1 b ofs) as [v1|] eqn:Hv1; [|constructor].
      edestruct Mem.load_extends as (v2 & Hv2 & Hv); eauto.
      rewrite Hv2. rewrite val_inject_lessdef_eqrel. rauto.
    Qed.
    (* cklr_store *)
    Next Obligation.
      intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp v1 v2 Hv. inv Hm.
      apply coreflexivity in Hp; subst. simpl. red.
      destruct (Mem.store chunk m1 b ofs v1) as [m1'|] eqn:Hm1'; [|constructor].
      apply val_inject_lessdef in Hv.
      edestruct Mem.store_within_extends as (m2' & Hm2' & Hm'); eauto.
      rewrite Hm2'. constructor.
      eexists _; split; repeat rstep.
      constructor; auto.
      - eapply krel_invar; eauto.
        eapply Mem.store_unchanged_on; eauto.
        intros ofs' Hofs. intros Hp. specialize (H6 _ _ Hp). apply H6.
        exploit Mem.store_valid_access_3. apply Hm1'.
        unfold Mem.valid_access. intros [Hpr ?]. specialize (Hpr _ Hofs).
        eapply Mem.perm_cur_max. eapply Mem.perm_implies. apply Hpr. constructor.
      - unfold no_perm_on in *. intros.
        specialize (H6 _ _ H). intros Hp. apply H6.
        eapply Mem.perm_store_2; eauto.
    Qed.
    (* cklr_loadbytes *)
    Next Obligation.
      intros [ ] m1 m2 Hm [b ofs] p2 Hp sz. inv Hm.
      apply coreflexivity in Hp; subst. simpl. red.
      destruct (Mem.loadbytes m1 b ofs sz) as [v1|] eqn:Hv1; [|constructor].
      edestruct Mem.loadbytes_extends as (v2 & Hv2 & Hv); eauto.
      rewrite Hv2. rauto.
    Qed.
    (* cklr_storebytes *)
    Next Obligation.
      intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp vs1 vs2 Hv. inv Hm.
      apply coreflexivity in Hp. subst. simpl. red.
      destruct (Mem.storebytes m1 b1 ofs1 vs1) as [m1'|] eqn:Hm1'; [|constructor].
      edestruct Mem.storebytes_within_extends as (m2' & Hm2' & Hm'); eauto.
      eapply list_rel_forall2. apply Hv.
      rewrite Hm2'. constructor.
      eexists _; split; repeat rstep.
      constructor; auto.
      - eapply krel_invar; eauto.
        eapply Mem.storebytes_unchanged_on; eauto.
        intros ofs' Hofs. intros Hp. specialize (H6 _ _ Hp). apply H6.
        exploit Mem.storebytes_range_perm. apply Hm1'.
        rewrite length_rel; eauto. intros.
        eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. constructor.
      - unfold no_perm_on in *. intros.
        specialize (H6 _ _ H). intros Hp. apply H6.
        eapply Mem.perm_storebytes_2; eauto.
    Qed.
    (* cklr_perm *)
    Next Obligation.
      intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp p' ? H. inv Hm.
      apply coreflexivity in Hp. subst. simpl in *.
      eapply Mem.perm_extends; eauto.
    Qed.
    (* cklr_valid_block *)
    Next Obligation.
      intros [ ] m1 m2 Hm b1 b2 Hb. inv Hm.
      apply coreflexivity in Hb. subst.
      apply Mem.valid_block_extends; eauto.
    Qed.
    (* cklr_no_overlap *)
    Next Obligation.
      intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 Hb Hb1' Hb2' Hp1 Hp2. inv H.
      inv Hb1'. inv Hb2'. eauto.
    Qed.
    (* cklr_representable *)
    Next Obligation. xomega. Qed.
    (* cklr_aligned_area_inject *)
    Next Obligation. rewrite Z.add_0_r. assumption. Qed.
    (* cklr_disjoint_or_equal_inject *)
    Next Obligation. intuition xomega. Qed.
    (* cklr_perm_inv *)
    Next Obligation.
      inv H0. unfold inject_id in *. inv H3.
      replace (ofs1 + 0) with ofs1 in *; try omega.
      inv H. eapply Mem.perm_extends_inv; eauto.
    Qed.
    (* cklr_nextblock_incr *)
    Next Obligation.
      destruct H0 as (w' & Hw' & H'). inv Hw'.
      inv H. inv H'.
      apply Mem.mext_next in H0.
      apply Mem.mext_next in H5.
      rewrite H0. rewrite H5. reflexivity.
    Qed.

  End CKLR.

End KCC.

Section SIMULATION.
  Context {K1 K2} (R: @krel' K2 K1).

  Lemma cont_match_mr w w' k1 k2:
    cont_match (KCC.krel_cklr R) w k1 k2 ->
    cont_match (KCC.krel_cklr R) w' k1 k2.
  Proof.
    induction 1; try constructor; auto.
  Qed.

  Lemma clight_sim p: forward_simulation (krel_kcc R) (krel_kcc R) (semantics2 p @ K1) (semantics2 p @ K2).
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    intros ? se w Hse Hse1. inv Hse. cbn -[semantics2] in *.
    pose (ms := fun '(s1, k1) '(s2, k2) =>
                  Clightrel.state_match (KCC.krel_cklr R) (KCC.kw se k1 k2) s1 s2).
    apply forward_simulation_step with (match_states := ms).
    - intros [q1 k1] [q2 k2] [s1 k1'] Hq Hs1. inv Hq. inv Hs1.
      cbn in *. subst k1'. inv H. cbn in *.
      exists (Callstate vf2 vargs2 Kstop m2, k2). split.
      + constructor; auto. cbn.
        econstructor; eauto.
        * unfold globalenv. cbn.
          exploit (@find_funct_inject p (KCC.krel_cklr R) (KCC.kw se k1 k2) (globalenv se p)).
          split; cbn; eauto.
          eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
          constructor. eauto. intro Hx. apply Hx.
        * eapply val_casted_list_inject; eauto.
        * simpl. eapply match_stbls_nextblock; eauto.
          instantiate (2 := KCC.krel_cklr R). instantiate (1 := KCC.kw se k1 k2).
          constructor. constructor; auto.
      + constructor; auto. cbn.
        apply list_inject_subrel'.
        auto. constructor. constructor; auto.
    - intros [s1 k1] [s2 k2] [r1 k1'] Hs Hfinal.
      inv Hfinal. cbn in *. subst k1'. inv H. inv Hs. inv H5.
      eexists (_, k2). split. split; cbn; auto.
      + inv H4. econstructor.
      + constructor; cbn; auto.
    - intros [s1 k1] [s2 k2] [q1 k1'] Hs Hext.
      inv Hext. cbn in *. subst k1'. inv H. inv Hs. inv H8.
      eexists se, (_, _). repeat apply conj; cbn; eauto.
      + cbn. econstructor.
        exploit (@find_funct_inject p (KCC.krel_cklr R) (KCC.kw se k1 k2) (globalenv se p)).
        split; cbn; eauto.
        eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
        constructor. eauto. intros Hx. subst f. apply Hx.
      + constructor; cbn; auto.
        eapply list_inject_subrel. auto.
        destruct vf; cbn in *; congruence.
      + intros [r1 kr1] [r2 kr2] [s1' k1'] Hr [Hafter H].
        inv Hafter. cbn in *. subst k1'. inv Hr. inv H.
        cbn in *. eexists (_, kr2). split. split; auto.
        cbn. econstructor.
        constructor; auto. eapply cont_match_mr. eauto.
        constructor; auto.
    - intros [s1 k1] t [s1' k1'] Hstep [s2 k2] Hs.
      inv Hstep. cbn in H.
      exploit step2_rel; eauto. unfold genv_match.
      eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
      constructor. intros (s2' & Hstep' & w' & Hw' & Hs').
      exists (s2', k2). inv Hw'. split; auto.
      constructor. apply Hstep'. reflexivity.
    - apply well_founded_ltof.
  Qed.

End SIMULATION.

Unset Asymmetric Patterns.

Inductive krel: Type -> Type -> Type :=
| krel_singleton {K1 K2} : krel' K1 K2 -> krel K1 K2
| krel_compose {K1 K2 K3} : krel K1 K2 -> krel K2 K3 -> krel K1 K3.

Fixpoint krel_cc {K1 K2} (rel: krel K1 K2): callconv (li_c @ K2) (li_c @ K1) :=
  match rel with
  | krel_singleton r => krel_kcc r
  | krel_compose r1 r2 => (krel_cc r2) @ (krel_cc r1)
  end.

Coercion krel_cc : krel >-> callconv.

Lemma clight_krel {K1 K2} (R: krel K2 K1) p:
  forward_simulation R R (Clight.semantics2 p @ K1) (Clight.semantics2 p @ K2).
Proof.
  induction R; simpl.
  - apply clight_sim.
  - eapply compose_forward_simulations; eauto.
Qed.

Require Import SmallstepLinking.
Require Import compcertox.CModule.

Lemma cmodule_krel {K1 K2} (R: @krel K2 K1) M sk:
  skel_module_compatible M sk ->
  forward_simulation R R (semantics M sk @ K1) (semantics M sk @ K2).
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
    + cbn. apply clight_krel.
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
