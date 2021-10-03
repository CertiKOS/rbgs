Require Import Relations RelationClasses Relators.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ Linking.
Require Import Memory Values.
Require Import SimplLocalsproof.
Require Import CKLR Extends.
Require Import Clight_ Clightrel_.
Require Import Lifting.

Definition no_perm_on (m: mem) (vars: block -> Z -> Prop): Prop :=
  forall b ofs, vars b ofs -> ~ Mem.perm m b ofs Max Nonempty.

(* The KRel relation defines the abstraction relation for certified abstraction
   layers. The relation corresponds to the following diagram:

   m1    k1
   |    /|
   |   / |
   | Rr  Rk
   | /   |
   m2    k2

   where part of the concrete values in the target program memory m2 are abstracted
   into the abstract data in k1 *)
Record krel {K1 K2: Type}: Type :=
  mk_krel {
      Rk: K1 -> K2 -> Prop;
      Rr: K1 -> mem -> Prop;
      vars :> ident -> Prop;
      others := fun i => ~ vars i;
      (* location of the static variables *)
      blocks (se: Genv.symtbl) (b: block) (ofs: Z) :=
        exists v, vars v /\ Genv.find_symbol se v = Some b;
      other_blocks (se: Genv.symtbl) (b: block) (ofs: Z) :=
        exists v, others v /\ Genv.find_symbol se v = Some b;
      (* properties *)
      G_unchanged: forall se k1 m m', Rr k1 m -> Mem.unchanged_on (blocks se) m m' -> Rr k1 m';
      G_valid: forall se k1 m b ofs, Rr k1 m -> (blocks se) b ofs -> Mem.valid_block m b;
    }.
Arguments krel: clear implicits.

(* The CKLR is indexed by k1 and it is used to ensure the internal steps of the
   client code won't mess up the blocks in the memory that are abstracted
   according to the KRel. The proof relies on the fact that the source program
   doesn't have permissions on those blocks *)
Section KREL_CKLR.
  Context {K1 K2} (R: @krel K1 K2).

  Inductive krel_world := krelw (se: Genv.symtbl) (k1: K1).
  Inductive krel_mm: krel_world -> mem -> mem -> Prop :=
    match_intro: forall se k1 m1 m2,
      Mem.extends m1 m2 -> Rr R k1 m2 ->
      (* The source program would crash if it tries to manipulate data on blocks
         defined in G *)
      no_perm_on m1 (blocks R se) ->
      krel_mm (krelw se k1) m1 m2.
  Inductive krel_match_se: krel_world -> Genv.symtbl -> Genv.symtbl -> Prop :=
    match_se_intro: forall se k,
      krel_match_se (krelw se k) se se.

  Program Definition krel_cklr: cklr :=
    {|
      world := krel_world;
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
    - eapply G_unchanged; eauto.
      eapply Mem.alloc_unchanged_on; eauto.
    - unfold no_perm_on in *. intros.
      specialize (H5 _ _ H). intros Hp. apply H5.
      eapply Mem.perm_alloc_4 in Hp; eauto.
      eapply Mem.alloc_result in Hm1. subst.
      eapply G_valid in H2; eauto.
      erewrite Mem.mext_next; eauto.
      Unshelve. exact se.
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
    - eapply G_unchanged; eauto.
      eapply Mem.free_unchanged_on; eauto.
      intros ofs Hofs Hv. specialize (H5 _ _ Hv). apply H5.
      exploit Mem.free_range_perm. apply Hm1'. eauto.
      intros Hp. eapply Mem.perm_cur_max.
      eapply Mem.perm_implies. apply Hp. constructor.
    - unfold no_perm_on in *. intros.
      specialize (H5 _ _ H). intros Hp. apply H5.
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
    - eapply G_unchanged; eauto.
      eapply Mem.store_unchanged_on; eauto.
      intros ofs' Hofs. intros Hp. specialize (H5 _ _ Hp). apply H5.
      exploit Mem.store_valid_access_3. apply Hm1'.
      unfold Mem.valid_access. intros [Hpr ?]. specialize (Hpr _ Hofs).
      eapply Mem.perm_cur_max. eapply Mem.perm_implies. apply Hpr. constructor.
    - unfold no_perm_on in *. intros.
      specialize (H5 _ _ H). intros Hp. apply H5.
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
    - eapply G_unchanged; eauto.
      eapply Mem.storebytes_unchanged_on; eauto.
      intros ofs' Hofs. intros Hp. specialize (H5 _ _ Hp). apply H5.
      exploit Mem.storebytes_range_perm. apply Hm1'.
      rewrite length_rel; eauto. intros.
      eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. constructor.
    - unfold no_perm_on in *. intros.
      specialize (H5 _ _ H). intros Hp. apply H5.
      eapply Mem.perm_storebytes_2; eauto.
  Qed.
  (* cklr_perm *)
  Next Obligation.
    intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp p' k H. inv Hm.
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
    apply Mem.mext_next in H4.
    rewrite H0. rewrite H4. reflexivity.
  Qed.

End KREL_CKLR.

(* The self-simulation property for program p given that the scope of p is
   disjoint from the scope of the abstraction relation R. *)
Section SIMULATION.
  Context {K1 K2} (R: krel K1 K2).
  Inductive krel_kcc_query: Genv.symtbl -> query (li_c @ K1) -> query (li_c @ K2) -> Prop :=
    krel_kcc_query_intro se vf1 vf2 sg vargs1 vargs2 m1 m2 k1 k2:
      Val.inject inject_id vf1 vf2 -> Val.inject_list inject_id vargs1 vargs2 ->
      Mem.extends m1 m2 -> vf1 <> Vundef -> no_perm_on m1 (blocks R se) ->
      Rr R k1 m2 -> Rk R k1 k2 ->
      krel_kcc_query se (cq vf1 sg vargs1 m1, k1) (cq vf2 sg vargs2 m2, k2).
  Inductive krel_kcc_reply: Genv.symtbl -> reply (li_c @ K1) -> reply (li_c @ K2) -> Prop :=
    krel_kcc_reply_intro se vres1 m1 vres2 m2 k1 k2:
      Val.inject inject_id vres1 vres2 ->
      Mem.extends m1 m2 -> no_perm_on m1 (blocks R se) ->
      Rr R k1 m2 -> Rk R k1 k2 ->
      krel_kcc_reply se (cr vres1 m1, k1) (cr vres2 m2, k2).

  (* Maybe we could allow an identity injection in match_senv? *)
  Inductive krel_kcc_senv: Genv.symtbl -> Genv.symtbl -> Genv.symtbl -> Prop :=
    krel_kcc_senv_intro se: krel_kcc_senv se se se.

  Instance symtbl_kf: KripkeFrame unit Genv.symtbl :=
    {| acc _ := eq; |}.

  Program Definition krel_kcc: callconv (li_c @ K1) (li_c @ K2) :=
    {|
      ccworld := Genv.symtbl;
      match_senv := krel_kcc_senv;
      match_query := krel_kcc_query;
      (* For simplicity, symbol table should be preserved. We can't use
         accessibility here because that implies the abstract data stays
         intact *)
      match_reply := (<> krel_kcc_reply)%klr;
    |}.
  Next Obligation. inv H. reflexivity. Qed.
  Next Obligation. inv H. auto. Qed.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  Lemma val_casted_list_inject f vargs vargs' targs:
    Cop.val_casted_list vargs targs ->
    Val.inject_list f vargs vargs' ->
    Cop.val_casted_list vargs' targs.
  Proof.
    intro H. revert vargs'.
    induction H; inversion 1; subst; constructor; eauto.
    eapply val_casted_inject; eauto.
  Qed.

  Lemma list_inject_subrel' f:
    Related (Val.inject_list f) (list_rel (Val.inject f)) subrel.
  Proof.
    intros x y H. induction H; constructor; auto.
  Qed.

  Lemma cont_match_mr w w' k1 k2:
    cont_match (krel_cklr R) w k1 k2 ->
    cont_match (krel_cklr R) w' k1 k2.
  Proof.
    induction 1; try constructor; auto.
  Qed.

  (* for the self-simulation it is not necessary to require disjoint scope. If p
     and G interfere with each other, the source program would fail. *)
  Lemma clight_sim p: forward_simulation krel_kcc krel_kcc (semantics2 p @ K1) (semantics2 p @ K2).
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    intros ? se w Hse Hse1. inv Hse. cbn -[semantics2] in *.
    pose (ms := fun '(s1, k1) '(s2, k2) =>
                  Clightrel_.state_match (krel_cklr R) (krelw se k1) s1 s2 /\ Rk R k1 k2).
    apply forward_simulation_step with (match_states := ms).
    - intros [q1 k1] [q2 k2] [s1 k1'] Hq Hs1. inv Hq. inv Hs1.
      cbn in *. subst k1'. inv H. cbn in *.
      exists (Callstate vf2 vargs2 Kstop m2, k2). split.
      + constructor; auto. cbn.
        econstructor; eauto.
        * unfold globalenv. cbn.
          exploit (@find_funct_inject p (krel_cklr R) (krelw se k1) (globalenv se p)).
          split; cbn; eauto.
          eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
          constructor. eauto. intro Hx. apply Hx.
        * eapply val_casted_list_inject; eauto.
        * simpl. eapply match_stbls_nextblock; eauto.
          instantiate (2 := krel_cklr R). instantiate (1 := krelw se k1).
          constructor. constructor; auto.
      + split; auto.
        constructor; auto. cbn.
        apply list_inject_subrel'.
        auto. constructor. constructor; auto.
    - intros [s1 k1] [s2 k2] [r1 k1'] (Hs & Hk) Hfinal.
      inv Hfinal. cbn in *. subst k1'. inv H. inv Hs.
      eexists (_, k2). split. split; cbn; auto.
      + inv H4. econstructor.
      + exists se. constructor; cbn; auto.
        inv H5. constructor; eauto.
    - intros [s1 k1] [s2 k2] [q1 k1'] (Hs & Hk) Hext.
      inv Hext. cbn in *. subst k1'. inv H. inv Hs.
      eexists se, (_, _). repeat apply conj; cbn; eauto.
      + cbn. econstructor.
        exploit (@find_funct_inject p (krel_cklr R) (krelw se k1) (globalenv se p)).
        split; cbn; eauto.
        eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
        constructor. eauto. intros Hx. subst f. apply Hx.
      + inv H8. constructor; cbn; auto.
        eapply list_inject_subrel. auto.
        destruct vf; cbn in *; congruence.
      + constructor.
      + intros [r1 kr1] [r2 kr2] [s1' k1'] [w' Hr] Hafter.
        inv Hafter. cbn in *. subst k1'. inv H.
        destruct Hr as [<- Hr]. inv Hr. inv H8.
        cbn in *. eexists (_, kr2). split. split; auto.
        cbn. econstructor. split; auto.
        constructor; auto. eapply cont_match_mr. eauto.
        constructor; auto.
    - intros [s1 k1] t [s1' k1'] Hstep [s2 k2] [Hs Hk].
      inv Hstep. cbn in H.
      exploit step2_rel; eauto. unfold genv_match.
      eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
      constructor. intros (s2' & Hstep' & w' & Hw' & Hs').
      exists (s2', k2). inv Hw'. split; split; auto.
    - apply well_founded_ltof.
  Qed.
End SIMULATION.

(* FIXME: this probably gets function definitions involved. But they are not
   supposed to be changed anycase *)
Definition all_vars (se: Genv.symtbl) (b: block) (ofs: Z) :=
  exists v, Genv.find_symbol se v = Some b.

Section KREL_MCC.
  Context {K1 K2} (R: krel K1 K2).

  Inductive mkrel_world := mkrelw (se:Genv.symtbl) (w: mem * mem).

  Inductive mkrel_world_acc: mkrel_world -> mkrel_world -> Prop :=
  | mkrel_world_acc_intro se m1 m2 m1' m2':
      Mem.unchanged_on (all_vars se) m1 m1' ->
      Mem.unchanged_on (other_blocks R se) m2 m2' ->
      mkrel_world_acc (mkrelw se (m1, m2)) (mkrelw se (m1', m2')).

  Instance mkrel_kframe: KripkeFrame unit mkrel_world :=
    {| acc _ := mkrel_world_acc; |}.

  Inductive mkrel_query: mkrel_world -> query (li_c@K1) -> query (li_c@K2) -> Prop :=
  | mkrel_query_intro se vf1 sg vargs1 m1 vf2 vargs2 m2 k1 k2:
      Val.inject inject_id vf1 vf2 ->
      Val.inject_list inject_id vargs1 vargs2 ->
      vf1 <> Vundef ->
      Mem.extends m1 m2 -> no_perm_on m1 (blocks R se) ->
      Rr R k1 m2 -> Rk R k1 k2 ->
      mkrel_query (mkrelw se (m1, m2)) (cq vf1 sg vargs1 m1, k1) (cq vf2 sg vargs2 m2, k2).

  Inductive mkrel_reply: mkrel_world -> reply (li_c@K1) -> reply (li_c@K2) -> Prop :=
  | mkrel_reply_intro se retval1 m1 retval2 m2 k1 k2:
      Val.inject inject_id retval1 retval2 ->
      Mem.extends m1 m2 -> no_perm_on m1 (blocks R se) ->
      Rr R k1 m2 -> Rk R k1 k2 ->
      mkrel_reply (mkrelw se (m1, m2)) (cr retval1 m1, k1) (cr retval2 m2, k2).

  Inductive mkrel_match_se: mkrel_world -> Genv.symtbl -> Genv.symtbl -> Prop :=
  | mkrel_match_se_intro: forall se mm,
      mkrel_match_se (mkrelw se mm) se se.

  (* A calling convention derived from a krel indexed by the target program memory *)
  Program Definition krel_mcc: callconv (li_c@K1) (li_c@K2) :=
    {|
      ccworld := mkrel_world;
      match_senv := mkrel_match_se;
      match_query := mkrel_query;
      match_reply := (<> mkrel_reply)%klr;
    |}.
  Next Obligation. inv H. reflexivity. Qed.
  Next Obligation. now inv H. Qed.
  Next Obligation.
    inv H. inv H0. cbn.
    apply val_inject_id in H6. inv H6.
    reflexivity. easy.
  Qed.
  Next Obligation.
    inv H.  cbn.
    apply val_inject_id in H4. inv H4.
    reflexivity. easy.
  Qed.

End KREL_MCC.

Section PROD.
  Context {K1 K2 K3 K4} (R1: krel K1 K2) (R2: krel K3 K4).
  Program Definition prod_krel: krel (K1*K3) (K2*K4) :=
    {|
      Rk '(k1, k3) '(k2, k4) := Rk R1 k1 k2 /\ Rk R2 k3 k4;
      Rr '(k1, k3) m := Rr R1 k1 m /\ Rr R2 k3 m;
      vars i := vars R1 i \/ vars R2 i;
    |}.
  Next Obligation.
    split; eapply G_unchanged; eauto; eapply Mem.unchanged_on_implies; eauto;
      intros; unfold blocks in *; cbn in *.
    - destruct H2 as [? [? ?]]. eexists; split; eauto.
    - destruct H2 as [? [? ?]]. eexists; split; eauto.
  Qed.
  Next Obligation.
    destruct H2; [ eapply (G_valid R1) | eapply (G_valid R2) ]; eauto.
    - eexists; split; eauto.
    - eexists; split; eauto.
      Unshelve. exact ofs. exact ofs.
  Qed.

  Lemma other_blocks_implies se b ofs:
    other_blocks R1 se b ofs -> (forall r, R2 r -> R1 r) -> other_blocks R2 se b ofs.
  Proof.
    unfold other_blocks, others. intros [v [? ?]] Hv.
    eexists; split; eauto.
  Qed.

  Lemma blocks_either se b ofs:
    blocks prod_krel se b ofs -> blocks R1 se b ofs \/ blocks R2 se b ofs.
  Proof.
    intros [v [[Hv|Hv] Hb]]; [left|right]; eexists; split; eauto.
  Qed.

  Lemma blocks_implies se b ofs:
    blocks R1 se b ofs -> (forall r, R1 r -> R2 r) -> blocks R2 se b ofs.
  Proof.
    unfold blocks. intros [v [? ?]] Hv.
    eexists; split; eauto.
  Qed.
End PROD.

Infix "*" := prod_krel.
Coercion krel_mcc : krel >-> callconv.


Section Properties.

  Context {K1 K2 K3 K4} (R1: krel K1 K2) (R2: krel K3 K4).
  Hypothesis Hdisjoint: forall i, R1 i -> R2 i -> False.

  Lemma prod_match_reply se m1 m2 r1 r2 k1 k2 k3 k4:
    match_reply R1 (mkrelw se (m1, m2)) (r1, k1) (r2, k2) ->
    Rk R2 k3 k4 -> Rr R2 k3 m2 ->
    no_perm_on m1 (blocks R2 se) -> Mem.extends m1 m2 ->
    match_reply (R1 * R2) (mkrelw se (m1, m2)) (r1, (k1, k3)) (r2, (k2, k4)).
  Proof.
    intros [w' [Hw Hr]] Hk Hkm Hperm Hm.
    exists w'; inv Hw; split.
    - cbn in *.  constructor; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      cbn in *. intros. eapply other_blocks_implies; eauto.
      intros. now left.
    - inv Hr. cbn in *. constructor; eauto.
      + intros b ofs Hb. apply blocks_either in Hb as [Hv|Hv].
        * unfold no_perm_on in *. intuition eauto.
        * unfold no_perm_on in *. intros contra.
          specialize (Hperm b ofs Hv). apply Hperm.
          eapply Mem.perm_unchanged_on_2; intuition eauto.
          destruct Hv as [v [Hv Hb]]. eexists; eauto.
          apply Mem.perm_valid_block in contra.
          erewrite Mem.valid_block_extends; [ | eauto].
          eapply (G_valid R2); eauto.
      + split; eauto. eapply G_unchanged; eauto.
        eapply Mem.unchanged_on_implies. intuition eauto.
        cbn. intros. destruct H as [v [Hv Hb]]. eexists; split; eauto.
        unfold others. intros contra. eapply Hdisjoint; eauto.
      + split; eauto.
  Qed.

  Lemma prod_match_query se m1 m2 q1 q2 k1 k2 k3 k4:
    match_query (R1 * R2) (mkrelw se (m1, m2)) (q1, (k1, k3)) (q2, (k2, k4)) ->
    match_query R1 (mkrelw se (m1, m2)) (q1, k1) (q2, k2) /\ Rk R2 k3 k4 /\ Rr R2 k3 m2 /\
    no_perm_on m1 (blocks R2 se) /\ Mem.extends m1 m2.
  Proof.
    intros. inv H. repeat apply conj; cbn in *; intuition.
    constructor; eauto.
    - intros b ofs Hg. apply H11. eapply blocks_implies. eauto.
      intuition. now left.
    - intros b ofs Hg. apply H11. eapply blocks_implies. eauto.
      intuition. now right.
  Qed.

  Lemma match_query_comm w q1 q2 k1 k2 k3 k4:
    match_query (R2 * R1) w (q1, (k3, k1)) (q2, (k4, k2)) ->
    match_query (R1 * R2) w (q1, (k1, k3)) (q2, (k2, k4)).
  Proof.
    intros. inv H. constructor; auto.
    - intros b ofs Hg. apply H9. eapply blocks_implies; eauto.
      intros i [|]; [right|left]; auto.
    - cbn in *. intuition.
    - cbn in *. intuition.
  Qed.

  Lemma match_reply_comm w r1 r2 k1 k2 k3 k4:
    match_reply (R2 * R1) w (r1, (k3, k1)) (r2, (k4, k2)) ->
    match_reply (R1 * R2) w (r1, (k1, k3)) (r2, (k2, k4)).
  Proof.
    intros [w' [Hw H]]. exists w'. inv Hw. inv H. split.
    - cbn in *. constructor; eauto.
      eapply Mem.unchanged_on_implies. eauto.
      intros. eapply other_blocks_implies. eauto.
      intros i [|]; [right|left]; auto.
    - econstructor; auto.
      + cbn in *. intros b ofs Hv. apply H11.
        eapply blocks_implies; eauto.
        intros i [|]; [right|left]; auto.
      + cbn in *. intuition.
      + cbn in *. intuition.
  Qed.

End Properties.

Generalizable All Variables.

(* A vertically compositional abstraction relation *)
Inductive crel: Type -> Type -> Type :=
| empty_rel K: crel K K
| singleton_rel `(krel K1 K2): crel K1 K2
| vcomp_rel `(crel K1 K2) `(crel K2 K3): crel K1 K3.

Fixpoint crel_to_cc {K1 K2} (rel: crel K1 K2): callconv (li_c @ K1) (li_c @ K2) :=
  match rel with
  | empty_rel _ => cc_id | singleton_rel _ _ r => krel_kcc r
  | vcomp_rel _ _ r1 _ r2 => (crel_to_cc r1) @ (crel_to_cc r2)
  end.

Delimit Scope krel_scope with krel.
Bind Scope krel_scope with crel.

Notation "[ R ]" := (singleton_rel R) (at level 30): krel_scope.
Notation "R1 ∘ R2" := (vcomp_rel R1 R2): krel_scope.

Coercion crel_to_cc : crel >-> callconv.

Lemma clight_krel {K1 K2} (R: crel K1 K2) p:
  forward_simulation R R (Clight_.semantics2 p @ K1) (Clight_.semantics2 p @ K2).
Proof.
  induction R; simpl.
  - apply lifting_simulation.
    apply identity_forward_simulation.
  - apply clight_sim.
  - eapply compose_forward_simulations; eauto.
Qed.

Module MCC.
  (* An absfun client makes no change to memory blocks *)
  Section PURE_CLIENT_CKLR.

    Inductive pure_mm: mkrel_world -> mem -> mem -> Prop :=
    | match_intro se m1 m2:
        no_perm_on m1 (all_vars se) ->
        Mem.extends m1 m2 ->
        pure_mm (mkrelw se (m1, m2)) m1 m2.

    Inductive pure_world_acc: mkrel_world -> mkrel_world -> Prop :=
    | cklr_world_acc_intro se m1 m2 m1' m2':
        Mem.unchanged_on (all_vars se) m1 m1' ->
        Mem.unchanged_on (all_vars se) m2 m2' ->
        pure_world_acc (mkrelw se (m1, m2)) (mkrelw se (m1', m2')).

    Program Definition pure_cklr: cklr :=
    {|
      world := mkrel_world;
      wacc := pure_world_acc;
      mi w := inject_id;
      match_mem := pure_mm;
      match_stbls := mkrel_match_se;
    |}.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.

  End PURE_CLIENT_CKLR.

  Section SIM.
    Context {K1 K2} (R: krel K1 K2).
    (* The underlay calls may update the corresponding part in memory *)
    Inductive client_world_acc: mkrel_world -> mkrel_world -> Prop :=
    | client_world_acc_intro se m1 m2 m1' m2':
        Mem.unchanged_on (all_vars se) m1 m1' ->
        Mem.unchanged_on (other_blocks R se) m2 m2' ->
        client_world_acc (mkrelw se (m1, m2)) (mkrelw se (m1', m2')).

    Instance client_kf: KripkeFrame unit mkrel_world :=
      {| acc _ := client_world_acc; |}.

    Inductive state_rel: K1 -> state -> Prop :=
    | State_rel f s k e le m k1:
        Rr R k1 m -> state_rel k1 (State f s k e le m)
    | Callstate_rel vf args k m k1:
        Rr R k1 m -> state_rel k1 (Callstate vf args k m)
    | Returnstate_rel res k m k1:
        Rr R k1 m -> state_rel k1 (Returnstate res k m).

    Lemma cont_match_mr w w' k1 k2:
      cont_match pure_cklr w k1 k2 ->
      cont_match pure_cklr w' k1 k2.
    Proof.
      induction 1; try constructor; auto.
    Qed.

    Lemma clight_sim p: forward_simulation R R (semantics2 p @ K1) (semantics2 p @ K2).
    Proof.
      constructor. econstructor; eauto. intros i; reflexivity.
      instantiate (1 := fun _ _ _ => _). cbn beta.
      intros ? se w Hse Hse1. inv Hse. cbn -[semantics2] in *.
      pose (ms := fun '(s1, k1) '(s2, k2) =>
                    klr_diam (kf := client_kf) tt
                             (Clightrel_.state_match pure_cklr)
                             (mkrelw se mm) s1 s2
                    /\ Rk R k1 k2 /\ state_rel k1 s2).
      apply forward_simulation_step with (match_states := ms).
      - intros [q1 k1] [q2 k2] [s1 k1'] Hq Hs1. inv Hq. inv Hs1.
        cbn [fst snd] in *. subst k1'. inv H. exists (Callstate vf2 vargs2 Kstop m2, k2). split.
        + constructor; cbn; auto. econstructor; eauto.
          * unfold globalenv. cbn.
            exploit (@find_funct_inject p pure_cklr (mkrelw se (m1, m2)) (globalenv se p)).
            split; cbn; eauto.
            eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
            constructor. eauto. intro Hx. apply Hx.
          * eapply val_casted_list_inject; eauto.
          * simpl. eapply match_stbls_nextblock; eauto.
            instantiate (2 := pure_cklr). instantiate (1 := mkrelw se (m1, m2)).
            constructor. constructor; auto.
        + split; auto. exists (krelw se (m1, m2)); split. constructor; apply Mem.unchanged_on_refl.
          constructor; try constructor; eauto. now apply list_inject_subrel'.
          split; auto. constructor; auto.
      - intros [s1 k1] [s2 k2] [r1 kr1] [Hs Hk] Hfinal. inv Hfinal.
        cbn [fst snd] in *. subst kr1. inv H. destruct Hs as [w' [Hw' Hs]].
        inv Hs. inv H4. inv H5. destruct w as [m1 m2].
        rename m into m1'. rename y1 into m2'.
        cbn in *. inv Hw'. eexists (_, k2). split.
        + split; auto. cbn. constructor.
        + exists (m1', m2'). split.
          * constructor; auto.
          * constructor; destruct Hk as [? Hk]; auto. now inv Hk.
      - intros [s1 ks1] [s2 ks2] [q1 kq1] [Hs Hk] Hext. inv Hext.
        cbn [fst snd] in *. subst kq1. inv H. destruct Hs as [w' [Hw' Hs]].
        inv Hw'. exists (m1', m2'). inv Hs. eexists (_, _). repeat apply conj; cbn; eauto.
        + econstructor.
          exploit (@find_funct_inject p (krel_cklr R) (krelw se (m1', m2')) (globalenv se p)).
          split; cbn; eauto.
          eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
          constructor. eauto. intros Hx. subst f. apply Hx.
        + inv H10. constructor; destruct Hk as [Hkr Hrr]; eauto; cbn in *.
          eapply list_inject_subrel. auto.
          destruct vf; cbn in *; congruence.
          eapply G_unchanged; eauto. inv Hrr. eauto.
          eapply Mem.unchanged_on_refl.
        + intros [r1 kr1] [r2 kr2] [s1' k1'] [w'' [Hw'' Hr]] H.
          destruct w'' as [m1'' m2'']. destruct H as [H Hkk].
          cbn [fst snd] in *. subst k1'. inv H. inv Hr. eexists (_, kr2).
          split. split; cbn; auto.
          * econstructor.
          * repeat apply conj; auto; try constructor; auto.
            exists (krelw se (m', m2'')). split.
            -- split. destruct Hw''. eapply Mem.unchanged_on_trans; eauto.
               destruct Hw''. eapply Mem.unchanged_on_trans; eauto.
            -- constructor; auto.
               eapply cont_match_mr. eauto.
               constructor; eauto.
      - intros [s1 k1] t [s1' k1'] Hstep [s2 k2] [Hs Hk].
        inv Hstep. cbn in H. destruct Hs as [w' [Hw' Hs]].
        destruct w'. inv Hw'.
        exploit step2_rel; eauto.
        {
          unfold genv_match.
          eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
          constructor.
        }
        intros (s2' & Hstep' & w' & Hw' & Hs').
        exists (s2', k2). inv Hw'. split; split; auto.
        exists (krelw se0 (m1'0, m2'0)). split; auto.
        split; eapply Mem.unchanged_on_trans; eauto.
        eapply Mem.unchanged_on_implies; eauto. intuition.
        split; destruct Hk as [? Hk]; auto.
        clear -Hs Hs' Hk H7.
        inv Hk; inv Hs; inv Hs';
        repeat (match goal with
                | [ H: match_mem _ _ _ _ |- _ ] => inv H
                end);
        constructor; eapply G_unchanged; eauto; eapply Mem.unchanged_on_implies; intuition eauto.
      - apply well_founded_ltof.
    Qed.

  End SIM.

End MCC.

(*

   There are two kinds of calling convention that are derived from an
   abstraction relation R. kcc denotes the one indexed by the source program
   abstract data K1 (the index is not used for calling convention though) and
   mcc denotes the one indexed by the target program memory.

   The commonalities: both calling conventions are based on memory extension and
   they require the abstraction relation between the abstract data and the
   memory holds in both queries and replies.

   The kcc convention is the most basic relation on queries and replies, which
   is essentially a naive embedding of the abstraction relation.

   The first problem we encounter is running the client code on top of certified
   layers. Across two consecutive external calls to the underlay, the abstract
   data is unchanged because the lifted semantics simply threads through the
   abstract data. Therefore, the internal steps of the client code can't modify
   the variables of the underlay (otherwise the queries won't match when it
   calls the underlay). To prove this property, we exploit the CKLR which
   abstracts out the key properties to ensure the internal steps preserve a
   particular relation.

   The vertical composition doesn't have the inconsistency issue because the
   composition of calling conventions is essentially treating (m,k) as a
   whole. The inconsistency issue pops up when we try to define the relations in
   the abstraction relation separately, i.e. to define relation between abstract
   data and relation between abstract data and memory separately.

   The second problem is to horizontally compose abstraction relations. To
   ensure the execution of one component doesn't mess up the other abstraction
   relation, we need to strengthen the calling convention to guarantee the
   variables not belong to the component are unchanged throughout the
   transition. However, such calling conventions do not compose.

   The third problem is to compose an absfun layer with an underlay and the mcc
   calling convention is maintained. So the client code can't touch the
   variables belong to the underlay (for the same reason in vertical
   composition) and it can't change other part of the memory as well (otherwise
   the mcc convention can't be preserved)

   The horizontally compositional layers have the abstraction relation
   interpreted as mcc. When the layer is ready for vertical composition the mcc
   is refined to kcc. Note that the refinement is only for one direction. In the
   section, we prove the refinement. *)

Require Import CallconvAlgebra_.

Section CC_REF.

  Context {K1 K2: Type} (R: @krel K1 K2).
  Context (L1: layer K1) (L2: layer K2).

  Definition layer_fsim_kcc := forward_simulation 1 (krel_kcc R) L1 L2.
  Definition layer_fsim_mcc := forward_simulation 1 (krel_mcc R) L1 L2.

  Lemma kcc_ref_mcc: ccref (krel_kcc R) (krel_mcc R).
  Proof.
    unfold ccref. intros w se1 se2 [q1 k1] [q2 k2] Hse Hq.
    inv Hse. inv Hq. inv H4. cbn in *. exists (m1, m2). repeat apply conj; auto.
    - constructor; eauto. inv H1. auto. inv H1. auto.
    - intros [r1 kr1] [r2 kr2] [w' [Hw' Hr]].
      destruct w' as [m1' m2']. cbn in *.
      inv Hr. exists kr1. constructor; auto.
      constructor; auto. constructor; auto.
  Qed.

  Lemma layer_fsim_refine: layer_fsim_mcc -> layer_fsim_kcc.
  Proof.
    apply open_fsim_ccref. reflexivity. unfold flip. apply kcc_ref_mcc.
  Qed.

End CC_REF.
