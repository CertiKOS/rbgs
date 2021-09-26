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
      G: block -> Z -> Prop;         (* private variables *)

      G_unchanged: forall k1 m m', Rr k1 m -> Mem.unchanged_on G m m' -> Rr k1 m';
      G_valid: forall k1 m b ofs, Rr k1 m -> G b ofs -> Mem.valid_block m b;
    }.
Arguments krel: clear implicits.

(* The CKLR is indexed by k1 with accessibility condition simply being equality
   so that the internal steps won't mess up the blocks in the memory that are
   abstracted according to the KRel *)
Section KREL_CKLR.
  Context {K1 K2} (R: @krel K1 K2).

  Inductive krel_world := krelw (se: Genv.symtbl) (k1: K1).
  Inductive krel_mm: krel_world -> mem -> mem -> Prop :=
    match_intro: forall se k1 m1 m2,
      Mem.extends m1 m2 -> Rr R k1 m2 ->
      (* The source program would crash if it tries to manipulate data on blocks
         defined in G *)
      no_perm_on m1 (G R) ->
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
  Inductive krel_cc_query cc_query:
    krel_world -> query (li_c @ K1) -> query (li_c @ K2) -> Prop :=
    krel_cc_query_intro se q1 k1 q2 k2:
      cc_query (krelw se k1) q1 q2 -> Rr R k1 (cq_mem q2) -> Rk R k1 k2 ->
      krel_cc_query cc_query (krelw se k1) (q1, k1) (q2, k2).
  Inductive krel_cc_reply cc_reply:
    krel_world -> reply (li_c @ K1) -> reply (li_c @ K2) -> Prop :=
    krel_cc_reply_intro se r1 k1 r2 k2:
      cc_reply (krelw se k1) r1 r2 -> Rr R k1 (cr_mem r2) -> Rk R k1 k2 ->
      krel_cc_reply cc_reply (krelw se k1) (r1, k1) (r2, k2).

  (* Promoting an abstraction relation to a memory extension based calling
     convention *)
  Coercion krel_cklr : krel >-> cklr.

  (* A calling convention derived from a krel indexed by the abstract data K *)
  Program Definition krel_kcc: callconv (li_c @ K1) (li_c @ K2) :=
    {|
      ccworld := world R;
      match_senv := match_stbls R;
      match_query := krel_cc_query (cc_c_query R);
      (* For simplicity, symbol table should be preserved. We can't use
         accessibility here because that implies the abstract data stays
         intact *)
      match_reply w r1 r2 :=
        match w with
        | krelw se _ => exists k, krel_cc_reply (cc_c_reply R) (krelw se k) r1 r2
        end;
    |}.
  Next Obligation. inv H. reflexivity. Qed.
  Next Obligation. inv H. auto. Qed.
  Next Obligation.
    inv H0. eapply (match_senv_symbol_address (cc_c R)); eauto.
  Qed.
  Next Obligation.
    inv H. eapply (match_query_defined (cc_c R)); eauto.
  Qed.

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
    cont_match R w k1 k2 ->
    cont_match R w' k1 k2.
  Proof.
    induction 1; try constructor; auto.
  Qed.

  (* for the self-simulation it is not necessary to require disjoint scope. If p
     and G interfere with each other, the source program would fail. *)
  Lemma clight_sim p: forward_simulation krel_kcc krel_kcc (semantics1 p @ K1) (semantics1 p @ K2).
  Proof.
    constructor. econstructor; eauto.
    intros i. reflexivity.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    intros ? se w Hse Hse1. inv Hse. cbn -[semantics1] in *.
    pose (ms := fun '(s1, k1) '(s2, k2) =>
                  Clightrel_.state_match R (krelw se k1) s1 s2 /\ Rk R k1 k2).
    apply forward_simulation_step with (match_states := ms).
    - intros [q1 k1] [q2 k2] [s1 k1'] Hq Hs1. inv Hq. inv Hs1.
      cbn in *. subst k1'. inv H. inv H4. cbn in *.
      exists (Callstate vf2 vargs2 Kstop m2, k2). split.
      + constructor; auto. cbn.
        econstructor; eauto.
        * unfold globalenv. cbn.
          exploit (@find_funct_inject p R (krelw se k1) (globalenv se p)).
          split; cbn; eauto.
          eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
          constructor. eauto. intro Hx. apply Hx.
        * eapply val_casted_list_inject; eauto.
        * simpl. eapply match_stbls_nextblock; eauto.
          instantiate (2 := R). instantiate (1 := krelw se k1).
          constructor. apply H13.
      + split; auto.
        constructor; auto. cbn.
        apply list_inject_subrel'.
        auto. constructor.
    - intros [s1 k1] [s2 k2] [r1 k1'] (Hs & Hk) Hfinal.
      inv Hfinal. cbn in *. subst k1'. inv H. inv Hs.
      eexists (_, k2). split. split; cbn; auto.
      + inv H4. econstructor.
      + exists k1. constructor; cbn; auto.
        constructor; eauto.
        inv H5. auto.
    - intros [s1 k1] [s2 k2] [q1 k1'] (Hs & Hk) Hext.
      inv Hext. cbn in *. subst k1'. inv H. inv Hs.
      eexists (krelw se k1), (_, _). repeat apply conj; cbn; eauto.
      + cbn. econstructor.
        exploit (@find_funct_inject p R (krelw se k1) (globalenv se p)).
        split; cbn; eauto.
        eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
        constructor. eauto. intros Hx. subst f. apply Hx.
      + constructor; cbn; auto.
        constructor; auto. cbn in *.
        eapply list_inject_subrel. auto.
        destruct vf; cbn in *; congruence.
        inv H8. auto.
      + constructor.
      + intros [r1 kr1] [r2 kr2] [s1' k1'] [w' Hr] Hafter.
        inv Hafter. cbn in *. subst k1'. inv H. inv Hr. inv H9.
        cbn in *. eexists (_, kr2). split. split; auto.
        cbn. econstructor. split; auto.
        constructor; auto. eapply cont_match_mr. eauto.
    - intros [s1 k1] t [s1' k1'] Hstep [s2 k2] [Hs Hk].
      inv Hstep. cbn in H.
      exploit step1_rel; eauto. unfold genv_match.
      eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
      constructor. intros (s2' & Hstep' & w' & Hw' & Hs').
      exists (s2', k2). inv Hw'. split; split; auto.
    - apply well_founded_ltof.
  Qed.
End SIMULATION.

Section KREL_MCC.
  Context {K1 K2} (R: krel K1 K2).

  Let krel_world := (mem * mem)%type.
  (* The permissions in the source memory are preserved and the blocks do not
     belong to the transition system are not modified in the target memory *)
  Instance krel_kframe: KripkeFrame unit krel_world :=
    {|
      acc _ '(m1, m2) '(m1', m2'):=
        Mem.unchanged_on (fun _ _ => True) m1 m1' /\ Mem.unchanged_on (fun b ofs => ~ G R b ofs) m2 m2';
    |}.

  Inductive krel_query: krel_world -> query (li_c@K1) -> query (li_c@K2) -> Prop :=
  | krel_query_intro vf1 sg1 vargs1 m1 vf2 sg2 vargs2 m2 k1 k2:
      Val.inject inject_id vf1 vf2 ->
      Val.inject_list inject_id vargs1 vargs2 ->
      vf1 <> Vundef ->
      Mem.extends m1 m2 -> no_perm_on m1 (G R) ->
      Rr R k1 m2 -> Rk R k1 k2 ->
      krel_query (m1, m2) (cq vf1 sg1 vargs1 m1, k1) (cq vf2 sg2 vargs2 m2, k2).

  (* Add the source memory to the index if we need to prove the permissions
       are preserved *)
  Inductive krel_reply: krel_world -> reply (li_c@K1) -> reply (li_c@K2) -> Prop :=
  | krel_reply_intro retval1 m1 retval2 m2 k1 k2:
      Val.inject inject_id retval1 retval2 ->
      Mem.extends m1 m2 -> no_perm_on m1 (G R) ->
      Rr R k1 m2 -> Rk R k1 k2 ->
      krel_reply (m1, m2) (cr retval1 m1, k1) (cr retval2 m2, k2).

  (* A calling convention derived from a krel indexed by the target program memory *)
  Program Definition krel_mcc: callconv (li_c@K1) (li_c@K2) :=
    {|
      ccworld := krel_world;
      match_senv _ := eq;
      match_query := krel_query;
      match_reply := (<> krel_reply)%klr;
    |}.
  Next Obligation. inv H0. cbn. apply val_inject_id in H4. now inv H4. Qed.
  Next Obligation. inv H. cbn. apply val_inject_id in H4. now inv H4. Qed.

End KREL_MCC.

Section PROD.
  Context {K1 K2 K3 K4} (R1: krel K1 K2) (R2: krel K3 K4).
  Program Definition prod_krel: krel (K1*K3) (K2*K4) :=
    {|
      Rk '(k1, k3) '(k2, k4) := Rk R1 k1 k2 /\ Rk R2 k3 k4;
      Rr '(k1, k3) m := Rr R1 k1 m /\ Rr R2 k3 m;
      G b ofs := G R1 b ofs \/ G R2 b ofs;
    |}.
  Next Obligation.
    split; eapply G_unchanged; eauto; eapply Mem.unchanged_on_implies; eauto;
      intros; cbn; [left | right]; auto.
  Qed.
  Next Obligation.
    destruct H0; [ eapply (G_valid R1) | eapply (G_valid R2) ]; eauto.
  Qed.

End PROD.

Infix "*" := prod_krel.
Coercion krel_mcc : krel >-> callconv.

Section Properties.

  Context {K1 K2 K3 K4} (R1: krel K1 K2) (R2: krel K3 K4).
  Hypothesis Hdisjoint: forall b ofs, G R1 b ofs -> G R2 b ofs -> False.

  Lemma prod_match_reply w r1 r2 k1 k2 k3 k4:
    match_reply R1 w (r1, k1) (r2, k2) -> Rk R2 k3 k4 -> Rr R2 k3 (snd w) ->
    no_perm_on (fst w) (G R2) -> Mem.extends (fst w) (snd w) ->
    match_reply (R1 * R2) w (r1, (k1, k3)) (r2, (k2, k4)).
  Proof.
    intros [w' [Hw Hr]] H.
    exists w'; destruct w as [m1 m2]; destruct w' as [m1' m2']; split.
    - cbn in *. intuition.
      eapply Mem.unchanged_on_implies; eauto.
      cbn in *. intros. firstorder.
    - inv Hr. cbn in *. constructor; eauto.
      + intros b ofs [Hv | Hv].
        * unfold no_perm_on in *. intuition eauto.
        * unfold no_perm_on in *. intros contra.
          specialize (H1 b ofs Hv). apply H1.
          eapply Mem.perm_unchanged_on_2; intuition eauto.
          apply Mem.perm_valid_block in contra.
          erewrite Mem.valid_block_extends; [ | eauto].
          eapply (G_valid R2); eauto.
      + split; eauto. eapply G_unchanged; eauto.
        eapply Mem.unchanged_on_implies. intuition eauto.
        cbn. intros. intuition eauto.
      + split; eauto.
  Qed.

  Lemma prod_match_query w q1 q2 k1 k2 k3 k4:
    match_query (R1 * R2) w (q1, (k1, k3)) (q2, (k2, k4)) ->
    match_query R1 w (q1, k1) (q2, k2) /\ Rk R2 k3 k4 /\ Rr R2 k3 (snd w) /\
    no_perm_on (fst w) (G R2) /\ Mem.extends (fst w) (snd w).
  Proof.
    intros. inv H. repeat apply conj; cbn in *; intuition.
    constructor; eauto.
    - intros b ofs Hg. apply H9. now left.
    - intros b ofs Hg. apply H9. now right.
  Qed.

  Lemma match_query_comm w q1 q2 k1 k2 k3 k4:
    match_query (R2 * R1) w (q1, (k3, k1)) (q2, (k4, k2)) ->
    match_query (R1 * R2) w (q1, (k1, k3)) (q2, (k2, k4)).
  Proof.
    intros. inv H. constructor; auto.
    - intros b ofs Hg. apply H9. cbn in *. intuition.
    - cbn in *. intuition.
    - cbn in *. intuition.
  Qed.

  Lemma match_reply_comm w r1 r2 k1 k2 k3 k4:
    match_reply (R2 * R1) w (r1, (k3, k1)) (r2, (k4, k2)) ->
    match_reply (R1 * R2) w (r1, (k1, k3)) (r2, (k2, k4)).
  Proof.
    intros [w' [Hw H]].
    exists w'; destruct w as [m1 m2]; destruct w' as [m1' m2']; split.
    - cbn in *. intuition eauto. eapply Mem.unchanged_on_implies. eauto. cbn. intuition.
    - inv H. econstructor; auto.
      + cbn in *. intros b ofs Hv. apply H8. destruct Hv; intuition.
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
Coercion singleton_rel : krel >-> crel.

Lemma clight_krel {K1 K2} (R: crel K1 K2) p:
  forward_simulation R R (Clight_.semantics1 p @ K1) (Clight_.semantics1 p @ K2).
Proof.
  induction R; simpl.
  - apply lifting_simulation.
    apply identity_forward_simulation.
  - apply clight_sim.
  - eapply compose_forward_simulations; eauto.
Qed.

(* The horizontally compositional layers have the abstraction relation
   interpreted as krel_mcc denoted by [R]. When the layer is ready for vertical
   composition the krel_mcc is refined to krel_kcc, denoted by [|R|]. Note that
   the refinement is only for one direction. In the section, we prove the
   refinement. *)

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
