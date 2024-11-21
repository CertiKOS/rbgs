Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.
Require Import IntStrat.
Require Import Classical_Prop.
Require Import Coqlib.
Require Import CompCertStrat Frame.

Require Import BQUtil.
Require Import CModule.
Require Import Memory Globalenvs.
Require LanguageInterface.
Import -(notations) LanguageInterface.
Require CallconvAlgebra.

(** * §6.4 Certified Abstraction Layers *)

(** For certified abstraction layers, we use Clight programs as layer
    implementations. As the layers compose, the implementation programs
    accumulate. Therefore, we use a module of Clight program here. The
    definitions and properties for the modules are in CModule.v *)

(** ** Auxiliary definitions and properties *)

(** We show the frame property applies to modules. *)

Section FRAME_PROPERTY.

  Existing Instance CallconvAlgebra.open_fsim_ccref.

  Lemma frame_property_cmodule M sk:
    Linking.linkorder (cmod_skel M) sk ->
    Smallstep.determinate (semantics M) ->
    rsq join_conv join_conv (lts_strat_sk sk (semantics M) @ mem) (lts_strat_sk sk (semantics M)).
  Proof.
    intros Hlink HM.
    unfold join_conv. eapply rsq_vcomp.
    3: apply rsq_lift_emor.
    1-2: eauto using lts_strat_determ, Determ.lifting_determinate.
    apply fsim_rsq_sk; eauto.
    eapply CallconvAlgebra.open_fsim_ccref.
    1-2: apply CallconvAlgebra.cc_compose_id_left.
    eapply Smallstep.compose_forward_simulations.
    apply Lifting.lift_horizontal_comp.
    apply SmallstepLinking.semantics_simulation'.
    - intros i. edestruct (cmodule_program M i) as (p & ? & Hp). rewrite Hp.
      apply frame_property.
    - intros i. edestruct (cmodule_program M i) as (p & Hp1 & Hp2). rewrite Hp2.
      pose proof (cmod_skel_order M).
      eapply Forall_forall in H; cbn; eauto.
  Qed.

End FRAME_PROPERTY.

(** The refinement square for refinement conventions that are relations *)

Arguments rel_conv {_ _}.

Section REL_RSQ.
  Lemma lsp_rel_conv_when {S1 S2} (R: S1 -> S2 -> Prop) (p1 p2: position)
    (lp1: lpos _ p1) (lp2: lpos _ p2) (p: rspos p1 p2):
    match lp1, lp2 with
    | lready _ _, lready _ _ => True
    | lrunning _ _ s1 t1, lrunning _ _ s2 t2 => R s1 s2 /\ R t1 t2
    | lsuspended _ _ s1 t1, lsuspended _ _ s2 t2 => R s1 s2 /\ R t1 t2
    | _, _ => False
    end ->
    rsq_when (rel_conv R) (rel_conv R) p (lens_strat_when lid lp1) (lens_strat_when lid lp2).
  Proof.
    intros Hp s Hs. cbn in Hs. revert p2 lp1 lp2 p Hp Hs.
    induction s; intros;
      dependent destruction p;
      dependent destruction lp1; dependent destruction lp2; cbn in *; auto.
    - apply rsp_ready. cbn; eauto.
    - apply rsp_suspended. cbn; eauto.
    - dependent destruction m. dependent destruction Hs. cbn in Hs.
      apply rsp_oq. cbn; eauto.
      intros q2 Hq2. cbn in Hq2. inv Hq2.
      erewrite lens_strat_next_oq; eauto. cbn. eapply IHs; eauto.
      cbn. split; eauto.
    - dependent destruction m; dependent destruction Hs; cbn in Hs.
      + eapply rsp_pq. constructor. apply Hp.
        rewrite lens_strat_next_pq. eapply IHs; eauto.
        cbn. eauto.
      + eapply rsp_pa. intros Hx. inv Hx. apply HA. apply Hp.
        erewrite lens_strat_next_pa; cbn; eauto.
        rewrite rel_conv_rcnext; try easy. eapply IHs; eauto.
        cbn. easy.
    - dependent destruction m; dependent destruction Hs; cbn in Hs.
      eapply rsp_oa. cbn. eauto.
      intros n2 Hn.
      destruct (classic (R n n2)). 2: { exfalso. apply Hn. constructor; easy. }
                                 rewrite lens_strat_next_oa; cbn; eauto.
      rewrite rel_conv_rcnext; try easy. eapply IHs; eauto.
      cbn. easy.
  Qed.

  Lemma lsp_rel_conv {S1 S2} (R: S1 -> S2 -> Prop):
    lsq (rel_conv R) (rel_conv R) lid lid.
  Proof.
    apply lsp_rel_conv_when. easy.
  Qed.

  Lemma lsp_id {U: Type}:
    lsq (emor_rc (glob U)) (emor_rc (glob U)) lid lid.
  Proof.
    rewrite emor_rc_id. apply rsq_id_conv. reflexivity.
  Qed.

End REL_RSQ.

(** An associator for spatial composition and its properties *)

Section SCOMP_EMOR.

  Definition scomp_emor {E S1 S2}: emor (E@(S1*S2)) (E@S1@S2) :=
    fun '((q, s1), s2) => econs (q, (s1, s2)) (fun '(r, (s1, s2)) => ((r, s1), s2)).

  Lemma scomp_emor_operator {E S1 S2} q s1 s2:
    (q, (s1, s2)) = operator ((@scomp_emor E S1 S2) (q, s1, s2)).
  Proof. intros. reflexivity. Qed.

  Lemma id_emor_operator {E} (m: E):
    m = operator (eid m).
  Proof. reflexivity. Qed.

  Lemma emor_rc_forbid_contrapos:
    forall {E1 E2 : esig} (f : emor E1 E2) (m : E2) (n1 : ar (operator (f m))) (n2 : ar m),
      ~ emor_rc_has f (rcp_forbid (operator (f m)) m n1 n2) -> operand (f m) n1 = n2.
  Proof.
    intros * Hn. destruct (classic (operand (f m) n1 = n2)); try easy.
    apply emor_rc_forbid in H. easy.
  Qed.

  Lemma pa_eq_inv {E F} (m: op E) n1 n2:
    @pa F E m n1 = pa n2 -> n1 = n2.
  Proof.
    intros H. injection H. intros Hx. xsubst. reflexivity.
  Qed.

  Lemma oa_eq_inv {E F} (q: op F) (m: op E) n1 n2:
    @oa F E m q n1 = oa n2 -> n1 = n2.
  Proof.
    intros H. injection H. intros Hx. xsubst. reflexivity.
  Qed.

  Lemma rsq_scomp_emor_when {E F S1 S2} p (σ: strat E F p) p1 p2 p3
    (lp1: lpos lid p1) (lp2: lpos lid p2) (lp3: lpos lid p3) ps pt pt'
    (tp1: tpos p p1 ps) (tp2: tpos p p2 pt') (tp3: tpos pt' p3 pt)
    (rp: rspos ps pt):
    match lp1, lp2, lp3 with
    | lready _ _, lready _ _, lready _ _ => True
    | lrunning _ _ (s1, s2) (t1, t2), lrunning _ _ u1 v1, lrunning _ _ u2 v2 =>
        s1 = u1 /\ s2 = u2 /\ t1 = v1 /\ t2 = v2
    | lsuspended _ _ (s1, s2) (t1, t2), lsuspended _ _ u1 v1, lsuspended _ _ u2 v2 =>
        s1 = u1 /\ s2 = u2 /\ t1 = v1 /\ t2 = v2
    | _, _, _ => False
    end ->
    rsq_when (@scomp_emor _ S1 S2) scomp_emor rp
      (tstrat_when tp1 σ (lens_strat_when lid lp1))
      (tstrat_when tp3 (tstrat_when tp2 σ (lens_strat_when lid lp2)) (lens_strat_when lid lp3)).
  Proof.
    intros Hp s Hs. cbn in *. destruct Hs as (s1 & s2 & Hs1 & Hs2 & Hs).
    revert σ Hp s1 s2 Hs1 Hs2 Hs.
    revert p p1 p2 p3 lp1 lp2 lp3 pt pt' tp1 tp2 tp3 rp.
    induction s; intros;
      dependent destruction p;
      dependent destruction rp;
      dependent destruction tp1;
      dependent destruction tp2;
      dependent destruction tp3;
      dependent destruction lp1;
      dependent destruction lp2;
      dependent destruction lp3.
    - dependent destruction Hs1.
      eapply rsp_ready. exists pnil_ready, pnil_ready.
      repeat split; cbn; eauto. constructor.
    - dependent destruction Hs1.
      destruct q3. destruct m3. destruct Hp as (?&?&?&?). subst.
      eapply rsp_suspended. eexists (pnil_suspended _ _), (pnil_suspended _ _).
      repeat split; cbn; eauto. constructor.
    - dependent destruction m. dependent destruction Hs1. dependent destruction Hs.
      cbn in *. apply rsp_oq.
      { exists pnil_ready, pnil_ready. repeat split; cbn; eauto. constructor.
        exists pnil_ready, pnil_ready. repeat split. constructor.
        eapply Downset.closed; eauto. constructor.
        constructor. }
      intros [[? ?] ?] Hq. inv Hq. cbn in *. inv H0.
      setoid_rewrite tstrat_next_oq. setoid_rewrite tstrat_next_oq.
      erewrite !lens_strat_next_oq; eauto. cbn. eapply IHs; eauto.
      cbn. easy.
    - destruct q2. destruct u. destruct Hp as (?&?&?&?). subst.
      dependent destruction m.
      + dependent destruction Hs1. dependent destruction Hs. inv x.
        eapply rsp_pq.
        { setoid_rewrite scomp_emor_operator. constructor. }
        setoid_rewrite tstrat_next_pq. setoid_rewrite tstrat_next_pq.
        erewrite !lens_strat_next_pq; eauto. eapply IHs; eauto.
        cbn. easy.
      + cbn in *. destruct r as [? [? ?]]. cbn in *.
        simple inversion Hs1; try congruence.
        { inv H1. inv H2. xsubst. destruct m2. inv H6. }
        inv H1. inv H2. xsubst. destruct r2.
        (* I suspect this is a bug in Coq *)
        assert (r1 = a).
        {
          apply pcons_eq_inv_l in H6.
          apply pa_eq_inv in H6. inv H6. easy.
        }
        subst. inv H6. xsubst.
        intros Hss1. dependent destruction Hs.
        eapply rsp_pa.
        { intros Hx. cbn in Hx. dependent destruction Hx. apply H. eauto. }
        cbn in *.
        setoid_rewrite tstrat_next_pa. setoid_rewrite tstrat_next_pa.
        erewrite !lens_strat_next_pa; cbn; eauto.
        rewrite regular_conv.
        2: { setoid_rewrite scomp_emor_operator. constructor. }
        2: { intros Hx. inv Hx. xsubst. cbn in *. easy. }
        eapply IHs; eauto. easy.
    - destruct q2. destruct m3. destruct Hp as (?&?&?&?). subst.
      dependent destruction m. destruct n as [? [? ?]].
      simple inversion Hs1; try congruence.
      { inv H1. xsubst. inv H5. }
      inv H1. inv H2.  xsubst. destruct n2.
      assert (n1 = a).
      {
        apply pcons_eq_inv_l in H6.
        apply oa_eq_inv in H6. inv H6. easy.
      }
      subst. inv H6. xsubst.
      intros Hss1. dependent destruction Hs.
      apply rsp_oa.
      { eexists (pnil_suspended _ _), (pnil_suspended _ _). repeat split.
        - constructor.
        - eexists (pnil_suspended _ _), (pnil_suspended _ _). repeat split; eauto.
          + eapply Downset.closed; eauto. constructor.
          + constructor.
        - constructor. }
      intros nr Hnr.
      unfold scomp in Hnr.
      assert (Hnr': ~ Downset.has (emor_rc scomp_emor) (rcp_forbid (operator ((@scomp_emor E S1 S2) (m0, m2, m5))) (m0, m2, m5) (a, (s0, s3)) nr)).
      { apply Hnr. }
      eapply emor_rc_forbid_contrapos in Hnr'. cbn in *. subst.
      setoid_rewrite tstrat_next_oa. setoid_rewrite tstrat_next_oa.
      erewrite !lens_strat_next_oa; cbn; eauto.
      rewrite regular_conv.
      2: { setoid_rewrite scomp_emor_operator. constructor. }
      2: { intros Hx. inv Hx. xsubst. cbn in *. easy. }
      eapply IHs; eauto. easy.
  Qed.

  Lemma rsq_scomp_emor {E F S1 S2} (σ: E ->> F):
    rsq (@scomp_emor _ S1 S2) scomp_emor (σ @ lid) (σ @ lid @ lid).
  Proof.
    apply rsq_scomp_emor_when. easy.
  Qed.

End SCOMP_EMOR.

(** An auxiliary refinement convention used to simplify the composition proof. *)

Section SJOIN.

  Context (S: Type).

  Inductive sjoin_match_query : op (li_c @ (mem * S)) -> op (li_c @ S) -> Prop :=
  | sjoin_match_query_intro se m1 m2 vf args sg s m:
    Join.join m m1 m2 ->
    sjoin_match_query ((se, cq vf sg args m1)%embed, (m, s))
      ((se, cq vf sg args m2)%embed, s).

  Inductive sjoin_match_reply : forall (m1: op (li_c @ (mem * S))) (m2: op (li_c @ S)), ar m1 -> ar m2 -> Prop :=
  | sjoin_match_reply_intro q1 q2 m1 m2 m rv s:
    Join.join m m1 m2 ->
    sjoin_match_reply q1 q2 (cr rv m1, (m, s)) (cr rv m2, s).

  Definition sjoin_conv : erel (li_c @ (mem * S)) (li_c @ S) :=
    {|
      CompCertStrat.match_query := sjoin_match_query;
      CompCertStrat.match_reply := sjoin_match_reply;
    |}.

  Lemma sjoin_conv_eq: erel_conv sjoin_conv = scomp_emor ;; join_conv @ glob S.
  Proof.
    apply antisymmetry.
    - apply regular_conv_ref. 1-2: typeclasses eauto.
      + cbn. intros [[se1 q1] [mx s1]] [[se2 q2] s2] Hm.
        inv Hm. inv HM.
        eexists ((_, _)%embed, _, _). split.
        { rewrite (@scomp_emor_operator li_c mem S). constructor. }
        split.
        2: { rewrite (id_emor_operator s2) at 1. constructor. }
        eexists (_, Datatypes.pair _ _)%embed. split.
        * rewrite lift_emor_operator. constructor.
        * econstructor; cbn; eauto. constructor. eauto.
      + cbn. intros [[se1 q1] [mx s1]] [[se2 q2] s2]
               [[cr1 m3] [my s3]] [[cr2 m4] s4] Hn.
        inv Hn. cbn in *. inv HM.
        eexists ((_, _)%embed, _, _). split.
        { rewrite (@scomp_emor_operator li_c mem S). constructor. }
        split.
        { split.
          - eexists (_, Datatypes.pair _ _)%embed. split.
            + rewrite lift_emor_operator. constructor.
            + econstructor; cbn; eauto. constructor. eauto.
          - rewrite (id_emor_operator s2) at 1. constructor. }
        intros [[[cr3 m5] my1] s5]. apply not_imply_or. intros Hn1.
        split.
        { eexists (_, Datatypes.pair _ _)%embed. split.
          - rewrite lift_emor_operator. constructor.
          - econstructor; cbn; eauto. constructor. eauto. }
        split.
        { rewrite (id_emor_operator s2) at 1. constructor. }
        destruct (classic (s4 = s5)).
        2: { right. rewrite (id_emor_operator s2). constructor.
             cbn. congruence. }
        left. subst.
        eexists (_, Datatypes.pair _ _)%embed. split.
        { rewrite lift_emor_operator. constructor. } split.
        { econstructor; cbn; eauto. constructor. eauto. }
        intros [[cr4 m6] mz].
        apply not_imply_or. intros Hn2.
        econstructor. reflexivity. constructor. eauto.
        intros Hn3. inv Hn3. apply HA.
        rewrite (@scomp_emor_operator li_c mem S) in Hn1.
        apply emor_rc_forbid_contrapos in Hn1. cbn in Hn1. inv Hn1.
        rewrite lift_emor_operator in Hn2.
        apply emor_rc_forbid_contrapos in Hn2. cbn in Hn2. inv Hn2.
        econstructor. eauto.
    - apply regular_conv_ref. 1-2: typeclasses eauto.
      + cbn. intros [[se1 q1] [mx s1]] [[se2 q2] s2] Hm.
        destruct Hm as ([[[se3 q3] my] s3] & Hm1 & Hm2).
        inv Hm1. cbn in *. inv H0.
        destruct Hm2 as (Hm2 & Hm3).
        inv Hm3.
        destruct Hm2 as ([se3 [q3 mz]] & Hm2 & Hm3).
        inv Hm2. cbn in *. inv H0.
        inv Hm3. cbn in *. subst. inv HM.
        econstructor. econstructor; eauto.
      + cbn. intros [[se1 q1] [mx s1]] [[se2 q2] s2]
               [[cr1 m3] [my s3]] [[cr2 m4] s4] Hn.
        destruct Hn as ([[[se3 q3] mz] s5] & Hn1 & Hn2 & Hn3).
        inv Hn1. cbn in *. inv H0.
        destruct Hn2. cbn in *. inv H0.
        destruct H as ([se3 [q3 mw]] & H1 & H2).
        inv H1. cbn in *. inv H0.
        inv H2. cbn in *. subst.
        econstructor.
        { inv HM. constructor; eauto. }
        specialize (Hn3 (cr cr1 m3, my, s3)) as [Hn3|Hn3].
        { exfalso. inv Hn3. cbn in *. easy. }
        destruct Hn3 as (Hn4 & Hn5 & Hn6). clear Hn5.
        destruct Hn4 as ([se3 [q3 m5]] & Hn5 & Hn7).
        inv Hn5. cbn in *. inv H0.
        inv Hn7. cbn in *.
        destruct Hn6 as [Hn6|Hn6].
        2: { inv Hn6. cbn in *. intros Hx. apply H0. inv Hx. easy. }
        destruct Hn6 as ([se3 [q3 mz]] & Hn6 & Hn7 & Hn8).
        inv Hn6. cbn in *. inv H0.
        specialize (Hn8 (cr cr1 m3, my)) as [Hn8|Hn8].
        { exfalso. inv Hn8. cbn in *. easy. }
        inv Hn8. intros Hx. apply HN. inv Hx.
        econstructor. eauto.
        Unshelve. all: cbn; exact tt.
  Qed.

End SJOIN.

(** ** Abstraction Relation *)

(** The abstraction relation is parametrized by the symbol table, therefore we
    need to ensure that the symbol table used in Clight program semantics is the
    same as the one for the abstraction relation. The following refinement
    convention fixes a symbol table for the Clight semantics. *)

Section SE.

  Context (se: Genv.symtbl).

  Definition c_erel: erel li_c li_c :=
    {|
      CompCertStrat.match_query '(se1, q1) '(se2, q2) :=
        se = se1 /\ se = se2 /\ q1 = q2;
      CompCertStrat.match_reply '(se1, q1) '(se2, q2) r1 r2 :=
        se = se1 /\ se = se2 /\ q1 = q2 /\ r1 = r2;
    |}%embed.

  Lemma rc_next_c_erel q r:
    rcnext (se, q)%embed (se, q)%embed r r c_erel = c_erel.
  Proof.
    apply antisymmetry; intros p Hp; cbn in *.
    - inv Hp. apply HK. constructor; easy.
    - constructor; eauto. constructor; easy.
  Qed.

  Hint Resolve next_strat_preserve_se : core.

  Lemma rsq_c_erel_when pi (p: rspos pi pi) (L: @strat li_c li_c pi):
    (match pi with
    | ready => True
     | running (se1, _) => se = se1
    | suspended (se1, _) (se2, _) => se = se1 /\ se = se2
    end)%embed ->
    strat_preserve_se L ->
    rsq_when c_erel c_erel p L L.
  Proof.
    intros Hp HL s Hs. revert p Hp L HL Hs. induction s; intros; dependent destruction p;
      cbn; eauto; dependent destruction m.
    - apply rsp_oq. eapply Downset.closed; eauto; constructor.
      intros q2 Hq. inv Hq. destruct q. destruct q2. inv HM.
      destruct H0; subst. eauto.
    - destruct q1. subst.
      pose proof (HL _ Hs) as HLs. dependent destruction HLs.
      eapply rsp_pq. instantiate (1 := (_, _)%embed). repeat econstructor; eauto.
      eauto.
    - destruct q1. subst.
      eapply rsp_pa. instantiate (1 := r). intros Hr. inv Hr. apply HA. repeat constructor.
      rewrite rc_next_c_erel. eauto.
    - destruct q1. destruct m1. destruct Hp. subst.
      apply rsp_oa. eapply Downset.closed; eauto; constructor.
      intros n2 Hn2. destruct (classic (n = n2)).
      2: { exfalso. apply Hn2.
           repeat econstructor; cbn; eauto.
           intros Hx. easy. }
      subst. rewrite rc_next_c_erel. eauto.
  Qed.

  Lemma rsq_c_erel (L: li_c ->> li_c):
    strat_preserve_se L -> rsq c_erel c_erel L L.
  Proof.
    apply rsq_c_erel_when. easy.
  Qed.

End SE.

(** ** Abstraction relation *)

Section ABREL.
  Context {D2 D1: Type}.

  (** The abstraction relation relates the high level data [D₂] and the low
      level data [D₁] combined with the memory state. *)
  Record abrel : Type := {
      abrel_rel (se: Genv.symtbl) :> D2 -> mem * D1 -> Prop;
    }.
  Section ABREL_RC.
    Context (se: Genv.symtbl) (R: abrel).

    (** Promoting the abstraction relation to refinement convention:
          R̂ := (mem @ R) ;; (Y @ D1) *)
    Definition abrel_rc : conv (li_c @ D2) (li_c @ D1) :=
      (c_erel se) @ rel_conv (R se) ;; scomp_emor ;; join_conv @ glob D1.

  End ABREL_RC.
End ABREL.

Arguments abrel : clear implicits.

(** ** Property of abstraction relation *)

Section ABREL_RSQ.

  Hint Constructors lens_has : core.

  Lemma rsq_abrel {D1 D2} (R: abrel D2 D1) M sk se
    (HM: Smallstep.determinate (semantics M))
    (HL: Linking.linkorder (cmod_skel M) sk):
    rsq (abrel_rc se R) (abrel_rc se R)
      ((lts_strat_sk sk (semantics M)) @ lid)
      ((lts_strat_sk sk (semantics M)) @ lid).
  Proof.
    assert (HD: Deterministic (lts_strat_sk sk (semantics M))).
    { apply lts_strat_determ. eauto. }
    unfold abrel_rc. eapply rsq_vcomp.
    3: {
      apply scomp_rsq. apply rsq_c_erel. apply lts_preserve_se. apply lsp_rel_conv.
    }
    1-2: typeclasses eauto.
    eapply rsq_vcomp.
    4: {
      eapply scomp_rsq.
      apply frame_property_cmodule; eauto.
      apply lsp_id.
    }
    1-2: typeclasses eauto.
    apply rsq_scomp_emor.
  Qed.

End ABREL_RSQ.

(** ** Definition of layer correctness *)

Notation "0" := E0_conv : conv_scope.

Section LAYER.

  Context {D2 D1} (L1: 0 ->> li_c @ D1) (R: abrel D2 D1) (M: cmodule) (L2: 0 ->> li_c @ D2).

  (** L1 ⊢_R M : L2 ⇔ L2 ≤_{0 ↠ R} (Clight(M) @ D1) ⊙ L1 *)
  Definition layer_correctness sk se :=
    rsq 0 (abrel_rc se R) L2 (lts_strat_sk sk (semantics M) @ D1 ⊙ L1).

End LAYER.

(** ** Composition of abstraction relations *)

Section ABREL_COMP.

  Context {D3 D2 D1} (R: abrel D2 D1) (S: abrel D3 D2).

  (** R ⋅ S := S ;; (mem @ R) ;; (Y @ D1) *)
  Definition abrel_comp : abrel D3 D1 :=
    {|
      abrel_rel se d3 '(m, d1) :=
        exists d2 m2 m1, R se d2 (m1, d1) /\ S se d3 (m2, d2) /\ Join.join m1 m2 m;
    |}.

  Context (se: Genv.symtbl).

  Lemma abrel_rc_comp:
    abrel_rc se abrel_comp = vcomp (abrel_rc se S) (abrel_rc se R).
  Proof.
    unfold abrel_rc.
    rewrite <- !sjoin_conv_eq.
    apply antisymmetry.
    - apply regular_conv_ref. 1-2: typeclasses eauto.
      + intros [[se1 q1] d3] [[se3 q3] d1] Hm. cbn in *.
        destruct Hm as ([[se2 q2] [mx d1']] & (Hm1 & Hm2) & Hm3).
        inv Hm1. inv HM. destruct H0. subst.
        inv Hm2. inv Hm3. inv HM. destruct HQ as (d2 & md2 & md1 & HR & HS & HJ).
        edestruct (Join.join_associative_exist _ _ _ _ _ HJ H0) as (mj & Hj1 & Hj2).
        eexists ((se3, cq _ _ _ _)%embed, d2). split.
        * eexists ((se3, cq _ _ _ _)%embed, (_, d2)). repeat split.
          -- repeat constructor.
          -- constructor; eauto.
          -- econstructor. econstructor. eauto.
        * eexists ((se3, cq _ _ _ _)%embed, (_, _)). repeat split.
          -- repeat econstructor.
          -- constructor; eauto.
          -- econstructor. econstructor. eauto.
      + intros [[se1 q1] d3] [[se3 q3] d1] [[rv1 mr1] dr3] [[rv3 mr3] dr1] Hn. cbn in *.
        destruct Hn as (m2 & Hm1 & Hm2 & Hn). destruct m2 as [[se2 q2] [mx d1']].
        inv Hm2. inv HM. destruct Hm1 as (Hm1 & Hm2).
        inv Hm1. inv HM. destruct H1. subst.
        inv Hm2. destruct HQ as (d2 & md2 & md1 & HR & HS & Hj).
        edestruct (Join.join_associative_exist _ _ _ _ _ Hj H0) as (mj & Hj1 & Hj2).
        eexists ((se3, cq _ _ _ _)%embed, d2). split.
        { eexists ((se3, cq _ _ _ _)%embed, (_, d2)). repeat split.
          - repeat constructor.
          - constructor; eauto.
          - econstructor. econstructor. eauto. }
        split.
        { eexists ((se3, cq _ _ _ _)%embed, (_, _)). repeat split.
          - repeat econstructor.
          - constructor; eauto.
          - econstructor. econstructor. eauto. }
        intros [[rv2 mr2] dr2]. apply not_imply_or. intros Hr1.
        eexists ((se3, cq _ _ _ _)%embed, (_, _)). split.
        { split.
          - repeat constructor.
          - constructor; eauto. }
        split. { constructor. constructor; eauto. }
        intros [[cr4 mr4] [my dr4]].
        apply not_imply_or. intros Hr2.
        constructor. { constructor. eauto. }
        intros Hx. cbn in *. inv Hx.
        apply not_and_or in Hr2 as [Hr2|Hr2].
        { apply Hr2. repeat constructor. }
        apply not_and_or in Hr2 as [Hr2|Hr2].
        { apply Hr2. repeat constructor. eauto. }
        apply not_or_and in Hr2 as [Hr2 Hr3].
        destruct (classic (rv2 = rv3 /\ mr2 = mr4)).
        2: { apply Hr2. repeat constructor.
             intros Hx. inv Hx. destruct H2. destruct H4. inv H5.
             apply H. easy. } clear Hr2.
        destruct H. subst.
        destruct (classic (R se3 dr2 (my, dr1))) as [HR1|].
        2: { apply Hr3. constructor; eauto. } clear Hr3.
        apply Hr1. clear Hr1.
        eexists ((se3, cq _ _ _ _)%embed, (_, _)). split.
        { split.
          - repeat constructor.
          - constructor. eauto. }
        split. { constructor. constructor. eauto. }
        intros [[rv4 m3] [mz ddr2]].
        apply not_imply_or. intros Hr2.
        constructor. { constructor. eauto. }
        intros Hr3. inv Hr3. apply Hr2. clear Hr2. split.
        { repeat constructor. }
        split. { constructor. eauto. }
        apply not_imply_or. intros Hr2. constructor; eauto.
        intros Hss. apply Hr2. clear Hr2. constructor.
        { constructor; eauto. }
        intros Hr. inv Hr. destruct H1. destruct H2. inv H2. inv H5.
        apply Join.join_commutative in H3.
        apply Join.join_commutative in H4.
        edestruct (Join.join_associative_exist _ _ _ _ _ H4 H3) as (mi & Hi1 & Hi2).
        specialize (Hn (cr rv3 m3, (mi, dr1))). cbn in *.
        destruct Hn as [(A&B&[Hn|Hn])|Hn].
        * inv Hn. apply HA. constructor; eauto.
        * inv Hn. apply HA. eexists _, _, _.
          split; eauto. split; eauto. apply Join.join_commutative. eauto.
        * inv Hn. apply HA. constructor. apply Join.join_commutative. eauto.
    - apply regular_conv_ref. 1-2: typeclasses eauto.
      + intros [[se1 q1] d3] [[se3 q3] d1] Hm. cbn in *.
        destruct Hm as ([[se2 q2] d2] & Hm1 & Hm2).
        destruct Hm1 as ([[? ?] [? ?]] & (Hm11 & Hm12) & Hm13).
        destruct Hm2 as ([[? ?] [? ?]] & (Hm21 & Hm22) & Hm23).
        inv Hm11. inv HM. destruct H0. subst. inv Hm12. inv Hm13. inv HM.
        inv Hm21. inv HM. destruct H1. subst. inv Hm22. inv Hm23. inv HM.
        apply Join.join_commutative in H0.
        apply Join.join_commutative in H2.
        edestruct (Join.join_associative_exist _ _ _ _ _ H0 H2) as (mi & Hi1 & Hi2).
        eexists ((_, cq _ _ _ _)%embed, (_, _)). split.
        * split.
          -- repeat constructor.
          -- constructor. eexists _, _, _.
             split; eauto. split; eauto.
             apply Join.join_commutative. eauto.
        * constructor. constructor. apply Join.join_commutative. eauto.
      + intros [[se1 q1] d3] [[se3 q3] d1] [[rv1 mr1] dr3] [[rv3 mr3] dr1] Hn. cbn in *.
        destruct Hn as (m2 & Hm1 & Hm2 & Hn).
        destruct m2 as [[se2 q2] d2].
        destruct Hm1 as ([[? ?] [mx ?]] & (Ha & Hb) & Hc).
        inv Ha. inv HM. destruct H0. subst s. subst c.
        inv Hb. inv Hc. inv HM.
        destruct Hm2 as ([[? ?] [my ?]] & (Ha & Hb) & Hc).
        inv Ha. inv HM. destruct H1. subst s. subst c.
        inv Hb. inv Hc. inv HM.
        apply Join.join_commutative in H0.
        apply Join.join_commutative in H2.
        edestruct (Join.join_associative_exist _ _ _ _ _ H0 H2) as (mi & Hi1 & Hi2).
        eexists ((_, cq _ _ _ _)%embed, (_, _)). split.
        { split.
          - repeat constructor.
          - constructor. eexists _, _, _.
            split; eauto. split; eauto.
            apply Join.join_commutative. eauto. }
        split. { constructor. constructor. apply Join.join_commutative. eauto. }
        intros [[rv2 mr2] [mrr1 drr1]]. apply or_commut. apply not_imply_or.
        intros Hr. eapply erel_mr_elim in Hr.
        2: { constructor. apply Join.join_commutative. eauto. }
        cbn in Hr. dependent destruction Hr.
        split. { repeat constructor. }
        split. { constructor. eexists _, _, _.
                 split; eauto. split; eauto. apply Join.join_commutative. eauto. }
        apply not_imply_or. intros Hr. eapply erel_mr_elim in Hr.
        2: { repeat constructor. }
        cbn in Hr. destruct Hr. destruct H4. destruct H5. inv H6.
        constructor.
        { eexists _, _, _. split; eauto. split; eauto. apply Join.join_commutative. eauto. }
        intros (dr2 & mmr1 & mmr2 & HR1 & HS1 & HJ).
        clear H3 H4 H5.
        edestruct (Join.join_associative_exist _ _ _ _ _ HJ H1) as (mj & Hj1 & Hj2).
        specialize (Hn (cr rv3 mj, dr2)) as [Hn|Hn].
        * destruct Hn as ([[se qn] [mn dn2]] & Hnm1 & Hnm2 & Hn).
          inv Hnm1. inv H3. inv H4. inv HM. destruct H4. subst.
          inv Hnm2. inv HM.
          specialize (Hn (cr rv3 mr2, (mmr1, dr2))) as [(Hnm1 & Hnm2 & [Hn|Hn])|Hn].
          ++ inv Hnm1. inv HM. destruct H6. inv H7.
             inv Hnm2. inv Hn. apply HA. constructor; easy.
          ++ inv Hnm1. inv HM. destruct H6. inv H7.
             inv Hnm2. inv Hn. apply HA. eauto.
          ++ inv Hn. apply HA. constructor. apply Hj1.
        * destruct Hn as ([[se qn] [mn dn2]] & Hnm1 & Hnm2 & Hn).
          inv Hnm1. inv H3. inv H4. inv HM. destruct H4. subst.
          inv Hnm2. inv HM.
          specialize (Hn (cr rv3 mj, (mmr2, dr1))) as [(Hnm1 & Hnm2 & [Hn|Hn])|Hn].
          ++ inv Hnm1. inv HM. destruct H6. inv H7.
             inv Hnm2. inv Hn. apply HA. constructor; easy.
          ++ inv Hnm1. inv HM. destruct H6. inv H7.
             inv Hnm2. inv Hn. apply HA. eauto.
          ++ inv Hn. apply HA. constructor. apply Hj2.
  Qed.

End ABREL_COMP.

Infix "⋅" := abrel_comp (at level 50, left associativity).

(** ** Layer composition *)

Section LAYER_COMP.

  Context N M MN (Hmod: cmod_app N M = Some MN).
  Context `{!cmodule_vertical_linkable N M}.
  Context `{Smallstep.determinate (semantics N)}
    `{Smallstep.determinate (semantics M)} `{Smallstep.determinate (semantics MN)}.
  Let sk := cmod_skel MN.
  Context (se: Genv.symtbl).

  Notation " X ⊢ [ R ] M : Y " := (layer_correctness X R M Y sk se) (at level 85, M at level 99).
  Definition cmod_strat (M: cmodule) := lts_strat_sk sk (semantics M).
  Local Coercion cmod_strat: cmodule >-> strat.

  Context {D1 D2 D3 L1 L2 L3} (R: abrel D2 D1) (S: abrel D3 D2)
    (ψ12: L1 ⊢ [R] M : L2) (ψ23: L2 ⊢ [S] N : L3).
  Context `{!Deterministic L1} `{!Deterministic L2}.

  Instance deterministic_n: Deterministic N.
  Proof. apply lts_strat_determ. eauto. Qed.

  Instance deterministic_mn: Deterministic MN.
  Proof. apply lts_strat_determ. eauto. Qed.

  Lemma layer_comp : L1 ⊢ [ R ⋅ S ] MN : L3.
  Proof.
    unfold layer_correctness in *.
    rewrite abrel_rc_comp.
    rewrite (E0_conv_vcomp E0_conv).
    eapply rsq_vcomp. 3: apply ψ23.
    1-2: typeclasses eauto.
    assert (HMN: N ⊙ M [= cmod_strat MN).
    { setoid_rewrite cc_comp_ref.
      eapply rsq_id_conv.
      rewrite <- cc_conv_id.
      eapply fsim_rsq. eauto.
      apply cmodule_categorical_comp_simulation; eauto.
      apply cmodule_vertical_linkable_cond; eauto. }
    unfold scomp_strat. rewrite <- HMN.
    rewrite <- (lcomp_lid_r (bij_lens (@bid D1))).
    setoid_rewrite scomp_compose.
    rewrite compose_assoc.
    eapply rsq_comp. 2: apply ψ12.
    apply rsq_abrel; eauto.
    unfold sk.
    apply cmod_app_skel in Hmod.
    apply Linking.link_linkorder in Hmod. apply Hmod.
  Qed.

End LAYER_COMP.
