Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.
Require Import IntStrat.
Require Import Classical_Prop.
Require Import Coqlib.
Require Import CompCertStrat.

Require Import BQUtil.
Require Import CModule.
Require Import Memory Globalenvs.
Require LanguageInterface.
Import -(notations) LanguageInterface.
Require CallconvAlgebra.

(** Some auxiliary lemmas *)

Section FRAME_PROPERTY.

  Existing Instance CallconvAlgebra.open_fsim_ccref.

  Lemma frame_property_cmodule M sk:
    Linking.linkorder (cmod_skel M) sk ->
    Smallstep.determinate (semantics M) ->
    rsq join_conv join_conv (lts_strat_sk sk (semantics M) @ mem) (lts_strat_sk sk (semantics M)).
  Proof.
    intros Hlink HM.
    unfold join_conv. eapply rsq_vcomp.
    3: apply rsq_lift_convert.
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

Lemma lsp_id {U: Type}:
  lsq (emor_rc (glob U)) (emor_rc (glob U)) lid lid.
Proof.
  rewrite emor_rc_id. apply rsq_id_conv. reflexivity.
Qed.

(** ** Abstraction Relation *)

Section ABREL.
  Context {D2 D1: Type}.

  Record abrel : Type := {
      abrel_rel (se: Genv.symtbl) :> D2 -> mem * D1 -> Prop;
    }.
  Section ABREL_RC.
    Context (R: abrel).

    Inductive abrel_c_mq: rel (op (li_c @ D2)) (op (li_c @ Mem.mem @ D1)) :=
    | abrel_c_mq_intro q se d1 d2 m (Hrel: R se d2 (m, d1)):
      abrel_c_mq ((se, q)%embed, d2) ((se, q)%embed, m, d1).
    Inductive abrel_c_mr: forall (m1: op (li_c @ D2)) (m2: op (li_c @ Mem.mem @ D1)), ar m1 -> ar m2 -> Prop :=
    | abrel_c_mr_intro q se d0 m2 r d1 d2 m (Hrel: R se d2 (m, d1)):
      abrel_c_mr ((se, q)%embed, d0) m2 (r, d2) (r, m ,d1).

    (** Ideally, we'd like to define (mem @ R) as in the paper. But because:

        1) the C language interface doesn't set apart the memory from other
        parts;

        2) the abstraction relation is parameterized by the symbol table;

        So we define it in the following way. *)
    Definition abrel_c : @esig_rel (li_c @ D2) (li_c @ Mem.mem @ D1) :=
      {|
        CompCertStrat.match_query := abrel_c_mq;
        CompCertStrat.match_reply := abrel_c_mr;
      |}.

    (** R̂ := (mem @ R) ;; (Y @ D1) *)
    Definition abrel_rc : conv (li_c @ D2) (li_c @ D1) :=
      abrel_c ;; join_conv @ glob D1.

  End ABREL_RC.
End ABREL.

Arguments abrel : clear implicits.

(** ** Property of abstraction relation *)

Section ABREL_RSQ.

  Local Hint Constructors tstrat_has lens_has lts_strat_has: core.

  Lemma abrel_rsq {D1 D2} (R: abrel D2 D1) L sk:
    rsq (abrel_c R) (abrel_c R)
      (lts_strat_sk sk L @ D2) (lts_strat_sk sk L @ mem @ D1).
  Proof.
    Ltac crush :=
      repeat match goal with
      | [ |- exists _ _, _  ] => eexists _, _
      | [ |- _ /\ _ ] => split
      end; try solve [ repeat constructor; eauto ].
    setoid_rewrite <- closure_lift.
    setoid_rewrite <- closure_lift.
    eapply rsq_closure; eauto with typeclass_instances.
    intros p (s & t & Hs & Ht & Hst). cbn in *.
    dependent destruction Ht.
    { xinv Hs. apply rsp_ready. cbn. crush. }
    dependent destruction Hs. apply rsp_oq.
    { cbn. crush. }
    intros qx Hq. xinv Hq. inv HM. rename q2 into d2.
    simple inversion Hst; try congruence. xsubst; congruence.
    clear Hst. xsubst. inv H2. inv H3. xsubst. intros Hst Hu.
    eapply rsp_ref. 1-3: reflexivity.
    { setoid_rewrite tstrat_next_oq.
      setoid_rewrite tstrat_next_oq.
      setoid_rewrite lens_strat_next_oq.
      2-3: cbn; eauto.
      assert (Href:
               state_strat L se q s0 (running (se, q)%embed)
                 [= next (oq (se, q)%embed) (lts_strat' L sk ready)).
      { cbn. intros. econstructor; eauto. }
      rewrite <- Href. reflexivity. }
    cbn in Hu. subst u.
    cbn [init_state lid].
    clear HVF INIT.
    revert Hrel Hst.
    generalize d2 at 1 4 as dd2.
    generalize m at 1 12 as mm.
    generalize d1 at 1 9 as dd1.
    revert d2 m d1 s s2 Hs.
    dependent induction HS; intros.
    - dependent destruction Hs. dependent destruction Hst.
      eapply rsp_pq. { crush. }
      dependent destruction Hs. dependent destruction Hst.
      apply rsp_suspended. cbn. crush.
    - dependent destruction Hs. dependent destruction Hst.
      eapply rsp_pq. { crush. }
      dependent destruction Hs. dependent destruction Hst. apply rsp_oa.
      { cbn. crush. }
      cbn. intros [[cr mr] d1r] Hr. eapply esig_rel_mr_elim in Hr.
      2: { constructor; eauto. }
      inv Hr. rewrite regular_conv. 2: { crush. }
      2: { intros Hr. xinv Hr. apply HA. inv HM. constructor; eauto. }
      eapply rsp_ref. 1-3: reflexivity.
      2: { eapply IHHS; eauto. }
      intros p Hp. cbn in Hp |- *.
      destruct Hp as (p1 & p2 & (Hp1 & (p3 & p4 & Hp2 & Hp3 & Hp4) & Hp5)).
      crush. econstructor; eauto.
    - do 2 dependent destruction Hs. do 2dependent destruction Hst.
      eapply rsp_pa.
      { intros Hr. xinv Hr. apply HA.
        instantiate (1 := (_, _, _)).
        econstructor. eauto. }
      apply rsp_ready. cbn. crush. all: repeat econstructor.
    - eapply rsp_ref. 1-3: reflexivity.
      2: { eapply IHHS; eauto. }
      intros p Hp. cbn in Hp |- *.
      destruct Hp as (p1 & p2 & (Hp1 & (p3 & p4 & Hp2 & Hp3 & Hp4) & Hp5)).
      crush. econstructor 4; eauto.
  Qed.

End ABREL_RSQ.

(** ** Definition of layer correctness *)

Notation "0" := E0_conv : conv_scope.

Section LAYER.

  Context {D2 D1} (L1: 0 ->> li_c @ D1) (R: abrel D2 D1) (M: cmodule) (L2: 0 ->> li_c @ D2).

  (** L1 ⊢_R M : L2 ⇔ L2 ≤_{0 ↠ R} (Clight(M) @ D1) ⊙ L1 *)
  Definition layer_correctness sk :=
    rsq 0 (abrel_rc R) L2 (lts_strat_sk sk (semantics M) @ D1 ⊙ L1).

End LAYER.

(** ** Composition of abstraction relation *)

Section ABREL_COMP.

  Context {D3 D2 D1} (R: abrel D2 D1) (S: abrel D3 D2).

  (** R ⋅ S := S ;; (mem @ R) ;; (Y @ D1) *)
  Definition abrel_comp : abrel D3 D1 :=
    {|
      abrel_rel se d3 '(m, d1) :=
        exists d2 m2 m1, R se d2 (m1, d1) /\ S se d3 (m2, d2) /\ Join.join m1 m2 m;
    |}.

  Lemma abrel_rc_comp :
    abrel_rc abrel_comp = vcomp (abrel_rc S) (abrel_rc R).
  Proof.
    unfold abrel_rc.
    rewrite <- vcomp_assoc. f_equal.
  Admitted.

End ABREL_COMP.

Infix "⋅" := abrel_comp (at level 50, left associativity).

(** ** Layer composition *)

Section LAYER_COMP.

  Context N M MN (Hmod: cmod_app N M = Some MN).
  Context `{!cmodule_vertical_linkable N M}.
  Context `{Smallstep.determinate (semantics N)}
    `{Smallstep.determinate (semantics M)} `{Smallstep.determinate (semantics MN)}.
  Let sk := cmod_skel MN.

  Notation " X ⊢ [ R ] M : Y " := (layer_correctness X R M Y sk) (at level 85, M at level 99).
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
    assert (HN: rsq (abrel_rc R) (abrel_rc R) (N @ lid) (N @ lid)).
    { unfold abrel_rc. eapply rsq_vcomp.
      3: apply abrel_rsq.
      3: eapply (scomp_rsq _ _ _ _ _ _ _ _
                  (frame_property_cmodule _ _ _ _) lsp_id).
      all: typeclasses eauto.
      Unshelve.
      - apply cmod_app_skel in Hmod. eapply Linking.link_linkorder in Hmod. apply Hmod.
      - eauto.
    }
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
    apply HN.
  Qed.

End LAYER_COMP.
