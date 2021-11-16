Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra.
Require Import LanguageInterface Events Globalenvs Smallstep CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Clight Linking.
Require Import AbstractStateRel Lifting CModule TensorComp.
Require Import Ctypes.

(* FIXME: why the precedence can't be looser than 9? *)
Notation "[ R ]" := (singleton_rel R) (at level 9): krel_scope.

Section PROG_LAYER_DEF.
  (* L1 is the high level spec with K1 as the abstract data whereas the program
     running on top of L2 is the low level spec *)
  Context {K1 K2: Type} (L1: layer K1) (L2: layer K2) (p: Clight.program).

  Definition prog_layer_comp sk := comp_semantics' (Clight.semantics2 p @ K2) L2 sk.

  (* The version of certified abstraction layers for vertical composition *)
  Definition prog_ksim (R: crel K1 K2) :=
    linkorder (skel L2) (skel L1) /\ linkorder (AST.erase_program p) (skel L1) /\
    forward_simulation 1 R L1 (prog_layer_comp (skel L1)).

  (* The version that is horizontally compositional *)
  Definition prog_ksim_mcc (R: krel K1 K2) :=
    linkorder (skel L2) (skel L1) /\ linkorder (AST.erase_program p) (skel L1) /\
    forward_simulation 1 (krel_mcc R) L1 (prog_layer_comp (skel L1)).

  Lemma prog_ksim_ref (R: krel K1 K2): prog_ksim_mcc R -> prog_ksim [R].
  Proof.
    unfold prog_ksim, prog_ksim_mcc. intuition.
    apply layer_fsim_refine. auto.
  Qed.
End PROG_LAYER_DEF.

Section MOD_LAYER_DEF.

  Context {K1 K2: Type} (L1: layer K1) (L2: layer K2) (M: cmodule).

  Definition layer_comp sk := comp_semantics' (semantics M sk @ K2) L2 sk.

  Definition ksim (R: crel K1 K2) :=
    linkorder (skel L2) (skel L1) /\ skel_module_compatible M (skel L1) /\
    forward_simulation 1 R L1 (layer_comp (skel L1)).

  Definition ksim_mcc (R: krel K1 K2) :=
    linkorder (skel L2) (skel L1) /\ skel_module_compatible M (skel L1) /\
    forward_simulation 1 R L1 (layer_comp (skel L1)).

  Definition ksim_ref (R: krel K1 K2): ksim_mcc R -> ksim [R].
  Proof.
    unfold ksim, ksim_mcc. intuition.
    apply layer_fsim_refine. auto.
  Qed.

End MOD_LAYER_DEF.


(* "M:Y" part should have higher priority than the type annotation "a:T" which
   is at level 100 *)
Notation " X ⊢ [ R ] M : Y " := (ksim_mcc Y X M R) (at level 85, M at level 99).
Notation " X ⊢ { R } M : Y " := (ksim Y X M R) (at level 85, M at level 99).

Instance ksim_mcc_proper {K1 K2: Type}:
  Proper ((forward_simulation 1 1) --> (forward_simulation 1 1) ==> eq  ==> eq ==> impl) (@ksim_mcc K1 K2).
Proof.
  intros L2 L2' HL2 L1 L1' HL1 M N Hmn R S Hrs H.
  unfold impl, flip in *. subst. destruct H as (?&?&?). split; [| split].
  - destruct HL1. destruct X.
    destruct HL2. destruct X. congruence.
  - destruct HL2. destruct X. congruence.
  - eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations. eauto.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. eauto.

    destruct HL2. destruct X. rewrite fsim_skel.
    unfold layer_comp.
    eapply categorical_compose_simulation';
      [ reflexivity | assumption | apply linkorder_refl | assumption ].
Qed.

Instance ksim_monotonic {K1 K2: Type}:
  Proper ((forward_simulation 1 1) --> (forward_simulation 1 1) ==> eq  ==> eq ==> impl) (@ksim K1 K2).
Proof.
  intros L2 L2' HL2 L1 L1' HL1 M N Hmn R S Hrs H.
  unfold impl, flip in *. subst. destruct H as (?&?&?). split; [| split].
  - destruct HL1. destruct X.
    destruct HL2. destruct X. congruence.
  - destruct HL2. destruct X. congruence.
  - eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations. eauto.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. eauto.

    destruct HL2. destruct X. rewrite fsim_skel.
    unfold layer_comp.
    eapply categorical_compose_simulation';
      [ reflexivity | assumption | apply linkorder_refl | assumption ].
Qed.

Goal forall K1 K2 (L1: layer K1) (L2: layer K2) R M L2',
    L1 ⊢ [ R ] M : L2 -> L2' ≤ L2 -> L1 ⊢ [ R ] M : L2'.
Proof.
  intros * H HL2. now rewrite HL2.
Qed.

Section HCOMP_SINGLETON.

  Import SmallstepLinking Smallstep.
  Context {li} (L: semantics li li).
  Variable sk: AST.program unit unit.
  Context `{!ProgramSem L}.

  Let LS := fun k : unit + Empty_set =>
              match k with
              | inl _ => L
              | inr e => match e with end
              end.

  Inductive singleton_match: state L -> list (frame LS) -> Prop :=
  | singleton_match_intro s: singleton_match s (st LS (inl tt) s :: nil).

  Ltac esca := eexists; split; try constructor; intuition auto.
  Lemma hcomp_singleton_fsim: skel_extend L sk ≤ SmallstepLinking.semantics' LS sk.
  Proof.
    constructor. econstructor; eauto. intros i.
    { split; cbn; intros. exists (inl tt). apply H. destruct H as [[|] Hx]. apply Hx. inv e. }
    intros se _ [ ] [ ] _. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := singleton_match); cbn; intros; subst.
    - esca. eapply incoming_query_valid. eauto.
    - inv H. esca.
    - inv H. exists tt. eexists; repeat apply conj; eauto. constructor; eauto.
      intros [|]. destruct u. eapply outgoing_query_invalid; eauto. inv e.
      intros; subst. esca.
    - inv H0. esca.
    - apply well_founded_ltof.
  Qed.

End HCOMP_SINGLETON.

Lemma singleton_ksim {K1 K2} L1 L2 p (R: crel K1 K2): prog_ksim L1 L2 p R -> ksim L1 L2 (p :: nil) R.
Proof.
  unfold prog_ksim, ksim. intuition.
  - unfold skel_module_compatible. rewrite Forall_forall.
    intros x Hx. cbn in Hx. destruct Hx; intuition. subst. auto.
  - unfold layer_comp. unfold semantics. unfold ref. cbn.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. eauto.

    unfold prog_layer_comp.
    etransitivity. apply lift_comp_component3 with (sk1 := (skel L1)).
    eapply categorical_compose_simulation'; [ | reflexivity | apply linkorder_refl | auto].
    replace (skel_extend (semantics2 p @ K2) (skel L1))
      with (skel_extend (semantics2 p) (skel L1) @ K2) by reflexivity.
    apply lifting_simulation. apply hcomp_singleton_fsim. typeclasses eauto.
Qed.

Lemma compatible_app sk M N:
  skel_module_compatible M sk -> skel_module_compatible N sk ->
  skel_module_compatible (M ++ N) sk.
Proof.
  unfold skel_module_compatible.
  rewrite !Forall_forall.
  intros Hm Hn p Hp. apply in_app_or in Hp.
  destruct Hp; [ apply Hm | apply Hn ]; auto.
Qed.

Lemma compatible_trans sk1 sk2 N:
  linkorder sk1 sk2 -> skel_module_compatible N sk1 -> skel_module_compatible N sk2.
Proof.
  unfold skel_module_compatible.
  rewrite !Forall_forall.
  intros; eapply linkorder_trans; eauto.
Qed.

Section SKEL_EXT.
  Context {liA liB liC} (L1: Smallstep.semantics liB liC) (L2: Smallstep.semantics liA liB).
  Lemma skel_extend_compose sk sk': skel_extend (comp_semantics' L1 L2 sk) sk' ≤ comp_semantics' L1 L2 sk'.
  Proof.
    constructor. eapply Forward_simulation with _ (fun _ _ _ => _); auto.
    - intros. reflexivity.
    - intros se ? [ ] [ ] Hse.
      eapply forward_simulation_plus with (match_states := eq);
        cbn; intros; subst; eauto 10 using plus_one.
      exists tt, q1. intuition (subst; eauto).
  - apply well_founded_ltof.
  Qed.
End SKEL_EXT.

Section VCOMP.

  Context {K1 K2 K3 L1 L2 L3} {M N: cmodule} {R: crel K1 K2} {S: crel K2 K3}
          (HL1: ksim L1 L2 M R) (HL2: ksim L2 L3 N S).
  (* FIXME: the linkable hypothesis should be simplified *)
  Context `{!CategoricalLinkable (semantics M (skel L1)) (semantics N (skel L1))}.

  Theorem layer_vcomp: ksim L1 L3 (M ++ N) (R ∘ S).
  Proof.
    unfold ksim in *.
    destruct HL1 as [Hsk1 [Hmod1 H1]]. clear HL1.
    destruct HL2 as [Hsk2 [Hmod2 H2]]. clear HL2.
    split. eapply linkorder_trans; eauto.
    split. apply compatible_app; eauto.
    eapply compatible_trans; eauto.

    edestruct (cmodule_krel S M (skel L1)). auto.
    exploit @categorical_compose_simulation'.
    constructor. exact X. apply H2.
    instantiate (1 := (skel L1)). apply linkorder_refl. auto.
    clear X. intros X.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. reflexivity.
    cbn. eapply compose_forward_simulations.
    apply H1. unfold layer_comp.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. apply X. clear X.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations.
    unfold layer_comp. apply assoc1.

    eapply categorical_compose_simulation';
      [ | apply identity_forward_simulation
        | apply linkorder_refl
        | eapply linkorder_trans; eauto
      ].

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations.
    apply lift_categorical_comp2.
    apply lifting_simulation.
    apply cmodule_app_simulation'; eauto.
  Qed.

End VCOMP.

Lemma layer_comp_extend_skel {K} M L sk sk':
  linkorder sk' sk -> linkorder (skel L) sk ->
  skel_extend (layer_comp L M sk') sk ≤ layer_comp (K2 := K) L M sk.
Proof.
  unfold layer_comp.
  replace (skel_extend (comp_semantics' (semantics M sk' @ K) L sk') sk)
    with (comp_semantics' (semantics M sk' @ K) L sk) by reflexivity.
  etransitivity. 2: { apply lift_comp_component1. }
  eapply categorical_compose_simulation';
                   [ apply identity_forward_simulation
                   | reflexivity | .. ]; auto.
Qed.

Lemma if_rewrite {A B} (f: A -> B) a b:
  (fun (i : bool) => f (if i then a else b)) = (fun i => if i then f a else f b).
Proof.
  apply Axioms.functional_extensionality; intros [|]; auto.
Qed.

Section HCOMP.

  Generalizable All Variables.
  Context `{R: crel K1 K2} {M N: cmodule} `(HL1: ksim L1 L3 M R) `(HL2: ksim L2 L3 N R).
  Variable (sk: AST.program unit unit).
  Hypothesis (Hk1: linkorder (skel L1) sk)
             (Hk2: linkorder (skel L2) sk).
  Let Mi := (fun i : bool => if i then semantics M sk else semantics N sk).
  Context `{!FlatLinkable Mi}.

  Let L i := match i with true => L1 | false => L2 end.

  Theorem layer_hcomp: ksim (flat_comp_semantics' L sk) L3 (M ++ N) R.
  Proof.
    unfold ksim in *.
    destruct HL1 as [Hsk1 [Hmod1 H1]]. clear HL1.
    destruct HL2 as [Hsk2 [Hmod2 H2]]. clear HL2.
    split. eapply linkorder_trans; eauto.
    split. apply compatible_app; (eapply compatible_trans; [ | eauto]); eauto.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations.

    set (Ls := fun i => match i with true => layer_comp L3 M (skel L1)
                             | false => layer_comp L3 N (skel L2) end).
    apply (flat_composition_simulation' _ _ _ Ls); try (intros [|]; auto). cbn.

    (* To use the distributivity, we first unify the code skeleton of the
       individual components being flat composed *)
    etransitivity. apply lift_flat_comp_component. cbn.
    rewrite if_rewrite with (f := fun x => skel_extend x sk).

    set (Ls := fun i => match i with true => layer_comp L3 M sk | false => layer_comp L3 N sk end).
    etransitivity. instantiate (1 := flat_comp_semantics' Ls sk).
    {
      apply flat_composition_simulation'.
      - intros [|]; apply layer_comp_extend_skel; auto;
          eapply linkorder_trans; eauto.
      - intros [|]; apply linkorder_refl.
    }

    subst Ls. unfold layer_comp.
    rewrite <- if_rewrite with (f := fun x => comp_semantics' x L3 sk).
    etransitivity.  apply distributivity2. constructor. exact true.
    eapply categorical_compose_simulation';
      [ | apply identity_forward_simulation
        | apply linkorder_refl
        | eapply linkorder_trans; eauto ].

    rewrite <- if_rewrite.
    etransitivity. apply lift_flat_comp2.
    apply lifting_simulation.
    apply cmodule_flat_comp_simulation; auto.
  Qed.

End HCOMP.

Section TCOMP.

  Context {K1 K2 K3 K4: Type} (R: krel K1 K2) (S: krel K3 K4).
  Context (L1: layer K1) (L2: layer K2) (L3: layer K3) (L4: layer K4).
  Context (M N: cmodule).
  Hypothesis (HL1: L2 ⊢ [R] M : L1) (HL2: L4 ⊢ [S] N : L3).
  Variable (sk: AST.program unit unit).
  Hypothesis (Hk1: linkorder (skel L1) sk) (Hk2: linkorder (skel L3) sk).
  Let Mi := (fun i : bool => if i then semantics M sk else semantics N sk).
  Context `{!FlatLinkable Mi}.
  Hypothesis Hdisjoint: forall i, vars S i -> vars R i -> False.

  Lemma layer_tcomp: ksim_mcc (tensor_comp_semantics' L1 L3 sk)
                              (tensor_comp_semantics' L2 L4 sk)
                              (M ++ N) (R * S).
  Proof.
    destruct HL1 as [Hsk1 [Hmod1 H1]]. clear HL1.
    destruct HL2 as [Hsk2 [Hmod2 H2]]. clear HL2.
    split. eapply linkorder_refl.
    split. apply compatible_app; (eapply compatible_trans; [ | eauto]); eauto.

    exploit @tensor_compose_simulation; [exact H1 | exact H2 | .. ]; eauto. intros H.
    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. exact H.

    unfold tensor_comp_semantics'. cbn.
    unfold layer_comp.

    etransitivity.
    {
      apply flat_composition_simulation'. instantiate (1 := fun i => match i with true => _ | false => _ end).
      intros [|].
      - instantiate (1 := comp_semantics' (semantics M (skel L1) @ (K2 * K4)) (lift_layer_k L2) (skel L1)).
        etransitivity.
        + apply mapB_monotonicity. etransitivity.
          * apply mapA_monotonicity. apply lift_categorical_comp1.
          * apply mapA_comp.
        + etransitivity.
          * apply mapB_comp'. typeclasses eauto.
          * eapply categorical_compose_simulation'.
            -- apply lts_lifting_assoc.
            -- reflexivity.
            -- apply linkorder_refl.
            -- auto.
      - instantiate (1 := comp_semantics' (semantics N (skel L3) @ (K2 * K4)) (layer_comm (lift_layer_k L4)) (skel L3)).
        etransitivity.
        + apply mapB_monotonicity. etransitivity.
          * apply mapB_monotonicity. etransitivity.
            -- apply mapA_monotonicity. apply lift_categorical_comp1.
            -- apply mapA_comp.
          * apply mapB_comp'. typeclasses eauto.
        + etransitivity.
          * apply mapB_comp'. typeclasses eauto.
          * eapply categorical_compose_simulation'.
            -- etransitivity.
               ++ apply map_both_monotonicity. apply lts_lifting_assoc.
               ++ apply lts_lifting_comm.
            -- reflexivity.
            -- apply linkorder_refl.
            -- auto.
      - intros [|]; auto.
    }

    set (LX:= fun i:bool => if i then semantics M (skel L1) @ (K2 * K4) else semantics N (skel L3) @ (K2 * K4)).
    set (LY:= fun i:bool => if i then lift_layer_k L2 else layer_comm (lift_layer_k L4)).
    set (Lsk:= fun i:bool => if i then skel L1 else skel L3).
    replace (flat_comp_semantics' _ sk) with (flat_comp_semantics' (fun i:bool => comp_semantics' (LX i) (LY i) (Lsk i)) sk).
    2: {
      subst LX  LY Lsk. cbn. f_equal. apply Axioms.functional_extensionality.
      intros [|]; reflexivity.
    }

    etransitivity. apply categorical_flat_interchangeable.
    eapply categorical_compose_simulation'; [ | reflexivity | apply linkorder_refl | apply linkorder_refl ].
    subst LX. rewrite <- if_rewrite with (f := fun x => x @ (K2 * K4)).
    etransitivity. apply lift_flat_comp2. apply lifting_simulation.
    etransitivity. 2: { apply cmodule_flat_comp_simulation. eauto. }
    etransitivity. apply lift_flat_comp_component. cbn.
    rewrite if_rewrite with (f := fun x => skel_extend x sk). reflexivity.
  Qed.

End TCOMP.

(* A composition of krel for absfun and bottom layers *)
Import AbstractStateRel.

Class BotRel {K1 K2: Type} (R: krel K1 K2) :=
  Rk_true: forall k1 k2, Rk R k1 k2.

Class AbsfunRel {K1 K2: Type} (R: krel K1 K2) :=
  {
    Rr_true: forall se k1 m, Rr R se k1 m;
    vars_empty: forall i, ~ vars R i;
  }.

Section ABSFUN_CC.

  Context (K1 K2: Type) (R: krel K1 K2).

  Inductive absfun_query: query (li_c@K1) -> query (li_c@K2) -> Prop :=
  | absfun_query_intro vf1 sg1 vargs1 m1 k1 k2:
      Rk R k1 k2 -> absfun_query (cq vf1 sg1 vargs1 m1, k1) (cq vf1 sg1 vargs1 m1, k2).

  Inductive absfun_reply: reply (li_c@K1) -> reply (li_c@K2) -> Prop :=
  | absfun_reply_intro retval1 m1 k1 k2:
      Rk R k1 k2 -> absfun_reply (cr retval1 m1, k1) (cr retval1 m1, k2).

  Program Definition absfun_kcc: callconv (li_c@K1) (li_c@K2) :=
    {|
      ccworld := unit;
      match_senv _ := eq;
      match_query _ := absfun_query;
      match_reply _ := absfun_reply;
    |}.
  Next Obligation. inv H0. reflexivity. Qed.
  Next Obligation. inv H. reflexivity. Qed.

End ABSFUN_CC.

Arguments absfun_kcc {K1 K2} _.

Section BOT_COMP.

  Context {K1 K2 K3} (R: krel K1 K2) (S: krel K2 K3).
  Context `{!AbsfunRel R}  `{!BotRel S}.

  Program Definition comp_krel : krel K1 K3 :=
    {|
      Rk k1 k3 := True;
      Rr se k1 m  := exists k2, Rk R k1 k2 /\ Rr S se k2 m;
      vars i := vars R i \/ vars S i;
    |}.
  Next Obligation.
    exploit @G_unchanged; eauto. eapply Mem.unchanged_on_implies; eauto.
    intros b ofs [v [Hv Hb]] Hvb. eexists; split; eauto.
  Qed.
  Next Obligation.
    exploit @G_valid; eauto. destruct H1; eauto.
    - exfalso. exploit @vars_empty; eauto.
    - eexists; split; eauto.
      Unshelve. exact ofs.
  Qed.

  Instance comp_krel_bot: BotRel comp_krel. easy. Qed.

  Lemma absfun_ccref: ccref comp_krel (absfun_kcc R @ krel_mcc S).
  Proof.
    intros [se [m1 m3]] ? ? [q1 kq1] [q3 kq3] Hse Hq. inv Hse. inv Hq.
    exists (se2, tt, mkrelw se2 (m1, m3)). split. cbn. split; constructor.
    split.
    - destruct H11 as [k2 [Rk2 Rm2]]. destruct H12.
      econstructor; split; econstructor; eauto.
      intros b ofs Hg. apply H10.
      eapply blocks_implies; eauto. intros. now right.
    - intros [r1 kr1] [r3 kr3] [[r2 kr2] [Hr1 Hr2]].
      destruct Hr2 as [w' [Hw' Hr2]]. inv Hr1. inv Hr2.
      exists (mkrelw se (m0, m4)). split.
      + inv Hw'. constructor; eauto.
        eapply Mem.unchanged_on_implies. eauto.
        intros. eapply other_blocks_implies; eauto.
        intros. now right.
      + constructor; eauto.
        * intros b ofs Hg. apply H15.
          eapply blocks_implies. eauto.
          intros. destruct H. exploit @vars_empty; intuition eauto. auto.
        * eexists; split; eauto.
  Qed.

End BOT_COMP.

Definition ksim_absfun {K1 K2: Type} (L1: layer K1) (L2: layer K2) (M: cmodule) (R: krel K1 K2) :=
  linkorder (skel L2) (skel L1) /\ skel_module_compatible M (skel L1) /\
  forward_simulation 1 (absfun_kcc R) L1 (layer_comp L2 M (skel L1)).

(* TODO: move this definition to somewhere else *)
Definition module_pure (M: cmodule): Prop :=
  forall p, In p M -> MCC.prog_syscall_free p /\ MCC.prog_side_effect_free p.

Lemma cmodule_krel_mcc {K1 K2} (R: krel K1 K2) M sk:
  module_pure M -> skel_module_compatible M sk ->
  forward_simulation R R (semantics M sk @ K1) (semantics M sk @ K2).
Proof.
  intros Hpure Hsk.

  eapply open_fsim_ccref. apply cc_compose_id_left.
  unfold flip. apply cc_compose_id_left.
  eapply compose_forward_simulations.
  apply lift_horizontal_comp1.

  eapply open_fsim_ccref. apply cc_compose_id_right.
  unfold flip. apply cc_compose_id_right.
  eapply compose_forward_simulations.
  2: { apply lift_horizontal_comp2. }

  apply SmallstepLinking.semantics_simulation'.
  - intros. induction M as [| p ps]; try easy.
    destruct i.
    + cbn. apply MCC.clight_sim.
      eapply Hpure; eauto. now left.
      eapply Hpure; eauto. now left.
    + apply IHps.
      * unfold module_pure; intros. eapply Hpure; eauto. now right.
      * unfold skel_module_compatible in *.
        rewrite -> Forall_forall in *.
        intros x Hx. apply Hsk. right. auto.
  - intros. induction M as [| p ps]; try easy.
    destruct i.
    + cbn. unfold skel_module_compatible in *.
      rewrite -> Forall_forall in *. apply Hsk.
      left. auto.
    + apply IHps.
      * unfold module_pure; intros. eapply Hpure; eauto. now right.
      * unfold skel_module_compatible in *.
        rewrite -> Forall_forall in *.
        intros x Hx. apply Hsk. right. auto.
Qed.

Section ABSFUN.

  Context {K1 K2 K3 L1 L2 L3} (M N: cmodule) (R: krel K1 K2) (S: krel K2 K3)
          `(!AbsfunRel R) `(!BotRel S) (HL1: ksim_absfun L1 L2 M R) (HL2: ksim_mcc L2 L3 N S).
  Hypothesis (Hpure: module_pure M).
  Context `{!CategoricalLinkable (semantics M (skel L1)) (semantics N (skel L1))}.

  Theorem absfun_comp: ksim_mcc L1 L3 (M ++ N) (comp_krel R S).
  Proof.
    destruct HL1 as [Hsk1 [Hmod1 H1]]. clear HL1.
    destruct HL2 as [Hsk2 [Hmod2 H2]]. clear HL2.
    split. eapply linkorder_trans; eauto.
    split. apply compatible_app; eauto.
    eapply compatible_trans; eauto.

    eapply open_fsim_ccref. reflexivity. unfold flip. apply absfun_ccref; auto.
    edestruct (cmodule_krel_mcc S M (skel L1)); auto.
    exploit @categorical_compose_simulation'.
    constructor. exact X. apply H2.
    instantiate (1 := (skel L1)). apply linkorder_refl. auto.
    clear X. intros X.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. reflexivity.
    cbn. eapply compose_forward_simulations.
    apply H1. unfold layer_comp.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. apply X. clear X.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations.
    unfold layer_comp. apply assoc1.

    eapply categorical_compose_simulation';
      [ | apply identity_forward_simulation
        | apply linkorder_refl
        | eapply linkorder_trans; eauto
      ].

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations.
    apply lift_categorical_comp2.
    apply lifting_simulation.
    apply cmodule_app_simulation'; eauto.
  Qed.

End ABSFUN.

Section PUREREF.

  Context {K1 K2 K3 L1 L2 L3} (M: cmodule)
          (R: krel K1 K2) (S: krel K2 K3) `(!AbsfunRel R) `(!BotRel S)
          (HL1: forward_simulation 1 (absfun_kcc R) L1 L2) (HL2: L3 ⊢ [S] M : L2).

  Theorem pureref_comp: L3 ⊢ [comp_krel R S] M : L1.
  Proof.
    destruct HL2 as [Hsk2 [Hmod2 H2]]. clear HL2.
    assert (Hsk1: skel L1 = skel L2).
    { destruct HL1. exact (fsim_skel X). }
    unfold ksim_mcc. replace (skel L1). clear Hsk1. intuition.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    apply absfun_ccref; eauto.
    eapply compose_forward_simulations; eauto.
  Qed.

End PUREREF.

Instance prod_bot_rel {K1 K2 K3 K4} (R1: krel K1 K2) (R2: krel K3 K4)
         `(!BotRel R1) `(!BotRel R2): BotRel (R1 * R2).
Proof. intros [k1 k3] [k2 k4]. split; eauto. Qed.

Section NULL.
  Context {K: Type}.

  Definition null_lts : lts li_null (li_c @ K) unit :=
    {|
      genvtype := unit;
      Smallstep.step _ := fun s1 t s2 => False;
      Smallstep.initial_state := fun q s => False;
      Smallstep.at_external := fun s q => False;
      Smallstep.after_external := fun s1 r s2 => False;
      Smallstep.final_state := fun s r => False;
      Smallstep.globalenv := tt
    |}.

  Definition null_layer sk : Smallstep.semantics li_null (li_c @ K) :=
    {|
      Smallstep.skel := sk;
      Smallstep.state := unit;
      Smallstep.activate _ := null_lts;
      Smallstep.footprint _ := False;
    |}.

End NULL.

Lemma null_layer_fsim {K1 K2: Type} sk1 sk2 sk:
  forward_simulation 1 1 (tensor_comp_semantics' (@null_layer K1 sk1) (@null_layer K2 sk2) sk) (null_layer sk).
Proof.
  constructor. econstructor.
  - reflexivity.
  - intros. intuition. inv H. destruct x; inv H0.
  - instantiate (1 := fun _ _ _ => _). cbn beta.
    intros se1 se2 w Hse Hse1. inv Hse.
    apply forward_simulation_step; cbn.
    + intros. inv H0. destruct i; inv H1;inv H; inv H.
    + intros. inv H0. destruct i. inv H1. inv H0. inv H1. inv H0.
    + intros. inv H0. destruct i. inv H1. inv H0. inv H1. inv H0.
    + intros. inv H. destruct i.
      * destruct s. destruct s'. inv H1. inv H.
      * destruct s. destruct s'. inv H1. inv H.
  - apply well_founded_ltof.
    Unshelve. intros. exact True.
Qed.
