Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Clight_ Linking.
Require Import AbstractStateRel Lifting CModule TensorComp.
Require Import Ctypes.

Section PROG_LAYER_DEF.
  (* L1 is the high level spec with K1 as the abstract data whereas the program
     running on top of L2 is the low level spec *)
  Context {K1 K2: Type} (L1: layer K1) (L2: layer K2) (p: Clight_.program).

  Definition prog_layer_comp sk := comp_semantics' (Clight_.semantics2 p @ K2) L2 sk.

  (* The version of certified abstraction layers for vertical composition *)
  Definition prog_ksim (R: crel K1 K2) :=
    linkorder (skel L2) (skel L1) /\ linkorder (AST.erase_program p) (skel L1) /\
    forward_simulation 1 R L1 (prog_layer_comp (skel L1)).

  (* The version that is horizontally compositional *)
  Definition prog_ksim_mcc (R: krel K1 K2) :=
    linkorder (skel L2) (skel L1) /\ linkorder (AST.erase_program p) (skel L1) /\
    forward_simulation 1 (krel_mcc R) L1 (prog_layer_comp (skel L1)).

  Lemma prog_ksim_ref (R: krel K1 K2): prog_ksim_mcc R -> prog_ksim R.
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

  Definition ksim_ref (R: krel K1 K2): ksim_mcc R -> ksim R.
  Proof.
    unfold ksim, ksim_mcc. intuition.
    apply layer_fsim_refine. auto.
  Qed.

End MOD_LAYER_DEF.

Lemma singleton_ksim {K1 K2} L1 L2 p (R: crel K1 K2): prog_ksim L1 L2 p R -> ksim L1 L2 (p :: nil) R.
Proof.
Admitted.

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
  Context {liA liB liC} (L1: Smallstep_.semantics liB liC) (L2: Smallstep_.semantics liA liB).
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

  Hypothesis (HL1: ksim_mcc L1 L2 M R) (HL2: ksim_mcc L3 L4 N S).
  Variable (sk: AST.program unit unit).
  Hypothesis (Hk1: linkorder (skel L1) sk) (Hk2: linkorder (skel L3) sk).
  Let Mi := (fun i : bool => if i then semantics M sk else semantics N sk).
  Context `{!FlatLinkable Mi}.
  Hypothesis Hdisjoint: forall b ofs, AbstractStateRel.G S b ofs -> AbstractStateRel.G R b ofs -> False.

  Lemma layer_tcomp: ksim_mcc (tensor_comp_semantics' L1 L3 sk)
                              (tensor_comp_semantics' L2 L4 sk)
                              (M ++ N) (R * S).
  Proof.
    unfold ksim in *.
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
