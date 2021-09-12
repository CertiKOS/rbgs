Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Clight_ Linking.
Require Import AbstractStateRel Lifting CModule.
Require Import Ctypes.

Definition prog_layer_comp {K} (p: Clight_.program) (L: layer K) sk :=
  comp_semantics' (Clight_.semantics2 p @ K) L sk.

Definition prog_ksim {K1 K2: Type} (L1: layer K1) (L2: layer K2)
           (p: Clight_.program) (R: rel_adt K1 K2) :=
  linkorder (skel L2) (skel L1) /\
  linkorder (AST.erase_program p) (skel L1) /\
  forward_simulation 1 R L1 (prog_layer_comp p L2 (skel L1)).

Definition layer_comp {K} (M: cmodule) (L: layer K) sk :=
  comp_semantics' (semantics M sk @ K) L sk.

Definition ksim {K1 K2: Type} (L1: layer K1) (L2: layer K2)
           (M: cmodule) (R: rel_adt K1 K2) :=
  linkorder (skel L2) (skel L1) /\
  skel_module_compatible M (skel L1) /\
  forward_simulation 1 R L1 (layer_comp M L2 (skel L1)).

Lemma singleton_ksim {K1 K2} L1 L2 p (R: rel_adt K1 K2):
  prog_ksim L1 L2 p R -> ksim L1 L2 (p :: nil) R.
Proof.
Admitted.

Lemma compatible_app sk M N:
  skel_module_compatible M sk ->
  skel_module_compatible N sk ->
  skel_module_compatible (M ++ N) sk.
Proof.
  unfold skel_module_compatible.
  rewrite !Forall_forall.
  intros Hm Hn p Hp. apply in_app_or in Hp.
  destruct Hp; [ apply Hm | apply Hn ]; auto.
Qed.

Lemma compatible_trans sk1 sk2 N:
  linkorder sk1 sk2 ->
  skel_module_compatible N sk1 ->
  skel_module_compatible N sk2.
Proof.
  unfold skel_module_compatible.
  rewrite !Forall_forall.
  intros; eapply linkorder_trans; eauto.
Qed.

Section SKEL_EXT.
  Context {liA liB liC}
          (L1: Smallstep_.semantics liB liC)
          (L2: Smallstep_.semantics liA liB).
  Lemma skel_extend_compose sk sk':
    skel_extend (comp_semantics' L1 L2 sk) sk' ≤ comp_semantics' L1 L2 sk'.
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

  Context {K1 K2 K3 L1 L2 L3} {M N: cmodule}
          {R: rel_adt K1 K2} {S: rel_adt K2 K3}
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
  skel_extend (layer_comp M L sk') sk ≤ layer_comp (K := K) M L sk.
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
  Context `{R: rel_adt K1 K2} {M N: cmodule}
          `(HL1: ksim L1 L3 M R) `(HL2: ksim L2 L3 N R).
  Variable (sk: AST.program unit unit).
  Hypothesis (Hk1: linkorder (skel L1) sk)
             (Hk2: linkorder (skel L2) sk).
  Let Mi := (fun i : bool => if i then semantics M sk else semantics N sk).
  Context `{!FlatLinkable Mi}.

  Let L i := match i with true => L1 | false => L2 end.

  Theorem layer_hcomp:
    ksim (flat_comp_semantics' L sk) L3 (M ++ N) R.
  Proof.
    unfold ksim in *.
    destruct HL1 as [Hsk1 [Hmod1 H1]]. clear HL1.
    destruct HL2 as [Hsk2 [Hmod2 H2]]. clear HL2.
    split. eapply linkorder_trans; eauto.
    split. apply compatible_app; (eapply compatible_trans; [ | eauto]); eauto.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations.

    set (Ls := fun i => match i with true => layer_comp M L3 (skel L1)
                             | false => layer_comp N L3 (skel L2) end).
    apply (flat_composition_simulation' _ _ _ Ls); try (intros [|]; auto). cbn.

    (* To use the distributivity, we first unify the code skeleton of the
       individual components being flat composed *)
    etransitivity. apply lift_flat_comp_component. cbn.
    rewrite if_rewrite with (f := fun x => skel_extend x sk).

    set (Ls := fun i => match i with true => layer_comp M L3 sk | false => layer_comp N L3 sk end).
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

Require Import TensorComp.
(* Overriding notations *)
Import Smallstep_.

(* Any call into the empty layer yields undefined behavior *)

Definition empty_ident := 1%positive.

Definition empty_layer {K}: semantics li_null (li_c@K):=
  {|
    skel := AST.mkprogram nil nil empty_ident;
    state := Empty_set;
    footprint id := False;
    activate se :=
      {|
        genvtype := unit;
        globalenv := tt;
        step _ _ _ _ := False;
        initial_state _ _ := False;
        at_external _ _ := False;
        after_external _ _ _ := False;
        final_state _ _ := False;
      |};
  |}.

Lemma empty_sk_bot {K}: forall sk, linkorder (skel (@empty_layer K)) sk.
Admitted.

Generalizable All Variables.

Section APPROX.
  Context {E1 E2: Type}.
  Context (LM LN: semantics li_c li_c).
  Let LMN i := match i with true => LM | false => LN end.
  Context `(M: mem_ops).
  Variable (sk: AST.program unit unit).

  Let L1 := comp_semantics' (LM @ E1) empty_layer sk.
  Let L2 := comp_semantics' (LN @ E2) empty_layer sk.
  Let L := comp_semantics' ((SmallstepLinking_.semantics' LMN sk) @ (E1 * E2)) empty_layer sk.

  Lemma tensor_composition_approximation:
    Layer.tensor_semantics' L1 L2 M sk ≤ L.
  Admitted.

End APPROX.

Notation "R1 ⊗ R2" := (tcomp_rel R1 R2) (left associativity, at level 50): krel_scope.

Section TCOMP.

  Context {M N: cmodule}
          (* The C implement is supposed to be closed programs so E1 and E2 will
             be abstract data of the unit type or a product of the unit type if
             the implementation is a composition of several primitive layers *)
          `{R: rel_adt K1 E1} `{S: rel_adt K2 E2}
          `(HL1: ksim L1 empty_layer M R) `(HL2: ksim L2 empty_layer N S).
  Variable (sk: AST.program unit unit).
  Hypothesis (Hk1: linkorder (skel L1) sk) (Hk2: linkorder (skel L2) sk).
  Context (INV: CallConv_Invariants R S).

  (* The memory operations used in the layer composition is irrelevant because
     the layer interface only updates the abstract data. So theoretically we
     can feed whatever mem_ops to the definition and it should be provable *)
  Let L := Layer.tensor_semantics' L1 L2 INV sk.

  Lemma layer_tcomp:
    ksim L empty_layer (M ++ N) (R ⊗ S).
  Proof.
    unfold ksim in *.
    destruct HL1 as [Hsk1 [Hmod1 H1]]. clear HL1.
    destruct HL2 as [Hsk2 [Hmod2 H2]]. clear HL2.
    split. eapply linkorder_trans; eauto.
    split. apply compatible_app; (eapply compatible_trans; [ | eauto]); eauto.
    clear Hsk1 Hmod1 Hsk2 Hmod2.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations.
    {
      eapply Layer.tensor_compose_simulation'; eauto.
    }

    etransitivity.
    {
      replace (skel L1) with sk.
      replace (skel L2) with sk.
      apply tensor_composition_approximation.
      admit.
      admit.
    }

    unfold layer_comp.

    eapply categorical_compose_simulation'.
    - apply lifting_simulation. eapply cmodule_app_simulation.
    - reflexivity.
    - apply linkorder_refl.
    - apply empty_sk_bot.
  Admitted.

End TCOMP.
