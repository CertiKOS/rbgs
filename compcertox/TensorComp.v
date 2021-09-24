Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Linking.
Require Import Lifting AbstractStateRel.

Section Properties.

  Context {K1 K2 K3 K4} (R1: krel K1 K2) (R2: krel K3 K4).
  Lemma prod_match_reply w r1 r2 k1 k2 k3 k4:
    match_reply R1 w (r1, k1) (r2, k2) ->
    Rk R2 k3 k4 -> Rr R2 k3 (cr_mem r2) ->
    (* kmrel (krel_crel R2) (cr_mem r1, k3) (cr_mem r2, k4) -> *)
    match_reply (R1 * R2) w (r1, (k1, k3)) (r2, (k2, k4)).
  Proof.
    intros [w' [Hw' Hr]] H. exists w'; split.
    - cbn in *. eapply Mem.unchanged_on_implies; eauto.
      cbn in *. intros. intro contra. apply H1. now left.
    - inv Hr. cbn in *. constructor; eauto.
      + split; eauto.
      + split; eauto.
  Qed.

  Lemma prod_match_query w q1 q2 k1 k2 k3 k4:
    match_query (R1 * R2) w (q1, (k1, k3)) (q2, (k2, k4)) ->
    match_query R1 w (q1, k1) (q2, k2) /\ Rk R2 k3 k4 /\ Rr R2 k3 w.
  Proof.
    intros. inv H. repeat apply conj; cbn in *.
    constructor; eauto.
    - intros b ofs Hg. apply H9. now left.
    - firstorder.
    - firstorder.
    - firstorder.
    - firstorder.
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
    intros [w' [Hw H]]. exists w'; split.
    - cbn in *. eapply Mem.unchanged_on_implies. eauto. cbn. intuition.
    - inv H. econstructor; auto.
      + cbn in *. intuition.
      + cbn in *. intuition.
  Qed.

End Properties.

Generalizable All Variables.

(* A li_func convert from one language interface to another. This is useful
   because equivalence on the level of language interfaces can't be defined
   as definitional equality. *)
Record li_func (liA liB: language_interface) :=
  mk_li_func {
      query_func: query liB -> query liA;
      reply_func: reply liB -> reply liA;
    }.
Arguments query_func {liA liB} _ _.
Arguments reply_func {liA liB} _ _.

Section APPLY.

  Context {liA1 liA2 liB1 liB2 S} (L: lts liA1 liB1 S)
          (FA: li_func liA1 liA2) (FB: li_func liB1 liB2).

  Definition lts_map: lts liA2 liB2 S :=
    {|
      genvtype := genvtype L;
      globalenv := globalenv L;
      step := step L;
      initial_state q s := initial_state L (query_func FB q) s;
      at_external s q := at_external L s (query_func FA q);
      after_external s r s' := after_external L s (reply_func FA r) s';
      final_state s r := final_state L s (reply_func FB r);
    |}.

End APPLY.

Definition semantics_map {liA1 liA2 liB1 liB2} (L: semantics liA1 liB1)
           (F: li_func liA1 liA2) (G: li_func liB1 liB2) :=
  {|
    skel := skel L;
    activate se := lts_map (L se) F G;
    footprint := footprint L;
  |}.

Definition id_li_func {liA} := mk_li_func liA liA id id.

Definition map_outgoing {liA liB1 liB2} (L: semantics liA liB1) (F: li_func liB1 liB2) :=
  semantics_map L id_li_func F.

Definition map_incoming {liA1 liA2 liB} (L: semantics liA1 liB) (F: li_func liA1 liA2) :=
  semantics_map L F id_li_func.

Definition map_both {li1 li2} (L: semantics li1 li1) (F: li_func li1 li2) :=
  semantics_map L F F.

Infix "##" := map_incoming (at level 50): lts_scope.
Infix "$$" := map_outgoing (at level 50): lts_scope.
Infix "%%" := map_both (at level 50): lts_scope.

(* The generated definition looks funky
   Try use idtac as default *)
Program Definition li_func_null {K}: li_func (li_null @ K) li_null :=
  {|
    query_func q := match q with end;
    reply_func r := match r with end;
  |}.

Program Definition li_func_k {li K1 K2}: li_func ((li@K1)@K2) (li@(K1*K2)) :=
  {|
    query_func '(q, k) := ((q, fst k), snd k);
    reply_func '(r, k) := ((r, fst k), snd k);
  |}.

Program Definition li_func_comm {li K1 K2}: li_func (li@(K1*K2)) (li@(K2*K1)) :=
  {|
    query_func '(q, (k1, k2)) := (q, (k2, k1));
    reply_func '(r, (k1, k2)) := (r, (k2, k1));
  |}.

Definition lift_layer {li K} (L: semantics li_null li): semantics li_null (li@K) :=
  L@K ## li_func_null.

Definition lift_layer_k {li K1 K2} (L: semantics li_null (li@K1)): semantics li_null (li@(K1*K2)) :=
  L@K2 ## li_func_null $$ li_func_k.

Definition layer_comm {li K1 K2} (L: semantics li_null (li@(K2*K1))): semantics li_null (li@(K1*K2)) :=
  L $$ li_func_comm.

Definition lts_comm {li K1 K2} (L: semantics (li@(K2*K1)) (li@(K2*K1))): semantics (li@(K1*K2)) (li@(K1*K2)) :=
  L %% li_func_comm.

Lemma mapping_monotonicity1 {liA liB1 liB2} (L1 L2: semantics liA liB1) (F: li_func liB1 liB2):
  L1 ≤ L2 -> L1 $$ F ≤ L2 $$ F.
Proof.
Admitted.

Lemma mapping_monotonicity2 {liA1 liA2 liB} (L1 L2: semantics liA1 liB) (F: li_func liA1 liA2):
  L1 ≤ L2 -> L1 ## F ≤ L2 ## F.
Proof.
Admitted.

Lemma mapping_monotonicity3 {liA1 liA2} (L1 L2: semantics liA1 liA1) (F: li_func liA1 liA2):
  L1 ≤ L2 -> L1 %% F ≤ L2 %% F.
Proof.
Admitted.

Lemma mapping_comp1 {liA1 liA2 liB liC} (L1: semantics liB liC) (L2: semantics liA1 liB) (F: li_func liA1 liA2) sk:
  (comp_semantics' L1 L2 sk) ## F ≤ comp_semantics' L1 (L2 ## F) sk.
Proof.
Admitted.

Lemma mapping_comp2 {liA liB1 liB2} (L1: semantics liB1 liB1) (L2: semantics liA liB1) (F: li_func liB1 liB2) sk:
  (comp_semantics' L1 L2 sk) $$ F ≤ comp_semantics' (L1 %% F) (L2 $$ F) sk.
Proof.
Admitted.

Lemma layer_comm_simulation {K1 K2 K3 K4} (R: krel K1 K2) (S: krel K3 K4) L1 L2:
  forward_simulation 1 (R * S) L1 L2 -> forward_simulation 1 (S * R) (layer_comm L1) (layer_comm L2).
Proof.
  intros [[]]. constructor. econstructor; eauto.
  instantiate (1 := fsim_match_states).
  intros. exploit fsim_lts; eauto. clear. intros HL.
  constructor.
  - intros [q1 [k3 k1]] [q [k4 k2]] s1 Hq H.
    edestruct @fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
    apply match_query_comm; eauto. apply H.
    eexists _, _. split. apply Hs2. apply Hs.
  - intros idx s1 s2 [r [k3 k1]] Hs H.
    edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
    apply H. destruct r2 as [r2 [k2 k4]].
    eexists (_, (_, _)). split. apply Hr2.
    apply match_reply_comm. apply Hr.
  - intros ? ? ? [ ].
  - intros. edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
Qed.

Lemma lts_lifting_assoc (K1 K2: Type) {li} (L: semantics li li):
  (L @ K1) @ K2 %% li_func_k ≤ L @ (K1 * K2).
Proof.
Admitted.

Lemma lts_lifting_comm (K1 K2: Type) {li} (L: semantics li li):
  L @ (K1 * K2) %% li_func_comm ≤ L @ (K2 * K1).
Proof.
Admitted.


Section TENSOR.

  Context {K1 K2} (L1: semantics li_null (li_c@K1)) (L2: semantics li_null (li_c@K2)).
  Context {J1 J2} (jcc: krel J1 J2) (kcc: krel K1 K2).
  Context (HL: fsim_components 1 kcc L1 L2).
  Context (se1 se2: Genv.symtbl) (w : ccworld (kcc * jcc)).
  Context (Hse: match_senv (kcc * jcc) w se1 se2).
  Context (Hse1: Genv.valid_for (skel L1) se1).

  Hypothesis Hdisjoint: forall b ofs, G jcc b ofs -> G kcc b ofs -> False.

  Inductive state_match: fsim_index HL -> state L1 * J1 -> state L2 * J2 -> Prop :=
  | lift_state_match i s1 j1 s2 j2:
      fsim_match_states HL se1 se2 w i s1 s2 ->
      Rk jcc j1 j2 -> Rr jcc j1 w ->
      state_match i (s1, j1) (s2, j2).

  Lemma lift_layer_semantics_simulation:
    fsim_properties 1 (kcc * jcc) se1 se2 w
      (lift_layer_k L1 se1) (lift_layer_k L2 se2)
      (fsim_index HL) (fsim_order HL) state_match.
  Proof.
    split; cbn.
    - intros [q1 [k1 j1]] [q2 [k2 j2]] [s1 sj1] Hq [H Hj]; cbn in *.
      subst sj1. eapply prod_match_query in Hq.
      pose proof (fsim_lts HL _ w Hse Hse1).
      edestruct @fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
      apply Hq. exists idx, (s2, j2). split. split; auto.
      constructor; auto. apply Hq. apply Hq.
    - intros idx [s1 sj1] [s2 sj2] [r1 [kr1 jr1]] Hs [H Hj].
      inv Hs. pose proof (fsim_lts HL _ w Hse Hse1).
      edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
      cbn [fst snd] in *. destruct r2 as [r2 rk2]. subst sj1.
      exists (r2, (rk2, sj2)). split. split; eauto.
      apply prod_match_reply. apply Hr. auto.
      eapply G_unchanged; eauto.
      destruct Hr as [w' [Hw' Hr]]. inv Hr.
      eapply Mem.unchanged_on_implies. apply Hw'.
      cbn. intros. intros contra. eapply Hdisjoint; eauto.
    - intros i [s1 sj1] [s2 sj2] [ ].
    - intros [s1 sj1] t [s1' sj1'] H idx [s2 sj2] Hs. destruct H as [H <-].
      inv Hs. pose proof (fsim_lts HL _ w Hse Hse1).
      edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
      exists idx', (s2', sj2). split.
      + destruct Hs2'; [left | right].
        apply lifting_step_plus; eauto.
        split. apply lifting_step_star; eauto. intuition. intuition.
      + constructor; eauto.
  Qed.

End TENSOR.

Lemma layer_lifting_simulation {K1 K2 J1 J2} (kcc: krel K1 K2) (jcc: krel J1 J2) L1 L2:
  (forall b ofs, G jcc b ofs -> G kcc b ofs -> False) -> forward_simulation 1 kcc L1 L2 ->
  forward_simulation 1 (kcc * jcc) (lift_layer_k L1) (lift_layer_k L2).
Proof.
  intros Hdisjoint [HL]. constructor.
  eapply Forward_simulation with (fsim_order HL) (state_match L1 L2 jcc kcc HL).
  - eapply (fsim_skel HL).
  - intros. apply (fsim_footprint HL i).
  - intros. eapply lift_layer_semantics_simulation; eauto.
  - apply (fsim_order_wf HL).
Qed.

(* The definition of tensor composition in terms of flat composition *)
Section TENSOR.

  Context {K1 K2: Type} (L1: layer K1) (L2: layer K2).
  Let LK1 := lift_layer_k (K2 := K2) L1.
  Let LK2 := layer_comm (lift_layer_k (K2 := K1) L2).
  Let LK i := match i with true => LK1 | false => LK2 end.

  Definition tensor_comp_semantics' sk := flat_comp_semantics' LK sk.

End TENSOR.

Section MONOTONICITY.

  Context {K1 K2 K3 K4: Type} (R: krel K1 K2) (S: krel K3 K4).
  Context (L1: layer K1) (L2: layer K2) (L3: layer K3) (L4: layer K4).
  Hypothesis (HL1: forward_simulation 1 R L1 L2) (HL2: forward_simulation 1 S L3 L4).
  Variable (sk: AST.program unit unit).
  Hypothesis (Hsk1: linkorder (skel L1) sk) (Hsk2: linkorder (skel L3) sk).
  Hypothesis (Hdisjoint: forall b ofs, G R b ofs -> G S b ofs -> False).

  Lemma tensor_compose_simulation:
    forward_simulation 1 (R * S) (tensor_comp_semantics' L1 L3 sk) (tensor_comp_semantics' L2 L4 sk).
  Proof.
    unfold tensor_comp_semantics'. apply flat_composition_simulation'.
    - intros [|].
      + apply layer_lifting_simulation; eauto.
      + apply layer_comm_simulation.
        apply layer_lifting_simulation; eauto.
    - intros [|]; auto.
  Qed.

End MONOTONICITY.

Section INTERC.

  Context {I: Type} {liA liB liC: language_interface}.
  Context (L1: I -> semantics liB liC) (L2: I -> semantics liA liB).
  Context (ski: I -> AST.program unit unit).
  Variable (sk: AST.program unit unit).
  Let LC i := comp_semantics' (L1 i) (L2 i) (ski i).

  Lemma categorical_flat_interchangeable:
    flat_comp_semantics' LC sk ≤ comp_semantics' (flat_comp_semantics' L1 sk) (flat_comp_semantics' L2 sk) sk.
  Proof.
  Admitted.

End INTERC.

Require Import CModule.
Require Import Composition.
Require Import FunctionalExtensionality.

Section TCOMP.

  Context {K1 K2 K3 K4: Type} (R: krel K1 K2) (S: krel K3 K4).
  Context (L1: layer K1) (L2: layer K2) (L3: layer K3) (L4: layer K4).
  Context (M N: cmodule).

  Hypothesis (HL1: ksim L1 L2 M R) (HL2: ksim L3 L4 N S).
  Variable (sk: AST.program unit unit).
  Hypothesis (Hk1: linkorder (skel L1) sk) (Hk2: linkorder (skel L3) sk).
  Let Mi := (fun i : bool => if i then semantics M sk else semantics N sk).
  Context `{!FlatLinkable Mi}.
  Hypothesis Hdisjoint: forall b ofs, AbstractStateRel.G S b ofs -> AbstractStateRel.G R b ofs -> False.

  Lemma layer_tcomp: ksim (tensor_comp_semantics' L1 L3 sk)
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
        + apply mapping_monotonicity1. etransitivity.
          * apply mapping_monotonicity2. apply lift_categorical_comp1.
          * apply mapping_comp1.
        + etransitivity.
          * apply mapping_comp2.
          * eapply categorical_compose_simulation'.
            -- apply lts_lifting_assoc.
            -- reflexivity.
            -- apply linkorder_refl.
            -- auto.
      - instantiate (1 := comp_semantics' (semantics N (skel L3) @ (K2 * K4)) (layer_comm (lift_layer_k L4)) (skel L3)).
        etransitivity.
        + apply mapping_monotonicity1. etransitivity.
          * apply mapping_monotonicity1. etransitivity.
            -- apply mapping_monotonicity2. apply lift_categorical_comp1.
            -- apply mapping_comp1.
          * apply mapping_comp2.
        + etransitivity.
          * apply mapping_comp2.
          * eapply categorical_compose_simulation'.
            -- etransitivity.
               ++ apply mapping_monotonicity3. apply lts_lifting_assoc.
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
      subst LX  LY Lsk. cbn. f_equal. apply functional_extensionality.
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
