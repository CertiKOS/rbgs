From Coq Require Import
     Relations RelationClasses
     List FinFun.
From compcertox Require Import
     Lifting AbRel.
From compcert.lib Require Import
     Coqlib.
From compcert.common Require Import
     LanguageInterface Events
     Globalenvs Smallstep
     Linking Memory Values
     CallconvAlgebra
     CategoricalComp
     FlatComp.

Generalizable All Variables.
Close Scope Z_scope.

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

Class LiSurjective {liA liB} (F: li_func liA liB) :=
  LiSurj: Surjective (query_func F) /\ Surjective (reply_func F).

Arguments LiSurjective {_ _} _.

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

Definition semantics_map {liA1 liA2 liB1 liB2} (L: semantics liA1 liB1) F G: semantics liA2 liB2 :=
  {|
    skel := skel L;
    activate se := lts_map (L se) F G;
    footprint := footprint L;
  |}.

Definition map_monotonicity {liA1 liA2 liB1 liB2} L1 L2 (F: li_func liA1 liA2) (G: li_func liB1 liB2):
  L1 ≤ L2 -> semantics_map L1 F G ≤ semantics_map L2 F G.
Proof.
  intros [[]]. constructor. econstructor; eauto.
  instantiate (1 := fsim_match_states).
  intros. exploit fsim_lts; eauto. clear. intros HL.
  constructor.
  - intros q1 q2 s1 Hq H. inv Hq.
    edestruct @fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
    reflexivity. apply H.
    eexists _, _. split. apply Hs2. apply Hs.
  - intros idx s1 s2 r Hs H.
    edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
    apply H. inv Hr. eexists. split.
    apply Hr2. reflexivity.
  - intros idx s1 s2 q1 Hs Ht. exists tt.
    edestruct @fsim_match_external as (wx & qx2 & Hqx2 & Hqx & Hsex & H); eauto. apply Ht.
    inv Hqx. inv Hsex. exists q1; repeat apply conj; try constructor. apply Hqx2.
    intros r1 ? ? [ ] He. edestruct H as (idx' & s2' & Hs2' & Hs'); eauto. reflexivity.
    apply He. eexists _, _. split. apply Hs2'. apply Hs'.
  - intros. edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
Qed.

Definition id_li_func {liA} := mk_li_func liA liA id id.

Definition mapA {liA1 liA2 liB} (L: semantics liA1 liB) (F: li_func liA1 liA2) := semantics_map L F id_li_func.
Notation "F >> L" := (mapA L F) (at level 50): lts_scope.

Lemma mapA_monotonicity {liA1 liA2 liB} (L1 L2: semantics liA1 liB) (F: li_func liA1 liA2):
  L1 ≤ L2 -> F >> L1 ≤ F >> L2.
Proof. apply map_monotonicity. Qed.

Definition mapB {liA liB1 liB2} (L: semantics liA liB1) (F: li_func liB1 liB2) := semantics_map L id_li_func F.
Notation "L << F" := (mapB L F) (at level 50): lts_scope.

Lemma mapB_monotonicity {liA liB1 liB2} (L1 L2: semantics liA liB1) (F: li_func liB1 liB2):
  L1 ≤ L2 -> L1 << F ≤ L2 << F.
Proof. apply map_monotonicity. Qed.

Definition map_both {li1 li2} (L: semantics li1 li1) (F: li_func li1 li2) := semantics_map L F F.
Notation "F $$ L" := (map_both L F) (at level 50): lts_scope.
Lemma map_both_monotonicity {liA1 liA2} (L1 L2: semantics liA1 liA1) (F: li_func liA1 liA2):
  L1 ≤ L2 -> map_both L1 F ≤ map_both L2 F.
Proof. apply map_monotonicity. Qed.


Section MAPA_COMP.
  Context {liA1 liA2 liB liC} (L1: semantics liB liC) (L2: semantics liA1 liB) (F: li_func liA1 liA2).

  Inductive mapA_ms : comp_state L1 L2 -> comp_state L1 (F >> L2) -> Prop :=
  | mapA_ms1 s: mapA_ms (st1 _ _ s) (st1 _ _ s)
  | mapA_ms2 s1 s2: mapA_ms (st2 _ _ s1 s2) (st2 _ (F >> L2) s1 s2).

  Lemma mapA_comp sk: F >> (comp_semantics' L1 L2 sk) ≤ comp_semantics' L1 (F >> L2) sk.
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    intros se _ [ ] [ ] _. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := mapA_ms);
      cbn; intros; subst; unfold id in *.
    - inv H0. eexists; split; constructor. auto.
    - inv H0; inv H. eexists; split; constructor; auto.
    - inv H0; inv H. eexists _, _. intuition eauto.
      constructor; auto. subst. inv H0. eexists; split; constructor. auto.
    - inv H; inv H0; eexists; split;
        [ apply step1 | | apply step2 | | eapply step_push | | eapply step_pop |  ]; repeat constructor; eauto.
    - apply well_founded_ltof.
      Unshelve. exact tt.
  Qed.
End MAPA_COMP.

Section MAPB_COMP.

  Context {liA liB1 liB2} (L1: semantics liB1 liB1) (L2: semantics liA liB1) (F: li_func liB1 liB2).

  Inductive mapB_ms : comp_state L1 L2 -> comp_state (F $$ L1) (L2 << F) -> Prop :=
  | mapB_ms1 s: mapB_ms (st1 _ _ s) (st1 (F $$ L1) _ s)
  | mapB_ms2 s1 s2: mapB_ms (st2 _ _ s1 s2) (st2 (F $$ L1) (L2 << F) s1 s2).

  Context `{HS: !LiSurjective F}.

  Lemma mapB_comp' sk: (comp_semantics' L1 L2 sk) << F ≤ comp_semantics' (F $$ L1) (L2 << F) sk.
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    intros se _ [ ] [ ] _. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := mapB_ms);
      cbn; intros; subst; unfold id in *.
    - inv H0. eexists; split; constructor. auto.
    - inv H0; inv H. eexists; split; constructor; auto.
    - inv H0; inv H. eexists _, _. intuition eauto.
      constructor; auto. subst. inv H0. eexists; split; constructor. auto.
    - inv H; inv H0; eexists; (split; [ |constructor]).
      + apply step1. apply H1.
      + apply step2. apply H1.
      + specialize ((proj1 HS) q) as [q' Hq']. subst.
        eapply step_push. apply H1. apply H2.
      + specialize ((proj2 HS) r) as [r' Hr']. subst.
        eapply step_pop. apply H1. apply H2.
    - apply well_founded_ltof.
      Unshelve. exact tt.
  Qed.

End MAPB_COMP.

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

Instance li_func_k_surj {li K1 K2}: LiSurjective (@li_func_k li K1 K2).
Proof.
  split; intros [[x k1] k2]; exists (x, (k1, k2)); reflexivity.
Qed.

Program Definition li_func_comm {li K1 K2}: li_func (li@(K1*K2)) (li@(K2*K1)) :=
  {|
    query_func '(q, (k1, k2)) := (q, (k2, k1));
    reply_func '(r, (k1, k2)) := (r, (k2, k1));
  |}.

Instance li_func_comm_surj {li K1 K2}: LiSurjective (@li_func_comm li K1 K2).
Proof.
  split; intros [x [k1 k2]]; exists (x, (k2, k1)); reflexivity.
Qed.

Definition lift_layer {li K} (L: semantics li_null li): semantics li_null (li@K) :=
  li_func_null >> L@K.

Definition lift_layer_k {li K1 K2} (L: semantics li_null (li@K1)): semantics li_null (li@(K1*K2)) :=
  li_func_null >> L@K2 << li_func_k.

Definition layer_comm {li K1 K2} (L: semantics li_null (li@(K2*K1))): semantics li_null (li@(K1*K2)) :=
  L << li_func_comm.

Definition lts_comm {li K1 K2} (L: semantics (li@(K2*K1)) (li@(K2*K1))): semantics (li@(K1*K2)) (li@(K1*K2)) :=
   li_func_comm $$ L.

(** Some simple properties about the product of abstraction relations *)
Section Properties.

  Local Open Scope abrel_scope.

  Context {Ks1 Ks2 Kf1 Kf2} (R1: abrel Ks1 Kf1) (R2: abrel Ks2 Kf2).
  Hypothesis HR: disjoint_abrel R1 R2.

  Lemma match_query_comm w qs qf ks1 kf1 ks2 kf2:
    match_query (R2 * R1) w (qs, (ks2, ks1)) (qf, (kf2, kf1)) ->
    match_query (R1 * R2) w (qs, (ks1, ks2)) (qf, (kf1, kf2)).
  Proof.
    intros. inv H. constructor; auto.
    - intros b ofs Hg. apply MPERM.
      cbn in *. rewrite -> locsp_app in Hg |- *.
      now apply or_comm.
    - cbn in *. intuition.
  Qed.

  Lemma match_reply_comm w rs rf ks1 kf1 ks2 kf2:
    match_reply (R2 * R1) w (rs, (ks2, ks1)) (rf, (kf2, kf1)) ->
    match_reply (R1 * R2) w (rs, (ks1, ks2)) (rf, (kf1, kf2)).
  Proof.
    intros [w' [Hw H]]. exists w'. inv Hw. inv H. split.
    - cbn in *. constructor; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      cbn. intros * (A & B) V. split; eauto.
      intros X. apply B. rewrite locsp_app in *. intuition.
    - econstructor; eauto.
      + cbn in *. intros * V. apply MPERM.
        rewrite locsp_app in *. intuition.
      + cbn in *. intuition.
  Qed.

End Properties.

Lemma layer_comm_simulation `(R1: abrel Ks1 Kf1) `(R2: abrel Ks2 Kf2) L1 L2:
  forward_simulation 1 (R1 * R2)%abrel L1 L2 ->
  forward_simulation 1 (R2 * R1)%abrel (layer_comm L1) (layer_comm L2).
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

Ltac prod_crush :=
  repeat
    (match goal with
     | [ H: ?a * ?b |- _ ] => destruct H;cbn [fst snd] in *; subst
     | [ H: (?a, ?b) = (?c, ?d) |- _ ] => inv H
     | [ H: (?x * ?y)%rel _ _ |- _] => destruct H; cbn [fst snd] in *; subst
     | [ H: ?x /\ ?y |- _] => destruct H
  end).

Section LIFT_ASSOC.
  Context (K1 K2: Type) {li} (L: semantics li li).
  Inductive assoc_match: (state L * K1) * K2 -> state L * (K1 * K2) -> Prop :=
  | assoc_match_intro s k1 k2: assoc_match ((s, k1), k2) (s, (k1, k2)).

  Lemma lts_lifting_assoc: li_func_k $$ (L @ K1) @ K2 ≤ L @ (K1 * K2).
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    intros se _ [ ] [ ] _. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := assoc_match);
      cbn; intros; prod_crush.
    - eexists; split; [ | constructor ]. split; auto.
    - inv H. eexists; split; [ | constructor ]. split; auto.
    - inv H. eexists tt, _. intuition eauto. split; auto.
      prod_crush. eexists; split; [ | constructor ]. split; auto.
    - inv H0. eexists (_, (_, _)). split; [ | constructor ]. split; auto.
    - apply well_founded_ltof.
  Qed.

End LIFT_ASSOC.

Section LIFT_COMM.
  Context  (K1 K2: Type) {li} (L: semantics li li).

  Inductive comm_match: state L * (K1 * K2) -> state L * (K2 * K1) -> Prop :=
  | comm_match_intro s k1 k2: comm_match (s, (k1, k2)) (s, (k2, k1)).

  Lemma lts_lifting_comm: li_func_comm $$ L @ (K1 * K2) ≤ L @ (K2 * K1).
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    intros se _ [ ] [ ] _. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := comm_match);
      cbn; intros; prod_crush.
    - eexists; split; [ | constructor ]. split; auto.
    - inv H. eexists; split; [ | constructor ]. split; auto.
    - inv H. eexists tt, _. intuition eauto. split; auto.
      prod_crush. eexists; split; [ | constructor ]. split; auto.
    - inv H0. eexists (_, (_, _)). split; [ | constructor ]. split; auto.
    - apply well_founded_ltof.
  Qed.
End LIFT_COMM.

Require Import PcmRel Composition.

Lemma layer_comm_simulation' `(R1: abrel Ks1 Kf1) `(R2: abrel Ks2 Kf2) L1 L2:
  forward_simulation 0 (abrel_pcc (abrel_tens R1 R2)) L1 L2 ->
  forward_simulation 0 (abrel_pcc (abrel_tens R2 R1)) (layer_comm L1) (layer_comm L2).
Proof.
  intros [[]]. constructor. econstructor; eauto.
  instantiate (1 := fsim_match_states).
  intros. exploit fsim_lts; eauto. clear. intros HL.
  constructor.
  - intros [q1 [k3 k1]] [q [k4 k2]] s1 Hq H.
    inv Hq.
    edestruct @fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
    instantiate (2 := (_, (_, _))). instantiate (1 := (_, (_, _))).
    econstructor; eauto. cbn in ABS. split_hyps.
    eexists _, _. repeat split; eauto. apply pcm_comm. eauto.
    apply H.
    eexists _, _. split. apply Hs2. apply Hs.
  - intros idx s1 s2 [r [k3 k1]] Hs H.
    edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
    apply H. destruct r2 as [r2 [k2 k4]].
    eexists (_, (_, _)). split. apply Hr2.
    cbn in Hr. destruct Hr. prod_crush.
    econstructor; eauto. split; eauto.
    inv H1. cbn in ABS. split_hyps.
    constructor; eauto. eexists _, _. repeat split; eauto. apply pcm_comm. eauto.
  - intros ? ? ? [ ].
  - intros. edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
Qed.

Section LIFT_SIM.

  Context {liA1 liA2 liB1 liB2} (cc: callconv liB1 liB2)
          (L1: semantics liA1 liB1) (L2: semantics liA2 liB2)
          (H: forward_simulation 0 cc L1 L2).
  Context {Ks Kf} (R: abrel Ks Kf).

  Lemma lift_sim:
    forward_simulation 0 (cc_lift cc R) (L1@Ks) (L2@(mem*Kf)).
  Proof.
    destruct H. constructor.
    eapply Forward_simulation with
      (fsim_order X)
      (fun se1 se2 '(w, se) i '(s1, k1) '(s2, (m, k2)) =>
         fsim_match_states X se1 se2 w i s1 s2 /\
           R se k1 (m, k2)).
    apply (fsim_skel X). apply (fsim_footprint X).
    intros se1 se2 [w se] Hse Hse1.
    destruct Hse as [Hse SE]. inv SE. rename se2 into se.
    clear H. pose proof (fsim_lts X) as H.
    specialize (H _ _ _ Hse Hse1).
    econstructor; intros; cbn in *; prod_crush.
    - exploit @fsim_match_initial_states. 1-3: eauto.
      intros (? & ? & ? & ?). eexists _, (_, (_, _)).
      repeat split; eauto.
    - exploit @fsim_match_final_states. 1-3: eauto.
      intros (? & ? & ?). eexists (_, (_, _)).
      repeat split; eauto.
    - exploit @fsim_match_external. 1-3: eauto.
      intros (? & ? & ?). prod_crush. inv x.
    - exploit @fsim_simulation. 1-3: eauto. subst.
      intros (? & ? & [|] & ?); eexists _, (_, (_, _)).
      + repeat split; eauto. left.
        apply lifting_step_plus; eauto.
      + repeat split; eauto. prod_crush. right.
        split; eauto. apply  lifting_step_star; eauto.
    - apply (fsim_order_wf X).
  Qed.

End LIFT_SIM.

Class LayerFrameable liA K1 K2 (L: semantics liA _) :=
  layer_frame_sim: forward_simulation 0 (@cc_frame K1 K2) (L @ (mem * K2)) (L @ K2).

Lemma layer_lifting_simulation `(R1: abrel Ks1 Kf1) `(R2: abrel Ks2 Kf2) Ls (Lf: layer Kf1):
  LayerFrameable li_null _ Kf2 Lf ->
  disjoint_abrel R1 R2 ->
  forward_simulation 0 (abrel_pcc R1) Ls Lf ->
  forward_simulation 0 (abrel_pcc (abrel_tens R1 R2)) (lift_layer_k Ls) (lift_layer_k Lf).
Proof.
  intros HLF HR HL.
  eapply lift_sim with (R := R2) in HL. unfold LayerFrameable in HLF.
  exploit @compose_forward_simulations. apply HL. apply HLF.
  clear HLF HL.
  pose proof (lift_frame_cc R1 R2). destruct H. rewrite <- H.
  clear H H0. intros HX.
  rewrite cc_compose_null in HX.
  destruct HX. constructor.
  eapply Forward_simulation with
    (fsim_order X) (fun se1 se2 '(w, se) => fsim_match_states X se1 se2 (w, se)).
  1,2,4: apply X.
  intros se1 se2 [m se] Hse Hse1.
  exploit (fsim_lts X). apply Hse. apply Hse1. intros A.
  econstructor; intros; cbn in *; prod_crush.
  - exploit @fsim_match_initial_states. apply A.
    + instantiate (2 := (_, _, _)). instantiate (1 := (_, _, _)). cbn. apply H.
    + instantiate (1 := (_, _)). econstructor; eauto. reflexivity.
    + intros (i & (s2 & x2) & Hi & Hs).
      eexists _, (_, _); split; eauto. inv Hi. cbn in *; split; eauto.
  - exploit @fsim_match_final_states. apply A. apply H.
    instantiate (1 := (_, _)). constructor; eauto. reflexivity.
    intros (x & y & z). cbn in *. prod_crush.
    eexists (_, (_, _)). split; eauto.
    split; eauto.
  - easy.
  - subst. exploit @fsim_simulation. apply A.
    instantiate (3 := (_, _)). instantiate (1 := (_, _)). constructor; eauto.
    apply H0. intros (? & (s2 & x2) & Hi & Hx). eexists _, (_, _).
    split. 2: apply Hx.
    destruct Hi; [ left | right ]; eauto.
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

  Context `(R1: abrel Ks1 Kf1) `(R2: abrel Ks2 Kf2).
  Context `(HL1: forward_simulation (@cc_null li_null li_null) (abrel_pcc R1) Ls1 Lf1)
          `(HL2: forward_simulation (@cc_null li_null li_null) (abrel_pcc R2) Ls2 Lf2)
          `(HLF1: LayerFrameable _ _ Kf2 Lf1)
          `(HLF2: LayerFrameable _ _ Kf1 Lf2).
  Context sk (Hsk1: linkorder (skel Ls1) sk) (Hsk2: linkorder (skel Ls2) sk).
  Hypothesis (HR: disjoint_abrel R1 R2).

  Lemma tensor_compose_simulation:
    forward_simulation 0 (abrel_pcc (abrel_tens R1 R2))
                       (tensor_comp_semantics' Ls1 Ls2 sk)
                       (tensor_comp_semantics' Lf1 Lf2 sk).
  Proof.
    unfold tensor_comp_semantics'. apply flat_composition_simulation'.
    - intros [|].
      + apply layer_lifting_simulation; eauto.
      + apply layer_comm_simulation'.
        apply layer_lifting_simulation; eauto.
        intros se * A B. eapply HR; eauto.
    - intros [|]; auto.
  Qed.

End MONOTONICITY.

Section INTERC.

  Context {I: Type} {liA liB liC: language_interface}.
  Context (L1: I -> semantics liB liC) (L2: I -> semantics liA liB).
  Variable (sk sk1 sk2: AST.program unit unit) (ski: I -> AST.program unit unit).
  Let LC i := comp_semantics' (L1 i) (L2 i) (ski i).
  Let LF1 := flat_comp_semantics' L1 sk1.
  Let LF2 := flat_comp_semantics' L2 sk2.

  Inductive match_inter: flat_state LC -> comp_state LF1 LF2 -> Prop :=
  | match_inter1 i s:
      match_inter (flat_st LC i (st1 _ _ s)) (st1 LF1 _ (flat_st L1 i s))
  | match_inter2 i s1 s2:
      match_inter (flat_st LC i (st2 _ _ s1 s2)) (st2 LF1 LF2 (flat_st _ i s1) (flat_st _ i s2)).

  Lemma categorical_flat_interchangeable:
    flat_comp_semantics' LC sk ≤ comp_semantics' LF1 LF2 sk.
  Proof.
    constructor. econstructor; [ reflexivity | intros; cbn; firstorder | ..].
    intros se _ [ ] [ ] Hse. instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step with (match_states := match_inter).
    - intros q1 _ s1 [ ] H. inv H. inv H0.
      exists (st1 LF1 _ (flat_st L1 i s0)).
      split; repeat constructor. auto.
    - intros s1 s2 r1 Hs H. inv H. inv H0. inv Hs. SmallstepLinking.subst_dep.
      exists r1. split; repeat constructor. auto.
    - intros s1 s2 q Hs H. exists tt.
      inv H. inv H0. inv Hs. SmallstepLinking.subst_dep.
      exists q. repeat apply conj; try constructor. now constructor.
      intros r1 _ s1' [ ] Ht. inv Ht. inv H4. SmallstepLinking.subst_dep. inv H2.
      eexists. split; repeat constructor. auto.
    - intros. inv H.
      inv H1; inv H0; SmallstepLinking.subst_dep; eexists; split;
        [ apply step1 | | apply step2 | | eapply step_push | | eapply step_pop |  ]; repeat constructor; eauto.
    - apply well_founded_ltof.
  Qed.

End INTERC.

Require Import CModule SkelLinking.

Section LAYER_DEF.
  Context {Ks Kf} (Ls: layer Ks) (Lf: layer Kf) (M: cmodule).
  Definition cmod_layer_comp sk := comp_semantics' (semantics M @ Kf) Lf sk.
  Record cmod_sim (R: abrel Ks Kf) : Prop :=
    mk_cmod_sim {
        csim_sk_order: linkorder (skel Lf) (skel Ls) /\ linkorder (cmod_skel M) (skel Ls);
        csim_simulation: forward_simulation 0 (abrel_pcc R) Ls (cmod_layer_comp (skel Ls));
      }.
End LAYER_DEF.

Instance sim_monotonic `(ccA: callconv liA1 liA2) `(ccB: callconv liB1 liB2):
  Proper ((forward_simulation 1 1) --> (forward_simulation 1 1) ++> impl)
         (forward_simulation ccA ccB).
Proof.
  intros L1' L1 HL1 L2' L2 HL2 H. unfold flip in HL1.
  eapply open_fsim_ccref. apply cc_compose_id_left.
  unfold flip. apply cc_compose_id_left.
  eapply compose_forward_simulations. eauto.

  eapply open_fsim_ccref. apply cc_compose_id_right.
  unfold flip. apply cc_compose_id_right.
  eapply compose_forward_simulations; eauto.
Qed.

Section TCOMP.

  Context `(R1: abrel Ks1 Kf1) `(R2: abrel Ks2 Kf2) (M N: cmodule).
  Context `(HL1: cmod_sim Ls1 Lf1 M R1) `(HL2: cmod_sim Ls2 Lf2 N R2)
          (HLF1: LayerFrameable li_null Kf1 Kf2 Lf1) (HLF2: LayerFrameable li_null Kf2 Kf1 Lf2).
  Context sks (Hsks: link (skel Ls1) (skel Ls2) = Some sks)
          skf (Hskf: link (skel Lf1) (skel Lf2) = Some skf)
          MN (HMN: cmod_app M N = Some MN).
  Let Mi := (fun i : bool => if i then semantics M else semantics N).
  Context `{!FlatLinkable Mi}.
  Hypothesis HR: disjoint_abrel R1 R2.

  Lemma tens_skel_link1: linkorder skf sks.
  Proof.
    eapply link_monotonic.
    3-4: eauto. apply HL1. apply HL2.
  Qed.
  Lemma tens_skel_link2: linkorder (cmod_skel MN) sks.
  Proof.
    eapply link_monotonic.
    3-4: eauto using cmod_app_skel. apply HL1. apply HL2.
  Qed.

  Local Instance compose_layer_frameable2:
    LayerFrameable li_null Kf2 Kf1 (cmod_layer_comp Lf2 N (skel Ls2)).
  Proof.
    unfold LayerFrameable. unfold cmod_layer_comp.
    rewrite lift_categorical_comp1. rewrite <- lift_categorical_comp2.
    eapply categorical_compose_simulation'.
    2: apply HLF2.
  Admitted.

  Local Instance compose_layer_frameable1:
    LayerFrameable li_null Kf1 Kf2 (cmod_layer_comp Lf1 M (skel Ls1)).
  Admitted.

  Local Instance overlay_frameable1:
    LayerFrameable li_null Ks1 Ks2 Ls1.
  Proof.
    unfold LayerFrameable. destruct HL1 as [_ H1].

  Lemma layer_tcomp: cmod_sim (tensor_comp_semantics' Ls1 Ls2 sks)
                         (tensor_comp_semantics' Lf1 Lf2 skf) MN (abrel_tens R1 R2).
  Proof.
    destruct HL1 as [[HLsk1 Hmod1] H1].
    destruct HL2 as [[HLsk2 Hmod2] H2].
    split. split. apply tens_skel_link1. apply tens_skel_link2.

    (* rewrite <- (proj1 cc_id_null). *)
    (* rewrite -> (proj2 cc_id_null) in H1, H2. *)
    exploit @tensor_compose_simulation;
      [ exact H1 | exact H2 | .. ]; eauto.
    1-2: eapply link_linkorder in Hsks; apply Hsks.
    intros X. eapply open_fsim_ccref. apply cc_compose_id_right.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. exact X. clear X.

    unfold tensor_comp_semantics', cmod_layer_comp.

    etransitivity.
    {
      apply flat_composition_simulation'. instantiate (1 := fun i => match i with true => _ | false => _ end).
      intros [|].
      - instantiate (1 := comp_semantics' (semantics M @ (Kf1 * Kf2)) (lift_layer_k Lf1) (skel Ls1)).
        etransitivity.
        + apply mapB_monotonicity. etransitivity.
          * apply mapA_monotonicity. apply lift_categorical_comp1.
          * apply mapA_comp.
        + etransitivity.
          * apply mapB_comp'. typeclasses eauto.
          * eapply categorical_compose_simulation'.
            -- apply lts_lifting_assoc.
            -- reflexivity.
            -- exact Hmod1.
            -- auto.
      - instantiate (1 := comp_semantics' (semantics N @ (Kf1 * Kf2)) (layer_comm (lift_layer_k Lf2)) (skel Ls2)).
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
            -- exact Hmod2.
            -- auto.
      - intros [|]; cbn.
        1-2: eapply link_linkorder in Hsks; apply Hsks.
    }

    set (LX:= fun i:bool => if i then semantics M @ (Kf1 * Kf2) else semantics N @ (Kf1 * Kf2)).
    set (LY:= fun i:bool => if i then lift_layer_k Lf1 else layer_comm (lift_layer_k Lf2)).
    set (Lsk:= fun i:bool => if i then skel Ls1 else skel Ls2).
    replace (flat_comp_semantics' _ sks) with (flat_comp_semantics' (fun i:bool => comp_semantics' (LX i) (LY i) (Lsk i)) sks).
    2: {
      subst LX  LY Lsk. cbn. f_equal. apply Axioms.functional_extensionality.
      intros [|]; reflexivity.
    }

    etransitivity. apply categorical_flat_interchangeable. cbn.
    eapply categorical_compose_simulation'.
    - subst LX. rewrite <- if_rewrite with (f := fun x => x @ (Kf1 * Kf2)).
      etransitivity. apply lift_flat_comp2. apply lifting_simulation.
      apply cmodule_flat_comp_simulation; eauto.
    - reflexivity.
    - apply tens_skel_link2.
    - apply tens_skel_link1.
  Qed.

End TCOMP.
