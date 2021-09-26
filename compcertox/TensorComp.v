Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Linking.
Require Import Lifting AbstractStateRel.
Require Import Coq.Logic.FinFun.

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

Section TENSOR.

  Context {K1 K2} (L1: semantics li_null (li_c@K1)) (L2: semantics li_null (li_c@K2)).
  Context {J1 J2} (jr: krel J1 J2) (kr: krel K1 K2).
  Context (HL: fsim_components 1 kr L1 L2).
  Context (se1 se2: Genv.symtbl) (w : ccworld (kr * jr)).
  Context (Hse: match_senv (kr * jr) w se1 se2).
  Context (Hse1: Genv.valid_for (skel L1) se1).

  Hypothesis Hdisjoint: forall b ofs, G jr b ofs -> G kr b ofs -> False.

  Inductive state_match: fsim_index HL -> state L1 * J1 -> state L2 * J2 -> Prop :=
  | lift_state_match i s1 j1 s2 j2:
      fsim_match_states HL se1 se2 w i s1 s2 ->
      Rk jr j1 j2 -> Rr jr j1 (snd w) -> no_perm_on (fst w) (G jr) ->
      Mem.extends (fst w) (snd w) ->
  state_match i (s1, j1) (s2, j2).

  Lemma lift_layer_semantics_simulation:
    fsim_properties 1 (kr * jr) se1 se2 w
                    (lift_layer_k L1 se1) (lift_layer_k L2 se2)
                    (fsim_index HL) (fsim_order HL) state_match.
  Proof.
    split; cbn.
    - intros [q1 [k1 j1]] [q2 [k2 j2]] [s1 sj1] Hq [H Hj]; cbn in *.
      subst sj1. eapply prod_match_query in Hq.
      pose proof (fsim_lts HL _ w Hse Hse1).
      edestruct @fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
      apply Hq. exists idx, (s2, j2). split. split; auto.
      constructor; auto; apply Hq.
    - intros idx [s1 sj1] [s2 sj2] [r1 [kr1 jr1]] Hs [H Hj].
      inv Hs. pose proof (fsim_lts HL _ w Hse Hse1).
      edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
      cbn [fst snd] in *. destruct r2 as [r2 rk2]. subst sj1.
      exists (r2, (rk2, sj2)). split. split; eauto.
      apply prod_match_reply; auto. intros. eapply Hdisjoint; eauto.
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
  Let LF1 := flat_comp_semantics' L1 sk.
  Let LF2 := flat_comp_semantics' L2 sk.

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
    - intros s1 s2 r1 Hs H. inv H. inv H0. inv Hs. SmallstepLinking_.subst_dep.
      exists r1. split; repeat constructor. auto.
    - intros s1 s2 q Hs H. exists tt.
      inv H. inv H0. inv Hs. SmallstepLinking_.subst_dep.
      exists q. repeat apply conj; try constructor. now constructor.
      intros r1 _ s1' [ ] Ht. inv Ht. inv H4. SmallstepLinking_.subst_dep. inv H2.
      eexists. split; repeat constructor. auto.
    - intros. inv H.
      inv H1; inv H0; SmallstepLinking_.subst_dep; eexists; split;
        [ apply step1 | | apply step2 | | eapply step_push | | eapply step_pop |  ]; repeat constructor; eauto.
    - apply well_founded_ltof.
  Qed.

End INTERC.
