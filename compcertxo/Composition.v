Require Import Relations RelationClasses Relators.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface Events Globalenvs Smallstep.
Require Import Memory Values.
Require Import Clight Linking.
Require Import AbsRel ClightLinking Lifting CatComp.
Require Import Maps.

Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive rel_adt: Type -> Type -> Type :=
| empty_rel K: rel_adt K K
| singleton_rel {K1 K2} : krel K1 K2 -> rel_adt K1 K2
| vcomp_rel {K1 K2 K3} : rel_adt K1 K2 -> rel_adt K2 K3 -> rel_adt K1 K3.

(* Why asymmetric patterns flag doesn't work? *)
Fixpoint absrel_to_cc {K1 K2} (rel: rel_adt K1 K2):
  callconv (li_c @ K1) (li_c @ K2) :=
  match rel with
  | empty_rel _ => cc_id
  | singleton_rel _ _ r => kcc_c r
  | vcomp_rel _ _ _ r1 r2 => (absrel_to_cc r1) @ (absrel_to_cc r2)
  end.

Delimit Scope krel_scope with krel.
Bind Scope krel_scope with rel_adt.

Notation "[ R ]" := (singleton_rel R) (at level 30): krel_scope.
Notation "R1 ∘ R2" := (vcomp_rel R1 R2): krel_scope.

Coercion absrel_to_cc : rel_adt >-> callconv.

Definition layer_combine {K} (M: Clight.program) (L: layer K) sk :=
  layer_comp (semantics1 M @ K) L sk.


(* E@K1    -–M-->    F@K2 *)

(*               C_F@K2 *)
(*                 |    *)
(*                 R    *)
(*                 |    *)
(* C_E@K1 --M--> C_F@K1 *)

(*

  underlay -> (L2 : !E or 1 -> E)
  strategy -> M (Clight.program) or F (linear map E --o F)
  overlay -> F o L2

  K1 ~ trace F

  K2 ~ trace E + memory

  M_cnt o L_int


  1 |- M_int : L_int
  L_int |- M_cnt : L_cnt
------------------------------vcomp
  1 |- M_int + M_cnt : L_cnt




  counter:  L_cnt <=_R  M_cnt o L_int
  getter/setter:  L_int <= M_int

*)

Definition prog_ksim {K1 K2: Type} (L1: layer K1)
           (L2: layer K2) (M: Clight.program) (R: rel_adt K1 K2) :=
  forall sk, link (skel (semantics1 M)) (skel L2) = Some sk ->
        forward_simulation 1 R L1 (layer_combine M L2 sk).

Require Import Ctypes.

Lemma link_fundef_lemma {F} (x y z xy xyz: fundef F):
  link x y = Some xy -> link xy z = Some xyz -> exists yz, link y z = Some yz /\ link x yz = Some xyz.
Proof.
  Local Transparent Linker_fundef.
  intros Hxy Hxyz. inv Hxy. inv Hxyz.
  unfold link_fundef in *.
  destruct x eqn: Hx.
  - destruct y eqn: Hy; try congruence.
    destruct e eqn: He; try congruence.
    inv H0.
    destruct z eqn: Hz; try congruence.
    destruct e eqn: He'; try congruence.
    eexists. split. cbn.
Admitted.


Lemma link_def_lemma (x y z xy xyz: AST.globdef unit unit):
  link x y = Some xy -> link xy z = Some xyz -> exists yz, link y z = Some yz.
Proof.
  Local Transparent Linker_unit Linker_def Linker_vardef Linker_varinit.
  intros Hxy Hxyz. inv Hxy. inv Hxyz.
Admitted.

Lemma link_prog_lemma (x y z xy xyz: AST.program unit unit):
  link x y = Some xy -> link xy z = Some xyz -> exists yz, link y z = Some yz /\ link x yz = Some xyz.
Proof.
Admitted.
(* Local Transparent Linker_prog. *)
(* intros Hxy Hxyz. *)
(* pose proof (link_linkorder _ _ _ Hxy) as [Hox Hoy]. *)
(* inv Hxy. inv Hxyz. *)
(* apply link_prog_inv in H0 as (Ha1 & Hb1 & Hc1). *)
(* apply link_prog_inv in H1 as (Ha2 & Hb2 & Hc2). *)
(* eexists. cbn. unfold link_prog. *)
(* destruct (AST.ident_eq (_ y) (_ z)). *)
(* 2: { exfalso. rewrite Hc1 in Ha2. cbn in Ha2. congruence. } *)
(* simpl. destruct (Maps.PTree_Properties.for_all (_ y) _) eqn: Hx; *)
(*          [reflexivity | exfalso]. *)
(* rewrite Maps.PTree_Properties.for_all_false in Hx. *)
(* destruct Hx as (idx & def & Hx & Hy). *)
(* assert (link_prog_check y z idx def = true). *)
(* { *)
(*   clear Hy Hc2. unfold link_prog_check. *)
(*   rename Hx into Hy. *)
(*   destruct (Maps.PTree.get idx (_ z)) eqn: Hz; auto. *)
(*   destruct (Maps.PTree.get idx (AST.prog_defmap x)) eqn: Hx. *)
(*   - specialize (Hb1 _ _ _ Hx Hy) as (Ha & Hb & Hc). *)
(*     destruct (in_dec _ _ (_ y)); try congruence; simpl. *)
(*     pose proof (prog_defmap_linkorder x xy _ _ Hox Hx) as (gxy & Hxy & ?). *)
(*     specialize (Hb2 _ _ _ Hxy Hz) as (? & ? & ?). *)
(*     destruct (in_dec _ _ (_ z)); try congruence; simpl. *)
(*     destruct Hc as (gxy' & Hgxy). *)
(*     assert (gxy = gxy') as <-. *)
(*     + admit. *)
(*     + destruct H2 as (gxyz & Hgxyz). *)
(*       exploit link_def_lemma. apply Hgxy. eauto. *)
(*       intros (? & Hgyz). inv Hgyz. rewrite H3. auto. *)
(*   - admit. *)
(* (* Whether or not idx is a public definition in y doesn't affect how x and *)
(*          y are linked. But if it is private in y, xy and z cannot be linked  *) *)
(* } *)
(* now rewrite H in Hy. *)
(* Admitted. *)

Require Import CallconvAlgebra.

(* move to CatComp.v *)
Definition layer_compose {li} L1 (L2: Smallstep.semantics li_null li) :=
  option_map (layer_comp L1 L2) (link (skel L1) (skel L2)).

Lemma layer_comp_fsim' {li1 li2} (cc: callconv li1 li2) L1a L1b L1 L2a L2b L2:
  forward_simulation cc cc L1a L2a ->
  forward_simulation 1 cc L1b L2b ->
  layer_compose L1a L1b = Some L1 ->
  layer_compose L2a L2b = Some L2 ->
  forward_simulation 1 cc L1 L2.
Proof.
Admitted.

Lemma identity_lift_fsim {K liA liB} (L1 L2: Smallstep.semantics liA liB):
  forward_simulation 1 1 L1 L2 ->
  forward_simulation 1 1 (L1 @ K) (L2 @ K).
Proof.
Admitted.

Lemma lift_composition_fsim {K li} (L1 L2: Smallstep.semantics li li) L:
  SmallstepLinking.compose L1 L2 = Some L ->
  exists LK, SmallstepLinking.compose (L1 @ K) (L2 @ K) = Some LK /\
        forward_simulation 1 1 LK (L @ K).
Proof.
Admitted.

Lemma compose_forward_simulations1 {li} (L1 L2 L3: semantics li li):
  forward_simulation 1 1 L1 L2 -> forward_simulation 1 1 L2 L3 -> forward_simulation 1 1 L1 L3.
Proof.
  intros. eapply open_fsim_ccref.
  apply cc_compose_id_left.
  apply cc_compose_id_left.
  eapply compose_forward_simulations; eauto.
Qed.

Lemma magic_simulation {li} (L1 L2: Smallstep.semantics li li) L3 sk sk1 sk2:
  let LX := SmallstepLinking.semantics (fun i => match i with true => L1 | false => L2 end) sk1 in
  let LY := layer_comp L1 (layer_comp L2 L3 sk2) sk in
  forward_simulation 1 1 LY (layer_comp LX L3 sk).
Proof.
Admitted.

(* Lemma magic_simulation' {li K} (L1 L2: Smallstep.semantics li li) L3 LK L12 L23 L123 L123': *)
(*   SmallstepLinking.compose (L1 @ K) (L2 @ K) = Some L12 -> layer_compose LK L3 = Some L123' -> *)
(*   layer_compose (L2 @ K) L3 = Some L23 -> layer_compose (L1 @ K) L23 = Some L123 -> *)
(*   forward_simulation 1 1 L123 L123'. *)
(* Proof. *)
(* Admitted. *)

Lemma clight_sim' {K1 K2} (R: rel_adt K1 K2) p:
  forward_simulation R R (Clight.semantics1 p @ K1) (Clight.semantics1 p @ K2).
Proof.
  induction R; simpl.
  - apply identity_lift_fsim.
    apply identity_forward_simulation.
  - apply clight_sim.
  - eapply compose_forward_simulations; eauto.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma if_commute {A B} x y (f: A -> B):
  (fun i : bool => f (if i then x else y)) = (fun i : bool => (if i then f x else f y)).
Proof.
  apply functional_extensionality.
  intros i. destruct i; f_equal.
Qed.

Section VCOMP.

  Context {K1 K2 K3 L1 L2 L3} {M N: Clight.program}
          {R: rel_adt K1 K2} {S: rel_adt K2 K3}
          (HL1: prog_ksim L1 L2 M R) (HL2: prog_ksim L2 L3 N S).
  Context (p: Clight.program) (Hp: link M N = Some p).

  Theorem layer_vcomp: prog_ksim L1 L3 p (R ∘ S).
  Proof.
    intros sk Hsk.
    assert (Hskp: link (skel (semantics1 M)) (skel (semantics1 N)) = Some (skel (semantics1 p))).
    {
      apply link_erase_program.
      Local Transparent Linker_program.
      inv Hp. unfold link_program in H0.
      destruct (link (program_of_program M) (program_of_program N)); try congruence.
      destruct lift_option; try congruence.
      destruct s. destruct link_build_composite_env. destruct a.
      unfold program_of_program. inv H0. cbn. destruct p0. reflexivity.
    }
    exploit link_prog_lemma; [ apply Hskp | apply Hsk | ].
    intros (sk2 & Hsk2 & Hsk1). specialize (HL2 Hsk2). inv HL2. rename X into HL2.
    exploit HL1. rewrite (fsim_skel HL2). eauto. clear HL1. intros [HL1].

    simpl. exploit @compose_forward_simulations.
    constructor. apply HL1.
    2: {
      intro X. eapply open_fsim_ccref.
      apply cc_compose_id_left.
      unfold flip. reflexivity.
      apply X.
    }.

    eapply open_fsim_ccref. apply cc_compose_id_left. apply cc_compose_id_right.
    exploit @lift_composition_fsim. unfold SmallstepLinking.compose.
    rewrite Hskp. reflexivity.
    intros (LK & ? & HLK).
    eapply compose_forward_simulations.
    2: {
      assert (HX: layer_compose (semantics1 p @ K3) L3 =
                  Some (layer_combine p L3 sk)).
      unfold layer_compose. cbn -[link].
      cbn -[link] in Hsk. rewrite Hsk. reflexivity.

      eapply layer_comp_fsim';
        [ | apply identity_forward_simulation | | apply HX ].

      eapply compose_forward_simulations1.
      2: {
        apply identity_lift_fsim.
        apply clight_linking. eauto.
      }
      rewrite if_commute. cbn in HLK |- *. apply HLK.

      unfold layer_compose. destruct HLK.
      rewrite (fsim_skel f). cbn -[link semantics1].
      rewrite Hsk. reflexivity.
    } clear HLK.

    pose proof (magic_simulation (semantics1 M @ K3) (semantics1 N @ K3) L3 sk (AST.erase_program p) sk2) as X.
    cbn in X. unfold SmallstepLinking.compose in H. cbn in Hskp, H. rewrite Hskp in H. cbn in H.
    injection H. intros Hr. rewrite Hr in X. clear H.
    (* exploit @magic_simulation; [ apply H0 | ..]. *)
    (* { *)
    (*   instantiate (2 := L3). instantiate (2 := LK). *)
    (*   unfold SmallstepLinking.compose in H0. *)
    (*   Opaque Linker_prog. *)
    (*   cbn in H', H0. rewrite H' in H0. cbn in H0. *)
    (*   unfold layer_compose. injection H0. intros Hk. *)
    (*   rewrite <- Hk at 2. cbn in Hsk |- *. rewrite Hsk. reflexivity. *)
    (* } *)
    (* { *)
    (*   unfold layer_compose. cbn in Hsk2 |- *. rewrite Hsk2. reflexivity. *)
    (* } *)
    (* { *)
    (*   unfold layer_compose. cbn. inv HL2. rewrite (fsim_skel X) in *. *)
    (*   cbn in Hsk1 |- *. rewrite Hsk1. reflexivity. *)
    (* } *)
    (* intros X. *)

    eapply open_fsim_ccref. apply cc_compose_id_left. apply cc_compose_id_right.
    eapply compose_forward_simulations; [ | apply X ].
    eapply layer_comp_fsim'; [ | constructor; apply HL2 | ..].
    (* instantiate (1 := ((semantics1 M) @ K3)%sem). *)
    (* instantiate (1 := ((semantics1 M) @ K2)%sem). *)
    apply clight_sim'.
    unfold layer_compose. rewrite (fsim_skel HL2). cbn in Hsk1 |- *. rewrite Hsk1. reflexivity.
    unfold layer_combine, layer_compose.
    cbn in Hsk1 |- *. rewrite Hsk1. reflexivity.
  Qed.

End VCOMP.

Require Import FlatComp.
