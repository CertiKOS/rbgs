Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp SmallstepLinking_.
Require Import Memory Values.
Require Import Clight_ Linking.
Require Import AbstractStateRel Lifting.
Require Coq.omega.Omega.
Require Import Ctypes.

(* A module is a list of compilation units. Specifically, they are Clight
   programs at this time. Note that in the layer library the modules are
   organized as mapping from identifiers to vars or functions. A module like
   that is transformed into a Clight program by [make_program] because separate
   compilation is not supported. However, here a module is nothing but a list of
   programs and the semantics is given by the horizontal composition of the
   Clight programs *)
Notation cmodule := (list Clight_.program).

Fixpoint pos (M: cmodule): Type :=
  match M with
  | nil => Empty_set
  | p :: ps => unit + pos ps
  end.

Definition ref (M: cmodule) (k: pos M): Smallstep_.semantics li_c li_c.
Proof.
  induction M as [| p ps].
  - inv k.
  - destruct k.
    + refine (Clight_.semantics1 p).
    + apply IHps. apply p0.
Defined.

Definition semantics (M: cmodule) sk: Smallstep_.semantics li_c li_c :=
  SmallstepLinking_.semantics' (ref M) sk.

Require Import FunctionalExtensionality.
Require Import FinFun.

Global Instance cmod_progrom_sem M sk: ProgramSem (semantics M sk).
Proof.
  split.
  - intros. inv H. destruct H0 as (?&?&?&?).
  split; eauto. eexists; split; eauto.
  cbn. eexists; eauto.
  - intros. inv H. intros [Hq [x [Hx1 Hx2]]].
    destruct Hx1 as [j1 Hj]. apply (H1 j1).
    split; auto. exists x; split; auto.
Qed.

Section APP.

  Context (M N: cmodule).
  Variable (sk: AST.program unit unit).

  Let L := fun (b: bool) => match b with | true => (semantics M sk) | false => (semantics N sk) end.
  Let J := fun (b: bool) => match b with | true => pos M | false => pos N end.
  Definition Lij: forall (b: bool), J b -> Smallstep_.semantics li_c li_c.
  Proof.
    intros [|] j.
    - refine (ref M j).
    - refine (ref N j).
  Defined.

  Lemma Leq: L = (fun i => semantics' (fun j => Lij i j) sk).
  Proof.
    apply functional_extensionality. intros [|]; reflexivity.
  Qed.

  Definition F: pos (M ++ N) -> {b : bool & J b}.
  Proof.
    intros x. induction M as [| p ps].
    - refine (existT _ false x).
    - cbn in *. destruct x.
      + refine (existT _ true (inl u)).
      + specialize (IHps p0) as [[|] pp].
        * refine (existT _ true (inr pp)).
        * refine (existT _ false pp).
  Defined.

  Definition G: {b : bool & J b} -> pos (M ++ N).
  Proof.
    intros [[|] j].
    - cbn in *. induction M as [| p ps].
      + inv j.
      + cbn. destruct j.
        * refine (inl u).
        * refine (inr (IHps p0)).
    - cbn in *. induction M as [| p ps].
      + refine j.
      + refine (inr IHps).
  Defined.

  Lemma FG_bij: Bijective F.
  Proof.
    exists G. split; intros x.
    - unfold F, G. cbn.
      induction M as [| p ps].
      + reflexivity.
      + cbn in *. destruct x.
        * reflexivity.
        * cbn in *. specialize (IHps p0).
          remember (list_rect (fun l : cmodule => pos (l ++ N) -> _) _ _ ps p0) as lr.
          destruct lr as [b pb]. destruct b.
          -- f_equal. apply IHps.
          -- f_equal. apply IHps.
    - unfold F, G. cbn. destruct x as [[|] j].
      + cbn in *. induction M as [| p ps].
        * cbn in *. inv j.
        * cbn in *. destruct j.
          -- constructor.
          -- specialize (IHps p0). cbn in *.
             rewrite IHps. constructor.
      + cbn in *. induction M as [| p ps].
        * cbn in *. constructor.
        * cbn in *. rewrite IHps. constructor.
  Qed.

  Lemma LFeq: (fun i : pos (M ++ N) => (fun p : {x : bool & J x} => Lij (projT1 p) (projT2 p)) (F i)) = ref (M ++ N).
  Proof.
    apply functional_extensionality. intros x.
    unfold F, Lij. induction M as [| p ps].
    - cbn in *. reflexivity.
    - cbn in *. destruct x.
      + reflexivity.
      + cbn in *. specialize (IHps p0).
        remember (list_rect (fun l : cmodule => pos (l ++ N) -> _) _ _ ps p0) as lr.
        destruct lr as [b pb]. destruct b.
        * cbn in *. apply IHps.
        * cbn in *. apply IHps.
  Qed.

  Section CAT_APP.
    Context `{!CategoricalLinkable (semantics M sk) (semantics N sk)}.

    Lemma cmodule_app_simulation:
      comp_semantics' (semantics M sk) (semantics N sk) sk ≤ semantics (M ++ N) sk.
    Proof.
      etransitivity.
      apply categorical_compose_approximation; typeclasses eauto.
      fold L. rewrite Leq.
      etransitivity. apply level_simulation1.
      etransitivity. eapply bijective_map_simulation1 with (F := F).
      apply FG_bij. unfold semantics. rewrite <- LFeq.
      reflexivity.
    Qed.
  End CAT_APP.

  Section FLAT_APP.
    Context `{!FlatLinkable L}.

    Lemma cmodule_flat_comp_simulation:
      flat_comp_semantics' L sk ≤ semantics (M ++ N) sk.
    Proof.
      etransitivity.
      apply flat_composition_approximation;
        [ intros [|]; typeclasses eauto
        | eauto | decide equality ].
      rewrite Leq.
      fold @SmallstepLinking_.semantics.
      etransitivity. apply level_simulation1.
      etransitivity. eapply bijective_map_simulation1 with (F := F).
      apply FG_bij. unfold semantics. rewrite <- LFeq.
      reflexivity.
    Qed.
  End FLAT_APP.

End APP.

Lemma cmodule_app_simulation' M N sk sk':
  CategoricalLinkable (semantics M sk) (semantics N sk) -> linkorder sk' sk ->
  comp_semantics' (semantics M sk) (semantics N sk') sk ≤ semantics (M ++ N) sk.
Proof.
  intros Hsk.
  etransitivity. 2:{ apply cmodule_app_simulation; auto. }
  etransitivity. 2:{ apply lift_comp_component2. }
  eapply categorical_compose_simulation';
                   [ reflexivity
                   | apply identity_forward_simulation
                   | apply linkorder_refl | auto ].
Qed.

Definition skel_module_compatible (M: cmodule) (sk: AST.program unit unit) :=
  Forall (fun (p: Clight_.program) => linkorder (AST.erase_program p) sk) M.

Lemma cmodule_krel {K1 K2} (R: rel_adt K1 K2) M sk:
  skel_module_compatible M sk ->
  forward_simulation R R (semantics M sk @ K1) (semantics M sk @ K2).
Proof.
  intros Hsk.

  eapply open_fsim_ccref. apply cc_compose_id_left.
  unfold flip. apply cc_compose_id_left.
  eapply compose_forward_simulations.
  apply lift_horizontal_comp1.

  eapply open_fsim_ccref. apply cc_compose_id_right.
  unfold flip. apply cc_compose_id_right.
  eapply compose_forward_simulations.
  2: { apply lift_horizontal_comp2. }

  apply horizontal_compose_simulation'.
  - intros. induction M as [| p ps]; try easy.
    destruct i.
    + cbn. apply clight_krel.
    + apply IHps.
      unfold skel_module_compatible in *.
      rewrite -> Forall_forall in *.
      intros x Hx. apply Hsk. right. auto.
  - intros. induction M as [| p ps]; try easy.
    destruct i.
    + cbn. unfold skel_module_compatible in *.
      rewrite -> Forall_forall in *. apply Hsk.
      left. auto.
    + apply IHps.
      unfold skel_module_compatible in *.
      rewrite -> Forall_forall in *.
      intros x Hx. apply Hsk. right. auto.
Qed.

(* Legacy definition of C module and related proof *)

(* For some reason p ⊕ id can't be simply replaced by p *)
(* The patterns are overlapping because Coq is not able to find the termination
   order automatically *)

(* Fixpoint semantics (cmod: cmodule) sk: semantics li_c li_c := *)
(*   match cmod with *)
(*   | nil => id_semantics sk *)
(*   | (p :: nil) => skel_extend (Clight_.semantics1 p) sk *)
(*   | (p :: ps) => *)
(*     let L b := match b with *)
(*                | true  => skel_extend (Clight_.semantics1 p) sk *)
(*                | false => semantics ps sk *)
(*                end *)
(*     in SmallstepLinking_.semantics L sk *)
(*   end. *)

(* Section LIST_IND. *)
(*   Variable A: Type. *)
(*   Variable P: list A -> Prop. *)
(*   Variable P1: forall x, P (x :: nil). *)
(*   Variable Pcons: forall x xs, P xs -> P (x :: xs). *)

(*   Theorem list_ind1: forall xs, (List.length xs >= 1)%nat -> P xs. *)
(*   Proof. *)
(*     set (Q := fun l => (Datatypes.length l >= 1)%nat -> P l). *)
(*     apply (@list_ind A Q). *)
(*     - unfold Q. inversion 1. *)
(*     - subst Q. cbn. intros. *)
(*       destruct l. *)
(*       + apply P1. *)
(*       + apply Pcons. apply H. cbn. firstorder. *)
(*   Qed. *)
(* End LIST_IND. *)

(* Section HCOMP_STATE. *)
(*   Context {li} (L1 L2: Smallstep_.semantics li li). *)
(*   Let L := fun i => match i with | true => L1 | false => L2 end. *)

(*   Lemma initial_state_valid_comp sk: *)
(*     forall q s se, *)
(*       Smallstep_.initial_state (SmallstepLinking_.semantics L sk se) q s -> *)
(*       valid_query (SmallstepLinking_.semantics L sk) se q. *)
(*   Proof. *)
(*     intros q s se Hx. inv Hx. destruct i; firstorder. *)
(*   Qed. *)

(*   Lemma extcall_invalid_comp sk: *)
(*     forall q s se, *)
(*       Smallstep_.at_external (SmallstepLinking_.semantics L sk se) s q -> *)
(*       ~ valid_query (SmallstepLinking_.semantics L sk) se q. *)
(*   Proof. *)
(*     intros q s se Hx. inv Hx. destruct i. *)
(*     - intros (?&?&Hfp&?). destruct Hfp. *)
(*       + apply (H0 true). firstorder. *)
(*       + apply (H0 false). firstorder. *)
(*     - intros (?&?&Hfp&?). destruct Hfp. *)
(*       + apply (H0 true). firstorder. *)
(*       + apply (H0 false). firstorder. *)
(*   Qed. *)

(* End HCOMP_STATE. *)

(* Overlapping patterns in the definition of semantics results in duplicate
   proofs *)

(* Lemma cmodule_initial_state_valid sk M: *)
(*   (List.length M >= 1)%nat -> *)
(*   forall se s q, Smallstep_.initial_state (semantics M sk se) q s -> *)
(*             valid_query (semantics M sk) se q. *)
(* Proof. *)
(*   set (P := fun M => forall se s q, Smallstep_.initial_state (semantics M sk se) q s -> valid_query (semantics M sk) se q). *)
(*   apply (@list_ind1 _ P); subst P; cbn beta. *)
(*   - intros. eapply initial_state_valid; eauto. *)
(*   (* inv H. destruct H0 as (? & ? & ? & ?). destruct i. *) *)
(*   (* + unfold valid_query. split; auto. *) *)
(*   (*   eexists; split; eauto. now left. *) *)
(*   (* + inv H0. *) *)
(*   - intros p ps IH se s q H. cbn. destruct ps as [| p' ps']. *)
(*     + eapply initial_state_valid; eauto. *)
(*     + eapply initial_state_valid_comp. apply H. *)
(* Qed. *)

(* Lemma cmodule_extcall_invalid sk M: *)
(*   (List.length M >= 1)%nat -> *)
(*   forall se s q, Smallstep_.at_external (semantics M sk se) s q -> *)
(*             ~ valid_query (semantics M sk) se q. *)
(* Proof. *)
(*   set (P := fun M =>  forall se s q, Smallstep_.at_external ((semantics M sk) se) s q -> ~ valid_query (semantics M sk) se q). *)
(*   apply (@list_ind1 _ P); subst P; cbn beta. *)
(*   - intros. eapply extcall_invalid; eauto. *)
(*   - intros p ps IH se s q H. destruct ps as [| p' ps']. *)
(*     + eapply extcall_invalid; eauto. *)
(*     + eapply extcall_invalid_comp. apply H. *)
(* Qed. *)


(* M has to be non-empty is due to the fact that we can't prove id ∘ L ≡ L *)
(* No, the reason is the id LTS doesn't have initial_state_valid *)
(* Lemma cmodule_simulation {M N : cmodule} {sk: AST.program unit unit}: *)
(*   (List.length N >= 1)%nat -> (List.length M >= 1)%nat -> *)
(*   comp_semantics' (semantics M sk) (semantics N sk) sk ≤ semantics (M ++ N) sk. *)
(* Proof. *)
(*   intros HN HM. etransitivity. *)
(*   - apply categorical_compose_approximation. *)
(*     intros [|] se q s H. *)
(*     eapply cmodule_initial_state_valid; eauto. *)
(*     eapply cmodule_initial_state_valid; eauto. *)
(*   - induction M as [|p ps]. *)
(*     + cbn. etransitivity; [ | apply hcomp_left_identity1 ]. *)
(*       assert (skel (semantics N sk) = sk). *)
(*       { destruct N; auto. destruct N; auto. } *)
(*       rewrite H. apply identity_forward_simulation. *)
(*       apply cmodule_extcall_invalid; auto. *)
(*     + rewrite <- app_comm_cons. destruct ps as [| p' ps']. *)
(*       * destruct N as [| q qs]. *)
(*         -- apply hcomp_right_identity1. *)
(*            apply extcall_invalid. *)
(*            intros. exploit initial_state_valid. *)
(*            apply H. intros Hx. apply Hx. *)
(*         -- apply horizontal_compose_simulation'. *)
(*            ++ apply identity_forward_simulation. *)
(*            ++ fold semantics. apply identity_forward_simulation. *)
(*            ++ apply linkorder_refl. *)
(*            ++ destruct qs; apply linkorder_refl. *)
(*       * edestruct IHps. cbn. omega. *)
(*         set (ps := p' :: ps') in *. clear IHps. *)
(*         etransitivity. *)
(*         -- apply horizontal_compose_associativity. *)
(*         -- fold semantics. *)
(*            apply horizontal_compose_simulation'. *)
(*            ++ apply identity_forward_simulation. *)
(*            ++ fold semantics. constructor. apply X. *)
(*            ++ apply linkorder_refl. *)
(*            ++ apply linkorder_refl. *)
(* Qed. *)

(* Lemma cmodule_krel {K1 K2} (R: rel_adt K1 K2) M sk: *)
(*   (List.length M >= 1)%nat -> skel_module_compatible sk M -> *)
(*   forward_simulation R R (semantics M sk @ K1) (semantics M sk @ K2). *)
(* Proof. *)
(*   set (P := fun M => skel_module_compatible sk M -> *)
(*                   forward_simulation R R (semantics M sk @ K1) (semantics M sk @ K2)). *)
(*   apply (@list_ind1 _ P); subst P; cbn beta. *)
(*   - intros p Hsk. apply lift_skel_extend. apply clight_krel. now inv Hsk. *)
(*   - intros p ps Hp Hsk. *)
(*     destruct ps as [| p' ps']. *)
(*     + apply lift_skel_extend. apply clight_krel. now inv Hsk. *)
(*     + set (p' :: ps') as ps in *. *)
(*       eapply open_fsim_ccref. apply cc_compose_id_left. *)
(*       unfold flip. apply cc_compose_id_left. *)
(*       eapply compose_forward_simulations. *)
(*       apply lift_horizontal_comp1. *)

(*       fold semantics. *)
(*       eapply open_fsim_ccref. apply cc_compose_id_right. *)
(*       unfold flip. apply cc_compose_id_right. *)
(*       eapply compose_forward_simulations. *)
(*       2: { apply lift_horizontal_comp2. } *)

(*       fold semantics. *)
(*       apply horizontal_compose_simulation'. *)
(*       * apply lift_skel_extend. apply clight_krel. now inv Hsk. *)
(*       * apply Hp. now inv Hsk. *)
(*       * apply linkorder_refl. *)
(*       * destruct ps. apply linkorder_refl. *)
(*         destruct ps; apply linkorder_refl. *)
(* Qed. *)
