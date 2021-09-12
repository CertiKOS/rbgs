(* This file contains definitions that will be moved to CompCertO later *)

Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Linking.

(* Require Import SmallstepLinking_. *)

(* Section HCOMP_ASSOC. *)

(*   Context {li} (L1 L2 L3: Smallstep_.semantics li li). *)
(*   Variable (sk: AST.program unit unit). *)
(*   Let L12 := fun b => match b with | true => L1 | false => L2 end. *)
(*   Let L := fun b => match b with *)
(*                  | true => SmallstepLinking_.semantics L12 sk *)
(*                  | false => L3 *)
(*                  end. *)
(*   Let L23 := fun b => match b with | true => L2 | false => L3 end. *)
(*   Let L' := fun b => match b with *)
(*                   | true => L1 *)
(*                   | false => SmallstepLinking_.semantics L23 sk *)
(*                   end. *)

(*   Variant frame3: Type := *)
(*   | fm1: state L1 -> frame3 *)
(*   | fm2: state L2 -> frame3 *)
(*   | fm3: state L3 -> frame3. *)

(*   Inductive flatten1: list (frame L) -> list frame3 -> Prop := *)
(*   | flatten1_nil_nil: flatten1 nil nil *)
(*   | flatten1_fm1' s k2 k: *)
(*       flatten1 k2 k -> *)
(*       flatten1 (st L true (st L12 true s :: nil) :: k2) (fm1 s :: k) *)
(*   | flatten1_fm1 s k1 k2 k: *)
(*       k1 <> nil -> flatten1 (st L true k1 :: k2) k -> *)
(*       flatten1 (st L true (st L12 true s :: k1) :: k2) (fm1 s :: k) *)
(*   | flatten1_fm2' s k2 k: *)
(*       flatten1 k2 k -> *)
(*       flatten1 (st L true (st L12 false s :: nil) :: k2) (fm2 s :: k) *)
(*   | flatten1_fm2 s k1 k2 k: *)
(*       k1 <> nil -> flatten1 (st L true k1 :: k2) k -> *)
(*       flatten1 (st L true (st L12 false s :: k1) :: k2) (fm2 s :: k) *)
(*   | flatten1_fm3 s k1 k: *)
(*       flatten1 k1 k -> *)
(*       flatten1 (st L false s :: k1) (fm3 s :: k). *)

(*   Inductive flatten2: list (frame L') -> list frame3 -> Prop := *)
(*   | flatten2_nil_nil: flatten2 nil nil *)
(*   | flatten2_fm1 s k1 k: *)
(*       flatten2 k1 k -> *)
(*       flatten2 (st L' true s :: k1) (fm1 s :: k) *)
(*   | flatten2_fm2' s k2 k: *)
(*       flatten2 k2 k -> *)
(*       flatten2 (st L' false (st L23 true s :: nil) :: k2) (fm2 s :: k) *)
(*   | flatten2_fm2 s k1 k2 k: *)
(*       k1 <> nil -> flatten2 (st L' false k1 :: k2) k -> *)
(*       flatten2 (st L' false (st L23 true s :: k1) :: k2) (fm2 s :: k) *)
(*   | flatten2_fm3' s k2 k: *)
(*       flatten2 k2 k -> *)
(*       flatten2 (st L' false (st L23 false s :: nil) :: k2) (fm3 s :: k) *)
(*   | flatten2_fm3 s k1 k2 k: *)
(*       k1 <> nil -> flatten2 (st L' false k1 :: k2) k -> *)
(*       flatten2 (st L' false (st L23 false s :: k1) :: k2) (fm3 s :: k). *)

(*   Hint Constructors flatten1 flatten2. *)

(*   Definition state_match (s1: list (frame L)) (s2: list (frame L')): Prop := *)
(*     exists fm, flatten1 s1 fm /\ flatten2 s2 fm. *)

(*   Lemma horizontal_compose_associativity: *)
(*     SmallstepLinking_.semantics L sk ≤ SmallstepLinking_.semantics L' sk. *)
(*   Proof. *)
(*     constructor. econstructor. reflexivity. *)
(*     intros. apply or_assoc. *)
(*     intros se ? [ ] qset [ ] Hse. *)
(*     instantiate (1 := fun _ _ _ => _). cbn beta. *)
(*     apply forward_simulation_step *)
(*       with (match_states := state_match); cbn. *)
(*     - intros q ? s1 <- H. inv H. destruct i. *)
(*       (* initial state of L12 *) *)
(*       + cbn in *. inv H1. destruct i. *)
(*         (* initial state of L1 *) *)
(*         * cbn in *. eexists; split. *)
(*           apply initial_state_intro with (i := true). *)
(*           firstorder. eauto. *)
(*           eexists. split; eauto. *)
(*         (* initial state of L2 *) *)
(*         * cbn in *. eexists; split. *)
(*           apply initial_state_intro with (i := false). *)
(*           cbn. firstorder. *)
(*           apply initial_state_intro with (i := true). *)
(*           firstorder. eauto. *)
(*           eexists. split; eauto. *)
(*       (* initial state of L3 *) *)
(*       + cbn in *. eexists; split. *)
(*         apply initial_state_intro with (i := false). *)
(*         cbn. firstorder. *)
(*         apply initial_state_intro with (i := false). *)
(*         firstorder. eauto. *)
(*         eexists. split; eauto. *)
(*     - intros s1 s2 r Hs H. exists r; split; auto. *)
(*       inv H. destruct i. *)
(*       (* final state of L12 *) *)
(*       + cbn in *. inv H0. destruct i. *)
(*         (* final state of L1 *) *)
(*         * cbn in *. destruct Hs as [fs [Hs1 Hs2]]. *)
(*           admit. *)
(*         (* final state of L2 *) *)
(*         * admit. *)
(*       (* final state of L3 *) *)
(*       + cbn in *. destruct Hs as [fs [Hs1 Hs2]]. *)
(*         inv Hs1. subst_dep. *)
(*         inv H3. inv Hs2. inv H2. *)
(*         repeat constructor; auto. *)
(*         inv H4. *)
(*     - admit. *)
(*     - intros s1 t s1' Hstep s2 Hs. *)
(*       inv Hstep. *)
(*       (* internal step *) *)
(*       + destruct i. *)
(*         (* internal step of L12 *) *)
(*         * inv H. *)
(*           (* internal step of L1 or L2 *) *)
(*           { *)
(*             destruct i. *)
(*             (* internal step of L1 *) *)
(*             - destruct Hs as [fm [Hs1 Hs2]]. *)
(*               admit. *)
(*             (* internal step of L2 *) *)
(*             - admit. *)
(*           } *)
(*           (* cross component call between L1 and L2 *) *)
(*           -- admit. *)
(*           (* return *) *)
(*           -- admit. *)
(*         (* internal step of L3 *) *)
(*         * admit. *)
(*       (* cross component call between L12 and L3 *) *)
(*       + destruct i. *)
(*         (* call from L12 *) *)
(*         * cbn in *. inv H. destruct i. *)
(*           (* call from L1 *) *)
(*           -- admit. *)
(*           (* call from L2 *) *)
(*           -- admit. *)
(*         (* call from L3 *) *)
(*         * admit. *)
(*       (* return *) *)
(*       + admit. *)

(*   Admitted. *)

(* End HCOMP_ASSOC. *)