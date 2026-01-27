(*****************************************************)
(* Taken from https://github.com/QinxiangCao/UnifySL *)
(* Author: Qinxiang Cao                              *)
(*****************************************************)


Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ClassicalChoice.

Class Join (worlds: Type): Type := join: worlds -> worlds -> worlds -> Prop.

Class SeparationAlgebra (worlds: Type) {SA: Join worlds}: Type :=
{
  join_comm: forall m1 m2 m: worlds,
    join m1 m2 m ->
    join m2 m1 m;
  join_assoc: forall mx my mz mxy mxyz: worlds,
    join mx my mxy ->
    join mxy mz mxyz ->
    exists myz, join my mz myz /\ join mx myz mxyz
}.

Definition unit_element {worlds: Type} {J: Join worlds}: worlds -> Prop :=
  fun e => forall n n', join e n n' -> n = n'.

(***********************************)
(* Separation Algebra Generators   *)
(***********************************)

Section trivialSA.
  Context {worlds: Type}.
  
  Definition trivial_Join: Join worlds:=  (fun a b c => False).

  Definition trivial_SA: @SeparationAlgebra worlds trivial_Join.
  Proof.
    constructor; intuition.
    inversion H.
  Qed.
End trivialSA.

Section unitSA.
  Definition unit_Join: Join unit:=  (fun _ _ _ => True).

  Definition unit_SA: @SeparationAlgebra unit unit_Join.
  Proof.
    constructor.
    + intros. constructor.
    + intros; exists tt; split; constructor.
  Qed.

End unitSA.


Section equivSA.
  Context {worlds: Type}.
  
  Definition equiv_Join: Join worlds:=  (fun a b c => a = c /\ b = c).

  Definition equiv_SA: @SeparationAlgebra worlds equiv_Join.
  Proof.
    constructor.
    + intros.
      inversion H.
      split; tauto.
    + intros.
      simpl in *.
      destruct H, H0.
      subst mx my mxy mz.
      exists mxyz; do 2 split; auto.
  Qed.
End equivSA.

Section optionSA.
  Context (worlds: Type).
  
  Inductive option_join {J: Join worlds}: option worlds -> option worlds -> option worlds -> Prop :=
  | None_None_join: option_join None None None
  | None_Some_join: forall a, option_join None (Some a) (Some a)
  | Some_None_join: forall a, option_join (Some a) None (Some a)
  | Some_Some_join: forall a b c, join a b c -> option_join (Some a) (Some b) (Some c).

  Definition option_Join {SA: Join worlds}: Join (option worlds):=
    (@option_join SA).
  
  Definition option_SA
             {J: Join worlds}
             {SA: SeparationAlgebra worlds}:
    @SeparationAlgebra (option worlds) (option_Join).
  Proof.
    constructor.
    + intros.
      simpl in *.
      destruct H.
    - apply None_None_join.
    - apply Some_None_join.
    - apply None_Some_join.
    - apply Some_Some_join.
      apply join_comm; auto.
      + intros.
        simpl in *.
        inversion H; inversion H0; clear H H0; subst;
        try inversion H4; try inversion H5; try inversion H6; subst;
        try congruence;
        [.. | destruct (join_assoc _ _ _ _ _ H1 H5) as [? [? ?]];
           eexists; split; apply Some_Some_join; eassumption];
        eexists; split;
        try solve [ apply None_None_join | apply Some_None_join
                    | apply None_Some_join | apply Some_Some_join; eauto].
  Qed.

End optionSA.

Section exponentialSA.
  Definition fun_Join (A B: Type) {J_B: Join B}: Join (A -> B) :=
    (fun a b c => forall x, join (a x) (b x) (c x)).

  Definition fun_SA
             (A B: Type)
             {Join_B: Join B}
             {SA_B: SeparationAlgebra B}: @SeparationAlgebra (A -> B) (fun_Join A B).
  Proof.
    constructor.
    + intros.
      simpl in *.
      intros x; specialize (H x).
      apply join_comm; auto.
    + intros.
      simpl in *.
      destruct (choice (fun x fx => join (my x) (mz x) fx /\ join (mx x) fx (mxyz x) )) as [myz ?].
    - intros x; specialize (H x); specialize (H0 x).
      apply (join_assoc _ _ _ _ _ H H0); auto.
    - exists myz; firstorder.
  Qed.

End exponentialSA.

Section sumSA.

  Inductive sum_worlds {worlds1 worlds2}: Type:
    Type:=
  | lw (w:worlds1): sum_worlds
  | rw (w:worlds2): sum_worlds.

  Inductive sum_join {A B: Type} {J1: Join A} {J2: Join B}:
    @sum_worlds A B ->
    @sum_worlds A B ->
    @sum_worlds A B-> Prop :=
  | left_join a b c:
      join a b c ->
      sum_join (lw a) (lw b) (lw c)
  | right_join a b c:
      join a b c ->
      sum_join (rw a) (rw b) (rw c).

  Definition sum_Join (A B: Type) {Join_A: Join A} {Join_B: Join B}: Join (@sum_worlds A B) :=
    (@sum_join A B Join_A Join_B).

  Definition sum_SA (A B: Type) {Join_A: Join A} {Join_B: Join B} {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B}: @SeparationAlgebra (@sum_worlds A B) (sum_Join A B).
  Proof.
    constructor.
    - intros; inversion H;
      constructor; apply join_comm; auto.
    - intros.
      inversion H; subst;
      inversion H0;
      destruct (join_assoc _ _ _ _ _ H1 H3) as [myz [HH1 HH2]].
      + exists (lw myz); split; constructor; auto.
      + exists (rw myz); split; constructor; auto.
  Qed.

End sumSA.

Section productSA.

  Definition prod_Join (A B: Type) {Join_A: Join A} {Join_B: Join B}: Join (A * B) :=
    (fun a b c => join (fst a) (fst b) (fst c) /\ join (snd a) (snd b) (snd c)).

  Definition prod_SA (A B: Type) {Join_A: Join A} {Join_B: Join B} {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B}: @SeparationAlgebra (A * B) (prod_Join A B).
  Proof.
    constructor.
    + intros.
      simpl in *.
      destruct H; split;
      apply join_comm; auto.
    + intros.
      simpl in *.
      destruct H, H0.
      destruct (join_assoc _ _ _ _ _ H H0) as [myz1 [? ?]].
      destruct (join_assoc _ _ _ _ _ H1 H2) as [myz2 [? ?]].
      exists (myz1, myz2).
      do 2 split; auto.
  Qed.
End productSA.

Section setSA.
  
  

End setSA.



Class SeparationAlgebraUnit (worlds: Type) {SA: Join worlds} := {
  ue: worlds;
  unit_join: forall n, join n ue n;
  unit_spec: unit_element ue
}.