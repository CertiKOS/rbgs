Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.

Module SigDefinition (C : CocartesianCategory) <: Category.
    Import C.
    Open Scope obj_scope.

    Definition t : Type := C.t * C.t.
    Definition m : t -> t -> Type :=
        fun A => fun B =>
            C.m ((fst A) + (snd A)) ((fst B) + (snd B)).

    Definition id : forall A, m A A :=
        fun A => C.id ((fst A) + (snd A)).
    Definition compose : forall {A B C}, m B C -> m A B -> m A C :=
        fun A B C => fun g => fun f => g @ f.

    Proposition compose_id_left :
        forall {A B} (f : m A B), compose (id B) f = f.
    Proof.
        intros. apply compose_id_left.
    Qed.

    Proposition compose_id_right :
        forall {A B} (f : m A B), compose f (id A) = f.
    Proof.
        intros. apply compose_id_right.
    Qed.

    Proposition compose_assoc :
        forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
        compose (compose h g) f = compose h (compose g f).
    Proof.
        intros. apply compose_assoc.
    Qed.

    Include CategoryTheory.
End SigDefinition.

Module Type Sig (C : CocartesianCategory).
    Include (SigDefinition C).
End Sig.

Module SigCocartesian (C : CocartesianCategory) (S : Sig C) <: CocartesianCategory.
    Include S.
    Import C.
    Open Scope obj_scope.

    Module Plus <: CocartesianStructure S.
        Import S.
        Local Infix "@" := C.compose (at level 45, right associativity) : hom_scope.

        (** Initial object: (0, 0) *)
        Definition unit : S.t := (C.Plus.unit, C.Plus.unit).

        Definition ini : forall X, S.m unit X :=
            fun X => C.Plus.copair (C.Plus.ini _) (C.Plus.ini _).

        Proposition ini_uni : forall {X} (x y : S.m unit X), x = y.
        Proof.
            intros.
            unfold S.m, unit. simpl.
            rewrite <- (C.Plus.copair_iota_compose x).
            rewrite <- (C.Plus.copair_iota_compose y).
            f_equal; apply C.Plus.ini_uni.
        Qed.

        (** Binary coproducts: (A1, A2) + (B1, B2) = (A1 + B1, A2 + B2) *)
        Definition omap (A B : S.t) : S.t :=
            (C.Plus.omap (fst A) (fst B), C.Plus.omap (snd A) (snd B)).

        Definition i1 : forall {A B : S.t}, S.m A (omap A B) :=
            fun A B => C.Plus.i1 + C.Plus.i1.

        Definition i2 : forall {A B : S.t}, S.m B (omap A B) :=
            fun A B => C.Plus.i2 + C.Plus.i2.

        Definition interchange (A1 B1 A2 B2 : C.t) : C.iso ((A1 + B1) + (A2 + B2)) ((A1 + A2) + (B1 + B2)) :=
            C.compose_iso (C.Plus.assoc A1 A2 (B1 + B2))
            (C.compose_iso (C.Plus.fmap_iso C.id_iso (C.bw_iso (C.Plus.assoc A2 B1 B2)))
            (C.compose_iso (C.Plus.fmap_iso C.id_iso (C.Plus.fmap_iso (C.Plus.swap_iso B1 A2) C.id_iso))
            (C.compose_iso (C.Plus.fmap_iso C.id_iso (C.Plus.assoc B1 A2 B2))
            (C.bw_iso (C.Plus.assoc A1 B1 (A2 + B2)))))).

        (* First prove what happens when we compose interchange with i1 @ i1 *)
        Lemma interchange_i1_i1 A1 B1 A2 B2 :
            interchange A1 B1 A2 B2 @ C.Plus.i1 @ C.Plus.i1 = C.Plus.i1 @ C.Plus.i1.
        Proof.
            unfold interchange. cbn [C.fw C.compose_iso C.bw_iso C.Plus.fmap_iso C.id_iso].
            rewrite !C.compose_assoc.
            pose (C.Plus.assoc_i1 A1 B1 (A2 + B2)). apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e.
            symmetry in e. rewrite e.
            rewrite C.Plus.fmap_i1, C.compose_id_right.
            rewrite C.Plus.fmap_i1, C.compose_id_right.
            rewrite C.Plus.fmap_i1, C.compose_id_right.
            rewrite Plus.assoc_i1.
            reflexivity.
        Qed.

        Lemma interchange_i1_i2 A1 B1 A2 B2 :
            interchange A1 B1 A2 B2 @ C.Plus.i1 @ C.Plus.i2 = C.Plus.i2 @ C.Plus.i1.
        Proof.
            unfold interchange. cbn [C.fw C.compose_iso C.bw_iso C.Plus.fmap_iso C.id_iso].
            rewrite !C.compose_assoc. 
            pose (C.Plus.assoc_i2_i1 A1 B1 (A2 + B2)). 
            apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e. rewrite <- e.
            replace ((C.id A1 + Plus.assoc B1 A2 B2) @ C.Plus.i2 @ C.Plus.i1)
                with (((C.id A1 + Plus.assoc B1 A2 B2) @ C.Plus.i2) @ C.Plus.i1)
                by (rewrite <- C.compose_assoc; reflexivity).
            rewrite C.Plus.fmap_i2. rewrite C.compose_assoc.
            rewrite C.Plus.assoc_i1.
            replace ((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2 @ C.Plus.i1 @ C.Plus.i1)
                with ((((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2) @ C.Plus.i1) @ C.Plus.i1)
                by (rewrite <- !C.compose_assoc; reflexivity).
            rewrite C.Plus.fmap_i2.
            replace ((C.Plus.i2 @ (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i1)
                with (C.Plus.i2 (A := A1) @ ((Plus.swap_iso B1 A2 + C.id B2) @ C.Plus.i1))
                by (rewrite <- !C.compose_assoc; reflexivity).
            rewrite C.Plus.fmap_i1. rewrite !C.compose_assoc.
            rewrite C.Plus.swap_i1.
            replace ((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2 @ C.Plus.i1 @ C.Plus.i2)
                with ((((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2) @ C.Plus.i1) @ C.Plus.i2)
                by (rewrite <- !C.compose_assoc; reflexivity). 
            rewrite C.Plus.fmap_i2. rewrite !C.compose_assoc.
            clear e. pose (C.Plus.assoc_i2_i1 A2 B1 B2).
            apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e. rewrite <- e.
            rewrite <- !C.compose_assoc.
            replace ((Plus.assoc A1 A2 (B1 + B2) @ C.Plus.i2) @ C.Plus.i2)
                with (Plus.assoc A1 A2 (B1 + B2) @ C.Plus.i2 @ C.Plus.i2)
                by (rewrite <- !C.compose_assoc; reflexivity).
            rewrite C.Plus.assoc_i2_i2. reflexivity.
        Qed.

        Lemma interchange_i2_i1 A1 B1 A2 B2 :
            interchange A1 B1 A2 B2 @ C.Plus.i2 @ C.Plus.i1 = C.Plus.i1 @ C.Plus.i2.
        Proof.
            unfold interchange. cbn [C.fw C.compose_iso C.bw_iso C.Plus.fmap_iso C.id_iso].
            rewrite !C.compose_assoc.
            pose (C.Plus.assoc_i2_i2 A1 B1 (A2 + B2)). 
            apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e.
            symmetry in e. 
            replace (C.bw (Plus.assoc A1 B1 (A2 + B2)) @ C.Plus.i2 @ C.Plus.i1)
                with ((C.bw (Plus.assoc A1 B1 (A2 + B2)) @ C.Plus.i2) @ C.Plus.i1)
                by (rewrite <- C.compose_assoc; reflexivity). rewrite e.
            replace ((C.id A1 + Plus.assoc B1 A2 B2) @ (C.Plus.i2 @ C.Plus.i2) @ C.Plus.i1)
                with ((((C.id A1 + Plus.assoc B1 A2 B2) @ C.Plus.i2) @ C.Plus.i2) @ C.Plus.i1)
                by (rewrite !C.compose_assoc; reflexivity). rewrite C.Plus.fmap_i2. 
            replace (((C.Plus.i2 @ Plus.assoc B1 A2 B2) @ C.Plus.i2) @ C.Plus.i1) 
                with (C.Plus.i2 (A := A1) @ (Plus.assoc B1 A2 B2 @ C.Plus.i2 @ C.Plus.i1))
                by (rewrite !C.compose_assoc; reflexivity).
            rewrite C.Plus.assoc_i2_i1.
            replace ((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2 @ C.Plus.i1 @ C.Plus.i2)
                with (((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2) @ C.Plus.i1 @ C.Plus.i2)
                by (rewrite !C.compose_assoc; reflexivity).
            rewrite C.Plus.fmap_i2. rewrite C.compose_assoc.
            replace ((Plus.swap_iso B1 A2 + C.id B2) @ C.Plus.i1 @ C.Plus.i2)
                with (((Plus.swap_iso B1 A2 + C.id B2) @ C.Plus.i1) @ C.Plus.i2)
                by (rewrite !C.compose_assoc; reflexivity).
            rewrite C.Plus.fmap_i1.
            replace ((C.Plus.i1 @ Plus.swap_iso B1 A2) @ C.Plus.i2)
                with (C.Plus.i1 (B:= B2) @ (Plus.swap_iso B1 A2 @ C.Plus.i2))
                by (rewrite !C.compose_assoc; reflexivity).
            rewrite C.Plus.swap_i2.
            replace ((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2 @ C.Plus.i1 @ C.Plus.i1)
                with (((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2) @ C.Plus.i1 @ C.Plus.i1)
                by (rewrite !C.compose_assoc; reflexivity).
            rewrite C.Plus.fmap_i2. 
            clear e. pose (C.Plus.assoc_i1 A2 B1 B2). 
            apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e.
            replace ((C.Plus.i2 @ C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i1 @ C.Plus.i1)
                with (C.Plus.i2 (A := A1) @ (C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i1 @ C.Plus.i1)
                by (rewrite !C.compose_assoc; reflexivity). rewrite <- e.
            apply C.Plus.assoc_i2_i1.
        Qed.

        Lemma interchange_i2_i2 A1 B1 A2 B2 :
            interchange A1 B1 A2 B2 @ C.Plus.i2 @ C.Plus.i2 = C.Plus.i2 @ C.Plus.i2.
        Proof.
            unfold interchange. cbn [C.fw C.compose_iso C.bw_iso C.Plus.fmap_iso C.id_iso].
            rewrite !C.compose_assoc. 
            pose (C.Plus.assoc_i2_i2 A1 B1 (A2 + B2)). 
            apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e.
            symmetry in e. 
            replace (C.bw (Plus.assoc A1 B1 (A2 + B2)) @ C.Plus.i2 @ C.Plus.i2)
                with ((C.bw (Plus.assoc A1 B1 (A2 + B2)) @ C.Plus.i2) @ C.Plus.i2)
                by (rewrite <- C.compose_assoc; reflexivity). rewrite e.
            replace ((C.id A1 + Plus.assoc B1 A2 B2) @ (C.Plus.i2 @ C.Plus.i2) @ C.Plus.i2)
                with ((((C.id A1 + Plus.assoc B1 A2 B2) @ C.Plus.i2) @ C.Plus.i2) @ C.Plus.i2)
                by (rewrite <- !C.compose_assoc; reflexivity).
            rewrite C.Plus.fmap_i2. rewrite !C.compose_assoc.
            rewrite C.Plus.assoc_i2_i2.
            replace ((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2 @ C.Plus.i2)
                with (((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2) @ C.Plus.i2)
                by (rewrite <- !C.compose_assoc; reflexivity).
            rewrite C.Plus.fmap_i2. rewrite !C.compose_assoc. rewrite C.Plus.fmap_i2.
            rewrite C.compose_id_right.
            replace ((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2 @ C.Plus.i2)
                with (((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2) @ C.Plus.i2)
                by (rewrite <- !C.compose_assoc; reflexivity).
            rewrite C.Plus.fmap_i2. rewrite !C.compose_assoc.
            clear e. pose (C.Plus.assoc_i2_i2 A2 B1 B2). 
            apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e. rewrite <- e.
            rewrite <- C.Plus.assoc_i2_i2. rewrite !C.compose_assoc. reflexivity.
        Qed.

        Lemma interchange_i1 A1 B1 A2 B2 :
            interchange A1 B1 A2 B2 @ (C.Plus.i1 + C.Plus.i1) = C.Plus.i1.
        Proof.
            rewrite <- (C.Plus.copair_iota_compose C.Plus.i1).
            unfold C.Plus.fmap. rewrite C.Plus.copair_compose.
            f_equal.
            - apply interchange_i1_i1.
            - apply interchange_i2_i1.
        Qed.

        Lemma interchange_i2 A1 B1 A2 B2 :
            interchange A1 B1 A2 B2 @ (C.Plus.i2 + C.Plus.i2) = C.Plus.i2.
        Proof.
            rewrite <- (C.Plus.copair_iota_compose C.Plus.i2).
            unfold C.Plus.fmap. rewrite C.Plus.copair_compose.
            f_equal.
            - apply interchange_i1_i2.
            - apply interchange_i2_i2.
        Qed.

        Lemma interchange_bw A1 B1 A2 B2 :
            C.Plus.copair (C.Plus.i1 + C.Plus.i1) (C.Plus.i2 + C.Plus.i2) = 
            C.bw (interchange A1 B1 A2 B2).
        Proof.
            symmetry.  apply C.Plus.copair_uni.
            - symmetry. apply (C.eq_fw_bw_l_1 (interchange _ _ _ _)).
            apply interchange_i1.
            - symmetry. apply (C.eq_fw_bw_l_1 (interchange _ _ _ _)).
            apply interchange_i2.
        Qed.

        Definition copair : forall {X A B : S.t}, S.m A X -> S.m B X -> S.m (omap A B) X :=
            fun X A B f g =>
                C.Plus.copair f g @ interchange (fst A) (fst B) (snd A) (snd B).

        Proposition copair_i1 : forall {X A B} (f : S.m A X) (g : S.m B X),
            S.compose (copair f g) i1 = f.
        Proof.
            intros. unfold compose, copair, i1.
            rewrite C.compose_assoc.
            rewrite (interchange_i1 (fst A) (fst B) (snd A) (snd B)) at 1.
            apply C.Plus.copair_i1.
        Qed.

        Proposition copair_i2 : forall {X A B} (f : S.m A X) (g : S.m B X),
            S.compose (copair f g) i2 = g.
        Proof.
            intros. unfold compose, copair, i2.
            rewrite C.compose_assoc.
            rewrite (interchange_i2 (fst A) (fst B) (snd A) (snd B)) at 1.
            apply C.Plus.copair_i2.
        Qed.

        Proposition copair_iota_compose : forall {X A B} x,
            @copair X A B (S.compose x i1) (S.compose x i2) = x.
        Proof.
            intros. unfold compose, copair, i1, i2.
            rewrite <- C.Plus.copair_compose.
            rewrite C.compose_assoc.
            epose (interchange_bw (fst A) (fst B) (snd A) (snd B)).
            rewrite e at 1.
            rewrite (C.bw_fw (interchange (fst A) (fst B) (snd A) (snd B))) at 1.
            rewrite C.compose_id_right.
            reflexivity.
        Qed.

        Include CocartesianStructureTheory S.
        Include BifunctorTheory S S S.
        Include SymmetricMonoidalStructureTheory S.
    End Plus.

    Include CocartesianTheory S.
End SigCocartesian.

Module SigToSet (C : CocartesianCategory) (S : Sig C) <: FaithfulFunctor S C.
    Import C.
    Open Scope obj_scope.

    Definition omap (X : S.t) : C.t := (fst X) + (snd X).

    Definition fmap {A B : S.t} (f : S.m A B) : C.m (omap A) (omap B) :=
        f.

    Proposition fmap_id : forall A, fmap (S.id A) = C.id (omap A).
    Proof. reflexivity. Qed.

    Proposition fmap_compose :
        forall {A B C} (g : S.m B C) (f : S.m A B),
        fmap (S.compose g f) = (fmap g) @ (fmap f).
    Proof. reflexivity. Qed.

    Proposition faithful : 
        forall {A B} (f g : S.m A B), fmap f = fmap g -> f = g.
    Proof. intros; assumption. Qed.

    Include (FunctorTheory S C).
End SigToSet.
