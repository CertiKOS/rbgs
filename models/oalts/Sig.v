Require Import interfaces.Category.
Require Import interfaces.MonoidalCategory.

Module Sig (C : CocartesianCategory) <: Category.
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
End Sig.

