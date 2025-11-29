Require Import interfaces.Category.
Require Import interfaces.Functor.

Require Import ProofIrrelevance.


Module LCoalg (L C : Category) (F : BifunctorDefinition L C C) <: Category.
    Import C.

    Record coalg := 
        mk_coalg {
            labels : L.t;
            states : C.t;
            step :> C.m states (F.omap labels states);
        }.

    Record coalg_mor (α β : coalg) := 
        mk_coalg_mor {
            morL : L.m (labels α) (labels β);
            morS : C.m (states α) (states β);
            coalg_sim_cond : 
                β @ morS = (F.fmap morL morS) @ α;
        }.
    Arguments morL {_ _}.
    Arguments morS {_ _}.

    Definition t : Type := coalg.

    Definition m (α β : t) : Type := coalg_mor α β.

    Lemma meq {α β : coalg} (f : m α β) (g : m α β) : 
        (morL f) = (morL g) -> (morS f) = (morS g) -> f = g.
    Proof.
       destruct f as [fl fs Hf]; destruct g as [gl gs Hg].
       cbn. intros Hl Hs. subst. f_equal. apply proof_irrelevance.
    Qed.

    Program Definition id (α : t) : m α α :=
    {|
        morL := L.id (labels α);
        morS := C.id (states α);
    |}.
    Next Obligation.
        rewrite C.compose_id_right.
        rewrite F.fmap_id. rewrite C.compose_id_left. reflexivity.
    Defined.

    Program Definition compose {α β γ} (g : m β γ) (f : m α β) : m α γ :=
    {|
        morL := L.compose (morL g) (morL f);
        morS := (morS g) @ (morS f);
    |}.
    Next Obligation.
        rewrite <- compose_assoc. rewrite coalg_sim_cond. rewrite compose_assoc.
        rewrite coalg_sim_cond. rewrite <- compose_assoc.
        rewrite <- F.fmap_compose. reflexivity.
    Defined.

    Proposition compose_id_left :
        forall {A B} (f : m A B), compose (id B) f = f.
    Proof.
        intros. unfold compose, id. simpl.
        apply meq; cbn. rewrite L.compose_id_left; reflexivity.
        rewrite C.compose_id_left; reflexivity.
    Qed.

    Proposition compose_id_right :
        forall {A B} (f : m A B), compose f (id A) = f.
    Proof.
        intros. unfold compose, id. simpl.
        apply meq; cbn. rewrite L.compose_id_right; reflexivity.
        rewrite C.compose_id_right; reflexivity.
    Qed.

    Proposition compose_assoc :
        forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
        compose (compose h g) f = compose h (compose g f).
    Proof.
        intros. unfold compose. simpl. 
        apply meq; cbn. rewrite L.compose_assoc; reflexivity.
        rewrite C.compose_assoc; reflexivity.
    Qed.

    Include CategoryTheory.
End LCoalg.
