Require Import interfaces.Category.
Require Import interfaces.Functor.

Require Import ProofIrrelevance.
Require Import Coq.Logic.JMeq.

(** * Pullbacks *)

(** ** Category with weak pullbacks *)
(** It might seem superfluos at first to define weak pullbacks first
  and then pullbacks. However, many relevant categorical properties only depend
  on the existence of weak pullbacks.

  For example, to show bisimulations in the Aczel-Mendler representation
  compose it is enough to compute a weak pullback.

  Moreover, sometimes in practice using a weak pullback allows one to choose
  a simpler representation for the pullback product.
*)

Module Type WeakPullbacksDefinition (C : CategoryDefinition).
  (** Here is the pullback diagram for reference:
<<
    [pb_prod f g] ---- [pb_p2 f g] -----> [B]
        |                                  |
        |                                  |
        |                                  |
    [pb_p1 f g]                           [g]
        |                                  |
        |                                  |
        |                                  |
        V                                  V
       [A] ------------- [f] -----------> [C]
>>
  *)
  Parameter pb_prod :
    forall {A B C}, forall (f : C.m A C) (g : C.m B C), C.t.
  Parameter pb_p1 :
    forall {A B C}, forall (f : C.m A C) (g : C.m B C), C.m (pb_prod f g) A.
  Parameter pb_p2 :
    forall {A B C}, forall (f : C.m A C) (g : C.m B C), C.m (pb_prod f g) B.

  Definition pb_cone {A B C} (f : C.m A C) (g : C.m B C)
    {X} (ll : C.m X A) (rl : C.m X B) : Prop :=
        C.compose f ll = C.compose g rl.

  Parameter pb_pair :
    forall {A B C} {f : C.m A C} {g : C.m B C},
      forall {X : C.t} {ll : C.m X A} {rl : C.m X B},
        pb_cone f g ll rl -> C.m X (pb_prod f g).

  Axiom pb_square :
    forall {A B C}, forall (f : C.m A C) (g : C.m B C),
      pb_cone  f g (pb_p1 f g) (pb_p2 f g).
  Axiom pb_p1_pair :
    forall {A B C} {f : C.m A C} {g : C.m B C},
      forall {X : C.t} {ll : C.m X A} {rl : C.m X B}
        (sq : pb_cone f g ll rl),
        C.compose (pb_p1 f g) (pb_pair sq) = ll.
  Axiom pb_p2_pair :
    forall {A B C} {f : C.m A C} {g : C.m B C},
      forall {X : C.t} {ll : C.m X A} {rl : C.m X B}
        (sq : pb_cone f g ll rl),
        C.compose (pb_p2 f g) (pb_pair sq) = rl.
End WeakPullbacksDefinition.

Module Type WeakPullbacks (C : CategoryDefinition) :=
  WeakPullbacksDefinition C.

(** ** Category with pullbacks *)

(** A pullback is just a weak pullback for which pairings are uniquely defined *)

Module Type PullbacksDefinition (C : CategoryDefinition).
  Include (WeakPullbacksDefinition C).

  Axiom pb_pair_uni :
    forall {A B C} {f : C.m A C} {g : C.m B C},
      forall {X : C.t} {ll : C.m X A} {rl : C.m X B}
        (sq : C.compose f ll = C.compose g rl),
        forall {p : C.m X (pb_prod f g)},
          C.compose (pb_p1 f g) p = ll ->
          C.compose (pb_p2 f g) p = rl ->
          pb_pair sq = p.
End PullbacksDefinition.

Module Type PullbackSquare (C : CategoryDefinition).
  Record IsPullback {A B X P : C.t}
    (f : C.m A X) (g : C.m B X)
    (p1 : C.m P A) (p2 : C.m P B) :=
  {
    is_pb_pair : forall {Y} (ll : C.m Y A) (rl : C.m Y B),
      C.compose f ll = C.compose g rl -> C.m Y P;
    is_pb_square : C.compose f p1 = C.compose g p2;
    is_pb_p1_pair : forall {Y} (ll : C.m Y A) (rl : C.m Y B)
      (sq : C.compose f ll = C.compose g rl),
      C.compose p1 (is_pb_pair ll rl sq) = ll;
    is_pb_p2_pair : forall {Y} (ll : C.m Y A) (rl : C.m Y B)
      (sq : C.compose f ll = C.compose g rl),
      C.compose p2 (is_pb_pair ll rl sq) = rl;
    is_pb_uni : forall {Y} (ll : C.m Y A) (rl : C.m Y B)
      (sq : C.compose f ll = C.compose g rl) (h : C.m Y P),
      C.compose p1 h = ll -> C.compose p2 h = rl ->
      h = is_pb_pair ll rl sq;
  }.

  Arguments is_pb_pair {A B X P f g p1 p2} _ {Y} ll rl _.
  Arguments is_pb_square {A B X P f g p1 p2} _.
  Arguments is_pb_p1_pair {A B X P f g p1 p2} _ {Y} ll rl sq.
  Arguments is_pb_p2_pair {A B X P f g p1 p2} _ {Y} ll rl sq.
  Arguments is_pb_uni {A B X P f g p1 p2} _ {Y} ll rl sq h _ _.
End PullbackSquare.

Module PullbacksTheory (C : Category) (P : PullbacksDefinition C).
  Include (PullbackSquare C).
  Import P.

  (** Two morphisms into a pullback are equal if they have the same projections. *)
  (** In other words, projections out of a pullback are jointly monic. *)
  Proposition pb_mor_eq : forall {A B C} {f : C.m A C} {g : C.m B C}
    {X} (h k : C.m X (pb_prod f g)),
    C.compose (pb_p1 f g) h = C.compose (pb_p1 f g) k ->
    C.compose (pb_p2 f g) h = C.compose (pb_p2 f g) k ->
    h = k.
  Proof.
    intros A B C0 f g X h k Hp1 Hp2.
    assert (cone : pb_cone f g (C.compose (pb_p1 f g) h) (C.compose (pb_p2 f g) h)).
    { unfold pb_cone. rewrite <- !C.compose_assoc. f_equal. apply pb_square. }
    transitivity (pb_pair cone).
    - symmetry. apply pb_pair_uni; reflexivity.
    - apply pb_pair_uni; symmetry; assumption.
  Qed.

  (** The canonical pairing of projections is the identity. *)
  Lemma pb_pair_id : forall {A B C} (f : C.m A C) (g : C.m B C),
    pb_pair (pb_square f g) = C.id (pb_prod f g).
  Proof.
    intros. apply pb_pair_uni; rewrite C.compose_id_right; reflexivity.
  Qed.

  Program Definition pb_is_pb {A B X : C.t} (f : C.m A X) (g : C.m B X) :
      IsPullback f g (pb_p1 f g) (pb_p2 f g) :=
      {|
        is_pb_pair := fun Y ll rl sq => pb_pair sq;
      |}.
  Next Obligation.
    exact (pb_square f g).
  Qed.
  Next Obligation.
    exact (pb_p1_pair sq).
  Qed.
  Next Obligation.
    exact (pb_p2_pair sq).
  Qed.
  Next Obligation.
    symmetry. apply pb_pair_uni; reflexivity.
  Defined.

  Program Definition is_pb_iso {A B X P : C.t}
    {f : C.m A X} {g : C.m B X} {p1 : C.m P A} {p2 : C.m P B}
    (is_pb : IsPullback f g p1 p2) : C.iso P (P.pb_prod f g) :=
  {|
    C.fw := pb_pair (is_pb_square is_pb);
    C.bw := is_pb_pair is_pb (pb_p1 f g) (pb_p2 f g) (pb_square f g);
  |}.
  Next Obligation.
    rewrite (is_pb_uni is_pb p1 p2 (is_pb_square is_pb) (C.id P)).
    - apply is_pb_uni.
      + rewrite <- C.compose_assoc.
        rewrite is_pb_p1_pair.
        apply pb_p1_pair.
      + rewrite <- C.compose_assoc.
        rewrite is_pb_p2_pair.
        apply pb_p2_pair.
    - apply C.compose_id_right.
    - apply C.compose_id_right.
  Qed.
  Next Obligation.
    apply pb_mor_eq.
    - rewrite C.compose_id_right.
      rewrite <- C.compose_assoc.
      rewrite pb_p1_pair.
      apply is_pb_p1_pair.
    - rewrite C.compose_id_right.
      rewrite <- C.compose_assoc.
      rewrite pb_p2_pair.
      apply is_pb_p2_pair.
  Defined.

End PullbacksTheory.

Module Type Pullbacks (C : Category) :=
  PullbacksDefinition C <+ PullbacksTheory C.

Module Type PreservesPullbacks (C : CategoryDefinition) (PbC : PullbackSquare C)
  (D : CategoryDefinition) (PbD : PullbackSquare D) (F : FunctorDefinition C D).

  Axiom preserves_pb : forall {A B X P : C.t}
    {f : C.m A X} {g : C.m B X} {p1 : C.m P A} {p2 : C.m P B},
    PbC.IsPullback f g p1 p2 ->
    PbD.IsPullback (F.fmap f) (F.fmap g) (F.fmap p1) (F.fmap p2).

End PreservesPullbacks.

Module Type BifunctorPreservesPullbacks
  (C1 : CategoryDefinition) (PbC1 : PullbackSquare C1)
  (C2 : CategoryDefinition) (PbC2 : PullbackSquare C2)
  (D : CategoryDefinition) (PbD : PullbackSquare D)
  (F : BifunctorDefinition C1 C2 D).

  (** Preserves pullbacks in the first argument *)
  Axiom preserves_pb_fst : forall (X2 : C2.t) {A B X P : C1.t}
    {f : C1.m A X} {g : C1.m B X} {p1 : C1.m P A} {p2 : C1.m P B},
    PbC1.IsPullback f g p1 p2 ->
    PbD.IsPullback (F.fmap f (C2.id X2)) (F.fmap g (C2.id X2))
                   (F.fmap p1 (C2.id X2)) (F.fmap p2 (C2.id X2)).

  (** Preserves pullbacks in the second argument *)
  Axiom preserves_pb_snd : forall (X1 : C1.t) {A B X P : C2.t}
    {f : C2.m A X} {g : C2.m B X} {p1 : C2.m P A} {p2 : C2.m P B},
    PbC2.IsPullback f g p1 p2 ->
    PbD.IsPullback (F.fmap (C1.id X1) f) (F.fmap (C1.id X1) g)
                   (F.fmap (C1.id X1) p1) (F.fmap (C1.id X1) p2).

End BifunctorPreservesPullbacks.

(** ** Category with pullbacks *)

(** A category bundled with a pullback structure. *)

Module Type CategoryWithPullbacks.
  Declare Module C : Category.
  Declare Module Pb : Pullbacks C.
  Include C.
End CategoryWithPullbacks.


Module FunctorPullbackCat
  (C : CategoryDefinition) (CL : CategoryDefinition) (CR : CategoryDefinition)
  (F : FunctorDefinition CL C) (G : FunctorDefinition CR C) <: Category.

  Record pb_obj := {
    fst : CL.t;
    snd : CR.t;

    pb_eq_fst :
      F.omap fst = G.omap snd;
  }.

  Proposition pb_obj_meq :
    forall (A B : pb_obj),
      fst A = fst B -> snd A = snd B -> A = B.
  Proof.
    intros. destruct A, B. cbn in *. subst. f_equal. apply proof_irrelevance.
  Qed.

  Record pb_mor {A B : pb_obj} := {
      fst_mor : CL.m (fst A) (fst B);
      snd_mor : CR.m (snd A) (snd B);

      pb_eq :
        JMeq (F.fmap fst_mor) (G.fmap snd_mor);
    }.
  Arguments pb_mor : clear implicits.

  Proposition pb_mor_meq {A B : pb_obj} :
    forall (f g : pb_mor A B),
      fst_mor f = fst_mor g -> snd_mor f = snd_mor g -> f = g.
  Proof.
    intros. destruct f, g. cbn in *. subst. f_equal. apply proof_irrelevance.
  Qed.

  Definition t : Type := pb_obj.
  Definition m : t -> t -> Type := pb_mor.

  Program Definition id : forall A, m A A :=
    fun A =>
    {|
      fst_mor := CL.id _;
      snd_mor := CR.id _;
    |}.
  Next Obligation.
    rewrite F.fmap_id, G.fmap_id.
    destruct A as [fst snd H]. simpl. rewrite H. reflexivity.
  Defined.

  Lemma JMeq_compose_cong :
    forall {A1 A2 B1 B2 C1 C2 : C.t}
      (f1 : C.m A1 B1) (f2 : C.m A2 B2)
      (g1 : C.m B1 C1) (g2 : C.m B2 C2),
      A1 = A2 -> B1 = B2 -> C1 = C2 ->
      JMeq f1 f2 -> JMeq g1 g2 ->
      JMeq (C.compose g1 f1) (C.compose g2 f2).
  Proof.
    intros.
    destruct H, H0, H1.
    apply JMeq_eq in H2. apply JMeq_eq in H3.
    rewrite H2, H3. reflexivity.
  Qed.

  Program Definition compose : forall {A B C}, m B C -> m A B -> m A C :=
    fun A B C => fun g f =>
    {|
      fst_mor := CL.compose (fst_mor g) (fst_mor f);
      snd_mor := CR.compose (snd_mor g) (snd_mor f);
    |}.
    Next Obligation.
      destruct A as [fstA sndA HA].
      destruct B as [fstB sndB HB].
      destruct C as [fstC sndC HC].
      destruct f as [f_fst f_snd Hf].
      destruct g as [g_fst g_snd Hg].
      simpl in *.
      rewrite F.fmap_compose, G.fmap_compose.
      apply JMeq_compose_cong; assumption.
    Qed.

  (** Properties *)

  Proposition compose_id_left :
    forall {A B} (f : m A B), compose (id B) f = f.
  Proof.
    intros. unfold compose, id; cbn. apply pb_mor_meq; cbn.
    rewrite CL.compose_id_left. reflexivity.
    rewrite CR.compose_id_left. reflexivity.
  Qed.

  Proposition compose_id_right :
    forall {A B} (f : m A B), compose f (id A) = f.
  Proof.
    intros. unfold compose, id; cbn. apply pb_mor_meq; cbn.
    rewrite CL.compose_id_right. reflexivity.
    rewrite CR.compose_id_right. reflexivity.
  Qed.

  Proposition compose_assoc :
    forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
      compose (compose h g) f = compose h (compose g f).
  Proof.
    intros. unfold compose, id; cbn. apply pb_mor_meq; cbn.
    rewrite CL.compose_assoc. reflexivity.
    rewrite CR.compose_assoc. reflexivity.
  Qed.

  Include CategoryTheory.
End FunctorPullbackCat.

Module Type FunctorPullbackCatInstance
  (C : CategoryDefinition) (CL : CategoryDefinition) (CR : CategoryDefinition)
    (F : FunctorDefinition CL C) (G : FunctorDefinition CR C) .
  Include (FunctorPullbackCat C CL CR F G).
End FunctorPullbackCatInstance.