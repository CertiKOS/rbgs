Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.Pullbacks.
Require Import interfaces.DoubleCat.

Require Import Program.Equality.
Require Import ProofIrrelevance.

(** * Spans *)

(** ** Span data *)

(** Basic span definitions that can be used independently of the
    double category structure. *)

Module SpanData (C : CategoryDefinition).

  (** A span from [a] to [b] is a diagram [a <-- vtx --> b]. *)
  Record span (a b : C.t) := mk_span {
    vtx : C.t;
    src_leg : C.m vtx a;
    tgt_leg : C.m vtx b;
  }.
  Arguments mk_span {a b}.
  Arguments vtx {a b}.
  Arguments src_leg {a b}.
  Arguments tgt_leg {a b}.

  (** A morphism of spans with frame morphisms [f] and [g]:
<<
           A
       a <----- vtx(A) -----> b
       |          |           |
     f |          | vtx_mor   | g
       |          |           |
       v          v           v
       a' <---- vtx(B) -----> b'
           B
>>
  *)

  Record span_mor {a b a' b' : C.t}
    (A : span a b) (B : span a' b') (f : C.m a a') (g : C.m b b') :=
  mk_span_mor {
    vtx_mor :> C.m (vtx A) (vtx B);
    src_leg_eq : C.compose (src_leg B) vtx_mor = C.compose f (src_leg A);
    tgt_leg_eq : C.compose (tgt_leg B) vtx_mor = C.compose g (tgt_leg A);
  }.
  Arguments mk_span_mor {a b a' b' A B f g}.
  Arguments vtx_mor {a b a' b' A B f g}.
  Arguments src_leg_eq {a b a' b' A B f g}.
  Arguments tgt_leg_eq {a b a' b' A B f g}.

  (** Equality of span morphisms. *)

  Proposition meq {a b a' b' : C.t}
    {A : span a b} {B : span a' b'} {f : C.m a a'} {g : C.m b b'}
    (α β : span_mor A B f g) :
    vtx_mor α = vtx_mor β -> α = β.
  Proof.
    intros H. destruct α, β; cbn in *; subst.
    f_equal; apply proof_irrelevance.
  Qed.

End SpanData.


(** * Double Category of Spans *)

(** The double category [Span(C)] has:
    - Objects: objects of [C]
    - Vertical 1-cells: morphisms of [C]
    - Horizontal 1-cells: spans in [C]
    - 2-cells: morphisms of spans

    Horizontal composition is given by pullback. This requires [C] to
    have pullbacks. *)

Module SpanDoubleCat (V : CategoryWithPullbacks) <: DoubleCategoryDefinition V.

  (** ** Vertical 1-cell category *)
  Import V.

  (** ** Vertical category of spans *)

  Module Vert <: DoubleVerticalCatDefinition V.

    (** *** Span data *)

    Include (SpanData C).

    (** *** Cell data *)
    Module CD <: DoubleCellData V.
      Definition hcell : V.t -> V.t -> Type := span.

      Infix "-o->" := hcell (at level 90, right associativity) : type_scope.
      Infix "~~>" := V.m (at level 90, right associativity) : type_scope.

      Definition tcell {sA tA sB tB : V.t}
        (A : sA -o-> tA) (B : sB -o-> tB) (f : sA ~~> sB) (g : tA ~~> tB) : Type :=
        span_mor A B f g.

      Notation "A =[ f , g ]=> B" := (tcell A B f g)
        (at level 70, f at next level, g at next level, no associativity).

      (** *** Vertical composition *)

      Program Definition vid {s t : V.t} (A : s -o-> t) : A =[V.id s, V.id t]=> A :=
        {| vtx_mor := V.id (vtx A) |}.
      Next Obligation.
        rewrite V.compose_id_right, V.compose_id_left. reflexivity.
      Qed.
      Next Obligation.
        rewrite V.compose_id_right, V.compose_id_left. reflexivity.
      Qed.

      Program Definition vcomp {sA tA sB tB sC tC : V.t}
        {A : sA -o-> tA} {B : sB -o-> tB} {D : sC -o-> tC}
        {sf : sA ~~> sB} {tf : tA ~~> tB} {sg : sB ~~> sC} {tg : tB ~~> tC}
        (α : A =[sf, tf]=> B) (β : B =[sg, tg]=> D) :
        A =[V.compose sg sf, V.compose tg tf]=> D :=
        {| vtx_mor := V.compose (vtx_mor β) (vtx_mor α) |}.
      Next Obligation.
        rewrite <- V.compose_assoc, src_leg_eq.
        rewrite V.compose_assoc, src_leg_eq.
        rewrite V.compose_assoc. reflexivity.
      Qed.
      Next Obligation.
        rewrite <- V.compose_assoc, tgt_leg_eq.
        rewrite V.compose_assoc, tgt_leg_eq.
        rewrite V.compose_assoc. reflexivity.
      Qed.

      (** *** Horizontal identity *)

      Definition hid (a : V.t) : a -o-> a :=
        {| vtx := a; src_leg := V.id a; tgt_leg := V.id a |}.

      Program Definition hid_mor {a b : V.t} (f : a ~~> b) : hid a =[f, f]=> hid b :=
        {| vtx_mor := f |}.
      Next Obligation.
        rewrite V.compose_id_left, V.compose_id_right. reflexivity.
      Qed.
      Next Obligation.
        rewrite V.compose_id_left, V.compose_id_right. reflexivity.
      Qed.

    (** *** Horizontal composition *)

    (** Horizontal composition of spans is given by pullback:
<<
                          A ⨀ B
                        pb_prod
                          /   \
                    pb_p1 /     \ pb_p2
                        /         \
                       v           v
            a <--- vtx(A) --->b<--- vtx(B) ---> c
                        tgt_leg   src_leg
>>
    *)

      Definition hcomp {a b c : V.t} (A : a -o-> b) (B : b -o-> c) : a -o-> c :=
        {|
          vtx := V.Pb.pb_prod (tgt_leg A) (src_leg B);
          src_leg := V.compose (src_leg A) (V.Pb.pb_p1 _ _);
          tgt_leg := V.compose (tgt_leg B) (V.Pb.pb_p2 _ _);
        |}.

      Infix "⨀" := hcomp (at level 45, right associativity) : type_scope.

      (** *** Scopes and notations *)

      Declare Scope hom_scope.
      Delimit Scope hom_scope with hom.
      Bind Scope hom_scope with tcell.
      Open Scope hom_scope.

      (** *** Horizontal composition of 2-cells *)

      (** Uses the universal property of pullbacks. *)

      Lemma hcomp_fmap_cone {a a' b b' c c' : V.t}
        {A : a -o-> b} {A' : a' -o-> b'} {B : b -o-> c} {B' : b' -o-> c'}
        {f : a ~~> a'} {g : b ~~> b'} {h : c ~~> c'}
        (α : A =[f,g]=> A') (β : B =[g,h]=> B') :
        V.Pb.pb_cone (tgt_leg A') (src_leg B')
          (V.compose (vtx_mor α) (V.Pb.pb_p1 (tgt_leg A) (src_leg B)))
          (V.compose (vtx_mor β) (V.Pb.pb_p2 (tgt_leg A) (src_leg B))).
      Proof.
        unfold V.Pb.pb_cone.
        rewrite <- !V.compose_assoc.
        rewrite tgt_leg_eq, src_leg_eq.
        rewrite !V.compose_assoc.
        rewrite (V.Pb.pb_square (tgt_leg A) (src_leg B)).
        reflexivity.
      Qed.

      Program Definition hcomp_fmap_core {a a' b b' c c' : V.t}
        {A : a -o-> b} {A' : a' -o-> b'} {B : b -o-> c} {B' : b' -o-> c'}
        {f : a ~~> a'} {g : b ~~> b'} {h : c ~~> c'}
        (α : A =[f,g]=> A') (β : B =[g,h]=> B') : (A ⨀ B) =[f,h]=> (A' ⨀ B') :=
        {| vtx_mor := V.Pb.pb_pair (hcomp_fmap_cone α β) |}.
      Next Obligation.
        unfold hcomp; cbn.
        rewrite V.compose_assoc, V.Pb.pb_p1_pair.
        rewrite <- V.compose_assoc, src_leg_eq.
        rewrite V.compose_assoc. reflexivity.
      Qed.
      Next Obligation.
        unfold hcomp; cbn.
        rewrite V.compose_assoc, V.Pb.pb_p2_pair.
        rewrite <- V.compose_assoc, tgt_leg_eq.
        rewrite V.compose_assoc. reflexivity.
      Qed.
    End CD.
    Include CD.
    Include (DoubleCellDerived V CD).

    Lemma harr_meq {A B : harr} (f g : harr_mor A B) :
      src_mor f = src_mor g ->
      tgt_mor f = tgt_mor g ->
      vtx_mor (carrier_mor f) = vtx_mor (carrier_mor g) ->
      f = g.
    Proof.
      intros Hs Ht Hc.
      destruct f as [sf tf cf], g as [sg tg cg]; cbn in *.
      subst. f_equal. apply meq. exact Hc.
    Qed.

    (** *** Category axioms *)
    Proposition compose_id_left :
      forall {A B} (f : m A B), compose (id B) f = f.
    Proof.
      intros. apply harr_meq; cbn; apply V.compose_id_left.
    Qed.

    Proposition compose_id_right :
      forall {A B} (f : m A B), compose f (id A) = f.
    Proof.
      intros. apply harr_meq; cbn; apply V.compose_id_right.
    Qed.

    Proposition compose_assoc :
      forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
        compose (compose h g) f = compose h (compose g f).
    Proof.
      intros. apply harr_meq; cbn; apply V.compose_assoc.
    Qed.

  End Vert.
  Include Vert.
  Import Siso.

  Notation "f ;; g" := (Vert.compose g f)
    (at level 50, left associativity) : hom_scope.

  (** ** Functoriality of [hid] *)

  Proposition hid_fmap_id :
    forall A, Vert.hid_mor (V.id A) = Vert.id (Vert.hid A).
  Proof.
    intros. unfold Vert.hid_mor, Vert.id, Vert.vid.
    f_equal. apply meq; cbn. reflexivity.
  Qed.

  Proposition hid_fmap_compose :
    forall {A B C} (g : V.m B C) (f : V.m A B),
      Vert.hid_mor (V.compose g f) = Vert.compose (Vert.hid_mor g) (Vert.hid_mor f).
  Proof.
    intros. unfold Vert.hid_mor, Vert.compose, Vert.vcomp.
    f_equal. apply meq; cbn. reflexivity.
  Qed.

  (** ** Functoriality of [hcomp] *)

  Proposition hcomp_fmap_id :
    forall {a b c : V.t} (A : a -o-> b) (B : b -o-> c),
      (Vert.vid A ⊙ Vert.vid B) = Vert.vid (A ⨀ B).
    Proof.
      intros. apply meq. unfold vid, hcomp_fmap; cbn.
      apply Pb.pb_pair_uni;
      rewrite V.compose_id_right, V.compose_id_left; reflexivity.
    Qed.

  Proposition hcomp_fmap_compose :
    forall {a a' a'' b b' b'' c c' c'' : V.t}
      {A : a -o-> b} {A' : a' -o-> b'} {A'' : a'' -o-> b''}
      {B : b -o-> c} {B' : b' -o-> c'} {B'' : b'' -o-> c''}
      {f : a ~~> a'} {f' : a' ~~> a''} {g : b ~~> b'} {g' : b' ~~> b''}
      {h : c ~~> c'} {h' : c' ~~> c''}
      (α : A =[f,g]=> A') (α' : A' =[f',g']=> A'')
      (β : B =[g,h]=> B') (β' : B' =[g',h']=> B''),
      (vcomp α α') ⊙ (vcomp β β') = vcomp (α ⊙ β) (α' ⊙ β').
    Proof.
      intros. apply meq. unfold vcomp, hcomp; cbn.
      apply Pb.pb_pair_uni.
      - rewrite <- V.compose_assoc, Pb.pb_p1_pair.
        rewrite V.compose_assoc, Pb.pb_p1_pair.
        rewrite V.compose_assoc; reflexivity.
      - rewrite <- V.compose_assoc, Pb.pb_p2_pair.
        rewrite V.compose_assoc, Pb.pb_p2_pair.
        rewrite V.compose_assoc; reflexivity.
    Qed.

  (** ** Structural isomorphisms *)

  (** Associator: [(A ⨀ B) ⨀ C ≅ A ⨀ (B ⨀ C)] *)
  Program Definition assoc {a b c d : V.t}
    (A : a -o-> b) (B : b -o-> c) (C : c -o-> d) :
    Siso.sisocell ((A ⨀ B) ⨀ C) (A ⨀ (B ⨀ C)) :=
    {|
      Siso.fw := {| vtx_mor :=
        let rl := Pb.pb_pair (f := tgt_leg B) (g := src_leg C)
          (ll := Pb.pb_p2 (tgt_leg A) (src_leg B) @ Pb.pb_p1 (tgt_leg (A ⨀ B)) (src_leg C))
          (rl := Pb.pb_p2 (tgt_leg (A ⨀ B)) (src_leg C)) _ in
        Pb.pb_pair (f := tgt_leg A) (g := src_leg (B ⨀ C))
          (ll := Pb.pb_p1 (tgt_leg A) (src_leg B) @ Pb.pb_p1 (tgt_leg (A ⨀ B)) (src_leg C))
          (rl := rl) _ |};
      Siso.bw := {| vtx_mor :=
        let ll := Pb.pb_pair (f := tgt_leg A) (g := src_leg B)
          (ll := Pb.pb_p1 (tgt_leg A) (src_leg (B ⨀ C)))
          (rl := Pb.pb_p1 (tgt_leg B) (src_leg C) @ Pb.pb_p2 (tgt_leg A) (src_leg (B ⨀ C))) _ in
        Pb.pb_pair (f := tgt_leg (A ⨀ B)) (g := src_leg C)
          (ll := ll)
          (rl := Pb.pb_p2 (tgt_leg B) (src_leg C) @ Pb.pb_p2 (tgt_leg A) (src_leg (B ⨀ C))) _ |};
    |}.
  Next Obligation.
    unfold Pb.pb_cone. rewrite <- V.compose_assoc, Pb.pb_square. reflexivity.
  Qed.
  Next Obligation.
    unfold Pb.pb_cone.
    rewrite <- !V.compose_assoc, (Pb.pb_square (tgt_leg A) (src_leg B)).
    rewrite !V.compose_assoc, Pb.pb_p1_pair. reflexivity.
  Qed.
  Next Obligation.
    unfold Pb.pb_cone. rewrite V.compose_id_left.
    rewrite !V.compose_assoc. f_equal.
    rewrite Pb.pb_p1_pair. reflexivity.
  Qed.
  Next Obligation.
    rewrite !V.compose_assoc. rewrite V.compose_id_left.
    rewrite Pb.pb_p2_pair. rewrite Pb.pb_p2_pair.
    reflexivity.
  Qed.
  Next Obligation.
    unfold Pb.pb_cone. rewrite Pb.pb_square.
    rewrite !V.compose_assoc. reflexivity.
  Qed.
  Next Obligation.
    unfold Pb.pb_cone. rewrite !V.compose_assoc, Pb.pb_p2_pair.
    rewrite <- !V.compose_assoc, Pb.pb_square. reflexivity.
  Qed.
  Next Obligation.
    rewrite V.compose_id_left, !V.compose_assoc, !Pb.pb_p1_pair. reflexivity.
  Qed.
  Next Obligation.
    rewrite V.compose_id_left.
    rewrite !V.compose_assoc, Pb.pb_p2_pair. reflexivity.
  Qed.
  Next Obligation.
    unfold compose. apply harr_meq; cbn; try apply V.compose_id_left.
    apply Pb.pb_mor_eq.
    - rewrite V.compose_id_right.
      rewrite <- !V.compose_assoc, Pb.pb_p1_pair.
      rewrite !V.compose_assoc, Pb.pb_p1_pair.
      rewrite Pb.pb_p1_pair. reflexivity.
    - rewrite V.compose_id_right.
      rewrite <- !V.compose_assoc, Pb.pb_p2_pair.
      apply Pb.pb_mor_eq.
      + rewrite <- !V.compose_assoc, Pb.pb_p1_pair.
        rewrite !V.compose_assoc, Pb.pb_p1_pair.
        rewrite Pb.pb_p2_pair. reflexivity.
      + rewrite <- !V.compose_assoc, Pb.pb_p2_pair.
        rewrite Pb.pb_p2_pair. reflexivity.
  Qed.
  (* fw_bw: fw @ bw = id *)
  Next Obligation.
    unfold compose. apply harr_meq; cbn; try apply V.compose_id_left.
    apply Pb.pb_mor_eq.
    - rewrite V.compose_id_right. rewrite <- !V.compose_assoc, Pb.pb_p1_pair.
      apply Pb.pb_mor_eq.
      + rewrite <- !V.compose_assoc, Pb.pb_p1_pair. rewrite Pb.pb_p1_pair.
        reflexivity.
      + rewrite <- !V.compose_assoc, Pb.pb_p2_pair.
        rewrite !V.compose_assoc, Pb.pb_p2_pair.
        rewrite Pb.pb_p1_pair. reflexivity.
    - rewrite V.compose_id_right.
      rewrite <- !V.compose_assoc, Pb.pb_p2_pair.
      rewrite !V.compose_assoc, Pb.pb_p2_pair.
      rewrite Pb.pb_p2_pair. reflexivity.
  Defined.

  (** Left unitor: [hid a ⨀ A ≅ A] *)
  Program Definition lunit {a b : V.t} (A : a -o-> b) :
    Siso.sisocell (hid a ⨀ A) A :=
    {|
      Siso.fw := {| vtx_mor := Pb.pb_p2 (V.id a) (src_leg A); |};
      Siso.bw := {| vtx_mor :=
        Pb.pb_pair (f := V.id a) (g := src_leg A) (ll := src_leg A) (rl := V.id (vtx A)) _|};
    |}.
  Next Obligation.
    rewrite V.compose_id_left. rewrite <- Pb.pb_square. reflexivity.
  Qed.
  Next Obligation.
    rewrite V.compose_id_left. reflexivity.
  Qed.
  Next Obligation.
    unfold Pb.pb_cone. rewrite V.compose_id_left, V.compose_id_right. reflexivity.
  Qed.
  Next Obligation.
    rewrite !V.compose_id_left. rewrite Pb.pb_p1_pair. reflexivity.
  Qed.
  Next Obligation.
    rewrite V.compose_assoc. rewrite Pb.pb_p2_pair.
    rewrite V.compose_id_left, V.compose_id_right. reflexivity.
  Qed.
  Next Obligation.
    unfold compose. apply harr_meq; cbn; try (apply V.compose_id_left).
    rewrite Pb.pb_p2_pair. reflexivity.
  Qed.
  Next Obligation.
    unfold compose. apply harr_meq; cbn; try (apply V.compose_id_left).
    apply Pb.pb_mor_eq.
    - rewrite <- V.compose_assoc, Pb.pb_p1_pair.
      rewrite <- Pb.pb_square, V.compose_id_left, V.compose_id_right. reflexivity.
    - rewrite <- V.compose_assoc, Pb.pb_p2_pair.
      rewrite V.compose_id_left, V.compose_id_right. reflexivity.
  Defined.

  (** Right unitor: [A ⨀ hid b ≅ A] *)
  Program Definition runit {a b : V.t} (A : a -o-> b) :
    Siso.sisocell (A ⨀ hid b) A :=
    {|
      Siso.fw := {| vtx_mor := Pb.pb_p1 (tgt_leg A) (V.id b); |};
      Siso.bw := {| vtx_mor :=
        Pb.pb_pair (f := tgt_leg A) (g := V.id b) (ll := V.id (vtx A)) (rl := tgt_leg A) _|};
    |}.
  Next Obligation.
    rewrite V.compose_id_left. reflexivity.
  Qed.
  Next Obligation.
    rewrite V.compose_id_left. rewrite <- Pb.pb_square. reflexivity.
  Qed.
  Next Obligation.
    unfold Pb.pb_cone. rewrite V.compose_id_left, V.compose_id_right. reflexivity.
  Qed.
  Next Obligation.
    rewrite !V.compose_id_left. rewrite V.compose_assoc.
    rewrite Pb.pb_p1_pair. rewrite V.compose_id_right. reflexivity.
  Qed.
  Next Obligation.
    rewrite !V.compose_id_left. rewrite Pb.pb_p2_pair. reflexivity.
  Qed.
  Next Obligation.
    unfold compose. apply harr_meq; cbn; try (apply V.compose_id_left).
    rewrite Pb.pb_p1_pair. reflexivity.
  Qed.
  Next Obligation.
    unfold compose. apply harr_meq; cbn; try (apply V.compose_id_left).
    apply Pb.pb_mor_eq.
    - rewrite <- V.compose_assoc, Pb.pb_p1_pair.
      rewrite V.compose_id_left, V.compose_id_right. reflexivity.
    - rewrite <- V.compose_assoc, Pb.pb_p2_pair.
      rewrite Pb.pb_square, V.compose_id_left, V.compose_id_right. reflexivity.
  Defined.

  (** ** Naturality *)

  Proposition assoc_nat :
    forall {a a' b b' c c' d d' : V.t}
      {A : a -o-> b} {A' : a' -o-> b'}
      {B : b -o-> c} {B' : b' -o-> c'}
      {C : c -o-> d} {C' : c' -o-> d'}
      {f : V.m a a'} {g : V.m b b'} {h : V.m c c'} {k : V.m d d'}
      (α : A =[f,g]=> A') (β : B =[g,h]=> B') (γ : C =[h,k]=> C'),
      (assoc A B C) ;; (α ⊙ (β ⊙ γ)) = ((α ⊙ β) ⊙ γ) ;; (assoc A' B' C').
  Proof.
    intros. apply harr_meq; cbn;
      try (rewrite V.compose_id_left, V.compose_id_right; reflexivity).
    apply Pb.pb_mor_eq.
    - rewrite <- !V.compose_assoc, !Pb.pb_p1_pair.
      rewrite !V.compose_assoc, !Pb.pb_p1_pair.
      rewrite <- !V.compose_assoc. rewrite Pb.pb_p1_pair. reflexivity.
    - rewrite <- !V.compose_assoc, !Pb.pb_p2_pair.
      rewrite !V.compose_assoc. rewrite Pb.pb_p2_pair.
      apply Pb.pb_mor_eq.
      + rewrite <- !V.compose_assoc, !Pb.pb_p1_pair.
        rewrite !V.compose_assoc, !Pb.pb_p1_pair.
        rewrite <- !V.compose_assoc, Pb.pb_p2_pair. reflexivity.
      + rewrite <- !V.compose_assoc, !Pb.pb_p2_pair.
        rewrite !V.compose_assoc, Pb.pb_p2_pair. reflexivity.
  Qed.

  Proposition lunit_nat :
    forall {a a' b b' : V.t}
      {A : a -o-> b} {A' : a' -o-> b'}
      {f : V.m a a'} {g : V.m b b'}
      (α : A =[f,g]=> A'),
      (lunit A) ;; α = (hid_mor f ⊙ α) ;; (lunit A').
  Proof.
    intros. apply harr_meq; cbn;
      try (rewrite V.compose_id_left, V.compose_id_right; reflexivity).
    rewrite Pb.pb_p2_pair. reflexivity.
  Qed.

  Proposition runit_nat :
    forall {a a' b b' : V.t}
      {A : a -o-> b} {A' : a' -o-> b'}
      {f : V.m a a'} {g : V.m b b'}
      (α : A =[f,g]=> A'),
      (runit A) ;; α = (α ⊙ hid_mor g) ;; (runit A').
  Proof.
    intros. apply harr_meq; cbn;
    try (rewrite V.compose_id_left, V.compose_id_right; reflexivity).
    rewrite Pb.pb_p1_pair. reflexivity.
  Qed.

  (** ** Coherence *)

  Proposition assoc_coh :
    forall {a b c d e : V.t}
      (A : a -o-> b) (B : b -o-> c) (C : c -o-> d) (D : d -o-> e),
      ((assoc A B C) ⊙ vid D) ;; (assoc A (B ⨀ C) D) ;; (vid A ⊙ (assoc B C D))
      = (assoc (A ⨀ B) C D) ;; (assoc A B (C ⨀ D)).
  Proof.
    intros. apply harr_meq; cbn; (try (rewrite !V.compose_id_left; reflexivity)).
    apply Pb.pb_mor_eq.
    - rewrite <- !V.compose_assoc, !Pb.pb_p1_pair, V.compose_id_left.
      rewrite Pb.pb_p1_pair. rewrite !V.compose_assoc, !Pb.pb_p1_pair.
      rewrite <- !V.compose_assoc, Pb.pb_p1_pair.
      reflexivity.
    - rewrite <- !V.compose_assoc, !Pb.pb_p2_pair.
      apply Pb.pb_mor_eq.
      + rewrite <- !V.compose_assoc, !Pb.pb_p1_pair.
        rewrite !V.compose_assoc, Pb.pb_p1_pair.
        rewrite <- V.compose_assoc.
        set (p2term := Pb.pb_p2 (tgt_leg A)
         ((src_leg B @ Pb.pb_p1 (tgt_leg B) (src_leg C)) @ _)).
        set (pair1 := Pb.pb_pair _).
        set (pair2 := Pb.pb_pair _).
        replace (p2term @ pair1 @ pair2) with ((p2term @ pair1) @ pair2)
            by (apply V.compose_assoc).
        unfold p2term, pair1.  clear pair1. rewrite Pb.pb_p2_pair.
        rewrite V.compose_assoc.
        set (p1term := Pb.pb_p1 _ (src_leg D)).
        set (pair1 := Pb.pb_pair _).
        replace (p1term @ pair1 @ pair2) with ((p1term @ pair1) @ pair2)
          by (apply V.compose_assoc).
        unfold p1term, pair1; rewrite Pb.pb_p1_pair; clear p1term; clear pair1.
        rewrite !V.compose_assoc. unfold pair2; clear pair2.
        rewrite Pb.pb_p1_pair. rewrite <- !V.compose_assoc. f_equal.
        rewrite !V.compose_assoc. rewrite Pb.pb_p2_pair. rewrite Pb.pb_p1_pair.
        reflexivity.
      + rewrite <- !V.compose_assoc. rewrite !Pb.pb_p2_pair.
        symmetry. apply Pb.pb_pair_uni.
        * rewrite <- !V.compose_assoc. rewrite Pb.pb_p1_pair.
          rewrite !V.compose_assoc.
          set (p2term :=
            Pb.pb_p2 _ ((src_leg B @ Pb.pb_p1 (tgt_leg B) (src_leg C)) @ _)).
          set (pair1 := Pb.pb_pair _). set (pair2 := Pb.pb_pair _).
          replace (p2term @ pair1 @ pair2) with ((p2term @ pair1) @ pair2)
            by (apply V.compose_assoc).
          unfold p2term, pair1; clear p2term; clear pair1. rewrite Pb.pb_p2_pair.
          set (p1term := Pb.pb_p1 (tgt_leg C @ _) _).
          set (pair1 := Pb.pb_pair _).
          replace (p1term @ pair1 @ pair2) with ((p1term @ pair1) @ pair2)
            by (apply V.compose_assoc).
          unfold p1term, pair1; clear pair1; clear p1term. rewrite Pb.pb_p1_pair.
          rewrite !V.compose_assoc. unfold pair2; clear pair2.
          rewrite Pb.pb_p1_pair. rewrite <- !V.compose_assoc. f_equal.
          rewrite !V.compose_assoc. rewrite !Pb.pb_p2_pair. reflexivity.
        * rewrite <- !V.compose_assoc. rewrite Pb.pb_p2_pair.
          rewrite !V.compose_assoc.
          set (p2term := Pb.pb_p2 (tgt_leg A)
            ((src_leg B @ Pb.pb_p1 (tgt_leg B) (src_leg C)) @ _)).
          set (pair1 := Pb.pb_pair _). set (pair2 := Pb.pb_pair _).
          replace (p2term @ pair1 @ pair2) with ((p2term @ pair1) @ pair2)
            by (apply V.compose_assoc).
          unfold p2term, pair1; clear p2term; clear pair1. rewrite Pb.pb_p2_pair.
          rewrite <- V.compose_assoc. rewrite Pb.pb_p2_pair.
          unfold pair2; clear pair2.  rewrite Pb.pb_p2_pair.
          rewrite V.compose_id_left. reflexivity.
  Qed.

  Proposition unit_coh :
    forall {a b c : V.t} (A : a -o-> b) (B : b -o-> c),
      ((runit A) ⊙ vid B : Vert.m _ _) =
      (assoc A (hid b) B) ;; (vid A ⊙ (lunit B)).
  Proof.
    intros. apply harr_meq; cbn; (try (rewrite !V.compose_id_left; reflexivity)).
    apply Pb.pb_pair_uni.
    - rewrite <- !V.compose_assoc. rewrite Pb.pb_p1_pair.
      rewrite !V.compose_assoc. rewrite Pb.pb_p1_pair.
      rewrite !V.compose_id_left. reflexivity.
    - rewrite <- !V.compose_assoc. rewrite Pb.pb_p2_pair.
      rewrite !V.compose_assoc. rewrite !Pb.pb_p2_pair.
      rewrite !V.compose_id_left. reflexivity.
  Qed.

End SpanDoubleCat.

(** ** Full double category instance *)
Module SpanDouble (V : CategoryWithPullbacks) :=
  SpanDoubleCat V <+ DoubleCategoryTheory V.
