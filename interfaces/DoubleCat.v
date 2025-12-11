Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import Coq.Program.Equality.

(** Enable primitive projections for better type inference with coercions *)
Set Primitive Projections.

(** * Double Categories *)

(** A pseudo-double category consists of:
    - Objects (0-cells)
    - Vertical 1-cells forming a category [V]
    - Horizontal 1-cells between objects
    - 2-cells filling squares of 1-cells
    - Horizontal composition of 1-cells and 2-cells, coherent up to isomorphism

    The interface is divided into:
    - [DoubleCategoryDefinition]: the data and axioms
    - [DoubleCategoryTheory]: derived definitions and sanity checks *)

(** ** Design notes *)

(** The approach that would exploit modules and module functors the best
    is a definition like that appearing in:

    Michael Shulman, Framed bicategories and monoidal fibrations,
      Theory Appl. Categ. 20 (2008), No. 18, 650-738. MR 2534210

    That is, we would require the user to provide:
    - a category of vertical 1-cells [C_0]
    - a category of horizontal 1-cells [C_1]
    - functors satisfying some laws:
      - [Src : C_1 -> C_0]
      - [Tgt : C_1 -> C_0]
      - [Id  : C_0 -> C_1]
    - a functor [HComp : C_1 ×_{C_0} C_1 -> C_1] satisfying coherence laws

    While this definition is possible, taking the pullback of categories
    necessarily introduces dependent types (see its definition in Pullbacks.v).
    Unfortunately, these dependent types get quite complex to handle once
    one has to prove [HComp] is a functor (or even to define it!). It seems
    unlikely such a design would lead to a usable infrastructure for the
    end-user of the library.

    We opt for a more intensional design, which unfortunately re-uses less of
    the existing interfaces. Instead of requiring the user to provide
    category and functor modules as described before, and then adding some
    definitions and axioms on top, we codify directly the axioms that these
    modules would enforce.

    This does mean we do not enjoy the fact that most of these laws are already
    codified in other interfaces if instantiated like above. However, it does
    mean we will be able to derive the corresponding modules from a
    pseudo-double category definition. *)


(** ** Cell data *)

(** The basic data of horizontal 1-cells and 2-cells, parameterized
    by a category [V] of vertical 1-cells. *)

Module Type DoubleCellData (V : CategoryDefinition).
  Import V.

  (** *** Horizontal 1-cells *)

  Parameter hcell : V.t -> V.t -> Type.

  Infix "-o->" := hcell (at level 90, right associativity) : type_scope.
  Infix "~~>" := V.m (at level 90, right associativity) : type_scope.

  (** *** 2-cells *)

  (** A 2-cell [A =[f,g]=> B] fills a square:
<<
            A
       sA --o--> tA
       |       |
     f |   α   | g
       |       |
       v       v
       sB --o--> tB
            B
>>
  *)

  Parameter tcell : forall {sA tA sB tB : V.t},
    (sA -o-> tA) -> (sB -o-> tB) ->
    (sA ~~> sB) -> (tA ~~> tB) -> Type.

  Notation "A =[ f , g ]=> B" := (tcell A B f g)
    (at level 70, f at next level, g at next level, no associativity).

  (** *** Vertical composition *)

  Parameter vid : forall {s t : V.t} (A : s -o-> t),
    A =[V.id s, V.id t]=> A.

  Parameter vcomp : forall {sA tA sB tB sC tC : V.t}
    {A : sA -o-> tA} {B : sB -o-> tB} {C : sC -o-> tC}
    {sf : sA ~~> sB} {tf : tA ~~> tB} {sg : sB ~~> sC} {tg : tB ~~> tC},
    A =[sf, tf]=> B -> B =[sg, tg]=> C ->
    A =[V.compose sg sf, V.compose tg tf]=> C.

  (** *** Horizontal composition *)

  Parameter hid : forall (a : V.t), a -o-> a.

  Parameter hid_mor : forall {a b} (f : a ~~> b),
    hid a =[f, f]=> hid b.

  Parameter hcomp : forall {a b c : V.t},
    (a -o-> b) -> (b -o-> c) -> (a -o-> c).

  Infix "⨀" := hcomp (at level 45, right associativity) : type_scope.

  (** *** Scopes and notations *)

  Declare Scope hom_scope.
  Delimit Scope hom_scope with hom.
  Bind Scope hom_scope with tcell.
  Open Scope hom_scope.

  Parameter hcomp_fmap : forall {a a' b b' c c' : V.t}
    {A : a -o-> b} {A' : a' -o-> b'} {B : b -o-> c} {B' : b' -o-> c'}
    {f : a ~~> a'} {g : b ~~> b'} {h : c ~~> c'},
    A =[f,g]=> A' -> B =[g,h]=> B' -> (A ⨀ B) =[f,h]=> (A' ⨀ B').

  Infix "⊙" := hcomp_fmap (at level 45, right associativity) : hom_scope.

End DoubleCellData.


(** ** Double cell notations *)

(** Notation functor that sets up standard notations for double category cells.
    Include this after providing DoubleCellData. *)

Module DoubleCellNotations (V : CategoryDefinition) (D : DoubleCellData V).
  Import D.

  Infix "-o->" := hcell (at level 90, right associativity) : type_scope.
  Infix "~~>" := V.m (at level 90, right associativity) : type_scope.

  Notation "A =[ f , g ]=> B" := (tcell A B f g)
    (at level 70, f at next level, g at next level, no associativity).

  Infix "⨀" := hcomp (at level 45, right associativity) : type_scope.

  Declare Scope hom_scope.
  Delimit Scope hom_scope with hom.
  Bind Scope hom_scope with tcell.
  Open Scope hom_scope.

  Infix "⊙" := hcomp_fmap (at level 45, right associativity) : hom_scope.
End DoubleCellNotations.


(** ** Derived definitions *)

(** Given cell data, derive the horizontal arrow packaging, category structure,
    and coercions. These are always the same and should not be redefined. *)

Module DoubleCellDerived (V : CategoryDefinition) (D : DoubleCellData V).
  Import D.
  Include (DoubleCellNotations V D).

  (** *** Objects: horizontal arrows *)

  (** A horizontal arrow [harr] packages a horizontal 1-cell together
      with its source and target objects. *)

  Record harr := mk_harrow {
    arr_src : V.t;
    arr_tgt : V.t;
    carrier :> hcell arr_src arr_tgt;
  }.

  Definition hcell_to_harr {s t : V.t} (hc: s -o-> t) : harr :=
    mk_harrow s t hc.
  Coercion hcell_to_harr : hcell >-> harr.

  (** The [src] and [tgt] projections give the frame of a horizontal arrow. *)

  Definition src {s t : V.t} (hc : s -o-> t) : V.t := s.
  Definition tgt {s t : V.t} (hc : s -o-> t) : V.t := t.

  (** *** Morphisms: 2-cells *)

  (** A morphism [harr_mor A B] packages a 2-cell together with its
      frame morphisms. *)

  Record harr_mor {A B : harr} := mk_harr_mor {
    src_mor : src A ~~> src B;
    tgt_mor : tgt A ~~> tgt B;
    carrier_mor :> A =[src_mor,tgt_mor]=> B;
  }.
  Arguments harr_mor : clear implicits.

  Definition tcell_to_harr_mor {sA tA sB tB : V.t}
    {A : sA -o-> tA} {B : sB -o-> tB}
    {sf : sA ~~> sB} {tf : tA ~~> tB} (α : A =[sf,tf]=> B) : harr_mor A B :=
    mk_harr_mor A B sf tf α.
  Coercion tcell_to_harr_mor : tcell >-> harr_mor.

  Definition src_vmor {A B : harr} (α: harr_mor A B) : src A ~~> src B :=
    src_mor α.
  Definition tgt_vmor {A B : harr} (α : harr_mor A B) : tgt A ~~> tgt B :=
    tgt_mor α.

  (** *** Category structure *)

  Definition t := harr.
  Definition m := harr_mor.

  Definition id : forall A, m A A :=
    fun A => mk_harr_mor _ _ _ _ (vid A).

  Definition compose : forall {A B C}, m B C -> m A B -> m A C :=
    fun A B C g f => mk_harr_mor _ _ _ _ (vcomp f g).

  Notation "f ;; g" := (compose g f)
    (at level 50, left associativity) : hom_scope.

  (** *** Special cells and isocells *)

  (** A special cell is a 2-cell with vertical 1-cells. *)

  Definition scell {a b : V.t} (A B : a -o-> b) : Type :=
    A =[V.id a, V.id b]=> B.

  (** A special isocell is a special cell which is a isomorphism in [Vert] *)
  Module Siso.
    Record sisocell {a b : V.t} (A B : a -o-> b) := mk_sisocell {
      fw :> A =[V.id a, V.id b]=> B;
      bw : B =[V.id a, V.id b]=> A;
      bw_fw : bw ;; fw = id B;
      fw_bw : fw ;; bw = id A;
    }.
    Arguments mk_sisocell {a b A B}.
    Arguments sisocell {a b} A B.
    Arguments fw {a b A B}.
    Arguments bw {a b A B}.
    Arguments bw_fw {a b A B}.
    Arguments fw_bw {a b A B}.
  End Siso.

  Definition sisocell_to_scell {a b : V.t} {A B : a -o-> b}
    (s : Siso.sisocell A B) : scell A B := Siso.fw s.
  Coercion sisocell_to_scell : Siso.sisocell >-> scell.

End DoubleCellDerived.

(** ** Vertical category *)

(** The category [Vert] has horizontal 1-cells as objects and 2-cells
    as morphisms. Composition is vertical composition of 2-cells. *)

Module Type DoubleVerticalCatDefinition (V : CategoryDefinition) <: CategoryDefinition.
  Include (DoubleCellData V).
  Include (DoubleCellDerived V).

  (** *** Axioms *)

  Axiom compose_id_left :
    forall {A B} (f : m A B), compose (id B) f = f.

  Axiom compose_id_right :
    forall {A B} (f : m A B), compose f (id A) = f.

  Axiom compose_assoc :
    forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
      compose (compose h g) f = compose h (compose g f).

End DoubleVerticalCatDefinition.

(** ** Definition *)

Module Type DoubleCategoryDefinition (V : CategoryDefinition).
  Declare Module Vert : DoubleVerticalCatDefinition V.
  Include Vert.
  Import Siso.

  (** *** Functoriality of [hid] *)

  (** The operations [hid] and [hid_mor] form a functor [V -> Vert]. *)

  Axiom hid_fmap_id :
    forall A, Vert.hid_mor (V.id A) = Vert.id (Vert.hid A).

  Axiom hid_fmap_compose :
    forall {A B C} (g : V.m B C) (f : V.m A B),
      Vert.hid_mor (V.compose g f) = Vert.compose (Vert.hid_mor g) (Vert.hid_mor f).

  (** *** Functoriality of [hcomp] *)

  (** Horizontal composition [hcomp_fmap] preserves identities and composition. *)

  Parameter hcomp_fmap_id :
    forall {a b c : V.t} (A : a -o-> b) (B : b -o-> c),
      (Vert.vid A ⊙ Vert.vid B) = Vert.vid (A ⨀ B).

  Parameter hcomp_fmap_compose :
    forall {a a' a'' b b' b'' c c' c'' : V.t}
      {A : a -o-> b} {A' : a' -o-> b'} {A'' : a'' -o-> b''}
      {B : b -o-> c} {B' : b' -o-> c'} {B'' : b'' -o-> c''}
      {f : a ~~> a'} {f' : a' ~~> a''} {g : b ~~> b'} {g' : b' ~~> b''}
      {h : c ~~> c'} {h' : c' ~~> c''}
      (α : A =[f,g]=> A') (α' : A' =[f',g']=> A'')
      (β : B =[g,h]=> B') (β' : B' =[g',h']=> B''),
      (vcomp α α') ⊙ (vcomp β β') = vcomp (α ⊙ β) (α' ⊙ β').

  (** *** Structural isomorphisms *)

  (** Associator: [(A ⨀ B) ⨀ C ≅ A ⨀ (B ⨀ C)] *)
  Parameter assoc : forall {a b c d : V.t}
    (A : a -o-> b) (B : b -o-> c) (C : c -o-> d),
    sisocell ((A ⨀ B) ⨀ C) (A ⨀ (B ⨀ C)).

  (** Left unitor: [hid a ⨀ A ≅ A] *)
  Parameter lunit : forall {a b : V.t} (A : a -o-> b),
    sisocell (hid a ⨀ A) A.

  (** Right unitor: [A ⨀ hid b ≅ A] *)
  Parameter runit : forall {a b : V.t} (A : a -o-> b),
    sisocell (A ⨀ hid b) A.

  (** *** Naturality *)

  (** Naturality of [assoc]:
      [assoc ;; (α ⊙ (β ⊙ γ)) = ((α ⊙ β) ⊙ γ) ;; assoc] *)
  Axiom assoc_nat :
    forall {a a' b b' c c' d d' : V.t}
      {A : a -o-> b} {A' : a' -o-> b'}
      {B : b -o-> c} {B' : b' -o-> c'}
      {C : c -o-> d} {C' : c' -o-> d'}
      {f : V.m a a'} {g : V.m b b'} {h : V.m c c'} {k : V.m d d'}
      (α : A =[f,g]=> A') (β : B =[g,h]=> B') (γ : C =[h,k]=> C'),
      (assoc A B C) ;; (α ⊙ (β ⊙ γ)) = ((α ⊙ β) ⊙ γ) ;; (assoc A' B' C').

  (** Naturality of [lunit]:
      [lunit ;; α = (hid_mor f ⊙ α) ;; lunit] *)
  Axiom lunit_nat :
    forall {a a' b b' : V.t}
      {A : a -o-> b} {A' : a' -o-> b'}
      {f : V.m a a'} {g : V.m b b'}
      (α : A =[f,g]=> A'),
      (lunit A) ;; α = (hid_mor f ⊙ α) ;; (lunit A').

  (** Naturality of [runit]:
      [runit ;; α = (α ⊙ hid_mor g) ;; runit] *)
  Axiom runit_nat :
    forall {a a' b b' : V.t}
      {A : a -o-> b} {A' : a' -o-> b'}
      {f : V.m a a'} {g : V.m b b'}
      (α : A =[f,g]=> A'),
      (runit A) ;; α = (α ⊙ hid_mor g) ;; (runit A').

  (** *** Coherence *)

  (** Pentagon identity:
      [(assoc ⊙ vid) ;; assoc ;; (vid ⊙ assoc) = assoc ;; assoc] *)
  Axiom assoc_coh :
    forall {a b c d e : V.t}
      (A : a -o-> b) (B : b -o-> c) (C : c -o-> d) (D : d -o-> e),
      ((assoc A B C) ⊙ vid D) ;; (assoc A (B ⨀ C) D) ;; (vid A ⊙ (assoc B C D))
      = (assoc (A ⨀ B) C D) ;; (assoc A B (C ⨀ D)).

  (** Triangle identity:
      [runit ⊙ vid = assoc ;; (vid ⊙ lunit)] *)
  Axiom unit_coh :
    forall {a b c : V.t} (A : a -o-> b) (B : b -o-> c),
      ((runit A) ⊙ vid B : Vert.m _ _) =
      (assoc A (hid b) B) ;; (vid A ⊙ (lunit B)).

End DoubleCategoryDefinition.


(** ** Theory *)

(** Once the fields enumerated in [DoubleCategoryDefinition] have been
    defined, the user should include the following module, which provides
    derived definitions and sanity checks. *)

Module DoubleCategoryTheory (V : CategoryDefinition) (P : DoubleCategoryDefinition V).
  Import P.
  Import V.

  (** Include category theory for the base category [V]. *)
  Module VT := CategoryTheory V.

  (** *** Sanity checks *)

  (** We verify that our axioms imply [Src] and [Tgt] are functors,
      and that the expected functorial equalities hold. *)

  (** [Src] is a functor [Vert -> V]. *)
  Module Src <: FunctorDefinition Vert V.
    Import Vert.

    Definition omap : Vert.t -> V.t :=
      fun A => Vert.src A.

    Definition fmap : forall {A B}, Vert.m A B -> V.m (omap A) (omap B) :=
      fun A B α => src_vmor α.

    Proposition fmap_id :
      forall A, fmap (Vert.id A) = V.id (omap A).
    Proof. reflexivity. Qed.

    Proposition fmap_compose :
      forall {A B C} (g : Vert.m B C) (f : Vert.m A B),
        fmap (f ;; g) = V.compose (fmap g) (fmap f).
    Proof. reflexivity. Qed.
  End Src.

  (** [Tgt] is a functor [Vert -> V]. *)
  Module Tgt <: FunctorDefinition Vert V.
    Import Vert.

    Definition omap : Vert.t -> V.t :=
      fun A => Vert.tgt A.

    Definition fmap : forall {A B}, Vert.m A B -> V.m (omap A) (omap B) :=
      fun A B α => tgt_vmor α.

    Proposition fmap_id :
      forall A, fmap (Vert.id A) = V.id (omap A).
    Proof. reflexivity. Qed.

    Proposition fmap_compose :
      forall {A B C} (g : Vert.m B C) (f : Vert.m A B),
        fmap (f ;; g) = V.compose (fmap g) (fmap f).
    Proof. reflexivity. Qed.
  End Tgt.

  (** [Src] and [Tgt] commute with [HId]. *)
  Module SrcTgtChecks.
    Import Vert.

    Proposition hid_src :
      forall {a : V.t}, Src.omap (Vert.hid a) = a.
    Proof. reflexivity. Qed.

    Proposition hid_mor_src :
      forall {a b : V.t} (f : V.m a b),
        Src.fmap (Vert.hid_mor f) = f.
    Proof. reflexivity. Qed.

    Proposition hid_tgt :
      forall {a : V.t}, Tgt.omap (Vert.hid a) = a.
    Proof. reflexivity. Qed.

    Proposition hid_mor_tgt :
      forall {a b : V.t} (f : V.m a b),
        Tgt.fmap (Vert.hid_mor f) = f.
    Proof. reflexivity. Qed.

    (** [Src] and [Tgt] interact with [HComp] as expected. *)

    Proposition hcomp_src :
      forall {a b c : V.t} {B : b -o-> c} {A : a -o-> b},
        Src.omap (A ⨀ B) = Src.omap A.
    Proof. reflexivity. Qed.

    Proposition hcomp_fmap_src :
      forall {a b c a' b' c' : V.t}
        {A : a -o-> b} {B : b -o-> c} {A' : a' -o-> b'} {B' : b' -o-> c'}
        {f : V.m a a'} {g : V.m b b'} {h : V.m c c'}
        (α : A =[f,g]=> A') (β : B =[g,h]=> B'),
        Src.fmap (hcomp_fmap α β) = Src.fmap α.
    Proof. reflexivity. Qed.

    Proposition hcomp_tgt :
      forall {a b c : V.t} {B : b -o-> c} {A : a -o-> b},
        Tgt.omap (A ⨀ B) = Tgt.omap B.
    Proof. intros. unfold tgt. reflexivity. Qed.

    Proposition hcomp_fmap_tgt :
      forall {a b c a' b' c' : V.t}
        {A : a -o-> b} {B : b -o-> c} {A' : a' -o-> b'} {B' : b' -o-> c'}
        {f : V.m a a'} {g : V.m b b'} {h : V.m c c'}
        (α : A =[f,g]=> A') (β : B =[g,h]=> B'),
        Tgt.fmap (hcomp_fmap α β) = Tgt.fmap β.
    Proof. reflexivity. Qed.

    (** The structural isomorphisms have identity frame morphisms. *)

    Import Siso.

    Proposition assoc_src_id :
      forall {a b c d : V.t} {A : a -o-> b} {B : b -o-> c} {C : c -o-> d},
        Src.fmap (assoc A B C) = V.id _.
    Proof. reflexivity. Qed.

    Proposition assoc_tgt_id :
      forall {a b c d : V.t} {A : a -o-> b} {B : b -o-> c} {C : c -o-> d},
        Tgt.fmap (assoc A B C) = V.id _.
    Proof. reflexivity. Qed.

    Proposition lunit_src_id :
      forall {a b : V.t} {A : a -o-> b},
        Src.fmap (lunit A) = V.id _.
    Proof. reflexivity. Qed.

    Proposition lunit_tgt_id :
      forall {a b : V.t} {A : a -o-> b},
        Tgt.fmap (lunit A) = V.id _.
    Proof. reflexivity. Qed.

    Proposition runit_src_id :
      forall {a b : V.t} {A : a -o-> b},
        Src.fmap (runit A) = V.id _.
    Proof. reflexivity. Qed.

    Proposition runit_tgt_id :
      forall {a b : V.t} {A : a -o-> b},
        Tgt.fmap (runit A) = V.id _.
    Proof. reflexivity. Qed.
  End SrcTgtChecks.

  (** *** Cell types *)

  (** A globular cell is a 2-cell between horizontal identities. *)

  Definition gcell {a b : V.t} (f : V.m a b) (g : V.m a b) : Type :=
    hid a =[f, g]=> hid b.

  (** *** Isomorphisms *)

  (** *** Sisocell manipulation *)

  (** Extended [Siso] module with manipulation lemmas. *)
  Module Siso'.
    Import Vert.
    Import Siso.

    (** Post-composing with an iso is injective. *)
    Lemma compose_fw_r_eq {a b : V.t} {A B : a -o-> b}
      (f : sisocell A B) {C : Vert.t} (x y : Vert.m C A) :
      x ;; fw f = y ;; fw f <-> x = y.
    Proof.
      split; intro H; try congruence.
      assert (E : (x ;; fw f) ;; bw f = (y ;; fw f) ;; bw f)
        by (rewrite H; auto).
      rewrite <- !Vert.compose_assoc, fw_bw, !Vert.compose_id_left in E. exact E.
    Qed.

    Lemma compose_bw_r_eq {a b : V.t} {A B : a -o-> b}
      (f : sisocell A B) {C : Vert.t} (x y : Vert.m C B) :
      x ;; bw f = y ;; bw f <-> x = y.
    Proof.
      split; intro H; try congruence.
      assert (E : (x ;; bw f) ;; fw f = (y ;; bw f) ;; fw f)
        by (rewrite H; auto).
      rewrite <- !Vert.compose_assoc, bw_fw, !Vert.compose_id_left in E. exact E.
    Qed.

    (** Pre-composing with an iso is injective. *)
    Lemma compose_fw_l_eq {a b : V.t} {A B : a -o-> b}
      (f : sisocell A B) {C : Vert.t} (x y : Vert.m B C) :
      fw f ;; x = fw f ;; y <-> x = y.
    Proof.
      split; intro H; try congruence.
      assert (E : bw f ;; (fw f ;; x) = bw f ;; (fw f ;; y)) by (rewrite H; auto).
      rewrite !Vert.compose_assoc, bw_fw, !Vert.compose_id_right in E. exact E.
    Qed.

    Lemma compose_bw_l_eq {a b : V.t} {A B : a -o-> b}
      (f : sisocell A B) {C : Vert.t} (x y : Vert.m A C) :
      bw f ;; x = bw f ;; y <-> x = y.
    Proof.
      split; intro H; try congruence.
      assert (E : fw f ;; (bw f ;; x) = fw f ;; (bw f ;; y)) by (rewrite H; auto).
      rewrite !Vert.compose_assoc, fw_bw, !Vert.compose_id_right in E. exact E.
    Qed.

    (** Moving isos across equations. *)
    Lemma eq_fw_bw_r {a b : V.t} {A B : a -o-> b}
      (f : sisocell A B) {C : Vert.t} (x : Vert.m C A) y :
      x ;; fw f = y <-> x = y ;; bw f.
    Proof.
      split; intro H.
      - rewrite <- H, <- Vert.compose_assoc, fw_bw, Vert.compose_id_left. auto.
      - rewrite H, <- Vert.compose_assoc, bw_fw, Vert.compose_id_left. auto.
    Qed.

    Lemma eq_bw_fw_r {a b : V.t} {A B : a -o-> b}
      (f : sisocell A B) {C : Vert.t} (x : Vert.m C B) y :
      x ;; bw f = y <-> x = y ;; fw f.
    Proof.
      split; intro H.
      - rewrite <- H, <- Vert.compose_assoc, bw_fw, Vert.compose_id_left. auto.
      - rewrite H, <- Vert.compose_assoc, fw_bw, Vert.compose_id_left. auto.
    Qed.

    Lemma eq_fw_bw_l {a b : V.t} {A B : a -o-> b}
      (f : sisocell A B) {C : Vert.t} (x : Vert.m B C) y :
      fw f ;; x = y <-> x = bw f ;; y.
    Proof.
      split; intro H.
      - rewrite <- H, Vert.compose_assoc, bw_fw, Vert.compose_id_right. auto.
      - rewrite H, Vert.compose_assoc, fw_bw, Vert.compose_id_right. auto.
    Qed.

    Lemma eq_bw_fw_l {a b : V.t} {A B : a -o-> b}
      (f : sisocell A B) {C : Vert.t} (x : Vert.m A C) y :
      bw f ;; x = y <-> x = fw f ;; y.
    Proof.
      split; intro H.
      - rewrite <- H, Vert.compose_assoc, fw_bw, Vert.compose_id_right. auto.
      - rewrite H, Vert.compose_assoc, bw_fw, Vert.compose_id_right. auto.
    Qed.
  End Siso'.

  (** A general vertical isocell has explicit (possibly non-identity)
      frame morphisms. *)

  Import Siso.

  Module Viso.
    Record visocell {sA tA sB tB : V.t}
      {sf : V.m sA sB} {tf : V.m tA tB}
      {sb : V.m sB sA} {tb : V.m tB tA}
      (A : sA -o-> tA) (B : sB -o-> tB) := mk_visocell {
      fw :> A =[sf, tf]=> B;
      bw : B =[sb, tb]=> A;
      bw_fw : bw ;; fw = Vert.id B;
      fw_bw : fw ;; bw = Vert.id A;
    }.
    Arguments visocell {sA tA sB tB sf tf sb tb} A B.
    Arguments mk_visocell {sA tA sB tB sf tf sb tb A B}.
    Arguments fw {sA tA sB tB sf tf sb tb A B}.
    Arguments bw {sA tA sB tB sf tf sb tb A B}.
    Arguments bw_fw {sA tA sB tB sf tf sb tb A B}.
    Arguments fw_bw {sA tA sB tB sf tf sb tb A B}.

    (** Post-composing with an iso is injective. *)
    Lemma compose_fw_r_eq {sA tA sB tB : V.t}
      {sf : V.m sA sB} {tf : V.m tA tB} {sb : V.m sB sA} {tb : V.m tB tA}
      {A : sA -o-> tA} {B : sB -o-> tB}
      (f : @visocell sA tA sB tB sf tf sb tb A B) {C : Vert.t} (x y : Vert.m C A) :
      x ;; fw f = y ;; fw f <-> x = y.
    Proof.
      split; intro H; try congruence.
      assert (E : (x ;; fw f) ;; bw f = (y ;; fw f) ;; bw f)
        by (rewrite H; auto).
      rewrite <- !Vert.compose_assoc, fw_bw, !Vert.compose_id_left in E. exact E.
    Qed.

    Lemma compose_bw_r_eq {sA tA sB tB : V.t}
      {sf : V.m sA sB} {tf : V.m tA tB} {sb : V.m sB sA} {tb : V.m tB tA}
      {A : sA -o-> tA} {B : sB -o-> tB}
      (f : @visocell sA tA sB tB sf tf sb tb A B) {C : Vert.t} (x y : Vert.m C B) :
      x ;; bw f = y ;; bw f <-> x = y.
    Proof.
      split; intro H; try congruence.
      assert (E : (x ;; bw f) ;; fw f = (y ;; bw f) ;; fw f)
        by (rewrite H; auto).
      rewrite <- !Vert.compose_assoc, bw_fw, !Vert.compose_id_left in E. exact E.
    Qed.

    (** Pre-composing with an iso is injective. *)
    Lemma compose_fw_l_eq {sA tA sB tB : V.t}
      {sf : V.m sA sB} {tf : V.m tA tB} {sb : V.m sB sA} {tb : V.m tB tA}
      {A : sA -o-> tA} {B : sB -o-> tB}
      (f : @visocell sA tA sB tB sf tf sb tb A B) {C : Vert.t} (x y : Vert.m B C) :
      fw f ;; x = fw f ;; y <-> x = y.
    Proof.
      split; intro H; try congruence.
      assert (E : bw f ;; (fw f ;; x) = bw f ;; (fw f ;; y)) by (rewrite H; auto).
      rewrite !Vert.compose_assoc, bw_fw, !Vert.compose_id_right in E. exact E.
    Qed.

    Lemma compose_bw_l_eq {sA tA sB tB : V.t}
      {sf : V.m sA sB} {tf : V.m tA tB} {sb : V.m sB sA} {tb : V.m tB tA}
      {A : sA -o-> tA} {B : sB -o-> tB}
      (f : @visocell sA tA sB tB sf tf sb tb A B) {C : Vert.t} (x y : Vert.m A C) :
      bw f ;; x = bw f ;; y <-> x = y.
    Proof.
      split; intro H; try congruence.
      assert (E : fw f ;; (bw f ;; x) = fw f ;; (bw f ;; y)) by (rewrite H; auto).
      rewrite !Vert.compose_assoc, fw_bw, !Vert.compose_id_right in E. exact E.
    Qed.

    (** Moving isos across equations. *)
    Lemma eq_fw_bw_r {sA tA sB tB : V.t}
      {sf : V.m sA sB} {tf : V.m tA tB} {sb : V.m sB sA} {tb : V.m tB tA}
      {A : sA -o-> tA} {B : sB -o-> tB}
      (f : @visocell sA tA sB tB sf tf sb tb A B) {C : Vert.t} (x : Vert.m C A) y :
      x ;; fw f = y <-> x = y ;; bw f.
    Proof.
      split; intro H.
      - rewrite <- H, <- Vert.compose_assoc, fw_bw, Vert.compose_id_left. auto.
      - rewrite H, <- Vert.compose_assoc, bw_fw, Vert.compose_id_left. auto.
    Qed.

    Lemma eq_fw_bw_l {sA tA sB tB : V.t}
      {sf : V.m sA sB} {tf : V.m tA tB} {sb : V.m sB sA} {tb : V.m tB tA}
      {A : sA -o-> tA} {B : sB -o-> tB}
      (f : @visocell sA tA sB tB sf tf sb tb A B) {C : Vert.t} (x : Vert.m B C) y :
      fw f ;; x = y <-> x = bw f ;; y.
    Proof.
      split; intro H.
      - rewrite <- H, Vert.compose_assoc, bw_fw, Vert.compose_id_right. auto.
      - rewrite H, Vert.compose_assoc, fw_bw, Vert.compose_id_right. auto.
    Qed.
  End Viso.

  Definition sisocell_to_visocell {a b : V.t} {A B : a -o-> b}
    (s : sisocell A B) :
    @Viso.visocell a b a b (V.id a) (V.id b) (V.id a) (V.id b) A B :=
    match s with
    | mk_sisocell f b bf fb => Viso.mk_visocell f b bf fb
    end.
  Coercion sisocell_to_visocell : sisocell >-> Viso.visocell.

  (** A horizontal equivalence between objects [a] and [b] consists of
      horizontal arrows [M : a -o-> b] and [N : b -o-> a] with special
      isocells [M ⨀ N ≅ hid a] and [N ⨀ M ≅ hid b]. *)

  Module Hiso.
    Record hiso (a b : V.t) := mk_hiso {
      fw :> a -o-> b;
      bw : b -o-> a;
      fw_bw : sisocell (fw ⨀ bw) (hid a);
      bw_fw : sisocell (bw ⨀ fw) (hid b);
    }.
    Arguments mk_hiso {a b}.
    Arguments fw {a b}.
    Arguments bw {a b}.
    Arguments fw_bw {a b}.
    Arguments bw_fw {a b}.
  End Hiso.

  (** *** Derived Equations *)

  Proposition vid_hid {a : V.t} :
    vid (hid a) = hid_mor (V.id a).
  Proof.
    rewrite <- (hid_fmap_id a) at 1. reflexivity.
  Qed.

  Lemma tcell_to_harr_mor_inj {sA tA sB tB : V.t}
    {A : sA -o-> tA} {B : sB -o-> tB}
    {sf : sA ~~> sB} {tf : tA ~~> tB}
    (α β : A =[sf,tf]=> B) :
    (α : harr_mor A B) = (β : harr_mor A B) -> α = β.
  Proof.
    intro H. dependent destruction H. reflexivity.
  Qed.

  Proposition runit_hcomp_hid_runit {a : V.t} :
    runit (hid a) ⊙ (vid (hid a)) = runit (hid a ⨀ hid a).
  Proof.
    apply tcell_to_harr_mor_inj.
    pose (H := runit_nat (runit (hid a))).
    rewrite (Siso'.eq_fw_bw_r (runit (hid a))) in H at 1.
    rewrite <- Vert.compose_assoc in H.
    rewrite (fw_bw (runit (hid a))) in H at 1.
    rewrite Vert.compose_id_left in H.
    rewrite <- vid_hid in H. symmetry.
    exact H.
  Qed.

  Proposition hid_hcomp_lunit_lunit {a : V.t} :
    (vid (hid a)) ⊙ lunit (hid a) = lunit (hid a ⨀ hid a).
  Proof.
    apply tcell_to_harr_mor_inj.
    pose (H := lunit_nat (lunit (hid a))).
    rewrite (Siso'.eq_fw_bw_r (lunit (hid a))) in H at 1.
    rewrite <- Vert.compose_assoc in H.
    rewrite (fw_bw (lunit (hid a))) in H at 1.
    rewrite Vert.compose_id_left in H.
    rewrite <- vid_hid in H. symmetry.
    exact H.
  Qed.

  (** The left and right unitors agree on the horizontal identity.
      This is a standard coherence result for monoidal categories:
      λ_I = ρ_I where I is the unit object.

      The proof follows the strategy from nLab:
      https://ncatlab.org/nlab/show/monoidal+category#other_coherence_conditions

      Key steps:
      1. _ ⊙ vid I is faithful (since _ ⨀ hid is an equivalence via runit)
      2. From triangle (unit_coh): ρ_I ⊙ id_I = α ∘ (id_I ⊙ λ_I)
      3. From naturality: ρ_I ⊙ id_I = ρ_{I⊗I} and id_I ⊙ λ_I = λ_{I⊗I}
      4. The "dual triangle" λ_I ⊙ id_I = α ∘ (id_I ⊙ λ_I) follows from coherence
      5. Hence λ_I ⊙ id_I = ρ_I ⊙ id_I, so λ_I = ρ_I by faithfulness *)
  Proposition lunit_hid_runit_hid {a : V.t} :
    lunit (hid a) = runit (hid a).
  Proof.
  Admitted.

End DoubleCategoryTheory.

(** ** Overall interface *)

Module Type DoubleCategory (V : CategoryDefinition) :=
  DoubleCategoryDefinition V <+ DoubleCategoryTheory V.
