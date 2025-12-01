Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.Pullbacks.

(* TODOS:
  - Coherence axioms for hcomp
  - fix notation to make sure @ and ~~> are for V not Vert

*)

(** Pseudo-double category interface *)

(** The module type PseudoDoubleCategory defines the axioms and derived theory
  common to all pseud-double categories *)
(**
  There are some critical design choices here.

  The approach that would exploit modules and module functors the best
  is a definition like that appearing in:

  Michael Shulman, Framed bicategories and monoidal fibrations,
    Theory Appl. Categ. 20 (2008), No. 18, 650–738. MR 2534210

  That is, we would require the user to provide:
  - a category of vertical 1-cells C_0
  - a category of horizontal 1-cells C_1
  - functors:
    + Src : C_1 -> C_0
    + Tgt : C_1 -> C_0
    + Id  : C_0 -> C_1
  - As well as a functor HComp : C_1 x_{C_0} C_1 -> C_1 satisfying
    some coherence laws

  While this definition is possible, taking the pullback of categories
    necessarily introduces dependent types (see its definition in Pullbacks.v).
  Unfortunately, these dependent types get quite complex to handle once
    one has to prove HComp is a functor (or even to define it!). It seems
    unlikely such a design would lead to a usable infrastructure for the
    end-user of the library.

  We opt for a more intensional design, which unfortunately re-uses less of
    the existing interfaces. Instead of requiring the user to provide
    category and functor modules as described before, and then adding some
    definitions and axioms on top, we codify directly the axioms that these
    modules would enforce.

  This does mean we do not enjoy of the fact that most of these laws are already
    codified in other interfaces if instantiated like above. However, it does
    mean we will be able to derive the corresponding modules from a
    pseudo-double category definition.
*)

Module Type DblCellData (V : CategoryDefinition).
  Import V.

  (** *** Horizontal 1-cells *)
  Parameter hcell : V.t -> V.t -> Type.
  Infix "-o->" := hcell (at level 90, right associativity) : type_scope.
  Infix "~~>" := V.m (at level 90, right associativity) : type_scope.

  (** *** 2-cells *)
  (** TODO: add diagram *)
  Parameter tcell : forall {sA tA sB tB : V.t},
    (sA -o-> tA) -> (sB -o-> tB) ->
    (sA ~~> sB) -> (tA ~~> tB) -> Type.
  Notation "A =[ f , g ]=> B" := (tcell A B f g)
    (at level 70, f at next level, g at next level, no associativity).

  (** *** Vertical composition of 2-cells *)
  Parameter vid : forall {s t : V.t}, forall (A : s -o-> t),
    A =[V.id s, V.id t]=> A.
  Parameter vcomp : forall {sA tA sB tB sC tC : V.t},
    forall {A : sA -o-> tA} {B : sB -o-> tB} {C : sC -o-> tC},
    forall {sf : sA ~~> sB} {tf : tA ~~> tB} {sg : sB ~~> sC} {tg : tB ~~> tC},
      A =[sf, tf]=> B -> B =[sg, tg]=> C ->
        A =[V.compose sg sf, V.compose tg tf]=> C.

  (** *** Horizontal composition of 2-cells *)
  Parameter hid : forall (a : V.t), a -o-> a.
  Parameter hid_mor : forall {a b}, forall (f : a ~~> b),
    hid a =[f, f]=> hid b.

  Parameter hcomp :
    forall {a b c : V.t},
      (a -o-> b) -> (b -o-> c) -> (a -o-> c).
  Infix "⨀" := hcomp (at level 45, right associativity) : type_scope.

  Declare Scope hom_scope.
  Delimit Scope hom_scope with hom.
  Bind Scope hom_scope with tcell.
  Open Scope hom_scope.

  Parameter hcomp_fmap :
    forall {a a' b b' c c' : V.t},
      forall {A : a -o-> b} {A' : a' -o-> b'} {B : b -o-> c} {B' : b' -o-> c'}
        {f : a ~~> a'} {g : b ~~> b'} {h : c ~~> c'},
          A =[f,g]=> A' -> B =[g,h]=> B' -> (A ⨀ B) =[f,h]=> (A' ⨀ B').
  Infix "⊙" := hcomp_fmap (at level 45, right associativity) : hom_scope.

End DblCellData.

Module Type DblVerticalCatDefinition (V : CategoryDefinition) <: CategoryDefinition.
  Include (DblCellData V).

  (** A horizontal cell [hc : src -o-> tgt]
    define the objects of the category of horizontal 1-cells
    by internalizing [src] and [tgt] *)
  Record harr :=
    mk_harrow {
      arr_src : V.t;
      arr_tgt : V.t;
      carrier :> hcell arr_src arr_tgt;
    }.
  (** Note that horizontal arrows are defined so they coerce to the underlying
    horizontal cell *)
  (** We also define a reverse coercion *)
  Definition hcell_to_harr {s t : V.t} (hc: s -o-> t) : harr :=
    mk_harrow s t hc.
  Coercion hcell_to_harr : hcell >-> harr.

  (** The definition of [hcell] induces the underlying
    left frame [src] and right frame [tgt] functor object maps *)
  Definition src {s t : V.t} (hc : s -o-> t) : V.t := s.
  Definition tgt {s t : V.t} (hc : s -o-> t) : V.t := t.

  (** 2-cells define arrows between horizontal arrows *)
  Record harr_mor {A B : harr} :=
    mk_harr_mor {
      src_mor : src A ~~> src B;
      tgt_mor : tgt A ~~> tgt B;
      carrier_mor :>  A =[src_mor,tgt_mor]=> B;
    }.
  Arguments harr_mor : clear implicits.
  (** and we define compatible coercions for horizontal arrow morphisms *)
  Definition tcell_to_harr_mor {sA tA sB tB : V.t}
    {A : sA -o-> tA} {B : sB -o-> tB}
    {sf : sA ~~> sB} {tf : tA ~~> tB} (tc : A =[sf,tf]=> B) : harr_mor A B :=
      mk_harr_mor A B sf tf tc.
  Coercion tcell_to_harr_mor : tcell >-> harr_mor.
  (** Similarly, [tcell] induces underlying left frame [src_vmor] and
    right frame [tgt_vmor] morphisms *)
  Definition src_vmor {A B : harr} (tc: harr_mor A B) : src A ~~> src B
    := src_mor tc.
  Definition tgt_vmor {A B : harr} (tc : harr_mor A B) : tgt A ~~> tgt B
    := tgt_mor tc.

  Definition t := harr.
  Definition m := harr_mor.

  Definition id : forall A, m A A :=
    fun A => mk_harr_mor _ _ _ _ (vid A).
  Definition compose : forall {A B C}, m B C -> m A B -> m A C :=
    fun A B C => fun g f => mk_harr_mor _ _ _ _ (vcomp f g).

  Axiom compose_id_left : forall {A B} (f : m A B), compose (id B) f = f.
  Axiom compose_id_right : forall {A B} (f : m A B), compose f (id A) = f.
  Axiom compose_assoc : forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
    compose (compose h g) f = compose h (compose g f).
End DblVerticalCatDefinition.

Module Type DblIdFunctorDef (V : CategoryDefinition)
  (H : DblVerticalCatDefinition V) <: FunctorDefinition V H.
  Import H.

  Definition omap : V.t -> H.t :=
    fun a => hid a.
  Definition fmap : forall {A B}, V.m A B -> H.m (omap A) (omap B) :=
    fun A B => fun f => hid_mor f.

  Axiom fmap_id :
    forall A, fmap (V.id A) = H.id (omap A).

  Axiom fmap_compose :
    forall {A B C} (g : V.m B C) (f : V.m A B),
      fmap (V.compose g f) = H.compose (fmap g) (fmap f).
End DblIdFunctorDef.

(** ** Double Category Full Definition *)
Module Type DblCategoryDefinition (V : CategoryDefinition).

  Declare Module Vert : DblVerticalCatDefinition V.
  Import Vert.

  Declare Module HId : DblIdFunctorDef V Vert.

  Module VertTheory := CategoryTheory Vert.

  Parameter hcomp_fmap_id :
    forall {a b c : V.t}, forall (A : a -o-> b) (B : b -o-> c),
      (Vert.vid A ⊙ Vert.vid B) = Vert.vid (A ⨀ B).
  Parameter hcomp_fmap_compose :
    forall {a a' a'' b b' b'' c c' c'' : V.t},
      forall {A : a -o-> b} {A' : a' -o-> b'} {A'' : a'' -o-> b''}
        {B : b -o-> c}  {B' : b' -o-> c'} {B'' : b'' -o-> c''}
        {f : a ~~> a'} {f' : a' ~~> a''} {g : b ~~> b'} {g' : b' ~~> b''}
        {h : c ~~> c'} {h' : c' ~~> c''},
      forall (tcA : A =[f,g]=> A') (tcA' : A' =[f',g']=> A'')
        (tcB : B =[g,h]=> B')  (tcB' : B' =[g',h']=> B''),
        (vcomp tcA tcA') ⊙ (vcomp tcB tcB') = vcomp (tcA ⊙ tcB) (tcA' ⊙ tcB').

  (** *** Structural isomorphisms *)

  (** The structural isomorphisms are vertical isos (2-cells with identity frame
      morphisms). This ensures they can be whiskered using hcomp_fmap. *)

  (** Vertical (globular) isomorphism: isomorphism between horizontal 1-cells
      with the same frame endpoints. The frame morphisms are constrained to be
      identities in the type itself. *)
  Record viso {a b : V.t} (A B : a -o-> b) := {
    fw :> A =[V.id a, V.id b]=> B;
    bw :> B =[V.id a, V.id b]=> A;
    bw_fw : Vert.compose bw fw = Vert.id A;
    fw_bw : Vert.compose fw bw = Vert.id B;
  }.
  Arguments viso {a b} A B.
  Arguments fw {a b A B}.
  Arguments bw {a b A B}.
  Arguments bw_fw {a b A B}.
  Arguments fw_bw {a b A B}.

  (** Associator: (A ⨀ B) ⨀ C ≅ A ⨀ (B ⨀ C) *)
  Parameter assoc : forall {a b c d : V.t}
    (A : a -o-> b) (B : b -o-> c) (C : c -o-> d),
    viso ((A ⨀ B) ⨀ C) (A ⨀ (B ⨀ C)).

  (** Left unitor: hid a ⨀ A ≅ A *)
  Parameter lunit : forall {a b : V.t} (A : a -o-> b),
    viso (hid a ⨀ A) A.

  (** Right unitor: A ⨀ hid b ≅ A *)
  Parameter runit : forall {a b : V.t} (A : a -o-> b),
    viso (A ⨀ hid b) A.

  (** *** Naturality properties *)
  (** Stated at harr_mor level to handle frame morphism composition *)

  (** Naturality of associator:
      assoc ; (α ⊙ (β ⊙ γ)) = ((α ⊙ β) ⊙ γ) ; assoc *)
  Axiom assoc_nat :
    forall {a a' b b' c c' d d' : V.t}
      {A : a -o-> b} {A' : a' -o-> b'}
      {B : b -o-> c} {B' : b' -o-> c'}
      {C : c -o-> d} {C' : c' -o-> d'}
      {f : V.m a a'} {g : V.m b b'} {h : V.m c c'} {k : V.m d d'}
      (α : A =[f,g]=> A') (β : B =[g,h]=> B') (γ : C =[h,k]=> C'),
      Vert.compose (α ⊙ (β ⊙ γ)) (assoc A B C) =
      Vert.compose (assoc A' B' C') ((α ⊙ β) ⊙ γ).

  (** Naturality of left unitor:
      lunit ; α = (hid_mor ⊙ α) ; lunit *)
  Axiom lunit_nat :
    forall {a a' b b' : V.t}
      {A : a -o-> b} {A' : a' -o-> b'}
      {f : V.m a a'} {g : V.m b b'}
      (α : A =[f,g]=> A'),
      Vert.compose α (lunit A) =
      Vert.compose (lunit A') (hid_mor f ⊙ α).

  (** Naturality of right unitor:
      runit ; α = (α ⊙ hid_mor) ; runit *)
  Axiom runit_nat :
    forall {a a' b b' : V.t}
      {A : a -o-> b} {A' : a' -o-> b'}
      {f : V.m a a'} {g : V.m b b'}
      (α : A =[f,g]=> A'),
      Vert.compose α (runit A) =
      Vert.compose (runit A') (α ⊙ hid_mor g).

  (** *** Pentagon identity *)
  (** (α_{A,B,C} ⊙ id_D) ; α_{A,B⊙C,D} ; (id_A ⊙ α_{B,C,D})
      = α_{A⊙B,C,D} ; α_{A,B,C⊙D} *)

  Axiom assoc_coh :
    forall {a b c d e : V.t}
      (A : a -o-> b) (B : b -o-> c) (C : c -o-> d) (D : d -o-> e),
      Vert.compose
        (Vert.compose
          (vid A ⊙ (assoc B C D))
          ((assoc A (B ⨀ C) D)))
        (fw (assoc A B C) ⊙ vid D)
      =
      Vert.compose
        (fw (assoc A B (C ⨀ D)))
        (fw (assoc (A ⨀ B) C D)).

  (** *** Triangle identity *)
  (** ρ_A ⊙ id_B = (id_A ⊙ λ_B) ∘ α_{A,I,B} *)

  Axiom unit_coh :
    forall {a b c : V.t}
      (A : a -o-> b) (B : b -o-> c),
      (fw (runit A) ⊙ vid B : Vert.m _ _) =
      Vert.compose (vid A ⊙ fw (lunit B)) (fw (assoc A (hid b) B)).

End DblCategoryDefinition.

Module DblCategoryTheory (V : CategoryDefinition) (P : DblCategoryDefinition V).
  Import P.
  Import P.Vert.

  (** Before developing the theory of double categories we make several
    sanity checks *)

  (** [src], [src_mor] defines a functor on the vertical category *)
  Module Src <: FunctorDefinition P.Vert V.
    Import P.Vert.

    Definition omap : P.Vert.t -> V.t :=
      fun hc => P.Vert.src hc.
    Definition fmap : forall {A B}, P.Vert.m A B -> V.m (omap A) (omap B) :=
      fun A B => fun hc_mor => src_vmor hc_mor.

    Proposition fmap_id :
      forall A, fmap (P.Vert.id A) = V.id (omap A).
    Proof.
      reflexivity.
    Qed.

    Proposition fmap_compose :
      forall {A B C} (g : P.Vert.m B C) (f : P.Vert.m A B),
        fmap (P.Vert.compose g f) = V.compose (fmap g) (fmap f).
    Proof.
      reflexivity.
    Qed.
  End Src.

  (** [tgt], [tgt_mor] defines a functor on the vertical category *)
  Module Tgt <: FunctorDefinition P.Vert V.
    Import P.Vert.

    Definition omap : P.Vert.t -> V.t :=
      fun hc => P.Vert.tgt hc.
    Definition fmap : forall {A B}, P.Vert.m A B -> V.m (omap A) (omap B) :=
      fun A B => fun hc_mor => tgt_vmor hc_mor.

    Proposition fmap_id :
      forall A, fmap (P.Vert.id A) = V.id (omap A).
    Proof.
      reflexivity.
    Qed.

    Proposition fmap_compose :
      forall {A B C} (g : P.Vert.m B C) (f : P.Vert.m A B),
        fmap (P.Vert.compose g f) = V.compose (fmap g) (fmap f).
    Proof.
      reflexivity.
    Qed.
  End Tgt.

  (** Src ∘ HId = Id *)
  Proposition hid_src :
    forall {a : V.t}, Src.omap (HId.omap a) = a.
  Proof.
    reflexivity.
  Qed.

  Proposition hid_mor_src : forall {a b : V.t}, forall (f : V.m a b),
    Src.fmap (HId.fmap f) = f.
  Proof.
    reflexivity.
  Qed.

  (** Tgt ∘ HId = Id *)
  Proposition hid_tgt :
    forall {a : V.t}, Tgt.omap (HId.omap a) = a.
  Proof.
    reflexivity.
  Qed.

  Proposition hid_mor_tgt : forall {a b : V.t}, forall (f : V.m a b),
    Tgt.fmap (HId.fmap f) = f.
  Proof.
    reflexivity.
  Qed.

  (** We could fight the dependent typing to show HComp is a [Functor] as so:
    HComp : Vert ×_V Vert → Vert *)

  (* Src ∘ HComp = Src ∘ π_1 *)
  Proposition hcomp_src :
    forall {a b c : V.t}, forall {B : b -o-> c} {A : a -o-> b},
      Src.omap (A ⨀ B) = Src.omap A.
  Proof.
    reflexivity.
  Qed.

  Proposition hcomp_fmap_src :
    forall {a b c a' b' c' : V.t},
      forall {A : a -o-> b} {B : b -o-> c} {A' : a' -o-> b'} {B' : b' -o-> c'}
        {f : V.m a a'} {g : V.m b b'} {h : V.m c c'}
        (α : A =[f,g]=> A') (β : B =[g,h]=> B'),
        Src.fmap (hcomp_fmap α β) = Src.fmap α.
  Proof.
    reflexivity.
  Qed.

  (* Tgt ∘ HComp = Tgt ∘ π_1 *)
  Proposition hcomp_tgt :
    forall {a b c : V.t}, forall {B : b -o-> c} {A : a -o-> b},
      Tgt.omap (A ⨀ B) = Tgt.omap B.
  Proof.
    intros. unfold tgt. reflexivity.
  Qed.

  Proposition hcomp_fmap_tgt :
    forall {a b c a' b' c' : V.t},
      forall {A : a -o-> b} {B : b -o-> c} {A' : a' -o-> b'} {B' : b' -o-> c'}
        {f : V.m a a'} {g : V.m b b'} {h : V.m c c'}
        (α : A =[f,g]=> A') (β : B =[g,h]=> B'),
        Tgt.fmap (hcomp_fmap α β) = Tgt.fmap β.
  Proof.
    reflexivity.
  Qed.
End DblCategoryTheory.
