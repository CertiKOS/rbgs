Require Import interfaces.Category.
Require Import interfaces.Functor.

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
      src_mor : V.m (src A) (src B);
      tgt_mor : V.m (tgt A) (tgt B);
      carrier_mor :> tcell A B src_mor tgt_mor;
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
  Definition src_vmor {A B : harr} (tc: harr_mor A B) : V.m (src A) (src B)
    := src_mor tc.
  Definition tgt_vmor {A B : harr} (tc : harr_mor A B) : V.m (tgt A) (tgt B)
    := tgt_mor tc.

  Definition t := harr.
  Definition m := harr_mor.

  Parameter id : forall A, m A A.
  Parameter compose : forall {A B C}, m B C -> m A B -> m A C.

  Axiom compose_id_left : forall {A B} (f : m A B), compose (id B) f = f.
  Axiom compose_id_right : forall {A B} (f : m A B), compose f (id A) = f.
  Axiom compose_assoc : forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
    compose (compose h g) f = compose h (compose g f).

  Notation vid := id.
  Notation vcomp := compose.

End DblVerticalCatDefinition.

Module Type DblSrcFunctorDef (V : CategoryDefinition)
  (H : DblVerticalCatDefinition V) <: FunctorDefinition H V.
  Import H.

  Definition omap : H.t -> V.t :=
    fun hc => H.src hc.
  Definition fmap : forall {A B}, H.m A B -> V.m (omap A) (omap B) :=
    fun A B => fun hc_mor => src_vmor hc_mor.

  Axiom fmap_id :
    forall A, fmap (H.id A) = V.id (omap A).

  Axiom fmap_compose :
    forall {A B C} (g : H.m B C) (f : H.m A B),
      fmap (H.compose g f) = V.compose (fmap g) (fmap f).

End DblSrcFunctorDef.

Module Type DblTgtFunctorDef (V : CategoryDefinition)
  (H : DblVerticalCatDefinition V) <: FunctorDefinition H V.
  Import H.

  Definition omap : H.t -> V.t :=
    fun hc => H.tgt hc.
  Definition fmap : forall {A B}, H.m A B -> V.m (omap A) (omap B) :=
    fun A B => fun hc_mor => tgt_vmor hc_mor.

  Axiom fmap_id :
    forall A, fmap (H.id A) = V.id (omap A).

  Axiom fmap_compose :
    forall {A B C} (g : H.m B C) (f : H.m A B),
      fmap (H.compose g f) = V.compose (fmap g) (fmap f).

End DblTgtFunctorDef.

Module Type DblIdFunctorDef (V : CategoryDefinition)
  (H : DblVerticalCatDefinition V) <: FunctorDefinition V H.
  Import H.

  Parameter hid :
    forall (a : V.t), a -o-> a.

  Definition omap : V.t -> H.t :=
    fun a => hid a.
  Parameter fmap : forall {A B}, V.m A B -> H.m (omap A) (omap B).

  Axiom fmap_id :
    forall A, fmap (V.id A) = H.id (omap A).

  Axiom fmap_compose :
    forall {A B C} (g : V.m B C) (f : V.m A B),
      fmap (V.compose g f) = H.compose (fmap g) (fmap f).
End DblIdFunctorDef.


Module Type DblCategoryDefinition (V : CategoryDefinition).

Declare Module Vert : DblVerticalCatDefinition V.

  Include Vert.

  Declare Module Src : DblSrcFunctorDef V Vert.
  Declare Module Tgt : DblTgtFunctorDef V Vert.
  Declare Module Hid : DblIdFunctorDef V Vert.

  Definition hid (A : V.t) := Hid.hid A.

  Axiom hid_src : forall A, src (hid A) = A.
  Axiom hid_tgt : forall A, tgt (hid A) = A.

  Parameter hcomp :
    forall {a b c : V.t},
      (b -o-> c) -> (a -o-> b) -> (a -o-> c).
  Infix "⊙" := hcomp (at level 40, left associativity) : type_scope.

  (* need to add hcomp_fmap *)

  (* below still under work *)

  Include CategoryTheory.

  (** *** Structural isomorphisms *)
  Parameter assoc : forall A B C, C.iso (hcomp A (omap B C)) (omap (omap A B) C).
  Parameter lunit : forall A, C.iso (omap unit A) A.
  Parameter runit : forall A, C.iso (omap A unit) A.

  (** *** Naturality properties *)

  Axiom assoc_nat :
    forall {A1 B1 C1 A2 B2 C2: C.t} (f: C.m A1 A2) (g: C.m B1 B2) (h: C.m C1 C2),
      fmap (fmap f g) h @ assoc A1 B1 C1 = assoc A2 B2 C2 @ fmap f (fmap g h).

  Axiom lunit_nat :
    forall {A1 A2 : C.t} (f : C.m A1 A2),
      f @ lunit A1 = lunit A2 @ fmap (C.id unit) f.

  Axiom runit_nat :
    forall {A1 A2 : C.t} (f : C.m A1 A2),
      f @ runit A1 = runit A2 @ fmap f (C.id unit).

  (** *** Pentagon identity *)

  Axiom assoc_coh :
    forall A B C D : C.t,
      fmap (assoc A B C) (C.id D) @
        assoc A (omap B C) D @
        fmap (C.id A) (assoc B C D) =
      assoc (omap A B) C D @
        assoc A B (omap C D).

  (** *** Triangle identity *)

  Axiom unit_coh :
    forall A B : C.t,
      fmap (runit A) (C.id B) @ assoc A unit B =
      fmap (C.id A) (lunit B).
End DblCategoryDefinition.

Module DblCategoryTheory (V : CategoryDefinition) (P : DblCategoryDefinition V).
  Import P.

  (** These are just sanity checks *)
  Axiom hcomp_src :
    forall {a b c : V.t}, forall {B : b -o-> c} {A : a -o-> b},
      src (B ⊙ A) = src A.
  Axiom hcomp_tgt :
    forall {a b c : V.t}, forall {B : b -o-> c} {A : a -o-> b},
      tgt (B ⊙ A) = tgt A.
End DblCategoryTheory.
