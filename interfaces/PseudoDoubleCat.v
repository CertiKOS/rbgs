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

Module Type DblCategoryDefinition (V : CategoryDefinition).

Declare Module Vert : DblVerticalCatDefinition V.

  Include Vert.

  Declare Module Src : DblSrcFunctorDef V Vert.
  Declare Module Tgt : DblTgtFunctorDef V Vert.
  Declare Module HId : FunctorDefinition Vert V.

End DblCategoryDefinition.

Module DblCategoryTheory (V : CategoryDefinition) (P : DblCategoryDefinition V).
  Import P.

End DblCategoryTheory.
