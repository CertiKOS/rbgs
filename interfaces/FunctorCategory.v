Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.


(** * Functor categories *)

Module FunctorCategory (C D : CategoryDefinition) <: Category.

  (** The objects are functors from [C] to [D]. *)

  Record functor :=
    {
      oapply :> C.t -> D.t;
      fapply {A B} : C.m A B -> D.m (oapply A) (oapply B);

      fapply_id {A} :
        fapply (C.id A) = D.id (oapply A);
      fapply_compose {A B C} (g : C.m B C) (f : C.m A B) :
        fapply (C.compose g f) = D.compose (fapply g) (fapply f);
    }.

  Definition t := functor.
  Identity Coercion tf : t >-> functor.

  (** The morphisms are natural transformations. *)

  Record nt (F G : t) :=
    mknt {
      comp X :> D.m (F X) (G X);

      natural {X Y} (f : C.m X Y) :
        D.compose (comp Y) (fapply F f) = D.compose (fapply G f) (comp X);
    }.

  Arguments comp {F G}.
  Arguments natural {F G}.
  Arguments mknt {F G}.

  Definition m := nt.

  Lemma meq {F G} (η φ : m F G) :
    (forall X, η X = φ X) -> η = φ.
  Proof.
    destruct η as [η Hη], φ as [φ Hφ]. cbn. intro H.
    apply functional_extensionality_dep in H. subst.
    f_equal. apply proof_irrelevance.
  Qed.

  Lemma natural_rewrite {F G X Y Z} (η : m F G) (f : C.m X Y) (x : D.m Z _) :
    D.compose (η Y) (D.compose (fapply F f) x) =
    D.compose (fapply G f) (D.compose (η X) x).
  Proof.
    rewrite <- D.compose_assoc.
    rewrite natural.
    rewrite D.compose_assoc.
    reflexivity.
  Qed.

  (** Compositional structure *)

  Program Definition id F : m F F :=
    {|
      comp X := D.id (F X);
    |}.
  Next Obligation.
    rewrite D.compose_id_left, D.compose_id_right.
    reflexivity.
  Qed.

  Program Definition compose {F G H} (η : m G H) (φ : m F G) :=
    {|
      comp X := D.compose (η X) (φ X);
    |}.
  Next Obligation.
    rewrite D.compose_assoc, natural.
    rewrite <- D.compose_assoc, natural.
    rewrite D.compose_assoc. reflexivity.
  Qed.

  (** Properties *)

  Proposition compose_id_left {E F} (η : m E F) :
    compose (id F) η = η.
  Proof.
    apply meq. intros X.
    apply D.compose_id_left.
  Qed.

  Proposition compose_id_right {E F} (η : m E F) :
    compose η (id E) = η.
  Proof.
    apply meq. intros X.
    apply D.compose_id_right.
  Qed.

  Proposition compose_assoc {E F G H} :
    forall (η : m E F) (φ : m F G) (ψ : m G H),
      compose (compose ψ φ) η = compose ψ (compose φ η).
  Proof.
    intros. apply meq. cbn.
    intro X. apply D.compose_assoc.
  Qed.

  Include CategoryTheory.

End FunctorCategory.

(** Below it will be useful to be able to know that a module was
  constructed as a functor category, so we provide a corresponding
  module type. *)

Module Type FunctorCategoryInstance (C D : CategoryDefinition).
  Include (FunctorCategory C D).
End FunctorCategoryInstance.


(** * Functor composition *)

Module FunctorComposition (C D E : CategoryDefinition) 
  (CD : FunctorCategoryInstance C D)
  (DE : FunctorCategoryInstance D E)
  (CE : FunctorCategoryInstance C E)
<: Bifunctor DE CD CE.

  Import E.

  (** Objects compose as functors *)

  Program Definition omap (G : DE.t) (F : CD.t) : CE.t :=
    {|
      CE.oapply X := DE.oapply G (CD.oapply F X);
      CE.fapply X Y f := DE.fapply G (CD.fapply F f);
    |}.
  Next Obligation.
    rewrite CD.fapply_id.
    rewrite DE.fapply_id.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite CD.fapply_compose.
    rewrite DE.fapply_compose.
    reflexivity.
  Qed.

  (** Morphisms between composite functors are obtained by horizontal
    composition of natural transformations. *)

  Program Definition fmap {G1 F1 G2 F2} (φ : DE.m G1 G2) (η : CD.m F1 F2) :=
    @CE.mknt (omap G1 F1) (omap G2 F2)
             (fun X => E.compose (DE.comp φ (CD.oapply F2 X))
                                 (DE.fapply G1 (CD.comp η X))) _.
  Next Obligation.
    rewrite !E.compose_assoc.
    rewrite <- (DE.natural_rewrite φ).
    rewrite <- !DE.fapply_compose.
    rewrite CD.natural.
    reflexivity.
  Qed.

  (** Properties of horizontal composition. *)

  Proposition fmap_id G F :
    fmap (DE.id G) (CD.id F) = CE.id (omap G F).
  Proof.
    apply CE.meq. intro X. cbn.
    rewrite DE.fapply_id.
    rewrite E.compose_id_right.
    reflexivity.
  Qed.

  Proposition fmap_compose {G1 F1 G2 F2 G3 F3} (φ : DE.m G2 G3) (η : CD.m F2 F3)
                                               (φ': DE.m G1 G2) (η': CD.m F1 F2):
    fmap (DE.compose φ φ') (CD.compose η η') = CE.compose (fmap φ η) (fmap φ' η').
  Proof.
    apply CE.meq. intro X. cbn.
    rewrite !E.compose_assoc.
    rewrite DE.fapply_compose.
    rewrite DE.natural_rewrite.
    reflexivity.
  Qed.

  Include BifunctorTheory DE CD CE.

End FunctorComposition.


(** * Monoidal category of endofunctors under composition *)

(** When restricted to a single base category, functor composition
  acts as a monoidal structure. *)

Module EndofunctorComposition
  (C : CategoryDefinition)
  (CC : FunctorCategoryInstance C C).

  Import CC.
  Module Tens <: MonoidalStructure CC.

  Include FunctorComposition C C C CC CC CC.

  (** The unit is the identity functor for [C]. *)

  Program Definition unit : CC.t :=
    {|
      CC.oapply X := X;
      CC.fapply X Y f := f;
    |}.

  (** The associator and unitors are identity natural transformations,
    but we must redefine them because the source and target functors
    are not convertible even though they are equal. *)

  Program Definition assoc H G F : CC.iso (omap H (omap G F)) (omap (omap H G) F) :=
    {|
      fw := @CC.mknt (omap H (omap G F)) (omap (omap H G) F) (fun X => C.id _) _;
      bw := @CC.mknt (omap (omap H G) F) (omap H (omap G F)) (fun X => C.id _) _;
    |}.
  Next Obligation.
    rewrite C.compose_id_left, C.compose_id_right.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite C.compose_id_left, C.compose_id_right.
    reflexivity.
  Qed.
  Next Obligation.
    apply CC.meq. intro X. cbn.
    rewrite C.compose_id_left.
    reflexivity.
  Qed.
  Next Obligation.
    apply CC.meq. intro X. cbn.
    rewrite C.compose_id_left.
    reflexivity.
  Qed.

  Program Definition lunit F : CC.iso (omap unit F) F :=
    {|
      fw := @CC.mknt (omap unit F) F (fun X => C.id (F X)) _;
      bw := @CC.mknt F (omap unit F) (fun X => C.id (F X)) _;
    |}.
  Next Obligation.
    rewrite C.compose_id_left, C.compose_id_right; auto.
  Qed.
  Next Obligation.
    rewrite C.compose_id_left, C.compose_id_right; auto.
  Qed.
  Next Obligation.
    apply CC.meq. intro X. cbn.
    rewrite C.compose_id_left; auto.
  Qed.
  Next Obligation.
    apply CC.meq. intro X. cbn.
    rewrite C.compose_id_left; auto.
  Qed.

  Program Definition runit F : CC.iso (omap F unit) F :=
    {|
      fw := @CC.mknt (omap F unit) F (fun X => C.id (F X)) _;
      bw := @CC.mknt F (omap F unit) (fun X => C.id (F X)) _;
    |}.
  Next Obligation.
    rewrite C.compose_id_left, C.compose_id_right; auto.
  Qed.
  Next Obligation.
    rewrite C.compose_id_left, C.compose_id_right; auto.
  Qed.
  Next Obligation.
    apply CC.meq. intro X. cbn.
    rewrite C.compose_id_left; auto.
  Qed.
  Next Obligation.
    apply CC.meq. intro X. cbn.
    rewrite C.compose_id_left; auto.
  Qed.

  (** Naturality properties *)

  Proposition assoc_nat {F1 G1 H1 F2 G2 H2} :
    forall (η : CC.m F1 F2) (φ : CC.m G1 G2) (ψ : CC.m H1 H2),
      fmap (fmap η φ) ψ @ assoc F1 G1 H1 = assoc F2 G2 H2 @ fmap η (fmap φ ψ).
  Proof.
    intros. apply meq. intro X. cbn.
    rewrite C.compose_id_left, C.compose_id_right, C.compose_assoc.
    rewrite CC.fapply_compose.
    reflexivity.
  Qed.

  Proposition lunit_nat {F G : CC.t} (η : CC.m F G) :
    η @ lunit F = lunit G @ fmap (CC.id unit) η.
  Proof.
    apply meq. intro X. cbn.
    rewrite !C.compose_id_left, !C.compose_id_right.
    reflexivity.
  Qed.

  Proposition runit_nat {F G : CC.t} (η : CC.m F G) :
    η @ runit F = runit G @ fmap η (CC.id unit).
  Proof.
    apply meq. intro X. cbn.
    rewrite CC.fapply_id, !C.compose_id_left, !C.compose_id_right.
    reflexivity.
  Qed.

  (** Coherence conditions *)

  Proposition assoc_coh (A B C D : CC.t) :
    fmap (assoc A B C) (CC.id D) @
      assoc A (omap B C) D @
      fmap (CC.id A) (assoc B C D) =
    assoc (omap A B) C D @
      assoc A B (omap C D).
  Proof.
    apply meq. intro X. cbn.
    rewrite !CC.fapply_id, !C.compose_id_left.
    reflexivity.
  Qed.

  Proposition unit_coh (A B : CC.t) :
    fmap (runit A) (CC.id B) @ assoc A unit B = fmap (CC.id A) (lunit B).
  Proof.
    apply meq. intro X. cbn.
    rewrite CC.fapply_id, !C.compose_id_left.
    reflexivity.
  Qed.

  Include MonoidalStructureTheory CC.

  End Tens.
End EndofunctorComposition.

Module Type MonoidalCategory :=
  Category.Category <+ Monoidal.

Module EndofunctorCategory (C : CategoryDefinition) <: MonoidalCategory.
  Include FunctorCategory C C.
  Include EndofunctorComposition C.
  Include MonoidalTheory.
End EndofunctorCategory.

Module AddEndofunctors (C : CategoryDefinition).
  Module End.
    Include EndofunctorCategory C.
  End End.
  Module EndNotations.
    Coercion End.tf : End.t >-> End.functor.
    Coercion End.oapply : End.functor >-> Funclass.
    Infix "∘" := End.Tens.omap (at level 45, right associativity) : obj_scope.
    Infix "∘" := End.Tens.fmap (at level 45, right associativity) : hom_scope.
  End EndNotations.
End AddEndofunctors.

Module Type CategoryWithEndofunctors :=
  Category.Category
    <+ AddEndofunctors.


(** * Monads *)

(** Given a monoidal category [C], we can construct
  the category of monoids in [C]. *)

Module Monoids (C : MonoidalCategory) <: Category.
  Import C.

  (** ** Monoid objects and homomorphisms *)

  (** A monoid in [C] is an object [M ∈ C] (the carrier) equipped with
    a unit morphism [η : 1 ~~> M] and a multiplication [μ : M * M ~~> M].
    For the monoidal category of sets under cartesian products this
    definition reduces to the usual definition of monoid. *)

  Record mon :=
    {
      carrier :> C.t;
      eta : 1 ~~> carrier;
      mu : carrier * carrier ~~> carrier;

      mu_eta_l : mu @ (eta * id carrier) = fw (λ carrier);
      mu_eta_r : mu @ (id carrier * eta) = fw (ρ carrier);
      mu_mu : mu @ (id _ * mu) @ bw (α _ _ _) = mu @ (mu * id _);
    }.

  Definition t := mon.
  Identity Coercion tmon : t >-> mon.

  (** A monoid homomorphism is given by a morphism between the
    carriers which respects some coherence conditions with respect to
    the units and multiplications. *)

  Record mh (M N : mon) :=
    {
      map :> M ~~> N;
      map_eta : map @ eta M = eta N;
      map_mu : map @ mu M = mu N @ (map * map);
    }.

  Arguments map {M N} _.

  Definition m := mh.

  (** The following lemma are useful when proving that monoid
    homomorphisms are equal and when we use [map_eta] and [map_mu]
    to rewrite inside complex expressions. *)

  Lemma meq {M N} (f g : m M N) :
    map f = map g -> f = g.
  Proof.
    destruct f as [f Hf1 Hf2], g as [g Hg1 Hg2]. cbn. intro. subst.
    f_equal; auto using proof_irrelevance.
  Qed.

  Lemma map_eta_rewrite {M N X} (f : m M N) (x : C.m X _) :
    f @ eta M @ x = eta N @ x.
  Proof.
    rewrite <- !compose_assoc, map_eta.
    reflexivity.
  Qed.

  Lemma map_mu_rewrite {M N X} (f : m M N) (x : C.m X _) :
    f @ mu M @ x = mu N @ (f * f) @ x.
  Proof.
    rewrite <- !compose_assoc, map_mu.
    reflexivity.
  Qed.

  (** ** Compositional structure *)

  (** The identity and composition of monoid homomorphism are
    inherited from the underlying category. We just need to prove
    that coherence conditions are preserved. *)

  Program Definition id (M : t) : m M M :=
    {|
      map := C.id M;
    |}.
  Next Obligation.
    rewrite C.compose_id_left.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite C.Tens.fmap_id, C.compose_id_left, C.compose_id_right.
    reflexivity.
  Qed.

  Program Definition compose {M1 M2 M3} (g : m M2 M3) (f : m M1 M2) : m M1 M3 :=
    {|
      map := map g @ map f;
    |}.
  Next Obligation.
    rewrite C.compose_assoc, !map_eta.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite C.compose_assoc.
    rewrite map_mu, map_mu_rewrite, C.Tens.fmap_compose.
    reflexivity.
  Qed.

  (** Likewise the required properties are inherited from [C]. *)

  Proposition compose_id_left {A B} (f : m A B) :
    compose (id B) f = f.
  Proof.
    apply meq; cbn.
    apply C.compose_id_left.
  Qed.

  Proposition compose_id_right {A B} (f : m A B) :
    compose f (id A) = f.
  Proof.
    apply meq; cbn.
    apply C.compose_id_right.
  Qed.

  Proposition compose_assoc {A B C D} (f : m A B) (g : m B C) (h : m C D) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    apply meq; cbn.
    apply C.compose_assoc.
  Qed.

  Include CategoryTheory.

End Monoids.

(** When the underlying category is the monoidal category [C.End]
  of endofunctors over a base category [C], then monoids in [C.End]
  are the monads over [C]. *)

Module Monads (C : CategoryWithEndofunctors).
  Import C.EndNotations.
  Include Monoids C.End.
End Monads.

(** See [models/SET.v] for an example. *)
