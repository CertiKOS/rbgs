Require Import Program.

(** Directed multigraphs are sometimes referred to as "quivers"
  (a container for arrows) in the context of category theory.
  There, it can be understood as a pre-categorical structure with
  objects and arrows but no identities or composition operations. *)


(** * Basic definitions *)

(** ** Quivers *)

(** In dependent type theory, quivers can be represented in unbundled
  form by giving itset of vertices as a type [V : Type] and its edges
  as a family [E : V -> V -> Type], where an edge from [u : V]
  to [v : V] is an element of the type [E u v]. *)

Definition quiver (V : Type) := V -> V -> Type.

(** ** Quiver homomorphisms *)

(** Then a quiver homomorphism provides both a vertex map [f] as well
  as an edge map [F]. The expected structure preservation properties
  are captured by types in a straightforward way. *)

Definition qmor {U V} (f : U -> V) (E : quiver U) (F : quiver V) :=
  forall u v, E u v -> F (f u) (f v).

Definition qid {U} (E : quiver U) : qmor _ E E :=
  fun u v x => x.

Definition qcomp {U V W g f E F G} : @qmor V W g F G -> @qmor U V f E F -> qmor _ E G :=
  fun γ φ u v e => γ (f u) (f v) (φ u v e).

Infix "@" := qcomp (at level 45, right associativity).


(** * Free category *)

(** Given a category, we can forget the compositional structure to
  retain only the underlying quiver. Likewise every functor is a
  quiver homomorphism with additional constraints that we can forget.
  This defines a functor [U : Cat -> Quiv]. The left adjoint of [U]
  is the functor [F : Quiv -> Cat] which associates to a quiver [E]
  the category of its vertices and paths.

  We make extensive use of the adjunction [F -| U : Cat -> Quiv].
  While the template games of Paul-André Melliès are formulated in
  terms of categories and functors, in practice the categories used
  are all freely generated by quivers, and consequently functors
  between them can be represented as Kleisli morphisms for the quiver
  monad [UF : Quiv -> Quiv] defined below.

  This is invaluable because it allows us to do away entirely with the
  abstract notions of categories and functors. Instead we can work at
  the level of quiver and quiver homomorphisms, using the simple and
  type-friendly representations above, and only need to define the
  concrete structure provided by categories of vertices and paths,
  of which all template categories of interest are instances. *)

(** ** Definition *)

Inductive path {V} (T : quiver V) : quiver V :=
  | pnil {u} : path T u u
  | pcons {u v w} (e : T u v) (x : path T v w) : path T u w.

Arguments pnil {V T u}.
Arguments pcons {V T u v w} e x.

(*Declare Scope path_scope.*)
Delimit Scope path_scope with path.
Bind Scope path_scope with path.
Notation "[ ]" := pnil : path_scope.
Notation "[ x , .. , y ]" := (pcons x .. (pcons y pnil) .. ) : path_scope.

(** ** Compositional structure *)

(** In the free category, identities are provided by the empty path
  [pnil] associated with a given vertex. Composition is given by path
  concatenation, which can be defined as follows. *)

Fixpoint papp {V T} {u v w : V} (x : path T u v) : path T v w -> path T u w :=
  match x with
    | pnil => fun y => y
    | pcons t x => fun y => pcons t (papp x y)
  end.

Lemma papp_pnil_l {V T} {u v : V} (x : path T u v) :
  papp pnil x = x.
Proof.
  reflexivity.
Qed.

Lemma papp_pnil_r {V T} {u v : V} (x : path T u v) :
  papp x pnil = x.
Proof.
  induction x; cbn; congruence.
Qed.

Lemma papp_assoc {V T} {u v i j : V} (x : path T u v) (y : _ v i) (z : _ i j) :
  papp (papp x y) z = papp x (papp y z).
Proof.
  induction x; cbn; congruence.
Qed.

Infix "++" := papp : path_scope.

(** ** Monadic structure *)

(** *** Functoriality *)

(** The definition [path] above gives the object part of the functor
  [UF : Quiv -> Quiv]. The morphism part is as follows. *)

Definition pmap {U V E F} {f : U -> V} (φ : qmor f E F) : qmor f (path E) (path F) :=
  fix K {u v} x :=
    match x with
      | pnil => pnil
      | pcons e y => pcons (φ _ _ e) (K y)
    end.

Lemma pmap_pnil {U V E F} {f : U -> V} (φ : qmor f E F) {u} :
  pmap φ u u pnil = pnil.
Proof.
  reflexivity.
Qed.

Lemma pmap_papp {U V E F} {f : U -> V} (φ : qmor f E F) {u v w} x y :
  pmap φ u w (x ++ y)%path = (pmap φ u v x ++ pmap φ v w y)%path.
Proof.
  induction x; cbn; auto.
  rewrite IHx.
  reflexivity.
Qed.

(** *** Unit *)

(** The unit of the free category adjunction and of the associated
  monad is a natural transformation [η : 1 -> UF : Quiv -> Quiv]. *)

Definition pret {U} {E : quiver U} : qmor _ E (path E) :=
  fun u v e => [e]%path.

Lemma pmap_pret {U V} (f : U -> V) {E F} (φ : qmor f E F) {u v} (e : E u v) :
  pmap φ u v (pret u v e) = pret (f u) (f v) (φ u v e).
Proof.
  reflexivity.
Qed.

(** *** Multiplication *)

(** The multiplication is a natural transformation
  [μ : UFUF -> UF : Quiv -> Quiv] which flattens a path of paths. *)

Definition pjoin {U} {E : quiver U} : qmor _ (path (path E)) (path E) :=
  fix K {u v} x :=
    match x with
      | pnil => pnil
      | pcons e y => papp e (K y)
    end.

Lemma pmap_pjoin {U V} (f : U -> V) {E F} (φ : qmor f E F) {u v} (x : path (path E) u v) :
  pmap φ u v (pjoin u v x) = pjoin (f u) (f v) (pmap (pmap φ) u v x).
Proof.
  induction x; cbn; auto.
  rewrite pmap_papp, IHx.
  reflexivity.
Qed.

(** Note that [μ] is obtained as [μ := UϵF] from the counit
  [ϵ : FU -> 1 : Cat -> Cat] of the free category adjunction. This
  means in particular that the component [μE : UFUF E -> UF E ∈ Quiv]
  defined above is the residual quiver homomorphism of a functor
  [ϵFE : FUF E -> F E ∈ Cat], which therefore satisfies the following
  properties. *)

Lemma pjoin_pnil {U E u} :
  @pjoin U E u u pnil = pnil.
Proof.
  reflexivity.
Qed.

Lemma pjoin_papp {U E u v w} x y :
  @pjoin U E u w (x ++ y)%path = (pjoin u v x ++ pjoin v w y)%path.
Proof.
  induction x; cbn; auto.
  rewrite papp_assoc, IHx.
  reflexivity.
Qed.

(** *** Coherence conditions *)

Lemma pjoin_pret_l {V E u v} (x : @path V E u v) :
  pjoin u v (pret u v x) = x.
Proof.
  induction x; cbn; auto.
  rewrite papp_pnil_r.
  reflexivity.
Qed.

Lemma pjoin_pret_r {V E u v} (x : @path V E u v) :
  pjoin u v (pmap pret u v x) = x.
Proof.
  induction x; cbn; congruence.
Qed.

Lemma pjoin_assoc {V E u v} (x : path (path (@path V E)) u v) :
  pjoin u v (pmap pjoin u v x) = pjoin u v (pjoin u v x).
Proof.
  induction x; cbn; auto.
  rewrite pjoin_papp, IHx.
  reflexivity.
Qed.

(** *** Kleisli extension *)

Definition pbind {U V E F} {f : U -> V} (φ : qmor f E (path F)) : qmor f (path E) (path F) :=
  fun u v x => pjoin (f u) (f v) (pmap φ u v x).

(** Once again the quiver morphism above is actually of the form [Uφ†],
  where [φ† : FX -> FY ∈ Cat] is a functor between path categories. *)

Lemma pbind_pnil {U V E F f φ u} :
  @pbind U V E F f φ u u pnil = pnil.
Proof.
  reflexivity.
Qed.

Lemma pbind_papp {U V E F f φ u v w} x y :
  @pbind U V E F f φ u w (x ++ y)%path = (pbind φ u v x ++ pbind φ v w y)%path.
Proof.
  unfold pbind.
  rewrite pmap_papp, pjoin_papp.
  reflexivity.
Qed.

(** In fact, [φ†] is the morphism associated to [φ] by the universal
  property of the adjunction's unit [ηX : X -> UFX ∈ Quiv]. *)

Lemma pbind_pret_r {U V E F f φ u v e} :
  @pbind U V E F f φ u v (pret u v e) = φ u v e.
Proof.
  unfold pbind.
  rewrite pmap_pret, pjoin_pret_l.
  reflexivity.
Qed.

Lemma pbind_uniq {U V E F} {f : U -> V} (φ : qmor f E (path F)) (γ : qmor f (path E) (path F)) :
  (forall u, γ u u pnil = pnil) ->
  (forall u v w x y, γ u w (x ++ y) = γ u v x ++ γ v w y)%path ->
  (forall u v e, γ u v (pret u v e) = φ u v e) ->
  (forall u v x, γ u v x = pbind φ u v x).
Proof.
  intros γ_pnil γ_papp H u v x.
  induction x; cbn; auto.
  change (pcons e x) with (pret _ _ e ++ x)%path.
  rewrite γ_papp, H, IHx.
  reflexivity.
Qed.

(** From there we can derive the remaining Haskell-style properties. *)

Lemma pbind_pret_l {U} {E : quiver U} {u v} (x : path E u v) :
  pbind pret u v x = x.
Proof.
  symmetry.
  apply (pbind_uniq pret (fun u v e => e)); auto.
Qed.

Lemma pbind_pbind {U V W E F G f φ g γ} u v x :
  @pbind V W F G g γ (f u) (f v) (@pbind U V E F f φ u v x) =
  pbind (fun u v x => pbind γ (f u) (f v) (φ u v x)) u v x.
Proof.
  apply (pbind_uniq _ (fun u v x => pbind γ (f u) (f v) (pbind φ u v x))); intros.
  - rewrite !pbind_pnil; auto.
  - rewrite !pbind_papp; auto.
  - rewrite !pbind_pret_r; auto.
Qed.