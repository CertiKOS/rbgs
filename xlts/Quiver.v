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

(** ** Compositional structure *)

Definition qid {U} {E : quiver U} : qmor _ E E :=
  fun u v x => x.

Definition qcomp {U V W g f E F G} : @qmor V W g F G -> @qmor U V f E F -> qmor _ E G :=
  fun γ φ u v e => γ (f u) (f v) (φ u v e).

Infix "@" := qcomp (at level 45, right associativity).

(** Proving that quivers and quiver homomorphisms for a category is
  completely straightforward as everything is basically convertible. *)

Lemma qcomp_qid_l {U V f E F} (φ : @qmor U V f E F) :
  qid @ φ = φ.
Proof.
  reflexivity.
Qed.

Lemma qcomp_qid_r {U V f E F} (φ : @qmor U V f E F) :
  φ @ qid = φ.
Proof.
  reflexivity.
Qed.

Lemma qcomp_assoc {U V W X f g h E F G H} :
  forall (ψ : @qmor W X h G H) (γ : @qmor V W g F G) (φ : @qmor U V f E F),
    (ψ @ γ) @ φ = ψ @ γ @ φ.
Proof.
  reflexivity.
Qed.

(** ** Products *)

Definition qprod {U V} (E : quiver U) (F : quiver V) : quiver (U * V) :=
  fun u v => (E (fst u) (fst v) * F (snd u) (snd v))%type.

Definition qfst {U V E F} : qmor fst (@qprod U V E F) E :=
  fun u v x => fst x.

Definition qsnd {U V E F} : qmor snd (@qprod U V E F) F :=
  fun u v x => snd x.

Delimit Scope quiv_scope with quiv.
Bind Scope quiv_scope with quiver.
Infix "*" := qprod : quiv_scope.


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

  This is invaluable because it allows us to largely do away with the
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
Infix "::" := pcons : path_scope.
Notation "[ x , .. , y ]" := (x :: .. (y :: []) .. )%path : path_scope.

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

(** ** Adjunction properties *)

(** *** Functoriality *)

(** The definition [path] above gives the object part of the functor
  [UF : Quiv -> Quiv]. The morphism part is as follows. *)

Definition pmap {U V E F} {f : U -> V} (φ : qmor f E F) : qmor f (path E) (path F) :=
  fix K u v x :=
    match x with
      | pnil => pnil
      | pcons e y => pcons (φ _ _ e) (K _ _ y)
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

(** *** General categories *)

(** As discussed above, the target categories we consider when using
  the properties of the left adjoint [path] will largely be concrete
  freely generated categories of the form [path E] themselves, so in
  most cases we will only care about the way the adjunction flattens
  into a monad in Quiv. However in some cases we will also need to
  consider more general products of the form [path E1 * ... * path En].

  To make it possible to define the counit and the properties of the
  adjunction so that they can be used for these more general targets,
  we will use to following typeclasses. *)

Class Category {U} (E : quiver U) :=
  {
    id (u : U) : E u u;
    compose {u v w} : E u v -> E v w -> E u w;
    compose_id_l {u v} (f : E u v) : compose (id u) f = f;
    compose_id_r {u v} (f : E u v) : compose f (id v) = f;
    compose_assoc {u v w z} f g h :
      @compose u w z (@compose u v w f g) h =
      @compose u v z f (@compose v w z g h);
  }.

Global Instance path_cat {V} (E : quiver V) : Category (path E) :=
  {|
    id := @pnil V E;
    compose := @papp V E;
    compose_id_l := @papp_pnil_l V E;
    compose_id_r := @papp_pnil_r V E;
    compose_assoc := @papp_assoc V E;
  |}.

Section QPROD_CAT.
  Context {U V E F} `{CE : @Category U E} `{CF : @Category V F}.
  Obligation Tactic := cbn; intros.

  Program Instance qprod_cat : Category (qprod E F) :=
    {|
      id x := (id (fst x), id (snd x));
      compose x y z f g := (compose (fst f) (fst g), compose (snd f) (snd g));
    |}.
  Next Obligation.
    rewrite !compose_id_l, <- surjective_pairing.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite !compose_id_r, <- surjective_pairing.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite !compose_assoc.
    reflexivity.
  Qed.
End QPROD_CAT.

(** The general notion of a functor will be used
  to express the naturality of the counit. *)

Class Functor {U V E F} `{CE : Category U E} `{CF : Category V F} {f} (φ : qmor f E F) :=
  {
    fmap_id u :
      φ u u (id u) = id (f u);
    fmap_compose {u v w} (x : E u v) (y : E v w) :
      φ u w (compose x y) = compose (φ u v x) (φ v w y);
  }.

Global Instance pmap_functor {U V E F f φ} :
  Functor (@pmap U V E F f φ).
Proof.
  split; cbn.
  - reflexivity.
  - auto using pmap_papp.
Qed.

(** *** Counit *)

(** The counit is a natural transformation [ϵ : FU -> 1 : Cat -> Cat]
  which evaluates path in terms of an underlying category. *)

Definition peval `{CE : Category} : qmor _ (path E) E :=
  fix K u v x :=
    match x with
      | pnil => id _
      | pcons e y => compose e (K _ _ y)
    end.

(** The quiver homomorphism defined above is the underlying map of [ϵ].
  The functoriality properties are as follows. *)

Lemma peval_pnil `{CE : Category} (u : U) :
  peval u u pnil = id u.
Proof.
  reflexivity.
Qed.

Lemma peval_papp `{CE : Category} (u v w : U) (x : path E u v) (y : path E v w) :
  peval u w (papp x y) = compose (peval u v x) (peval v w y).
Proof.
  induction x; cbn.
  - rewrite compose_id_l.
    reflexivity.
  - rewrite IHx.
    rewrite compose_assoc.
    reflexivity.
Qed.

Instance peval_functor `{CE : Category} :
  Functor peval.
Proof.
  split; cbn.
  - apply peval_pnil.
  - apply peval_papp.
Qed.

(** In addition, the naturality of [ϵ] can be stated as below. *)

Lemma peval_pmap `{Functor} {u v} (x : path E u v) :
  peval (f u) (f v) (pmap φ u v x) = φ u v (peval u v x).
Proof.
  induction x; cbn; auto.
  - rewrite fmap_id. reflexivity.
  - rewrite fmap_compose, IHx. reflexivity.
Qed.

(** The zig-zag laws below which relate the unit and counit
  establish the adjunction. *)

Lemma peval_pret_l `{Category} {u v} (x : E u v) :
  peval u v (pret u v x) = x.
Proof.
  cbn. apply compose_id_r.
Qed.

Lemma peval_pret_r {V E u v} (x : @path V E u v) :
  peval u v (pmap pret u v x) = x.
Proof.
  induction x; cbn; congruence.
Qed.

(** *** Universal property of the unit *)

Definition pext {U V E F} `{CF: Category V F} {f: U -> V}: qmor f E F -> qmor f (path E) F :=
  fun φ u v x => peval (f u) (f v) (pmap φ u v x).

(** Once again the quiver morphism above is actually of the form [Uφ†],
  where [φ† : FX -> FY ∈ Cat] is a functor between path categories. *)

Lemma pext_pnil {U V E F CF f φ u} :
  @pext U V E F CF f φ u u pnil = id (f u).
Proof.
  reflexivity.
Qed.

Lemma pext_papp {U V E F CF f φ u v w} x y :
  @pext U V E F CF f φ u w (x ++ y)%path = compose (pext φ u v x) (pext φ v w y).
Proof.
  unfold pext.
  rewrite pmap_papp, peval_papp.
  reflexivity.
Qed.

(** In fact, [φ†] is the morphism associated to [φ] by the universal
  property of the adjunction's unit [ηX : X -> UFX ∈ Quiv]. *)

Lemma pext_pret_r {U V E F CF f φ u v e} :
  @pext U V E F CF f φ u v (pret u v e) = φ u v e.
Proof.
  unfold pext.
  rewrite pmap_pret, peval_pret_l.
  reflexivity.
Qed.

Lemma pext_uniq {U V E F} `{CF: Category V F} {f: U -> V} (φ: qmor f E F) (γ: qmor f (path E) F):
  (forall u, γ u u pnil = id (f u)) ->
  (forall u v w x y, γ u w (x ++ y)%path = compose (γ u v x) (γ v w y)) ->
  (forall u v e, γ u v (pret u v e) = φ u v e) ->
  (forall u v x, γ u v x = pext φ u v x).
Proof.
  intros γ_pnil γ_papp H u v x.
  induction x; cbn; auto.
  change (pcons e x) with (pret _ _ e ++ x)%path.
  rewrite γ_papp, H, IHx.
  reflexivity.
Qed.

(** From there we can derive the remaining Haskell-style properties. *)

Lemma pext_pret_l {U} {E : quiver U} {u v} (x : path E u v) :
  pext pret u v x = x.
Proof.
  symmetry.
  apply (pext_uniq pret (fun u v e => e)); auto.
Qed.

Lemma pext_pext {U V W E F G CG} {f φ g γ} u v x :
  @pext V W F G CG g γ (f u) (f v) (@pext U V E (path F) _ f φ u v x) =
  pext (fun u v x => pext γ (f u) (f v) (φ u v x)) u v x.
Proof.
  apply (pext_uniq _ (fun u v x => pext γ (f u) (f v) (pext φ u v x))); intros.
  - rewrite !pext_pnil; auto.
  - rewrite !pext_papp. cbn [compose path_cat].
    rewrite !pext_papp. auto.
  - rewrite !pext_pret_r; auto.
Qed.

(** *** Monad *)

(** Note that the monad multiplication [μ : UFUF -> UF : Quiv -> Quiv]
  can be obtained as [μ := UϵF] from the counit [ϵ : FU -> 1 : Cat -> Cat].
  In this case we will use the following notations and specialized properties. *)

Notation pjoin := (peval (CE := path_cat _)).
Notation pbind := (pext (CF := path_cat _)).

Lemma pmap_pjoin {U V} (f : U -> V) {E F} (φ : qmor f E F) {u v} (x : path (path E) u v) :
  pmap φ u v (pjoin u v x) = pjoin (f u) (f v) (pmap (pmap φ) u v x).
Proof.
  rewrite peval_pmap.
  reflexivity.
Qed.

Lemma pjoin_pnil {U E u} :
  pjoin u u pnil = @pnil U E u.
Proof.
  rewrite peval_pnil.
  reflexivity.
Qed.

Lemma pjoin_papp {U E u v w} (x y : path (@path U E) _ _) :
  pjoin u w (x ++ y)%path = (pjoin u v x ++ pjoin v w y)%path.
Proof.
  rewrite peval_papp.
  reflexivity.
Qed.

Lemma pjoin_pret_l {V E u v} (x : @path V E u v) :
  pjoin u v (pret u v x) = x.
Proof.
  apply peval_pret_l.
Qed.

Lemma pjoin_pret_r {V E u v} (x : @path V E u v) :
  pjoin u v (pmap pret u v x) = x.
Proof.
  apply peval_pret_r.
Qed.

Lemma pjoin_assoc {V E u v} (x : path (path (@path V E)) u v) :
  pjoin u v (pmap pjoin u v x) = pjoin u v (pjoin u v x).
Proof.
  rewrite (peval_pmap (f := fun x => x)).
  reflexivity.
Qed.

Lemma pbind_pnil {U V E F f φ u} :
  pbind φ u u (@pnil U E u) = (@pnil V F (f u)).
Proof.
  rewrite pext_pnil.
  reflexivity.
Qed.

Lemma pbind_papp {U V E F} {f : U -> V} {φ : qmor f E (path F)} {u v w} x y :
  pbind φ u w (x ++ y)%path = (pbind φ u v x ++ pbind φ v w y)%path.
Proof.
  rewrite pext_papp.
  reflexivity.
Qed.

Lemma pbind_pret_r {U V E F} {f : U -> V} {φ : qmor f E (path F)} {u v e} :
  pbind φ u v (pret u v e) = φ u v e.
Proof.
  apply pext_pret_r.
Qed.

Lemma pbind_pret_l {U} {E : quiver U} {u v} (x : path E u v) :
  pbind pret u v x = x.
Proof.
  apply pext_pret_l.
Qed.

Lemma pbind_pbind {U V W E F G} {f: U -> V} {φ: qmor f E (path F)} {g: V -> W} {γ: qmor g F (path G)} u v x:
  pbind γ (f u) (f v) (pbind φ u v x) =
  pbind (fun u v x => pbind γ (f u) (f v) (φ u v x)) u v x.
Proof.
  apply pext_pext.
Qed.


(** * Indexed quivers *)

(** ** Definitions *)

(** Sometimes we will consider a fibration-like quiver (P, M) whose
  vertices and edges are indexed by the vertices and edges of some
  base quiver (V, E). Using dependent types, we can represent a quiver
  of this kind very natually in the following, unbundled form. *)

Definition qquiv {V} (E : quiver V) (P : V -> Type) :=
  forall u v, E u v -> P u -> P v -> Type.

(** In the most general form, homomorphisms between indexed quivers
  sit above a homomorphism between the base quivers. *)

Definition qqmor {U V} (f : U -> V) {E F} (φ : qmor f E F) :=
  fun {P Q} (π : forall u, P u -> Q (f u)) (M : qquiv E P) (N : qquiv F Q) =>
    forall (u v : U) (e : E u v) (p : P u) (q : P v),
      M u v e p q -> N (f u) (f v) (φ u v e) (π u p) (π v q).

(** ** Compositional structure *)

(** The identities and composite morphisms can be defined as follows,
  and satisfy the expected categorical properties. *)

Definition qqid {V E P} {M : @qquiv V E P} : qqmor _ qid _ M M :=
  fun u v e p q m => m.

Definition qqcomp {U V W g f E F G γ φ P Q R ρ π L M N} :
    @qqmor V W g F G γ Q R ρ M N ->
    @qqmor U V f E F φ P Q π L M ->
    qqmor (fun u => g (f u)) (qcomp γ φ) (fun u p => ρ (f u) (π u p)) L N
  :=
    fun η μ u v e p q m =>
      η (f u) (f v) (φ u v e) (π u p) (π v q) (μ u v e p q m).

Infix "@@" := qqcomp (at level 45, right associativity).

Lemma qqcomp_qqid_l {U V f E F φ P Q π M N} (μ : @qqmor U V f E F φ P Q π M N) :
  qqid @@ μ = μ.
Proof.
  reflexivity.
Qed.

Lemma qqcomp_qqid_r {U V f E F φ P Q π M N} (μ : @qqmor U V f E F φ P Q π M N) :
  μ @@ qqid = μ.
Proof.
  reflexivity.
Qed.

(* qqcomp_assoc *)

(** ** Total space *)

(** Flattened quivers and projection functor *)

Section TS.
  Context {V E P} (M : @qquiv V E P).

  Inductive qts : quiver (sigT P) :=
    | qti {u v e p q} : M u v e p q -> qts (existT P u p) (existT P v q).

  Definition qtp : qmor (@projT1 V P) qts E :=
    fun _ _ '(@qti u v e p q m) => e.
End TS.

(** Morphisms between flattened quivers *)

Section TSM.
  Context {U V f E F φ P Q π M N} (μ : @qqmor U V f E F φ P Q π M N).

  Definition qtf : sigT P -> sigT Q :=
    fun '(existT _ u p) => existT _ (f u) (π u p).

  Definition qtm : qmor qtf (qts M) (qts N) :=
    fun _ _ '(@qti _ _ _ _ u v e p q m) => qti N (μ u v e p q m).
End TSM.

(** ** Given by a functor *)

Section QQF.
  Context {U I f E B} (p : @qmor U I f E B).

  Inductive qqp : I -> Type :=
    | qqpi u : qqp (f u).

  Inductive qq : qquiv B qqp :=
    | qqi {u v} (e : E u v) : qq (f u) (f v) (p u v e) (qqpi u) (qqpi v).

End QQF.

(** ** Pullback *)

Section QP.
  Context {U V f E F P} (φ : @qmor U V f E F) (M : qquiv F P).

  Definition qp : qquiv E (P ∘ f) :=
    fun u v e p q => M (f u) (f v) (φ u v e) p q.

  Definition qpm : qqmor f φ (fun u (p : (P∘f) u) => p) qp M :=
    qqid.

  Context {Q X} {π : forall u, Q u -> P (f u)} (ξ : qqmor f φ π X M).

  Definition qpu : qqmor _ qid π X qp :=
    fun u v e p q m => ξ u v e p q m.

  Lemma qpu_spec :
    qpm @@ ξ = qpu.
  Proof.
    reflexivity.
  Qed.
End QP.

(** ** Lifting *)

Section QF.
  Context {U V f E F P} (φ : @qmor U V f E F) (M : qquiv E P).

  Variant qfp : V -> Type :=
    | qfpm : forall u, P u -> qfp (f u).

  Variant qf : qquiv F qfp :=
    | qfm : qqmor f φ qfpm M qf.

  Context {Q X} {π : forall u, P u -> Q (f u)} (ξ : qqmor f φ π M X).

  Definition qfup : forall v, qfp v -> Q v :=
    fun _ '(qfpm u p) => π u p.

  Definition qfu : qqmor _ qid qfup qf X :=
    fun _ _ _ _ _ '(qfm u v e p q m) => ξ u v e p q m.

  Lemma qfu_spec :
    qfu @@ qfm = ξ.
  Proof.
    reflexivity.
  Qed.
End QF.