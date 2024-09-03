Require Import structures.Effects.

Set Asymmetric Patterns.
(* Set Universe Polymorphism. *)

Record Cat := {
    obj :> Type;
    mor : obj -> obj -> Type;

    id : forall {A}, mor A A;
    compose : forall {A B C}, mor B C -> mor A B -> mor A C;
  }.
Arguments id {_} _.
Arguments compose {_ _ _ _} _ _.
Infix " ∘ " := compose (at level 40, left associativity).

Definition Set_cat : Cat :=
  {|
    obj := Type;
    mor := fun A B => A -> B;
    id := fun A x => x;
    compose := fun A B C f g x => f (g x);
  |}.

Record Functor (C D: Cat) := {
  obj_map :> obj C -> obj D;
  mor_map : forall {A B}, mor C A B -> mor D (obj_map A) (obj_map B);
  mor_map_id : forall {A}, mor_map (@id C A) = @id D (obj_map A);
  mor_map_compose : forall {X Y Z} (f: mor C X Y) (g: mor C Y Z),
      mor_map (g ∘ f) = mor_map g ∘ mor_map f;
  }.
Arguments obj_map {_ _} _ _.
Arguments mor_map {_ _} _ {_ _} _.

Inductive effect (E: esig) (A: Type) : Type :=
  | run : forall {X: Type}, E X -> (X -> A) -> effect E A.
Arguments run {_ _ _} _ _.
Definition effect_fmap {E: esig} {A B: Type}
  (f: A -> B) (e: effect E A): effect E B :=
  match e with run _ m k => run m (fun x => f (k x)) end.

Program Definition Effect_functor E: Functor Set_cat Set_cat :=
  {|
    obj_map := effect E;
    mor_map := fun A B f => effect_fmap f;
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

Inductive free (E: esig) (A: Type) :=
  | ret : A -> free E A
  | op : forall {R: Type}, E R -> (R -> free E A) -> free E A.
Arguments ret {_ _} _.
Arguments op {_ _ _} _ _.
Fixpoint free_fmap {E: esig} {A B: Type} (f: A -> B) (x: free E A): free E B :=
  match x with
  | ret a => ret (f a)
  | op _ e k => op e (fun x => free_fmap f (k x))
  end.

Program Definition Free_functor {E: esig} : Functor Set_cat Set_cat :=
  {|
    obj_map := free E;
    mor_map := fun A B f => free_fmap f;
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

Record Alg {C: Cat} (F: Functor C C) := {
  carrier :> obj C;
  alpha :> mor C (F carrier) carrier;
  }.
Arguments carrier {_ _} _.
Arguments alpha {_ _} _.

Definition free_alpha (E: esig) (A: Type)
  (e: effect E (free E A)): free E A :=
  match e with run _ m k => op m k end.

Program Definition free_alg (E: esig) (A: Type): Alg (Effect_functor E) :=
  {|
    carrier := free E A;
    alpha := free_alpha E A;
  |}.

Definition forget_alg (E: esig) (A: Alg (Effect_functor E)) : Type :=
  carrier A.

Record Alg_hom {C: Cat} (F: Functor C C) (A B: Alg F) := {
    f : mor C A B;
    f_preserves : f ∘ A = B ∘ mor_map F f;
  }.
Arguments f {_ _ _ _} _.

Class Initial_alg {C: Cat} {F: Functor C C} (A: Alg F) := {
  initial : forall B, Alg_hom F A B;
  initial_unique : forall B (h: Alg_hom F A B),
      h = initial B;
  }.

Fixpoint cata {E: Type -> Type} (B: Alg (Effect_functor E))
  (t: free E Empty_set): carrier B :=
  match t with
  | ret a => match a with end
  | op _ e k => alpha B (run e (fun x => cata B (k x)))
  end.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Program Instance free_initial {E: Type -> Type} : Initial_alg (free_alg E Empty_set) :=
  {|
    initial B := {| f := cata B; |};
  |}.
Next Obligation.
  (* algebra homomorphism *)
  extensionality e. destruct e. cbn. reflexivity.
Qed.
Next Obligation.
  (* uniqueness *)
  destruct h. cbn in *.
  assert (f0 = cata B).
  { extensionality x. induction x.
    - destruct a.
    - cbn. setoid_rewrite <- H.
      apply equal_f with (x := (run e f1)) in f_preserves0.
      cbn in f_preserves0. apply f_preserves0. }.
  subst f0. f_equal.
  apply proof_irrelevance.
Qed.

Definition effect' (E: esig) (X: Type) (A: Type): Type := effect E A + X.

Definition effect'_fmap {E: esig} {X A B: Type}
  (f: A -> B) (e: effect' E X A): effect' E X B :=
  match e with inl i => inl (effect_fmap f i) | inr x => inr x end.

Program Definition Effect'_functor E (X: Type): Functor Set_cat Set_cat :=
  {|
    obj_map := effect' E X;
    mor_map A B := effect'_fmap;
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition free'_alpha (E: esig) (X: Type)
  (e: effect' E X (free E X)): free E X :=
  match e with
  | inl i => free_alpha E X i
  | inr x => ret x
  end.

Program Definition free'_alg (E: esig) (X: Type): Alg (Effect'_functor E X) :=
  {|
    carrier := free E X;
    alpha := free'_alpha E X;
  |}.

Fixpoint cata' {E: Type -> Type} (X: Type) (B: Alg (Effect'_functor E X))
  (t: free E X): carrier B :=
  match t with
  | ret a => alpha B (inr a)
  | op _ e k => alpha B (inl (run e (fun x => cata' X B (k x))))
  end.

Program Instance free'_initial {E: Type -> Type} (X: Type) : Initial_alg (free'_alg E X) :=
  {|
    initial B := {| f := cata' X B; |};
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

(* --- Isomorphisms --- *)

(* ----------------------------------------------------------------------- *)

(* The isomorphisms give the adjunction *)
(* Definition iso_alg1 (E: esig) (C: Type) (D: Alg E) *)
(*                     (h: Alg_hom E (free_alg E C) D) : C -> forget_alg E D := *)
(*   fun x => (f h) (ret x). *)

(* This is also the co-unit, I guess *)
(* Fixpoint iso_alg2' {E: esig} {C: Type} {D: Alg E} *)
(*                     (f: C -> forget_alg E D) (h: free E C): carrier D := *)
(*   match h with *)
(*   | ret a => f a *)
(*   | op _ e k => alpha D (run e (iso_alg2' f ∘ k)) *)
(*   end. *)

(* Program Definition iso_alg2 (E: esig) (C: Type) (D: Alg E) *)
(*   (f: C -> forget_alg E D) : Alg_hom E (free_alg E C) D := *)
(*   {| f := iso_alg2' f |}. *)
(* Next Obligation. Admitted. *)


Definition isomorphism {C: Cat} {A B: obj C} (f: mor C A B) (g: mor C B A) :=
  f ∘ g = id B /\ g ∘ f = id A.

(* --- Lambek's lemma --- *)

Section LAMBEK.
  Context {C: Cat} (F: Functor C C).

  Program Definition fmap_alg (A: Alg F): Alg F :=
    {|
      carrier := obj_map F A;
      alpha := mor_map F A;
    |}.

  Definition initial_inv (I: Alg F) {H: Initial_alg I}: mor C I (fmap_alg I) :=
    f (initial (fmap_alg I)).

  Lemma lambek (I: Alg F) {H: Initial_alg I} :
    isomorphism (alpha I) (initial_inv I).
  Proof.
    split; intros.
    - unfold initial_inv. admit.
    - unfold initial_inv. admit.
  Admitted.

End LAMBEK.

(* ------ CPO ------ *)

From coqrel Require Import LogicalRelations.

Record poset :=
  {
    poset_carrier :> Type;
    ref : poset_carrier -> poset_carrier -> Prop;
    ref_preo : PreOrder ref;
    ref_po : Antisymmetric poset_carrier eq ref;
  }.
Arguments ref {_}.
Delimit Scope poselt_scope with poselt.
Bind Scope poselt_scope with poset_carrier.
Notation "x [=  y" := (ref x%poselt y%poselt) (at level 70).

Definition Nat_poset : poset :=
  {| poset_carrier := nat; ref := le; |}.

Record chain (X: poset) :=
  { chain_carrier :> Nat_poset -> X;
    chain_mono : Monotonic chain_carrier (ref ++> ref);
  }.

Program Definition chain_map {X Y: poset} (f: X -> Y) (D: chain X): chain Y :=
  {| chain_carrier n := f (D n); |}.
Next Obligation. Admitted.

Record Dcpo := {
  dcpo_carrier :> poset;
  dsup : forall (D: chain dcpo_carrier), dcpo_carrier;
  dbot : dcpo_carrier;
  dsup_le : forall (D: chain dcpo_carrier), forall n, D n [= dsup D;
  dsup_lub : forall (D: chain dcpo_carrier), forall x, (forall n, D n [= x) -> dsup D [= x;
  dbot_le : forall x, dbot [= x;
  }.

Record Dcpo_hom (D E: Dcpo) := {
    dcpo_map :> D -> E;
    dcpo_map_monotonic : Monotonic dcpo_map (ref ++> ref);
    dcpo_map_continuous :
    forall (C: chain D), dcpo_map (dsup D C) = dsup E (chain_map dcpo_map C);
    dcpo_map_bottom : dcpo_map (dbot D) = dbot E;
  }.

Program Definition Dcpo_cat : Cat :=
  {|
    obj := Dcpo;
    mor := Dcpo_hom;
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition admissible {X: Dcpo} (P: X -> Prop) :=
  forall (D: chain X), (forall n, P (D n)) -> P (dsup _ D).

Section LFP.
  Context {X: Dcpo} (f: X -> X) {H: Monotonic f (ref ++> ref)}.

  Fixpoint iter (n: nat) (x: X) : X :=
    match n with
    | O => x | S n' => f (iter n' x)
    end.

  Program Definition iter_chain: chain X :=
    {| chain_carrier n := iter n (dbot X); |}.
  Next Obligation.
    intros n1 n2 Hn.
  Admitted.

  Class Lfp (x: X) :=
    {
      lfp_fixed : f x = x;
      lfp_least : forall y, f y [= y -> x [= y;
    }.

  Definition lfp: X := dsup X iter_chain.

  Instance lfp_fixed_point: Lfp lfp.
  Admitted.

  Lemma scott_induction (P: X -> Prop) :
    admissible P -> P (dbot X) -> (forall x, P x -> P (f x)) -> P lfp.
  Admitted.

End LFP.

Record Coalg {C: Cat} (F: Functor C C) := {
  coalg_carrier :> obj C;
  delta :> mor C coalg_carrier (F coalg_carrier);
  }.
Arguments coalg_carrier {_ _} _.
Arguments delta {_ _} _.

Record Coalg_hom {C: Cat} {F: Functor C C} (A B: Coalg F) := {
    g : mor C A B;
    g_preserves : B ∘ g = mor_map F g ∘ A;
  }.
Arguments g {_ _ _ _} _.

Class Final_coalg {C: Cat} {F: Functor C C} (C: Coalg F) := {
  final : forall D, Coalg_hom D C;
  final_unique : forall D (h: Coalg_hom D C),
      h = final D;
  }.

Section FINAL.
  Context (F: Functor Dcpo_cat Dcpo_cat) (I: Alg F) (H: Initial_alg I).

  Program Definition dcpo_coalg : Coalg F :=
    {|
      coalg_carrier := I;
      delta := initial_inv F I;
    |}.

  Definition ana_map (C: Coalg F) (f: mor Dcpo_cat C I): mor Dcpo_cat C I :=
    I ∘ mor_map F f ∘ C.

  Section DCPO_MOR.
    Context (X Y: Dcpo).

    Program Definition Dcpo_mor_poset : poset :=
      {|
        poset_carrier := Dcpo_hom X Y;
        ref := fun f g => forall x, f x [= g x;
      |}.
    Next Obligation. Admitted.
    Next Obligation. Admitted.

    Program Definition Dcpo_mor_dcpo : Dcpo :=
      {|
        dcpo_carrier := Dcpo_mor_poset;
        dsup := fun (D: chain Dcpo_mor_poset) =>
                  {| dcpo_map x := dsup Y (@chain_map Dcpo_mor_poset _ (fun f => f x) D); |};
        dbot := {| dcpo_map x := dbot Y |};
      |}.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.

  End DCPO_MOR.

  Instance ana_map_monotonic (C: Coalg F):
    Monotonic (ana_map C) ((@ref (Dcpo_mor_poset (coalg_carrier C) _)) ++> (@ref (Dcpo_mor_poset _ _))).
  Admitted.

  Definition ana (C: Coalg F): mor Dcpo_cat C I :=
    @lfp (Dcpo_mor_dcpo _ _) (ana_map C) _.

  (* Initial algebra and final coalgebra coindices *)
  Program Instance dcpo_coalg_final: Final_coalg dcpo_coalg :=
    {|
      final D := {| g := ana D |};
    |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

End FINAL.

Inductive free_ref (E: esig) (X: poset): free E X -> free E X -> Prop :=
  | free_ref_ret : forall x y, ref x y -> free_ref E X (ret x) (ret y)
  | free_ref_op : forall R (m: E R) k1 k2,
      (forall x, free_ref E X (k1 x) (k2 x)) ->
      free_ref E X (op m k1) (op m k2).

Program Definition free_poset (E: esig) (X: poset) : poset :=
  {|
    poset_carrier := free E X;
    ref := free_ref E X;
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

Program Definition free_dcpo (E: esig) (D: Dcpo) : Dcpo :=
  {|
    dcpo_carrier := free_poset E D;
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

(* Program Definition Effect'_dcpo_functor (E: esig) (X: Dcpo): Functor Dcpo_cat Dcpo_cat := *)
(*   {| *)
(*     obj_map := effect'_dcpo E X; *)
(*     mor_map A B := effect'_fmap E X; *)
(*   |}. *)
(* Next Obligation. Admitted. *)
(* Next Obligation. Admitted. *)

Definition free'_delta (E: esig) (X: Type) (A: free E X): effect' E X (free E X) :=
  match A with
  | ret x => inr x
  | op _ m k => inl (run m k)
  end.

Program Definition free'_coalg (E: esig) (X: Type) : Coalg (Effect'_functor E X) :=
  {|
    coalg_carrier := free E X;
    delta := free'_delta E X;
  |}.

Definition rc_rel (E F: esig) := forall ar1, E ar1 -> forall ar2, F ar2 -> (ar1 -> ar2 -> Prop) -> Prop.

Section SIM.

  Context (E1 E2: esig) (X1 X2: Type) (R: rc_rel E1 E2).
  Let I1 := free'_coalg E1 X1.
  Let I2 := free'_coalg E2 X2.

  Record sim (R_ret: X1 -> X2 -> Prop) :=
    {
      sim_rel : coalg_carrier I1 -> coalg_carrier I2 -> Prop;
      sim_ret s1 s2 r1:
        sim_rel s1 s2 -> delta I1 s1 = inr r1 -> exists r2, delta I2 s2 = inr r2 /\ R_ret r1 r2;
      sim_op s1 s2 N1 (m1: E1 N1) k1:
        sim_rel s1 s2 -> delta I1 s1 = inl (run m1 k1) ->
        exists N2 (m2: E2 N2) k2 R_k, delta I2 s2 = inl (run m2 k2) /\ R _ m1 _ m2 R_k /\
        forall n1 n2, R_k n1 n2 -> sim_rel (k1 n1) (k2 n2);
    }.

End SIM.

Module T.

    Inductive play {E : esig} {V: Type} :=
    | pret: V -> play
    | pmove: forall {X}, E X -> play
    | pcons: forall {X}, E X -> X -> play -> play.
    Arguments play: clear implicits.

    Inductive plays {E F : esig} :=
    | prun: forall {X}, F X -> play E (X * plays) -> plays.
    Arguments plays: clear implicits.

    Definition events (E: esig) := @play E unit.

    Inductive run_play {E X}: play E X -> events E -> option X -> Prop :=
    | run_pret v : run_play (pret v) (pret tt) (Some v)
    | run_pmove {X_m} (m: E X_m) : run_play (pmove m) (pmove m) None
    | run_pcons {X'} (m: E X') n p e (v: option X):
      run_play p e v ->
      run_play (pcons m n p) (pcons m n e) v.

    Inductive concat_events {E}: events E -> events E -> events E -> Prop := .

    Inductive runs {E F}: plays E F -> events F -> events E -> option (plays E F) -> Prop :=
    | runs_nil st: runs st (pret tt) (pret tt) (Some st)
    | runs_cons' {X} (m_f: F X) play_e es:
      run_play play_e es None -> runs (prun m_f play_e) (pmove m_f) es None
    | runs_cons {X} (m_f: F X) n_f play_e st_ef st_ef' es_e1 es_e2 es_e es_f:
      run_play play_e es_e1 (Some (n_f, st_ef)) ->
      runs st_ef es_f es_e2 st_ef' ->
      concat_events es_e1 es_e2 es_e ->
      runs (prun m_f play_e) (pcons m_f n_f es_f) es_e st_ef'.

    Inductive compose {E F G : esig}: plays E F -> plays F G -> plays E G -> Prop :=
    | compose_some {X} (m_g: G X) n_g play_e play_f st_ef st_ef' st_fg' st_eg' es_e es_f:
      compose st_ef' st_fg' st_eg' ->
      run_play play_f es_f (Some (n_g, st_fg')) ->
      runs st_ef es_f es_e (Some st_ef') ->
      run_play play_e es_e (Some (n_g, st_eg')) ->
      compose st_ef (prun m_g play_f) (prun m_g play_e)
    | compose_none {X} (m_g: G X) play_e play_f st_ef es_e es_f:
      run_play play_f es_f None ->
      runs st_ef es_f es_e None ->
      run_play play_e es_e None ->
      compose st_ef (prun m_g play_f) (prun m_g play_e).

    Inductive rc_play (E1 E2: esig)

End T.


Fixpoint bind {E: esig} {X Y: Type} (m: free E X) (k: X -> free E Y): free E Y :=
  match m with
  | ret x => k x
  | op _ m k' => op m (fun x => bind (k' x) k)
  end.

Definition handler (E: esig) (F: Type -> Type) (X: Type) : Type :=
  forall N (m: E N), F (N * X)%type.
(* S: E -> F *)
Inductive free_handler (E F: esig) (X: Type) : Type :=
  | free_handler_intro: (forall N (m: F N), free E (N * free_handler E F X)) -> free_handler E F X.
Arguments free_handler_intro {_ _ _} _.
Definition handle {E F: esig} {X: Type}
  (s: free_handler E F X) {N} (m: F N): free E (N * free_handler E F X) :=
  match s with free_handler_intro h => h _ m end.

Definition strategy (E F: esig) : Type := free_handler E F Empty_set.

Fixpoint subst {E F: esig} {X: Type} (s: strategy E F) (i: free F X): free E X :=
  match i with
  | ret x => ret x
  | op _ m k => bind (handle s m) (fun '(n, s') => subst s' (k n))
  end.

Program Fixpoint subst' {E F: esig} {X: Type} (s: strategy E F) (i: free F X): free E (X * strategy E F) :=
  match i with
  | ret x => ret (x, s)
  | op _ m k => bind (handle s m) (fun '(n, s') => subst' s' (k n))
  end.

Fixpoint strategy_compose {E F G: esig} (s: strategy E F) (t: strategy F G): strategy E G :=
  free_handler_intro (fun N m => bind (subst' s (handle t m)) (fun '(n, s', t') => ret (n, strategy_compose t' s' ))).

(* Inductive h (A: Type) : Type := *)
(*   | h_intro: (A -> h A) -> h A. *)

(* Inductive h2 (A: Type) : Type := *)
(*   | h2_intro: (A -> h2 A) -> h2 A. *)

(* Fixpoint h_map {A: Type} (f: A -> A) (x: h A): h2 A := *)
(*   match x with *)
(*   | h_intro g => h2_intro _ (fun x => h_map f (g x)) *)
(*   end. *)
