Require Import FunctionalExtensionality.
Require Import Classical.
From coqrel Require Import LogicalRelations OptionRel.
From structures Require Import
  Poset
  Lattice
  Effects
  Monad.
From lattices Require Import
  Downset
  Upset
  FCD
  LatticeProduct.
Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ClassicalChoice.

(** * Preliminaries *)

(** The following [Proper] instance enables rewriting under binders
  for infinitary operations like [sup] and [inf]. *)

Instance bigop_eq {I A B} (f : (I -> A) -> B) :
  Proper (pointwise_relation I eq ==> eq) f.
Proof.
  intros x y Hxy.
  apply functional_extensionality in Hxy.
  congruence.
Qed.

(* TODO: how to express the following lemmas in a cleaner way, like using a
   Proper class:

   Proper ((pointwise_relation _ eq) ++> eq ++> eq) (@FCD.ext C L).  *)
Section EXT_PROPER.
  Context {C: poset} {L: cdlattice} (f1 f2: C -> L) `{!PosetMorphism f1} `{!PosetMorphism f2}.

  Lemma ext_proper_eq:
    forall (x: FCD.F C) (EQ: forall c, f1 c = f2 c),
      FCD.ext f1 x = FCD.ext f2 x.
  Proof.
    intros x EQ.
    edestruct (FCD.join_meet_dense x) as (I & J & c & Hc). subst.
    rewrite !Sup.mor. setoid_rewrite Inf.mor.
    setoid_rewrite FCD.ext_ana.
    f_equal. apply functional_extensionality. intros i.
    f_equal. apply functional_extensionality. intros j.
    apply EQ.
  Qed.

  Lemma ext_proper_ref':
    forall (x: FCD.F C) (REF: forall c, f1 c [= f2 c),
      FCD.ext f1 x [= FCD.ext f2 x.
  Proof.
    intros x REF.
    edestruct (FCD.join_meet_dense x) as (I & J & c & Hc). rewrite Hc.
    setoid_rewrite Sup.mor. setoid_rewrite Inf.mor.
    setoid_rewrite @FCD.ext_ana; eauto.
    apply sup_iff. intros i. apply (sup_at i).
    apply inf_iff. intros j. apply (inf_at j).
    apply REF.
  Qed.

  Lemma ext_proper_ref:
    forall (x1 x2: FCD.F C) (FREF: forall c, f1 c [= f2 c) (XREF: x1 [= x2),
      FCD.ext f1 x1 [= FCD.ext f2 x2.
  Proof.
    intros. etransitivity.
    - apply ext_proper_ref'; eauto.
    - rauto.
  Qed.
End EXT_PROPER.
(*
(** The discrete poset on a set, currently unused. *)

Module Discrete.

  Record t A := emb { elt : A }.
  Arguments emb {A} _.
  Arguments elt {A} _.

  Instance poset A : Poset (t A) :=
    {
      ref := eq;
    }.
  Proof.
    abstract firstorder.
  Defined.

  Definition ext {A B} (f : A -> B) : t A -> B :=
    fun x => f (elt x).

  Instance mor {A B} `{!Poset B} (f : t A -> B) :
    PosetMorphism f.
  Proof.
    constructor. cbn. rauto.
  Qed.

End Discrete.
*)


(*
(** * Lattice interpretations of effect signature *)

Program Instance option_poset A : Poset (option A) :=
  {
    ref := option_le eq;
  }.
Next Obligation.
  split; typeclasses eauto.
Qed.
Next Obligation.
  intros x y Hxy Hyx.
  destruct Hxy; inversion Hyx; congruence.
Qed.

Class Interp (E : esig) (D : Type) :=
  {
    interp_cdl :> CDLattice D;
    eval : forall {ar}, E ar -> option (ar -> D) -> D;

    eval_sup {ar I} (m : E ar) (k : I -> option (ar -> D)) :
      eval m (fun n => ⋁ i:I; k i n) = ⋁ i:I; eval m (k i);
    eval_inf {ar I} (m : E ar) (k : I -> option ar -> D) :
      eval m (fun n => ⋀ i:I; k i n) = ⋀ i:I; eval m (k i);
  }.

Class InterpMorphism {E : esig} {A B} `{Interp E A} `{Interp E B} (f : A -> B) :=
  {
    int_mor :> CDL.Morphism f;
    eval_mor {ar} (m : E ar) (k : option ar -> A) `{!PosetMorphism k} :
      f (eval m k) = eval m (fun n => f (k n));
  }.
*)


(** * Free interpretation *)

Module ISpec.

  Ltac depsubst :=
    subst;
    lazymatch goal with
      | H : existT _ ?x _ = existT _ ?x _ |- _ =>
        apply inj_pair2 in H; depsubst
      | _ =>
        idtac
    end.

  Inductive play {E : esig} {V} :=
    | pret (v : V)
    | pmove {X} (m : E X)
    | pcons {X} (m : E X) (n : X) (s : play).

  Arguments play : clear implicits.

  Inductive pref {E : esig} {V} : relation (play E V) :=
    | pret_ref (v : V) :
        pref (pret v) (pret v)
    | pmove_ref {N} (m : E N) :
        pref (pmove m) (pmove m)
    | pmove_cons_ref {N} (m : E N) (n : N) (s : play E V) :
        pref (pmove m) (pcons m n s)
    | pcons_ref {N} (m : E N) (n : N) (s t : play E V) :
        pref s t -> pref (pcons m n s) (pcons m n t).

  Instance pref_preo (E : esig) V :
    PreOrder (@pref E V).
  Proof.
    split.
    - intros p.
      induction p; constructor; auto.
    - intros p1 p2 p3 Hp12. revert p3.
      induction Hp12; inversion 1; depsubst; constructor; auto.
  Qed.

  Instance pref_antisym (E : esig) V :
    Antisymmetric (play E V) eq pref.
  Proof.
    intros p1 p2 Hp12 Hp21.
    induction Hp12; inversion Hp21; depsubst; try congruence.
    - apply IHHp12 in H0. congruence.
  Qed.

  Canonical Structure play_poset E V : poset :=
    {|
      ref := @pref E V;
    |}.

  (*
  (** ** Free interpretation *)

  Program Instance ti E V : Interp E (t E V) :=
    {
      eval ar m k :=
        FCD.emb (pmove m) ⊔
        ⋁ n; FCD.ext (fun s => FCD.emb (pmove m n s)) (k n);
    }.

  Next Obligation.
    apply join_ub_l.
  Qed.

  Next Obligation.
    apply antisymmetry.
    - apply join_lub.
  Admitted.

  Next Obligation.
    rewrite <- @Inf.mor. f_equal.
  Admitted.
   *)

  (** ** Monad *)

  Definition t E V :=
    FCD.F (play_poset E V).

  Definition ret {E A} (a : A) : t E A :=
    FCD.emb (pret a).

  Fixpoint pbind {E A B} (f : A -> t E B) (p : play E A) : t E B :=
    match p with
      | pret a => f a
      | pmove m =>
        FCD.emb (pmove m)
      | pcons m n q =>
        FCD.emb (pmove m) ||
        FCD.ext (fun s => FCD.emb (pcons m n s)) (pbind f q)
    end.

  Global Instance pbind_mor E A B (f : A -> t E B):
    PosetMorphism (pbind f).
  Proof.
    constructor. intros x y Hxy.
    induction Hxy; cbn; try rauto.
    - apply join_ub_l.
    - apply join_lub.
      + apply join_ub_l.
      + apply join_r. rauto.
  Qed.

  Definition bind {E A B} (f : A -> t E B) : t E A -> t E B :=
    FCD.ext (pbind f).

  Instance bind_mor {E A B} (f : A -> t E B) :
    CDL.Morphism (bind f).
  Proof.
    unfold bind. typeclasses eauto.
  Qed.

  Instance bind_mor_params :
    Params (@bind) 1.
  Defined.

  Instance pcons_mor {E A B} (m: E A) (n: A):
    PosetMorphism (fun s : play E B => FCD.emb (pcons m n s)).
  Proof.
    split. intros x y Hxy. rstep. constructor. apply Hxy.
  Qed.

  Global Instance pbind_proper_ref {E A B}:
    Proper ((pointwise_relation _ ref) ++> ref ++> ref) (@pbind E A B).
  Proof.
    intros f g H x y Hx. induction Hx; cbn.
    - apply H.
    - reflexivity.
    - apply join_l. reflexivity.
    - apply join_lub.
      + apply join_l. reflexivity.
      + apply join_r. now rstep.
  Qed.

  Global Instance pbind_proper_eq {E A B}:
    Proper ((pointwise_relation _ eq) ++> eq ++> eq) (@pbind E A B).
  Proof.
    intros f g H x y Hx. induction Hx; cbn. induction x; cbn.
    - apply H.
    - reflexivity.
    - f_equal. rewrite IHx. reflexivity.
  Qed.

  Global Instance bind_proper_eq {E A B}:
    Proper ((pointwise_relation _ eq) ++> eq ++> eq) (@bind E A B).
  Proof.
    intros f g H x y <-.
    unfold bind. eapply ext_proper_eq; try typeclasses eauto.
    intros c. f_equal. apply functional_extensionality. apply H.
  Qed.

  Global Instance bind_proper_ref {E A B}:
    Proper ((pointwise_relation _ ref) ++> ref ++> ref) (@bind E A B).
  Proof.
    intros f g H x y Hx.
    unfold bind. eapply ext_proper_ref; try typeclasses eauto; eauto.
    intros c. induction c; cbn.
    - apply H.
    - reflexivity.
    - apply join_lub.
      + apply join_l. reflexivity.
      + apply join_r. now rstep.
  Qed.

  Lemma bind_ret_r {E A B} (a : A) (f : A -> t E B) :
    bind f (ret a) = f a.
  Proof. now setoid_rewrite FCD.ext_ana. Qed.

  Lemma pbind_ret_l {E A} :
    pbind (@ret E A) = FCD.emb.
  Proof.
    apply functional_extensionality. intros s.
    induction s; cbn; auto.
    rewrite IHs. rewrite FCD.ext_ana.
    apply ref_join. rstep. constructor.
  Qed.

  Lemma bind_ret_l {E A} (x : t E A) :
    bind ret x = x.
  Proof.
    unfold bind. rewrite pbind_ret_l.
    apply FCD.ext_emb.
  Qed.

  Lemma bind_pbind {E A B C} (g : B -> t E C) (f : A -> t E B) (x : play E A) :
    bind g (pbind f x) = pbind (fun a => bind g (f a)) x.
  Proof.
    unfold bind. induction x; cbn; eauto.
    - rewrite FCD.ext_ana. reflexivity.
    - rewrite Sup.mor_join. rewrite FCD.ext_ana. cbn.
      rewrite <- IHx. unfold t.
      rewrite !FCD.ext_ext.
      (* setoid_rewrite FCD.ext_ana. *)
      erewrite @ext_proper_eq. 4: { intros c. rewrite FCD.ext_ana. reflexivity. }
      + cbn. apply ext_join.
        split. intros a b Hab. rstep.
        now apply pbind_mor.
      + split. intros a b Hab. repeat rstep. now constructor.
      + split. intros a b Hab. cbn.
        apply join_lub.
        * apply join_l. reflexivity.
        * apply join_r. rstep.
          induction Hab; cbn; try reflexivity.
          -- apply join_l. reflexivity.
          -- apply join_lub.
             ++ apply join_l. reflexivity.
             ++ apply join_r. rstep. eauto.
  Qed.

  Lemma bind_bind {E A B C} (g : B -> t E C) (f : A -> t E B) (x : t E A) :
    bind g (bind f x) = bind (fun a => bind g (f a)) x.
  Proof.
    unfold bind, t. rewrite FCD.ext_ext.
    f_equal. apply functional_extensionality. intros p.
    apply bind_pbind.
  Qed.

  (** ** Interaction *)

  (** The interaction primitive triggers one of the actions from the
    signature and returns the environment's response. *)

  Definition int {E ar} (m : E ar) : t E ar :=
    sup k : option ar,
      match k with
        | Some n => FCD.emb (pcons m n (pret n))
        | None   => FCD.emb (pmove m)
      end.

  (** Morphisms between two effect signatures are substitutions,
    which give an interaction specification in [E] for each possible
    operation in [F]. *)

  Definition subst (E F : esig) : cdlattice :=
    pi ar, t E ar ^ F ar.

  (** To apply a substitution [f : E -> F] to an interaction
    specification in [F], we replace each move [m] by the
    corresponding interaction as given by [f m]. *)

  Fixpoint papply {E F A} (f : subst E F) (s : play F A) : t E A :=
    match s with
      | pret a => FCD.emb (pret a)
      | pmove m => bind (fun _ => bot) (f _ m)
      | pcons m n t => bind (fun n' => sup H : n' = n, papply f t) (f _ m)
    end.

  Global Instance papply_mor {E F A} (f : subst E F) :
    PosetMorphism (@papply E F A f).
  Proof.
    constructor. intros s t Hst.
    induction Hst; cbn in *; try rauto.
    - edestruct (FCD.join_meet_dense (f N m)) as (I & J & c & H). rewrite H.
      rewrite Sup.mor. apply sup_lub. intros i.
      rewrite Sup.mor. apply (sup_at i).
      rewrite Inf.mor. setoid_rewrite Inf.mor.
      apply inf_glb. intros j. apply (inf_at j).
      unfold bind. rewrite !FCD.ext_ana.
      induction (c i j); cbn.
      + apply bot_lb.
      + reflexivity.
      + apply join_lub; [apply join_l | apply join_r]; rauto.
    - edestruct (FCD.join_meet_dense (f N m)) as (I & J & c & H). rewrite H.
      rewrite Sup.mor. apply sup_lub. intros i.
      rewrite Sup.mor. apply (sup_at i).
      rewrite Inf.mor. setoid_rewrite Inf.mor.
      apply inf_glb. intros j. apply (inf_at j).
      unfold bind. rewrite !FCD.ext_ana.
      induction (c i j); cbn.
      + apply sup_lub. intros Hv. apply (sup_at Hv). auto.
      + reflexivity.
      + apply join_lub; [apply join_l | apply join_r]; rauto.
  Qed.

  Definition apply {E F A} (f : subst E F) : t F A -> t E A :=
    FCD.ext (papply f).

  Instance apply_mor {E F A} (f : subst E F) :
    CDL.Morphism (@apply E F A f).
  Proof.
    unfold apply. typeclasses eauto.
  Qed.

  Instance apply_mor_params :
    Params (@apply) 1.
  Defined.

  Definition compose {E F G} (g : subst F G) (f : subst E F) : subst E G :=
    fun ar m => apply f (g ar m).

  (** Properties of [apply]. *)

  Lemma apply_ret {E F A} (f : subst E F) (a : A) :
    apply f (ret a) = ret a.
  Proof.
    unfold apply, ret. rewrite FCD.ext_ana. cbn. auto.
  Qed.

  Lemma apply_fmap_cons {E F A X} (f: subst E F) m (n: X) (t: t F A):
    bind (fun _ => bot) (f _ m) || apply f (FCD.map (pcons m n) t) = bind (fun n' => sup _ : n' = n, apply f t) (f _ m).
  Proof.
    apply antisymmetry.
    - apply join_lub.
      + apply bind_proper_ref.
        * intros x. apply bot_lb.
        * reflexivity.
      + unfold FCD.map, apply, bind.
        edestruct (FCD.join_meet_dense t) as (I & J & c & Hc). subst t.
        repeat setoid_rewrite Sup.mor.
        repeat setoid_rewrite Inf.mor.
        setoid_rewrite FCD.ext_ana.
        setoid_rewrite FCD.ext_ana. cbn.
        unfold bind.
  Admitted.

  Lemma apply_bind {E F A B} (f : subst E F) (g : A -> t F B) (x : t F A) :
    apply f (bind g x) = bind (fun a => apply f (g a)) (apply f x).
  Proof.
    unfold apply, bind, t. rewrite !FCD.ext_ext.
    f_equal. apply functional_extensionality. intros p.
    induction p; cbn.
    - rewrite FCD.ext_ana. reflexivity.
    - rewrite FCD.ext_ana. cbn.
      unfold bind, t. rewrite FCD.ext_ext. f_equal.
      apply functional_extensionality. intros p.
      setoid_rewrite bind_pbind. f_equal.
      apply functional_extensionality. intros xx.
      Local Transparent bot.
      unfold bind, bot.
      rewrite (proj1 FCD.ext_mor). f_equal.
      apply functional_extensionality. intros [].
    - rewrite Sup.mor_join. rewrite FCD.ext_ana. cbn.
      setoid_rewrite bind_bind. unfold bind at 3.
      setoid_rewrite Sup.mor. setoid_rewrite <- IHp. clear IHp.
      setoid_rewrite apply_fmap_cons. reflexivity.
  Qed.

  Lemma apply_int_r {E F ar} (m : F ar) (f : subst E F) :
    apply f (int m) = f ar m.
  Proof.
    unfold apply, int.
    rewrite Sup.mor.
    edestruct (FCD.join_meet_dense (f ar m)) as (I & J & c & H).
    apply antisymmetry.
    - eapply sup_lub. intros i.
      destruct i; rewrite FCD.ext_ana; cbn.
      + rewrite H.
        setoid_rewrite Sup.mor. apply sup_lub. intros i. apply (sup_at i).
        setoid_rewrite Inf.mor. apply inf_glb. intros j. apply (inf_at j).
        unfold bind. rewrite FCD.ext_ana.
        induction (c i j); cbn.
        * apply sup_lub. intro. subst. reflexivity.
        * reflexivity.
        * apply join_lub.
          -- rstep. constructor.
          -- rewrite IHp. rewrite @FCD.ext_ana. reflexivity.
             constructor. repeat rstep. constructor. auto.
      + rewrite H.
        setoid_rewrite Sup.mor. apply sup_lub. intros i. apply (sup_at i).
        setoid_rewrite Inf.mor. apply inf_glb. intros j. apply (inf_at j).
        unfold bind. rewrite FCD.ext_ana.
        induction (c i j); cbn.
        * apply bot_lb.
        * reflexivity.
        * apply join_lub.
          -- rstep. constructor.
          -- rewrite IHp. rewrite @FCD.ext_ana. reflexivity.
             constructor. repeat rstep. constructor. auto.
  Admitted.

  Lemma apply_int_l {E A} (x : t E A) :
    apply (@int E) x = x.
  Proof.
    unfold apply, int. symmetry.
    change x with ((fun x => x) x) at 1.
    apply FCD.ext_unique.
    - admit. (* identity morphism *)
    - intros s.
      induction s; cbn.
      + reflexivity.
      + rewrite Sup.mor. unfold bind.
        apply antisymmetry.
        * apply (sup_at None).
          rewrite FCD.ext_ana. cbn.
          reflexivity.
        * apply sup_lub. intros i.
          destruct i; rewrite FCD.ext_ana; cbn.
          -- apply join_lub.
             ++ reflexivity.
             ++ Transparent bot. unfold bot. rewrite Sup.mor.
                apply sup_lub. intros [ ].
          -- reflexivity.
      +
  Admitted.

  Lemma apply_assoc {E F G A} (f : subst E F) (g : subst F G) (x : t G A) :
    apply f (apply g x) = apply (compose g f) x.
  Proof.
    unfold apply, compose.
    rewrite @FCD.ext_ext by typeclasses eauto.
    f_equal. apply functional_extensionality. intros s.
    induction s; cbn.
    - rewrite FCD.ext_ana. reflexivity.
    - unfold bind, apply. rewrite !@FCD.ext_ext by typeclasses eauto.
      f_equal. apply functional_extensionality. intros s.
      induction s; cbn.
      + rewrite FCD.ext_ana. cbn. admit.
      + rewrite FCD.ext_ana. cbn.
        unfold bind. rewrite @FCD.ext_ext by typeclasses eauto.
        f_equal. apply functional_extensionality. intros s.
        induction s; cbn.
        * admit. (* ext preserves bot *)
        * rewrite FCD.ext_ana. cbn. reflexivity.
        * admit. (* ext preserves join *)
      + admit.
    - admit.
  Admitted.

  (** Properties of [compose] *)

  Lemma compose_int_l {E F} (f : subst E F) :
    compose (@int F) f = f.
  Proof.
    unfold compose.
    apply functional_extensionality_dep; intros ar.
    apply functional_extensionality_dep; intros m.
    apply apply_int_r.
  Qed.

  Lemma compose_int_r {E F} (f : subst E F) :
    compose f (@int E) = f.
  Proof.
    unfold compose.
    apply functional_extensionality_dep; intros ar.
    apply functional_extensionality_dep; intros m.
    apply apply_int_l.
  Qed.

  Lemma compose_assoc {E F G H} (f : subst E F) (g : subst F G) (h : subst G H) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    unfold compose.
    apply functional_extensionality_dep; intros ar.
    apply functional_extensionality_dep; intros m.
    apply apply_assoc.
  Qed.

  Instance compose_proper_ref {A B C}:
    Proper (ref ++> ref ++> ref) (@compose A B C).
  Proof.
    intros f1 f2 Hf g1 g2 Hg. unfold compose.
    intros ar m. unfold apply.
    apply ext_proper_ref; try typeclasses eauto.
    - intros c. induction c; cbn.
      + reflexivity.
      + unfold bind. rstep. apply Hg.
      + unfold bind.
        apply ext_proper_ref; try typeclasses eauto.
        * intros p. apply pbind_proper_ref. intros x.
          apply sup_iff. intros xn. now apply (sup_at xn).
          reflexivity.
        * apply Hg.
    - apply Hf.
  Qed.

  Definition identity {E: esig}: subst E E := fun _ m => int m.

  Lemma compose_unit_l {E F} (f: subst E F):
    compose identity f = f.
  Proof.
    unfold ISpec.compose, identity.
    apply functional_extensionality_dep. intros ar.
    apply functional_extensionality_dep. intros m.
    apply apply_int_r.
  Qed.

  Lemma compose_unit_r {E F} (f: subst E F):
    compose f identity = f.
  Proof.
    unfold ISpec.compose, identity.
    apply functional_extensionality_dep. intros ar.
    apply functional_extensionality_dep. intros m.
    apply apply_int_l.
  Qed.

End ISpec.

Notation ispec := ISpec.t.

(** * Notations and Rewriting Tactic *)

Infix "~>" := ISpec.subst (at level 99).

Notation "x >>= f" := (ISpec.bind f x)
  (at level 40, left associativity).

Notation "v <- x ; M" := (x >>= fun v => M)
  (at level 65, right associativity).

Notation "x / f" := (ISpec.apply f x).

(* Infix "@" := ISpec.compose (at level 40, left associativity). *)
Infix "@" := ISpec.compose (at level 30, right associativity).

Hint Rewrite
  @ISpec.bind_ret_l
  @ISpec.bind_ret_r
  @ISpec.bind_bind
  @ISpec.apply_ret
  @ISpec.apply_bind
  @ISpec.apply_int_l
  @ISpec.apply_int_r
  : intm.

Ltac intm :=
  repeat progress (autorewrite with intm; cbn).

(** * State  *)

Import ISpec.

(** ** Keeping track of state *)

(** To interpret layer interfaces as morphisms in our category of
  effect signatures and substitution specifications, we use the
  following signature which adjoins a state in [S] to the operations
  and arities of the signature [E]. This is written [E@S] in the paper
  but since I plan on using [@] for composition I use [E#S] here. *)

Inductive est {S: Type} : esig :=
| est_intro: S -> est S.
Arguments est : clear implicits.

Definition state_sig (E : esig) (S : Type) : esig := E * est S.
Definition st {E S X} (m : E X) (k : S) : state_sig E S (X * S)%type :=
  (m * (est_intro k))%event.

Infix "#" := state_sig (at level 40, left associativity) : esig_scope.
Infix "#" := st (at level 40, left associativity).

(** To connect this with layer implementations, we must lift a
  state-free morphism [M : E ~> F] to a corresponding stateful
  morphism [E#S ~> F#S] which passes the state around unchanged. *)

Fixpoint stateful_play {E S A} (k: S) (s: play E A): t (E # S) (A * S) :=
  match s with
    | pret v => FCD.emb (pret (v, k))
    | pmove m => FCD.emb (pmove (st m k))
    | pcons m n t =>
      sup x : option S,
      match x with
      | Some k' => FCD.map (pcons (st m k) (n, k')) (stateful_play k' t)
      | None => FCD.emb (pmove (st m k))
      end
  end.

Instance stateful_play_mor E S A k :
  PosetMorphism (@stateful_play E S A k).
Proof.
  constructor. intros s t Hst. revert k.
  induction Hst; cbn; intro.
  - reflexivity.
  - reflexivity.
  - apply (sup_at None). reflexivity.
  - apply sup_lub. intro x. apply (sup_at x). repeat rstep.
    unfold FCD.map. repeat rstep. auto.
Qed.

Definition srun {E S A} (k : S) (x : t E A) : t (E # S) (A * S) :=
  FCD.ext (stateful_play k) x.

Instance srun_mor {E S A} (s: S) :
  CDL.Morphism (@srun E S A s).
Proof.
  unfold srun. split.
  - intros x y. rewrite Sup.mor. reflexivity.
  - intros x y. rewrite Inf.mor. reflexivity.
Qed.

Definition slift {E F S} (σ : E ~> F) : E#S ~> F#S :=
  fun ar '(etens_intro m k) =>
    match k with
    | est_intro s => srun s (σ _ m)
    end.

(** ** Properties *)

Lemma srun_slift {E F S A} (k : S) (x : t F A) (σ : E ~> F) :
  srun k x / slift σ = srun k (x / σ).
Proof.
  unfold srun, apply.
  rewrite !@FCD.ext_ext by typeclasses eauto. f_equal.
  apply functional_extensionality. intros s.
  induction s; cbn.
  - rewrite !FCD.ext_ana. cbn.
    reflexivity.
  - rewrite !FCD.ext_ana. cbn.
    unfold srun, bind.
    rewrite !@FCD.ext_ext by typeclasses eauto. f_equal.
    apply functional_extensionality. intros s.
    induction s; cbn.
    + rewrite FCD.ext_ana. cbn.
      admit. (* rewrite Downset.Sup.mor_bot *)
    + rewrite !FCD.ext_ana. cbn. reflexivity.
    + rewrite Downset.Sup.mor.
      rewrite Downset.Sup.mor_join.
      apply antisymmetry.
      * apply sup_lub. intros [k' | ].
        -- apply join_r. unfold FCD.map.
           rewrite !@FCD.ext_ext; try typeclasses eauto.
           ++ repeat setoid_rewrite FCD.ext_ana. cbn.
Admitted.

Lemma srun_bind {E S A B} (k : S) (f : A -> t E B) (x : t E A) :
  srun k (bind f x) = bind (fun '(a, k') => srun k' (f a)) (srun k x).
Admitted.

Lemma srun_int {E S ar} (k : S) (m : E ar) :
  srun k (int m) = int (st m k).
Admitted.

Lemma slift_identity {E S}:
  slift (S:=S) (identity (E:=E)) = identity.
Proof.
  unfold identity. extensionality x. extensionality mk.
  destruct mk as [? ? m [k]]. apply srun_int.
Qed.

Lemma slift_compose {E F G S} (f: F ~> G) (g: E ~> F):
  slift (S:=S) (f @ g) = slift f @ slift g.
Proof.
  unfold slift. extensionality x. extensionality mk.
  destruct mk as [? ? m [k]].
  unfold compose. rewrite <- srun_slift. reflexivity.
Qed.

Instance slift_proper_ref {E F S}:
  Proper (ref ==> ref) (@slift E F S).
Proof.
  intros x y Hxy. intros ? mk. destruct mk as [? m k]. cbn.
  unfold srun. destruct e. rstep. apply Hxy.
Qed.

Instance map_mor {A B: poset} (f: A -> B) :
  CDL.Morphism (@FCD.map A B f).
Proof. unfold FCD.map. typeclasses eauto. Qed.

(** ** Rewriting tactic *)

Hint Rewrite
  @srun_bind
  @srun_int
  : intm.

(** * Assert & Assume *)

Definition assert {E : esig} (P : Prop) : ispec E unit :=
  sup H : P, ISpec.ret tt.

Lemma assert_true {E} {P : Prop} (H : P) :
  @assert E P = ret tt.
Proof.
  unfold assert.
  apply antisymmetry.
  - apply sup_lub. reflexivity.
  - apply (sup_at H). reflexivity.
Qed.

Lemma assert_l {E A} (P : Prop) (x y : ispec E A) :
  (P -> x [= y) ->
  _ <- assert P; x [= y.
Proof.
  intros H. unfold assert.
  rewrite Sup.mor. apply sup_lub. intros HP.
  intm. auto.
Qed.

Lemma assert_r {E A} (P : Prop) (x y : ispec E A) :
  x [= y -> P ->
  x [= _ <- assert P; y.
Proof.
  intros Hxy HP.
  rewrite assert_true; intm; auto.
Qed.

Definition assume {E : esig} (P : Prop) : ispec E unit :=
  inf H : P, ret tt.

Lemma assume_l {E A} (P : Prop) (x y : ispec E A) :
  x [= y -> P ->
  _ <- assume P; x [= y.
Proof.
  intros Hxy HP. unfold assume.
  rewrite Inf.mor. eapply (inf_at HP).
  setoid_rewrite FCD.ext_ana. apply Hxy.
Qed.

Lemma assume_r {E A} (P : Prop) (x y : ispec E A) :
  (P -> x [= y) ->
  x [= _ <- assume P; y.
Proof.
  intros H. unfold assume.
  rewrite Inf.mor. eapply inf_glb. intros HP.
  setoid_rewrite FCD.ext_ana. eauto.
Qed.

Hint Rewrite @assert_true using solve [auto] : intm.

(** Misc *)
Import ISpec.
Lemma fmap_cons {E A B X} (f: A -> t E B) m (n: X) (t: t E A):
  bind f (FCD.ext (fun s => FCD.emb (pcons m n s)) t) [=
    FCD.emb (pmove m) || FCD.ext (fun s => FCD.emb (pcons m n s)) (bind f t).
Proof.
  unfold bind.
  edestruct (FCD.join_meet_dense t) as (I & J & c & Hc). rewrite Hc.
  rewrite !Sup.mor. repeat setoid_rewrite Inf.mor.
  setoid_rewrite FCD.ext_ana. setoid_rewrite FCD.ext_ana. cbn.
  apply sup_iff. intros i. rewrite <- join_inf.
  apply join_lub.
  - apply join_l. reflexivity.
  - apply join_r. apply (sup_at i). reflexivity.
Qed.
