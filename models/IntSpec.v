Require Import coqrel.LogicalRelations.
Require Import coqrel.OptionRel.
Require Import FunctionalExtensionality.
Require Import FCD.
Require Import Monad.
Require Import Classical.
Require Import Poset.
Require Import Lattice.
Require Import Downset.
Require Import Upset.

Definition esig := Type -> Type.

Instance functional_extensionality_subrel {A B} :
  subrelation (@pointwise_relation A B eq) eq.
Proof.
  cbv. intros.
Admitted.

Instance functional_extensionality_proper {I A B} (f : (I -> A) -> B) :
  Proper (pointwise_relation I eq ==> eq) f.
Proof.
  intros x y Hxy.
  f_equal.
Admitted.


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


(** * Lattice interpretations of effect signature *)

(*
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

  Definition play_poset E V : Poset (play E V) :=
    {|
      ref := pref;
    |}.

  Hint Extern 1 (Poset (play _ _)) =>
    apply @play_poset : typeclass_instances.

  (** ** Free interpretation *)

  (*
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
    FCD.F (play E V).

  Hint Extern 1 (CDLattice (t _ _)) =>
    apply @FCD.lattice : typeclass_instances.

  Definition ret {E A} (a : A) : t E A :=
    FCD.emb (pret a).

  Fixpoint pbind {E A B} (f : A -> t E B) (p : play E A) : t E B :=
    match p with
      | pret a => f a
      | pmove m =>
        FCD.emb (pmove m)
      | pcons m n q =>
        FCD.emb (pmove m) ⊔
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

  Lemma bind_ret_r {E A B} (a : A) (f : A -> t E B) :
    bind f (ret a) = f a.
  Proof.
    intros. unfold bind, ret.
    rewrite FCD.ext_ana.
    reflexivity.
  Qed.

  Lemma pbind_ret_l {E A} :
    pbind (@ret E A) = FCD.emb.
  Proof.
    apply functional_extensionality. intros s.
    induction s; cbn; auto.
    rewrite IHs. rewrite @FCD.ext_ana.
    - apply ref_join. rstep. constructor.
    - constructor. repeat rstep. constructor. auto.
  Qed.

  Lemma bind_ret_l {E A} (x : t E A) :
    bind ret x = x.
  Proof.
    unfold bind. rewrite pbind_ret_l.
    apply FCD.ext_emb.
  Qed.

  (** ** Interaction *)

  (** The interaction primitive triggers one of the actions from the
    signature and returns the environment's response. *)

  Definition int {E ar} (m : E ar) : t E ar :=
    ⋁ k : option ar;
      match k with
        | Some n => FCD.emb (pcons m n (pret n))
        | None   => FCD.emb (pmove m)
      end.

  (** Morphisms between two effect signatures are substitutions,
    which give an interaction specification in [E] for each possible
    operation in [F]. *)

  Definition subst (E F : esig) :=
    forall ar, F ar -> t E ar.

  (** To apply a substitution [f : E -> F] to an interaction
    specification in [F], we replace each move [m] by the
    corresponding interaction as given by [f m]. *)

  Fixpoint papply {E F A} (f : subst E F) (s : play F A) : t E A :=
    match s with
      | pret a => FCD.emb (pret a)
      | pmove m => bind (fun _ => bot) (f _ m)
      | pcons m n t => bind (fun n' => ⋁ H : n' = n; papply f t) (f _ m)
    end.

  Instance papply_mor {E F A} (f : subst E F) :
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
    unfold apply.
    typeclasses eauto.
  Qed.

  Definition compose {E F G} (g : subst F G) (f : subst E F) : subst E G :=
    fun ar m => apply f (g ar m).

  (** Properties of [apply]. *)

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
    apply functional_extensionality; intros m.
    apply apply_int_r.
  Qed.

  Lemma compose_int_r {E F} (f : subst E F) :
    compose f (@int E) = f.
  Proof.
    unfold compose.
    apply functional_extensionality_dep; intros ar.
    apply functional_extensionality; intros m.
    apply apply_int_l.
  Qed.

  Lemma compose_assoc {E F G H} (f : subst E F) (g : subst F G) (h : subst G H) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    unfold compose.
    apply functional_extensionality_dep; intros ar.
    apply functional_extensionality; intros m.
    apply apply_assoc.
  Qed.

End ISpec.

Notation ispec := ISpec.t.
