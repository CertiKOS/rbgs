Require Import coqrel.LogicalRelations.
Require Import FunctionalExtensionality.
Require Import ClassicalFacts.

Local Obligation Tactic := cbn; eauto.

(** Following the usual approach, we formalize strategies as
  prefix-closed sets of odd-length traces. To make it possible to
  define strategies in compositional and operational ways,
  we encapsulate this construction in the *interaction* monad
  [I_{M,N}] defined in this library.

  We use classical logic. The following axioms provide extensional
  equality for strategies. *)

Axiom prop_ext : prop_extensionality.
Axiom proof_irr : proof_irrelevance.


(** * The interaction monad *)

Module Intm.

  (* The interaction monad models a computation which may interact with
    its environment. The computation can perform an output [m : M],
    at which point it will be suspended until an input [n : N] is
    received from the environment. This is modeled by the operation:

        interact : M -> I_{M,N}(N).

    Additionally, to model specifications which permit a range of
    possible behaviors, we allow non-deterministic strategies.
    Consequently, the interaction monad is equipped with a complete
    refinement lattice, which we extend with a distinguished greatest
    element:

        undef : I_{M,N}(A),

    modelling a computation whose behavior is undefined.

    Finally, we model non-deterministic iteration with the operator:

        iter : (A -> I_{M,N}(A)) -> (A -> I_{M,N}(A)).

    Notably, [iter] is different from the Kleene star associated with
    the refinement lattice because we account for silent divergence as
    a specific behavior, incomparable with terminating computations,
    rather than identifying it with the unsatisfiable specification ⊥.

    Using the interaction monad, alternating strategies for the game
    [G = (M_O, M_P)], where [O] is expected to make the first move,
    can be modelled as computations of type:

        M_O -> I_{M_P, M_O}(∅).

   *)

  (** ** Traces *)

  (** The traces we will consider are essentially odd-length sequences
    of moves. In order to support the monadic structure and to account
    for undefined behaviors and silent divergence, we extend them with
    the distinguished, terminal moves [v : A], [div] and [undef].
    Any trace is considered a prefix of [undef]. *)

  Inductive trace {M N A} :=
    | val (a : A)
    | div
    | undef
    | move (m : M)
    | tcons (m : M) (n : N) (t : trace).

  Arguments trace : clear implicits.

  Inductive prefix {M N A} : relation (trace M N A) :=
    | val_prefix v : prefix (val v) (val v)
    | div_prefix : prefix div div
    | undef_prefix t : prefix t undef
    | move_prefix m : prefix (move m) (move m)
    | tcons_prefix m n s t : prefix s t -> prefix (tcons m n s) (tcons m n t)
    | move_tcons_prefix m n t : prefix (move m) (tcons m n t).

  Hint Constructors prefix.

  Global Instance prefix_po M N A :
    PreOrder (@prefix M N A).
  Proof.
    split.
    - intro t. induction t; constructor; eauto.
    - intros t1 t2 t3 H12 H23. revert t1 H12.
      induction H23; eauto; inversion 1; subst; eauto.
  Qed.

  (** ** Computations *)

  (** An interactive computation is a prefix-closed set of traces.
    Note that since any trace is a prefix of [undef], a computation
    which admits a trace ending with [undef] will also admit all
    possible defined interactions sharing the same initial segment. *)

  Record t {M N A} :=
    {
      has : trace M N A -> Prop;
      closed s t : has t -> prefix s t -> has s;
    }.

  Arguments t : clear implicits.

  Bind Scope behavior_scope with t.
  Delimit Scope behavior_scope with beh.

  Hint Extern 1 (has _) => eapply closed; [assumption | ].

  (** Refinement is defined as trace containement. *)

  Definition ref {M N A} : relation (t M N A) :=
    fun x y => forall t, has x t -> has y t.

  Global Instance has_ref :
    Monotonic (@has) (forallr -, forallr -, forallr -, ref ++> prefix --> impl).
  Proof.
    repeat rstep. intro. eauto using closed.
  Qed.

  (** With some axioms, we get extensional equality for interactive
    computations. *)

  Global Instance ref_preo M N A :
    PreOrder (@ref M N A).
  Proof.
    firstorder.
  Qed.

  Global Instance ref_antisym M N A :
    Antisymmetric _ eq (@ref M N A).
  Proof.
    intros [x Hx] [y Hy] Hxy Hyx.
    cut (x = y). { intro. subst. f_equal. apply proof_irr. }
    red in Hxy, Hyx; cbn in *.
    apply functional_extensionality; intro t.
    apply prop_ext; firstorder.
  Qed.

  Lemma ref_refl {M N A} (x : t M N A) :
    ref x x.
  Proof.
    firstorder.
  Qed.

  Hint Resolve ref_refl.

  (** ** Monad operations *)

  (** *** Definition *)

  (** The monad's unit associate to each value [v] the computation
    with a single trace [val v]. *)

  Program Definition ret {M N A} (v : A) : t M N A :=
    {| has := eq (val v) |}.
  Next Obligation.
    intros. subst. inversion H0; auto.
  Qed.

  (** The Kleisli extension [bind] corresponds to the sequential
    composition of a computation [x : I_{M,N}(A)] and a continuation
    [f : A -> I_{M,N}(B)]. The result is in [I_{M,N}(B)] and contains
    the traces of [x], where traces ending in [val v] have been
    concatenated with traces in [f(v)]. *)

  Section BIND.
    (* Context {M N A B} (f : A -> trace M N B -> Prop) (x : trace M N A -> Prop).
    Context (Hf : forall a s t, f a t -> prefix s t -> f a s).
    Context (Hx : forall s t, x t -> prefix s t -> x s). *)
    Context {M N A B} (f : A -> t M N B) (x : t M N A).

    (* We first define the result of concatenating a single trace with
      the continuation [f]. *)

    Inductive bind_trace : trace M N A -> trace M N B -> Prop :=
      | bind_val a t :
          has (f a) t ->
          bind_trace (val a) t
      | bind_div :
          bind_trace div div
      | bind_undef t :
          bind_trace undef t
      | bind_move m :
          bind_trace (move m) (move m)
      | bind_tcons m n s t :
          bind_trace s t ->
          bind_trace (tcons m n s) (tcons m n t).

    Hint Constructors bind_trace.

    Lemma bind_trace_closed s t t' :
      bind_trace s t ->
      prefix t' t ->
      exists s', bind_trace s' t' /\ prefix s' s.
    Proof.
      intros Ht Ht'.
      revert t' Ht'; induction Ht; intros;
      inversion Ht'; clear Ht'; subst; eauto 6 using closed.
      edestruct IHHt as (s' & Ht' & Hs'); eauto.
    Qed.

    (** Now [bind] is straightforward to define. *)

    Program Definition bind :=
      {| has t := exists s, has x s /\ bind_trace s t |}.
    Next Obligation.
      intros s t (u & Hu & Hut) Hst.
      edestruct @bind_trace_closed as (s' & Ht' & Hs'); eauto using closed.
    Qed.

    (*
    Definition bind_has (t : trace M N B) : Prop :=
      exists s, x s /\ bind_trace s t.

    Lemma bind_has_closed (t' t : trace M N B) :
      bind_has t ->
      prefix t' t ->
      bind_has t'.
    Proof.
      intros (s & Hs & Hst) Ht. red.
      edestruct @bind_trace_closed as (s' & Ht' & Hs'); eauto using closed.
    Qed.
     *)

  End BIND.

  Hint Constructors bind_trace.
  Local Notation "x >>= f" := (bind f x) (at level 40, no associativity).

  (** *** Properties *)

  Global Instance ret_ref :
    Monotonic
      (@ret)
      (forallr -, forallr -, forallr -, - ==> ref).
  Proof.
    firstorder.
  Qed.

  Global Instance bind_trace_ref :
    Monotonic
      (@bind_trace)
      (forallr -, forallr -, forallr -, forallr -,
        (- ==> ref) ++> - ==> - ==> impl).
  Proof.
    intros M N A B f g Hfg s t Hst.
    induction Hst; constructor; eauto.
    firstorder.
  Qed.

  Global Instance bind_ref :
    Monotonic
      (@bind)
      (forallr -, forallr -, forallr -, forallr -,
        (- ==> ref) ++> ref ++> ref).
  Proof.
    repeat rstep. intros t (? & ? & Ht). cbn in *.
    eapply bind_trace_ref in Ht; eauto.
  Qed.

  Lemma ret_bind {M N A B} (f : A -> t M N B) (a : A) :
    (ret a >>= f) = f a.
  Proof.
    apply antisymmetry.
    - intros t (s & [ ] & Hst). cbn in *. subst.
      inversion Hst. congruence.
    - intros t Ht. cbn.
      exists (val a). intuition auto.
  Qed.

  Lemma bind_ret {M N A} (x : t M N A) :
    (x >>= ret) = x.
  Proof.
    apply antisymmetry.
    - intros t (s & Hs & Hst). revert x Hs.
      cut (prefix t s); eauto using closed.
      induction Hst; intros; eauto using closed.
      + destruct H. auto.
    - intros t Ht. cbn.
      exists t. intuition auto. clear.
      induction t; constructor; cbn; eauto.
  Qed.

  Lemma bind_ret_eta {M N A} (x : t M N A) :
    (x >>= fun a => ret a) = x.
  Proof.
    apply bind_ret.
  Qed.

  Lemma bind_bind {M N A B C} (f : B -> t M N C) (g : A -> t M N B) x :
    ((x >>= g) >>= f) = (x >>= fun a => g a >>= f).
  Proof.
    apply antisymmetry.
    - intros t (v & (u & Hu & Huv) & Hvt).
      exists u. intuition auto. clear x Hu.
      revert t Hvt; induction Huv; intros.
      + constructor. cbn. eauto.
      + inversion Hvt; clear Hvt; subst; eauto.
      + constructor.
      + inversion Hvt; clear Hvt; subst; eauto.
      + inversion Hvt; clear Hvt; subst; eauto.
    - intros t (s & Hs & Hst). cbn.
      revert Hs. generalize (has x). clear x.
      induction Hst; intros.
      + destruct H as (u & Hu & Hut).
        exists u. cbn. intuition auto.
        exists (val a). intuition auto.
      + repeat (exists div; split; [auto | constructor]).
      + repeat (exists undef; split; [auto | constructor]).
      + repeat (exists (move m); split; [auto | constructor]).
      + edestruct (IHHst (fun t => P (tcons m n t))) as (v & Hv & Hvt); auto.
        clear s Hs Hst IHHst.
        destruct Hv as (u & Hu & Huv).
        exists (tcons m n v). intuition auto.
        exists (tcons m n u). intuition auto.
  Qed.

  Hint Rewrite @bind_ret @bind_ret_eta @ret_bind @bind_bind : monad.

  (** ** Relator *)

  (** *** Definition *)

  (** The relator associated with [I_{M,N}] generalizes [ref] by
    extending a relation on values [R] to a relation on computations
    [I_{M,N}(R)]. This yields a notion of simulation asserting that if
    the first computation terminates with a value [a], then after an
    identical interaction the second computation will also terminate
    with a value [b] such that [R a b]. *)

  Inductive trace_rel M N {A B} (R: rel A B) : rel (trace M N A) (trace M N B) :=
    | val_rel a b :
        R a b ->
        trace_rel M N R (val a) (val b)
    | div_rel :
        trace_rel M N R div div
    | undef_rel s :
        trace_rel M N R s undef
    | move_rel m :
        trace_rel M N R (move m) (move m)
    | tcons_rel m n ta tb :
        trace_rel M N R ta tb ->
        trace_rel M N R (tcons m n ta) (tcons m n tb).

  Hint Constructors trace_rel.

  Definition r M N {A B} (R : rel A B) : rel (t M N A) (t M N B) :=
    set_le (trace_rel M N R) @@ has.

  (** *** Properties of [trace_rel] *)

  Global Instance trace_subrel M N A B :
    Monotonic (@trace_rel M N A B) (subrel ++> subrel).
  Proof.
    intros R1 R2 HR u v Huv.
    induction Huv; constructor; eauto.
  Qed.

  Global Instance trace_subrel_params :
    Params (@trace_rel) 3.

  Global Instance trace_rel_refl {M N A} (R : relation A) :
    Reflexive R ->
    Reflexive (trace_rel M N R).
  Proof.
    intros HR t.
    induction t; constructor; eauto.
  Qed.

  Global Instance trace_rel_compose {M N A B C} RAB RBC RAC :
    @RCompose A B C RAB RBC RAC ->
    RCompose (trace_rel M N RAB) (trace_rel M N RBC) (trace_rel M N RAC).
  Proof.
    intros HR ta tb tc Htab Htbc. revert tc Htbc.
    induction Htab; intros; inversion Htbc; clear Htbc; subst; constructor.
    - ercompose; eauto.
    - eauto.
  Qed.

  (** In addition to the standard properties above, we can show that
    [trace_rel] is compatible with [bind_trace]. *)

  Global Instance bind_trace_rel :
    Monotonic
      (@bind_trace)
      (forallr - @ M, forallr - @ N, forallr RA, forallr RB,
        (RA ++> r M N RB) ++> trace_rel M N RA ++> set_le (trace_rel M N RB)).
  Proof.
    intros M N A1 A2 RA B1 B2 RB f1 f2 Hf u1 u2 Hu v1 Hv1.
    revert u2 Hu; induction Hv1; intros;
    inversion Hu; clear Hu; subst; eauto.
    - edestruct Hf as (? & ? & ?); eauto.
    - edestruct IHHv1 as (? & ? & ?); eauto.
  Qed.

  (** *** Properties of [r] *)

  (** We can use the properties of [trace_rel] to establish that [r]
    is a monad relator in the following sense. *)

  Global Instance r_subrel {M N A B} :
    Monotonic (@r M N A B) (subrel ++> subrel).
  Proof.
    unfold r. rauto.
  Qed.

  Global Instance r_subrel_params :
    Params (@r_subrel) 3.

  Global Instance r_refl {M N A} (R : relation A) :
    Reflexive R ->
    Reflexive (r M N R).
  Proof.
    unfold r. typeclasses eauto.
  Qed.

  Global Instance r_compose {M N A B C} RAB RBC RAC :
    @RCompose A B C RAB RBC RAC ->
    RCompose (r M N RAB) (r M N RBC) (r M N RAC).
  Proof.
    unfold r. typeclasses eauto.
  Qed.

  Global Instance has_r :
    Monotonic
      (@has)
      (forallr - @ M, forallr - @ N, forallr R,
       r M N R ++> set_le (trace_rel M N R)) | 10.
  Proof.
    firstorder.
  Qed.

  Global Instance ret_r :
    Monotonic
      (@ret)
      (forallr - @ M, forallr - @ N, forallr R, R ++> r M N R) | 10.
  Proof.
    unfold r. repeat rstep.
    intros _ [ ]. cbn. eauto.
  Qed.

  Global Instance bind_r :
    Monotonic
      (@bind)
      (forallr - @ M, forallr - @ N, forallr RA, forallr RB,
        (RA ++> r M N RB) ++> r M N RA ++> r M N RB) | 10.
  Proof.
    intros M N A1 A2 RA B1 B2 RB f1 f2 Hf x1 x2 Hx t1 (s1 & Hs1 & Hst1). cbn.
    edestruct has_r as (s2 & Hs2 & Hs); eauto.
    edestruct bind_trace_rel as (t2 & Ht2 & Ht); eauto.
  Qed.

  (** *** Properties of [ref] *)

  (** Note that [ref] corresponds to the special case [I_{M,N}(=)].
    This allows us use the relator properties to show that [ref] is a
    preorder. *)

  Lemma ref_r M N A :
    @ref M N A = r M N eq.
  Proof.
    apply functional_extensionality; intro a.
    apply functional_extensionality; intro b.
    apply prop_ext. split.
    - intros Hab t Ht.
      exists t. split; eauto. reflexivity.
    - intros Hab t Ht.
      edestruct Hab as (t' & Ht' & H); eauto.
      eapply closed; eauto.
      clear - H. induction H; subst; eauto.
  Qed.

  Global Instance ref_r_eqrel M N A :
    Related (@ref M N A) (r M N eq) eqrel.
  Proof.
    red. rewrite ref_r. reflexivity.
  Qed.

  Global Instance r_ref_subrel M N A :
    Related (r M N eq) (@ref M N A) subrel.
  Proof.
    red. rewrite ref_r. reflexivity.
  Qed.

  (*
  Global Instance ref_refl M N A :
    Reflexive (@ref M N A).
  Proof.
    rewrite ref_r. typeclasses eauto.
  Qed.

  Global Instance ref_trans M N A :
    Transitive (@ref M N A).
  Proof.
    rewrite ref_r. typeclasses eauto.
  Qed.
   *)

  (** ** Lattice structure *)

  Program Definition bot {M N A} : t M N A :=
    {| has t := False |}.

  Program Definition top {M N A} : t M N A :=
    {| has t := True |}.

  Program Definition join {M N A} (x1 x2 : t M N A) : t M N A :=
    {| has t := has x1 t \/ has x2 t |}.
  Next Obligation.
    intuition eauto using closed.
  Qed.

  Program Definition meet {M N A} (x1 x2 : t M N A) : t M N A :=
    {| has t := has x1 t /\ has x2 t |}.
  Next Obligation.
    intuition eauto using closed.
  Qed.

  Program Definition sup {M N A I} (x : I -> t M N A) : t M N A :=
    {| has t := exists i, has (x i) t |}.
  Next Obligation.
    intros M N A I x s t (i & Ht) Hst.
    exists i. eauto using closed.
  Qed.

  Program Definition inf {M N A I} (x : I -> t M N A) : t M N A :=
    {| has t := forall i, has (x i) t |}.
  Next Obligation.
    intros M N A I x s t Ht Hst.
    intros i. eauto using closed.
  Qed.

  Infix "\/" := join : behavior_scope.
  Infix "/\" := meet : behavior_scope.

  Lemma bot_ref {M N A} (x : t M N A) :
    ref bot x.
  Proof.
    firstorder.
  Qed.

  Lemma top_ref {M N A} (x : t M N A) :
    ref x top.
  Proof.
    firstorder.
  Qed.

  Lemma join_ub_l {M N A} (x y : t M N A) :
    ref x (join x y).
  Proof.
    firstorder.
  Qed.

  Lemma join_ub_r {M N A} (x y : t M N A) :
    ref y (join x y).
  Proof.
    firstorder.
  Qed.

  Lemma join_lub {M N A} (x y z : t M N A) :
    ref x z ->
    ref y z ->
    ref (join x y) z.
  Proof.
    firstorder.
  Qed.

  Lemma join_l {M N A} (x y z : t M N A) :
    ref x y ->
    ref x (join y z).
  Proof.
    firstorder.
  Qed.

  Lemma join_r {M N A} (x y z : t M N A) :
    ref x z ->
    ref x (join y z).
  Proof.
    firstorder.
  Qed.

  Global Instance join_ref :
    Monotonic (@join) (forallr -, forallr -, forallr -, ref ++> ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Global Instance join_rel :
    Monotonic
      (@join)
      (forallr - @ M, forallr - @ N, forallr R,
         r M N R ++> r M N R ++> r M N R) | 10.
  Proof.
    firstorder.
  Qed.

  Lemma meet_lb_l {M N A} (x y : t M N A) :
    ref (meet x y) x.
  Proof.
    firstorder.
  Qed.

  Lemma meet_lb_r {M N A} (x y : t M N A) :
    ref (meet x y) y.
  Proof.
    firstorder.
  Qed.

  Lemma meet_glb {M N A} (x y z : t M N A) :
    ref x y ->
    ref x z ->
    ref x (meet y z).
  Proof.
    firstorder.
  Qed.

  Global Instance meet_ref :
    Monotonic (@meet) (forallr -, forallr -, forallr -, ref ++> ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Lemma sup_ub {M N A I} (x : I -> t M N A) :
    forall i, ref (x i) (sup x).
  Proof.
    firstorder.
  Qed.

  Lemma sup_lub {M N A I} (x : I -> t M N A) y :
    (forall i, ref (x i) y) -> ref (sup x) y.
  Proof.
    firstorder.
  Qed.

  Lemma sup_at {M N A I} (x : t M N A) (f : I -> t M N A) i :
    ref x (f i) ->
    ref x (sup f).
  Proof.
    firstorder.
  Qed.

  Global Instance sup_ref :
    Monotonic
      (@sup)
      (forallr -, forallr -, forallr -, forallr -, (- ==> ref) ++> ref).
  Proof.
    firstorder.
  Qed.

  Lemma inf_lb {M N A I} (x : I -> t M N A) :
    forall i, ref (inf x) (x i).
  Proof.
    firstorder.
  Qed.

  Lemma inf_glb {M N A I} x (y : I -> t M N A) :
    (forall i, ref x (y i)) -> ref x (inf y).
  Proof.
    firstorder.
  Qed.

  Lemma inf_at {M N A I} (x : I -> t M N A) (y : t M N A) i :
    ref (x i) y ->
    ref (inf x) y.
  Proof.
    firstorder.
  Qed.

  Global Instance inf_ref :
    Monotonic
      (@inf)
      (forallr -, forallr -, forallr -, forallr -, (- ==> ref) ++> ref).
  Proof.
    firstorder.
  Qed.

  Hint Resolve join_l join_r join_lub sup_at sup_lub bot_ref top_ref.

  Lemma join_comm {M N A} (x y : t M N A) :
    join x y = join y x.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma join_assoc {M N A} (x y z : t M N A) :
    join (join x y) z = join x (join y z).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma join_bot_l {M N A} (x : t M N A) :
    join bot x = x.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma join_bot_r {M N A} (x : t M N A) :
    join x bot = x.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma join_bot_rl {M N A} (x y : t M N A) :
    join x (join bot y) = join x y.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Hint Rewrite @join_assoc @join_bot_l @join_bot_r @join_bot_rl : monad.

  (** ** Set and functions (§3.5) *)

  Program Definition choose {M N A} (P : A -> Prop) : t M N A :=
    {| has t := exists a, P a /\ t = val a |}.
  Next Obligation.
    intros M N A P s t (a & Ha & Ht) Hst. subst.
    inversion Hst; eauto.
  Qed.

  Global Instance choose_ref :
    Monotonic
      (@choose)
      (forallr -, forallr -, forallr -, (- ==> impl) ++> ref).
  Proof.
    firstorder.
  Qed.

  Global Instance choose_r :
    Monotonic
      (@choose)
      (forallr - @ M, forallr - @ N, forallr R, set_le R ++> r M N R) | 10.
  Proof.
    intros M N A B R p q H t (a & Ha & Ht). subst. cbn.
    apply H in Ha as (b & Hb & Hab). eauto 10.
  Qed.

  (** ** Interaction (§3.6) *)

  Program Definition interact {M N} (m : M) : t M N N :=
    {| has t := t = move m \/ exists n, t = tcons m n (val n) |}.
  Next Obligation.
    intros M N m u v Hv Huv.
    destruct Hv as [Hv | [n Hv]]; subst.
    - inversion Huv; subst; eauto.
    - inversion Huv; subst; eauto. inversion H1; subst; eauto.
  Qed.

  (** ** Misc. *)

  (** *** Guard *)

  Program Definition guard {M N} (P : Prop) : t M N unit :=
    {| has t := P /\ t = val tt |}.
  Next Obligation.
    intros M N P s t [H Ht] Hst. subst. intuition auto.
    inversion Hst; auto.
  Qed.

  Lemma guard_true {M N} (P : Prop) :
    P -> @guard M N P = ret tt.
  Proof.
    intros HP. apply antisymmetry.
    - intros t Ht. cbn in *. firstorder.
    - intros t Ht. cbn in *. firstorder.
  Qed.

  Lemma guard_false {M N} (P : Prop) :
    ~ P -> @guard M N P = bot.
  Proof.
    intros HP. apply antisymmetry; firstorder.
  Qed.

  Hint Rewrite @guard_true @guard_false using auto : monad.

  (** *** Other *)

  Program Definition filter {M N A} (P : A -> Prop) (a : A) : t M N A :=
    {| has t := P a /\ t = val a |}.
  Next Obligation.
    intros M N A P a s t [H Ht] Hst. subst. intuition auto.
    inversion Hst; auto.
  Qed.

  Lemma filter_ret {M N A} P a :
    @ref M N A (filter P a) (ret a).
  Proof.
    intros t [Ha Ht]; subst.
    constructor.
  Qed.

  Program Definition diverge {M N A} : t M N A :=
    {| has := eq div |}.
  Next Obligation.
    intros; subst. inversion H0; auto.
  Qed.

End Intm.

Bind Scope behavior_scope with Intm.t.
Delimit Scope behavior_scope with beh.

Notation beh := Intm.t.

Notation "x >>= f" := (Intm.bind f x)
    (at level 40, no associativity, only parsing).
Notation "v <- X ; Y" := (X >>= fun v => Y%beh)
    (at level 100, X at next level, right associativity) : behavior_scope.

Infix "\/" := Intm.join : behavior_scope.
Infix "/\" := Intm.meet : behavior_scope.
