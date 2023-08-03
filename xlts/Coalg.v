Require Import Program.
Require Import LogicalRelations.

(*
Definition sig := Type -> Type.
Record op (E : sig) := mkop {ar : Type; oper : E ar}.
Arguments ar {_} _.
Arguments mkop {_ _} _.
Arguments oper {_} _.
Coercion op : sig >-> Sortclass.
*)

Record sig :=
  {
    op :> Type;
    ar : op -> Type;
  }.

Arguments ar {_}.


(** * Multi-sorted endofunctors *)

Module MEnd.

  Record t :=
    {
      sort : Type;
      init : sort;
      apply :> (sort -> Type) -> (sort -> Type);
    }.

  (** ** Example: A -->> B *)

  Module Obj.
    Section OBJ.
      Context {A B : sig}.

      Inductive sort :=
        | passive
        | active (m : B)
        | cont (m : B) (p : A).

      Inductive action (next : sort -> Type) (m : B) :=
        | ask (p : A) (s : next (cont m p))
        | tau (s : next (active m))
        | ret (n : ar m) (s : next passive).

      Definition apply (next : sort -> Type) (t : sort) : Type :=
        match t with
          | passive => forall m : op B, next (active m)
          | active m => action next m
          | cont m p => ar p -> next (active m)
        end.

      Canonical Structure mend : t :=
        {|
          MEnd.sort := sort;
          MEnd.init := passive;
          MEnd.apply := apply;
        |}.
    End OBJ.

    Arguments ask {_ _ _ _}.
    Arguments tau {_ _ _ _}.
    Arguments ret {_ _ _ _}.
    Arguments mend : clear implicits.
  End Obj.

  Infix "-->>" := Obj.mend (at level 60).

  (** ** Coalgebra *)

  Record coalg {E : t} :=
    {
      state :> sort E -> Type;
      init_state : state (init E);
      step : forall {s}, state s -> E state s;
    }.

  Arguments coalg : clear implicits.
  Coercion coalg : t >-> Sortclass.

  Module IdObjSem.
    Section ID.
      Context (A : sig).

      Inductive state : Obj.sort -> Type :=
        | init : state Obj.passive
        | ask (m : A) : state (Obj.active m)
        | wait (m : A) : state (Obj.cont m m)
        | ans (m : A) (r : ar m) : state (Obj.active m).

      Definition step (t : Obj.sort) (k : state t) : Obj.apply state t :=
        match k in state s return Obj.apply state s with
          | init => fun m => ask m
          | ask m => Obj.ask m (wait m)
          | wait m => fun r => ans m r
          | ans m r => Obj.ret r init
        end.

      Canonical Structure Obj.mend.

      Definition id_objsem : A -->> A :=
        {|
          MEnd.state := state;
          MEnd.init_state := init;
          MEnd.step := step;
        |}.
    End ID.
  End IdObjSem.

  Module CompObjSem.
    Section COMP.
      Context (A B C : sig).
      Context (L1 : B -->> C).
      Context (L2 : A -->> B).

      Inductive state : Obj.sort -> Type :=
        | pasv :        L1  Obj.passive   -> L2  Obj.passive   -> state  Obj.passive
        | act1 {c} :    L1 (Obj.active c) -> L2  Obj.passive   -> state (Obj.active c)
        | act2 {c b}:   L1 (Obj.cont c b) -> L2 (Obj.active b) -> state (Obj.active c)
        | cont {c b a}: L1 (Obj.cont c b) -> L2 (Obj.cont b a) -> state (Obj.cont c a).

      Definition step (t : Obj.sort) (s : state t) : Obj.apply state t :=
        match s in state t return Obj.apply state t with
          | pasv s1 s2 =>
            fun c => act1 (step L1 s1 c) s2
          | act1 s1 s2 =>
            match step L1 s1 with
              | Obj.ask b s1' => Obj.tau (act2 s1' (step L2 s2 b))
              | Obj.tau s1' => Obj.tau (act1 s1' s2)
              | Obj.ret cr s1' => Obj.ret cr (pasv s1' s2)
            end
          | act2 s1 s2 =>
            match step L2 s2 with
              | Obj.ask a s2' => Obj.ask a (cont s1 s2')
              | Obj.tau s2' => Obj.tau (act2 s1 s2')
              | Obj.ret br s2' => Obj.tau (act1 (step L1 s1 br) s2')
            end
          | cont s1 s2 =>
            fun ar => act2 s1 (step L2 s2 ar)
        end.

      Canonical Structure Obj.mend.

      Definition compose : A -->> C :=
        {|
          MEnd.state := state;
          MEnd.init_state := pasv (init_state L1) (init_state L2);
          MEnd.step := step;
        |}.
    End COMP.
  End CompObjSem.


  (** ** Operators *)

  (** [Σ i . E i] chooses to run as one of the [E i] *)

  Module Sig.
    Section SIG.
      Context {I} (E : I -> t).

      Inductive sort :=
        | init
        | running (i : I) (t : MEnd.sort (E i)).

      Definition apply (next : sort -> Type) (t : sort) :=
        match t with
          | init => {i : I & next (running i (MEnd.init (E i)))}
          | running i t => E i (fun t => next (running i t)) t
        end.
    End SIG.
  End Sig.

  Definition sig {I} (E : I -> t) : t :=
    {|
      sort := Sig.sort E;
      init := Sig.init E;
      apply := Sig.apply E;
    |}.

  (** [∏ i . E i] first lets the environment choose an [i], then executes as [E i] *)

  Module Pi.
    Section PI.
      Context {I} (E : I -> t).

      Inductive sort :=
        | init
        | running (i : I) (t : MEnd.sort (E i)).

      Definition apply (next : sort -> Type) (t : sort) :=
        match t with
          | init => forall i:I, next (running i (MEnd.init (E i)))
          | running i t => E i (fun t => next (running i t)) t
        end.
    End PI.
  End Pi.

  Definition pi {I} (E : I -> t) : t :=
    {|
      sort := Pi.sort E;
      init := Pi.init E;
      apply := Pi.apply E;
    |}.

End MEnd.


(** * Transition systems *)

(** Here I formalize transition systems for a general notion of interface.
  In this approach, an interface is an endofunctor [E : Rel^T -> Rel^T],
  where [T] is set of sorts with a distinguished starting sort.
  A transition system is then a coalgebra [L : S -> E S] for
  a set [S : T -> Type] of "sorted states" indexed by [T],
  together with an initial state typed by the starting sort. *)

Module TS.

  (** The interface of a transition system is defined as an endofunctor
    on the category Rel^T, where T is a set of sorts *)

  Record int :=
    {
      sort : Type;
      start : sort;
      omap :> (sort -> Type) -> (sort -> Type);

      (* Action on relations *)
      fmap {U V : sort -> Type} (f : forall t, U t -> V t -> Prop) :
        forall t, omap U t -> omap V t -> Prop;
      fmap_id {U : sort -> Type} {t : sort} (x : omap U t):
        fmap (fun t => @eq (U t)) t x x;
      fmap_compose {U V W} R S t x y z:
        @fmap U V R t x y ->
        @fmap V W S t y z ->
        fmap (fun t => rel_compose (R t) (S t)) t x z;
    }.

  Arguments start {_}.

  (** Then a transition system is a coalgebra in Rel *)

  Record beh {E : int} :=
    {
      state :> sort E -> Type;
      init : state (@start E) -> Prop;
      step : forall {t}, state t -> E state t -> Prop;
    }.

  Arguments beh : clear implicits.
  Coercion beh : int >-> Sortclass.

  (** Simulations can be defined using [fmap] *)

  Record sim {E} (L1 L2 : beh E) :=
    {
      sim_rel : forall t, L1 t -> L2 t -> Prop;
      sim_init :
        forall s1 : L1 start, init L1 s1 ->
        exists s2 : L2 start, init L2 s2 /\ sim_rel start s1 s2;
      sim_step :
        forall t s1 s2, sim_rel t s1 s2 ->
        forall s1', step L1 s1 s1' ->
        exists s2', step L2 s2 s2' /\ fmap E sim_rel t s1' s2';
    }.

  (** Simulations form a preorder *)

  Obligation Tactic := cbn.
  
  Program Definition id_sim {E} (L : beh E) : sim L L :=
    {|
      sim_rel t := eq;
    |}.
  Next Obligation.
    eauto.
  Qed.
  Next Obligation.
    destruct 1.
    eauto using fmap_id.
  Qed.

  Program Definition compose_sim {E} (L1 L2 L3 : beh E) R S : sim L1 L3 :=
    {|
      sim_rel t := rel_compose (sim_rel L1 L2 R t) (sim_rel L2 L3 S t);
    |}.
  Next Obligation.
    intros.
    edestruct (sim_init L1 L2 R s1) as (s2 & Hs2 & Hs12); auto.
    edestruct (sim_init L2 L3 S s2) as (s3 & Hs3 & Hs23); auto.
    eauto 10.
  Qed.
  Next Obligation.
    intros until s1. intros s3 (s2 & Hs12 & Hs23) s1' Hs1'.
    edestruct (sim_step L1 L2 R t s1) as (s2' & Hs2' & Hs12'); eauto.
    edestruct (sim_step L2 L3 S t s2) as (s3' & Hs3' & Hs23'); eauto.
    eauto 10 using fmap_compose.
  Qed.

End TS.


(** * Object-based semantics *)

(** Now we formalize a notion of object with a behavior in [†(†A ⊸ B)] where
  both [A] and [B] are effect signatures. The object can be activated in [B],
  then can make an arbitrary number of calls in [A] before it returns in [B]
  and waits for the next activation. *)

Module Obj.

  (** ** Interface *)

  (** First, we must define the endofunctor corresponding to the kind
    of behaviors outlined above. *)

  Section OBJ.
    Context {A B : sig}.

    (** Invoking the object makes it transition from a passive state
      to an active state. When the object makes an outgoing call, the
      becomes a continuation. Resuming transistion back to the active
      state, and returning transitions back to the passive state. *)

    Inductive sort :=
      | inactive
      | running (m : B)
      | susp (m : B) (p : A).

    (** When in the active state, the following actions are available. *)

    Inductive action {continue : sort -> Type} {m : B} :=
      | ask (p : A) (s : continue (susp m p))
      (*| tau (s : continue (running m))*)
      | ret (n : ar m) (s : continue inactive).

    Arguments action : clear implicits.

    (** Overall, the following transitions are possible. *)

    Definition next (continue : sort -> Type) (t : sort) : Type :=
      match t with
        | inactive => forall m : op B, continue (running m)
        | running m => action continue m
        | susp m p => ar p -> continue (running m)
      end.

    (** The action on relations is as follows *)

    Inductive action_rel {U V} (R : forall t, U t -> V t -> Prop) (m : B) :
          action U m -> action V m -> Prop :=
      | ask_rel :
          Monotonic ask (forallr - @ p, R (susp m p) ++> action_rel R m)
     (* | tau_rel :
          Monotonic tau (R (running m) ++> action_rel R m) *)
      | ret_rel :
          Monotonic ret (forallr -, R inactive ++> action_rel R m).

    Definition next_rel {U V} (R : forall t, U t -> V t -> Prop) t :=
      match t return next U t -> next V t -> Prop with
        | inactive => fun u v => forall m, R (running m) (u m) (v m)
        | running m => action_rel R m
        | susp m p => fun u v => forall r, R (running m) (u r) (v r)
      end.

  End OBJ.

  Program Canonical Structure int A B : TS.int :=
    {|
      TS.sort := @sort A B;
      TS.start := @inactive A B;
      TS.omap := @next A B;
      TS.fmap := @next_rel A B;
    |}.
  Next Obligation.
    intros.
    destruct t; cbn; auto.
    destruct x; constructor; auto.
  Qed.
  Next Obligation.
    intros until z. intros Hxy Hyz.
    destruct t; cbn in *; eauto.
    destruct Hxy; inversion Hyz; subst; constructor; eauto.
    apply inj_pair2 in H2; subst. eauto.
  Qed.

  Infix "-->>" := int (at level 60).
  Coercion TS.beh : TS.int >-> Sortclass.
  Coercion TS.state : TS.beh >-> Funclass.

  (** ** Compositional structure *)

  (** *** Identity *)

  Module Id.
    Section ID.
      Context {A : sig}.

      Inductive state : sort -> Type :=
        | ready : state inactive
        | query (m : A) : state (running m)
        | wait (m : A) : state (susp m m)
        | reply (m : A) (r : ar m) : state (running m).

      Inductive step : forall t, state t -> next state t -> Prop :=
        | step_ready : step _ ready query
        | step_query m : step _ (query m) (ask m (wait m))
        | step_wait m : step _ (wait m) (fun r => reply m r)
        | step_reply m r : step _ (reply m r) (ret r ready).

    End ID.
  End Id.

  Definition id {A} : A -->> A :=
    {|
      TS.state := Id.state;
      TS.init := eq Id.ready;
      TS.step := Id.step;
    |}.

  (** *** Composition *)

  Module Comp.
    Section COMP.
      Context {A B C : sig}.
      Context (L1 : B -->> C).
      Context (L2 : A -->> B).

      Inductive state : sort -> Type :=
        | II :        L1 inactive    -> L2 inactive    -> state inactive
        | RI {c} :    L1 (running c) -> L2 inactive    -> state (running c)
        | SR {c b}:   L1 (susp c b)  -> L2 (running b) -> state (running c)
        | SS {c b a}: L1 (susp c b)  -> L2 (susp b a)  -> state (susp c a).

      Inductive init : state inactive -> Prop :=
        | init_intro s1 s2 :
            TS.init L1 s1 ->
            TS.init L2 s2 ->
            init (II s1 s2).

      Inductive step : forall t, state t -> next state t -> Prop :=
        | step_incoming_call s1 s1' s2 :
            TS.step L1 s1 s1' ->
            step _ (II s1 s2) (fun c => RI (s1' c) s2)
        | step_internal_call {c b} s1 s1' s2 s2' s'' :
            TS.step L1 (t:=running c) s1 (ask b s1') ->
            TS.step L2 (t:=inactive) s2 s2' ->
            step (running c) (SR s1' (s2' b)) s'' ->
            step (running c) (RI s1 s2) s''
        | step_outgoing_call {c b a} s1 s2 s2' :
            TS.step L2 (t:=running b) s2 (ask a s2') ->
            step (running c) (SR s1 s2) (ask a (SS s1 s2'))
        | step_outgoing_ret {c b a} s1 s2 s2' :
            TS.step L2 (t:=susp b a) s2 s2' ->
            step (susp c a) (SS s1 s2) (fun r => SR s1 (s2' r))
        | step_internal_ret {c b} s1 s2 r s1' s2' s'' :
            TS.step L2 (t:=running b) s2 (ret r s2') ->
            TS.step L1 (t:=susp c b) s1 s1' ->
            step (running c) (RI (s1' r) s2') s'' ->
            step (running c) (SR s1 s2) s''
        | step_incoming_ret {c} s1 s2 r s1' :
            TS.step L1 (t:=running c) s1 (ret r s1') ->
            step (running c) (RI s1 s2) (ret r (II s1' s2)).

    End COMP.
  End Comp.

  Definition comp {A B C} (L1 : B -->> C) (L2 : A -->> B) : A -->> C :=
    {|
      TS.state := Comp.state L1 L2;
      TS.init := Comp.init L1 L2;
      TS.step := Comp.step L1 L2;
    |}.

  (** *** Properties *)

  Inductive comp_id_l_sim {A B} {L : A -->> B} : forall t, comp id L t -> L t -> Prop :=
    | comp_id_l_inactive s :
        comp_id_l_sim inactive (Comp.II id L Id.ready s) s
    | comp_id_l_incoming_call s s' b :
        TS.step L s s' ->
        comp_id_l_sim (running b) (Comp.RI id L (Id.query b) s) (s' b)
    | comp_id_l_outgoing_call b a s :
        comp_id_l_sim (susp b a) (Comp.SS id L (Id.wait b) s) s
    | comp_id_l_outgoing_ret b s :
        comp_id_l_sim (running b) (Comp.SR id L (Id.wait b) s) s.

  Lemma comp_id_l {A B} (L : A -->> B) :
    TS.sim (comp id L) L.
  Proof.
    exists comp_id_l_sim; cbn.
    - intros _ [_ s [ ] Hs].
      exists s. split; auto.
      apply comp_id_l_inactive.
    - intros t s1 s2 Hs.
      destruct Hs; cbn.
      + intros s' Hs'.
        change (next (Comp.state id L) inactive) in s'.
        inversion Hs'. apply inj_pair2 in H2. cbn in *. subst.
        change (next (@Id.state B) inactive) in s1'.
        inversion H1. apply inj_pair2 in H2. cbn in *. subst. clear H1.
  Abort.

End Obj.
