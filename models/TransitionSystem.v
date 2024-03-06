From structures Require Import Effects.
Require Import List PeanoNat.
Import ListNotations.
From compcert Require Import Coqlib.
Require Import Classical.

Set Implicit Arguments.
Set Asymmetric Patterns.

Ltac clear_hyp :=
  repeat match goal with
         | [ H : (?t = ?t)%type |- _ ] => clear H
         end.

Ltac depsubst :=
  subst;
  lazymatch goal with
  | H : existT _ ?x _ = existT _ ?x _ |- _ =>
      apply inj_pair2 in H; depsubst
  | _ =>
      clear_hyp
  end.

(* Open Semantics *)
Record semantics {E F: esig} : Type := {
    transition_state: Type -> Type;
    init mf: F mf -> transition_state mf -> Prop;
    call me mf: transition_state mf -> E me -> (me -> transition_state mf -> Prop) -> Prop;
    return_ mf: transition_state mf -> mf -> Prop;
  }.
Arguments semantics : clear implicits.
Arguments init {_ _} _ {_} _ _.
Arguments call {_ _} _ {_ _} _ _ _.

Require Import RefConv.

Section FSIM.

  Context {E1 E2 F1 F2: esig}
    (rcE: refconv E1 E2) (rcF: refconv F1 F2)
    (L1: semantics E1 F1) (L2: semantics E2 F2).

  Record fsim_properties := {
      match_state mf1 mf2:
        transition_state L1 mf1 ->
        transition_state L2 mf2 ->
        (mf1 -> mf2 -> Prop) -> Prop;
      fsim_init mf1 mf2 (f1: F1 mf1) (f2: F2 mf2) s1 f_rel:
        rcF _ f1 _ f2 f_rel ->
        init L1 f1 s1 ->
        exists s2, init L2 f2 s2 /\
        match_state s1 s2 f_rel;
      fsim_call mf1 mf2 (s1: transition_state L1 mf1)
                    (s2: transition_state L2 mf2)
                    me1 (e1: E1 me1) kont1 f_rel:
        match_state s1 s2 f_rel ->
        call L1 s1 e1 kont1 ->
        exists me2 (e2: E2 me2) kont2 e_rel, call L2 s2 e2 kont2 /\
        rcE _ e1 _ e2 e_rel /\
        forall r1 r2 s1', kont1 r1 s1' -> e_rel r1 r2 -> exists s2', kont2 r2 s2' /\
        match_state s1' s2' f_rel;
      fsim_return mf1 mf2 s1 s2 (r1: mf1) f_rel:
        match_state s1 s2 f_rel ->
        return_ L1 s1 r1 ->
        exists r2: mf2, return_ L2 s2 r2 /\
        f_rel r1 r2;
    }.

End FSIM.

Definition fsim {E1 E2 F1 F2: esig}
    (rcE: refconv E1 E2) (rcF: refconv F1 F2)
    (L1: semantics E1 F1) (L2: semantics E2 F2) :=
  inhabited (fsim_properties rcE rcF L1 L2).

Section LComp.

  Context {E F G} (L1: semantics F G) (L2: semantics E F).

  Inductive lcomp_state (mg: Type) : Type :=
  | lcomp_state1:
      transition_state L1 mg -> lcomp_state mg
  | lcomp_state2 mf:
      transition_state L2 mf ->
      (mf -> transition_state L1 mg -> Prop) -> lcomp_state mg.

  Inductive internal_step (mg: Type): lcomp_state mg -> lcomp_state mg -> Prop :=
  | internal_step1 mf (s1: transition_state L1 mg)
                       (s2: transition_state L2 mf) f kont1
      (CALL: call L1 s1 f kont1) (INIT: init L2 f s2):
      internal_step (lcomp_state1 _ s1) (lcomp_state2 _ s2 kont1)
  | internal_step2 mf (s1: transition_state L1 mg)
      (s2: transition_state L2 mf)
      (kont1: mf -> transition_state L1 mg -> Prop) r2 s1'
      (RET: return_ L2 s2 r2) (KONT: kont1 r2 s1'):
      internal_step (lcomp_state2 _ s2 kont1) (lcomp_state1 _ s1').

  Inductive star {A: Type} (R: A -> A -> Prop): A -> A -> Prop :=
  | star_refl: forall a, star R a a
  | star_step: forall a b c, R a b -> star R b c -> star R a c.

  Inductive lcomp_init mg: G mg -> lcomp_state mg -> Prop :=
  | lcomp_init1 (g: G mg) s r:
      init L1 g s ->
      (* this is only for proving identity *)
      return_ L1 s r ->
      lcomp_init g (lcomp_state1 _ s)
  | lcomp_init2 mf (g: G mg) (f: F mf) kont1 s1 s2:
      init L1 g s1 ->
      call L1 s1 f kont1 ->
      init L2 f s2 ->
      lcomp_init g (lcomp_state2 _ s2 kont1).

  Inductive lift_kont mg mf me
      (kont2: me -> transition_state L2 mf -> Prop)
      (kont1: mf -> transition_state L1 mg -> Prop):
      me -> lcomp_state mg -> Prop :=
  | lift_kont_intro: forall r s2',
      kont2 r s2' -> lift_kont kont2 kont1 r (lcomp_state2 _ s2' kont1).

  Inductive lcomp_call me mg: lcomp_state mg -> E me ->
                                 (me -> lcomp_state mg -> Prop) -> Prop :=
  | lcomp_call_intro:
    forall mf s (s2: transition_state L2 mf) (e: E me) kont1 kont2,
      star (internal_step (mg:=mg)) s (lcomp_state2 _ s2 kont1) ->
      call L2 s2 e kont2 ->
      lcomp_call s e (lift_kont kont2 kont1).

  Inductive lcomp_return mg: lcomp_state mg -> mg -> Prop :=
  | lcomp_return_intro s s1 r:
      star (internal_step (mg:=mg)) s (lcomp_state1 _ s1) ->
      return_ L1 s1 r -> lcomp_return s r.

  Definition lcomp: semantics E G := {|
    transition_state := lcomp_state;
    init := lcomp_init;
    call := lcomp_call;
    return_ := lcomp_return;
  |}.

End LComp.

Section IdSem.

  Context {E: esig}.

  Inductive id_state (me: Type): Type :=
  | id_state1: E me -> id_state me
  | id_state2: me -> id_state me.

  Inductive id_init (me: Type): E me -> id_state me -> Prop :=
  | id_init_intro e: id_init e (id_state1 e).

  Inductive id_kont (me: Type): me -> id_state me -> Prop :=
  | id_kont_intro e: id_kont e (id_state2 e).

  Inductive id_call:
    forall me2 me1, id_state me1 -> E me2 -> (me2 -> id_state me1 -> Prop) -> Prop :=
  | id_call_intro me e: @id_call me me (id_state1 e) e (@id_kont me).

  Inductive id_return (me: Type): id_state me -> me -> Prop :=
  | id_return_intro e: id_return (id_state2 e) e.

  Definition id: semantics E E := {|
    transition_state := id_state;
    init := id_init;
    call := id_call;
    return_ := id_return;
  |}.

End IdSem.

Arguments lcomp_state1 {_ _ _} L1 L2 {_} _.
Arguments lcomp_state2 {_ _ _} L1 L2 {_ _} _ _.
Arguments id_state1 {_ _} _.
Arguments id_state2 {_ _} _.

Import RelDefinitions.

Section Properties.

  Section Unit.

    Context {E F: esig} (L: semantics E F).

    Inductive left_unit_match_state: forall mf1 mf2,
      transition_state (lcomp id L) mf1 -> transition_state L mf2 -> (mf1 -> mf2 -> Prop) -> Prop :=
    | left_unit_match_state1 mf (f: F mf) s f_rel:
        subrel eq f_rel ->
        init L f s -> @left_unit_match_state mf mf
                       (lcomp_state1 id L (id_state1 f)) s f_rel
    | left_unit_match_state2 mf s f_rel:
      subrel eq f_rel ->
      @left_unit_match_state
        mf mf (lcomp_state2 id L s (@id_kont F mf)) s f_rel.

    Lemma left_unit1: fsim rc_id rc_id (lcomp id L) L.
    Proof.
      econstructor.
      eapply Build_fsim_properties
        with (match_state:= left_unit_match_state).
      - intros * Hrc Hinit. inv Hinit.
        + inv H. inv H0.
        + inv H.
          (* FIXME: rc_id is tricky: inversion doesn't work; but simple
             inversion works *)
          destruct Hrc as (R & Hrel & Hsub).
          simple inversion Hrel. depsubst.
          inv H0. depsubst.
          exists s2. split; repeat constructor; eauto.
      - intros * Hs Hcall. inv Hcall.
        simple inversion Hs.
        + admit.
        + depsubst. intros Hsub.
          inv H. depsubst.
          * admit.
          * inv H1. depsubst.
            inv KONT.




  End Unit.



End Properties.

Section LCompProp.

  Context {E1 F1 G1} (S1: semantics F1 G1) (T1: semantics E1 F1)
          {E2 F2 G2} (S2: semantics F2 G2) (T2: semantics E2 F2)
          (rcE: refconv E1 E2) (rcF: refconv F1 F2) (rcG: refconv G1 G2)
          (HS: fsim_properties rcF rcG S1 S2)
          (HT: fsim_properties rcE rcF T1 T2).

  Inductive lcomp_match_state mg1 mg2:
    lcomp_state S1 T1 mg1 -> lcomp_state S2 T2 mg2 -> (mg1 -> mg2 -> Prop) -> Prop :=
  | lcomp_match_state1 s1 s2 g_rel
    (MS: match_state HS s1 s2 g_rel):
    lcomp_match_state (state1 S1 T1 _ s1) (state1 S2 T2 _ s2) g_rel
  | lcomp_match_state2 mf1 mf2 (st1: transition_state T1 mf1)
      (st2: transition_state T2 mf2)
      (kont1: mf1 -> transition_state S1 mg1 -> Prop)
      (kont2: mf2 -> transition_state S2 mg2 -> Prop) f_rel g_rel
    (MT: match_state HT st1 st2 f_rel)
    (MKONT: forall fr1 fr2 s1',
        kont1 fr1 s1' -> f_rel fr1 fr2 ->
        exists s2', kont2 fr2 s2' /\
        lcomp_match_state (state1 S1 T1 _ s1') (state1 S2 T2 _ s2') g_rel):
    lcomp_match_state (state2 S1 T1 _ st1 kont1) (state2 S2 T2 _ st2 kont2) g_rel.

  Lemma step_fsim mg1 (s1 s1': lcomp_state S1 T1 mg1)
    mg2 (s2: lcomp_state S2 T2 mg2) g_rel:
    internal_step (mg:=mg1) s1 s1' ->
    lcomp_match_state s1 s2 g_rel ->
    exists s2', internal_step (mg:=mg2) s2 s2' /\
             lcomp_match_state s1' s2' g_rel.
  Proof.
    intros * Hstep Hmatch. inv Hstep.
    - inv Hmatch.
      edestruct (fsim_call HS) as (mf2 & f2 & kont2 & f_rel & Hcall2 & Hf & Hr).
      apply MS. apply CALL.
      edestruct (fsim_init HT) as (s2' & Hs2' & Hm).
      apply Hf. apply INIT.
      exists (state2 S2 T2 _ s2' kont2). split; econstructor; eauto.
      intros * Hk Hx.
      edestruct Hr as (st2' & Hst2' & Hm2). apply Hk. apply Hx.
      exists st2'. split; eauto. econstructor; eauto.
    - inv Hmatch. depsubst.
      edestruct (fsim_return HT) as (rt2 & Hr2 & Hr).
      apply MT. apply RET.
      edestruct MKONT as (s2' & Hs2' & Hm).
      apply KONT. apply Hr.
      inv Hm.
      exists (state1 S2 T2 _ s2'). split; econstructor; eauto.
  Qed.

  Lemma star_step_fsim mg1 (s1 s1': lcomp_state S1 T1 mg1)
    mg2 (s2: lcomp_state S2 T2 mg2) g_rel:
    star (internal_step (mg:=mg1)) s1 s1' ->
    lcomp_match_state s1 s2 g_rel ->
    exists s2', star (internal_step (mg:=mg2)) s2 s2' /\
             lcomp_match_state s1' s2' g_rel.
  Proof.
    intros * Hstar Hmatch. revert s2 Hmatch.
    induction Hstar; intros * Hmatch.
    - exists s2. split; eauto. econstructor.
    - eapply step_fsim in H; eauto.
      destruct H as (s1' & Hs1 & Hm1).
      specialize (IHHstar _ Hm1).
      destruct IHHstar as (s2' & Hs2 & Hm2).
      exists s2'. split; eauto. econstructor; eauto.
  Qed.

  Lemma lcomp_fsim: fsim rcE rcG (LComp S1 T1) (LComp S2 T2).
  Proof.
    econstructor. eapply Build_fsim_properties with (match_state:= lcomp_match_state).
    - intros * Hg Hinit. inv Hinit.
      rename mf1 into mg1. rename mf2 into mg2.
      edestruct (fsim_init HS) as (s2 & Hs & Hm). apply Hg. apply H.
      exists (state1 S2 T2 _ s2). split; constructor; eauto.
    - intros * Hs Hcall. rename mf1 into mg1. rename mf2 into mg2.
      inv Hcall. rename mf into mf1.
      rename kont0 into konts1. rename kont2 into kontt1.
      edestruct star_step_fsim as (s2' & Hs2' & Hm).
      apply H. apply Hs. inv Hm. depsubst.
      rename kont2 into konts2.
      edestruct (fsim_call HT) as (me2 & e2 & kontt2 & e_rel & Hcall2 & He & Hr).
      apply MT. apply H0.
      eexists _, e2, (lift_kont kontt2 konts2), e_rel.
      repeat apply conj; eauto.
      + econstructor; eauto.
      + intros * Hk Hx. inv Hk.
        edestruct Hr as (st2' & Hst2' & Hm). apply H1. apply Hx.
        exists (state2 S2 T2 _ st2' konts2).
        split; econstructor; eauto.
    - intros * Hs Hret. rename mf1 into mg1. rename mf2 into mg2.
      inv Hret.
      edestruct star_step_fsim as (s2' & Hs2' & Hm).
      apply H. apply Hs. inv Hm.
      edestruct (fsim_return HS) as (r2 & Hr2 & Hr).
      apply MS. apply H0.
      exists r2. split; eauto. econstructor; eauto.
  Qed.

End LCompProp.

(* Lift signature with states *)
Inductive state_esig {S: Type} : esig :=
  | state_intro: S -> state_esig S.
Arguments state_esig : clear implicits.

Definition with_state (E: esig) (S: Type) : esig := E * (state_esig S).
Definition op_with_state {E S X} (m : E X) (s: S): with_state E S (X * S)%type :=
  (m * state_intro s)%event.

Infix "#" := with_state (at level 60, no associativity): esig_scope.
Infix "#" := op_with_state (at level 60, no associativity): event_scope.

(* Example *)
Section BoundedQueue.

  Parameter val : Type.
  Parameter N : nat.

  (* Spec of bounded queue *)
  Inductive bq_sig : esig :=
  | enq (v : val) : bq_sig unit
  | deq : bq_sig val.

  Definition bq_state := list val.

  Inductive bq_transition_state : Type -> Type :=
  | enq_state : val -> bq_state -> bq_transition_state (unit * bq_state)
  | deq_state : bq_state -> bq_transition_state (val * bq_state).

  Inductive bq_init: forall m, (bq_sig # bq_state)%esig m -> bq_transition_state m -> Prop :=
  | enq_init v q : bq_init (enq v * state_intro q)%event (enq_state v q)
  | deq_init q : bq_init (deq * state_intro q)%event (deq_state q).

  Inductive bq_call: forall m1 m2,
      bq_transition_state m2 -> empty_sig m1 ->
      (m1 -> bq_transition_state m2 -> Prop) -> Prop := .

  Inductive bq_return: forall m, bq_transition_state m -> m -> Prop :=
  | enq_return v q : bq_return (enq_state v q) (tt, v :: q)
  | deq_return v q : bq_return (deq_state (v :: q)) (v, q).

  Definition L_bq: semantics empty_sig (bq_sig # bq_state) := {|
    transition_state := bq_transition_state;
    init := bq_init;
    call := bq_call;
    return_ := bq_return;
  |}.

  (* Spec of ring buffer *)
  Inductive rb_sig : esig :=
  | set (i : nat) (v : val) : rb_sig unit
  | get (i : nat) : rb_sig val
  | inc1 : rb_sig nat
  | inc2 : rb_sig nat.

  Definition rb_state := ((nat -> val) * nat * nat)%type.

  Definition update (f : nat -> val) (i : nat) (v : val) : nat -> val :=
    fun j => if Nat.eq_dec i j then v else f j.

  Inductive rb_transition_state : Type -> Type :=
  | set_state : nat -> val -> rb_state -> rb_transition_state (unit * rb_state)
  | get_state : nat -> rb_state -> rb_transition_state (val * rb_state)
  | inc1_state : rb_transition_state (nat * rb_state)
  | inc2_state : rb_transition_state (nat * rb_state).

  Inductive rb_init: forall m, (rb_sig # rb_state)%esig m -> rb_transition_state m -> Prop :=
  | set_init i v s : rb_init (set i v * state_intro s)%event (set_state i v s)
  | get_init i s : rb_init (get i * state_intro s)%event (get_state i s)
  | inc1_init s : rb_init (inc1 * state_intro s)%event inc1_state
  | inc2_init s : rb_init (inc2 * state_intro s)%event inc2_state.

  Inductive rb_call: forall m1 m2,
      rb_transition_state m2 -> empty_sig m1 ->
      (m1 -> rb_transition_state m2 -> Prop) -> Prop := .

  Inductive rb_return: forall m, rb_transition_state m -> m -> Prop :=
  | set_return i v f c1 c2 :
    rb_return (set_state i v (f, c1, c2)) (tt, (update f i v, c1, c2))
  | get_return i f c1 c2 :
    rb_return (get_state i (f, c1, c2)) (f i, (f, c1, c2))
  | inc1_return f c1 c2 :
    rb_return inc1_state (c1, (f, (S c1) mod N, c2))%nat
  | inc2_return f c1 c2 :
    rb_return inc2_state (c2, (f, c1, (S c2) mod N))%nat.

  Definition L_rb: semantics empty_sig (rb_sig # rb_state)%esig := {|
    transition_state := rb_transition_state;
    init := rb_init;
    call := rb_call;
    return_ := rb_return;
  |}.

  (* Impl of bounded queue *)
  Inductive bq_impl_transition_state: Type -> Type :=
  | enq_impl_state1 (v: val) : bq_impl_transition_state unit
  | enq_impl_state2 (v: val) (i: nat) : bq_impl_transition_state unit
  | enq_impl_state3 : bq_impl_transition_state unit
  | deq_impl_state1 : bq_impl_transition_state val
  | deq_impl_state2 (i: nat) : bq_impl_transition_state val
  | deq_impl_state3 (v: val) : bq_impl_transition_state val.

  Inductive bq_impl_init: forall m, bq_sig m -> bq_impl_transition_state m -> Prop :=
  | bq_impl_enq_init v : bq_impl_init (enq v) (enq_impl_state1 v)
  | bq_impl_deq_init : bq_impl_init deq deq_impl_state1.

  Inductive enq_kont1 v: nat -> bq_impl_transition_state unit -> Prop :=
  | enq_kont1_intro i : enq_kont1 v i (enq_impl_state2 v i).

  Inductive enq_kont2 : unit -> bq_impl_transition_state unit -> Prop :=
  | enq_kont2_intro : enq_kont2 tt enq_impl_state3.

  Inductive deq_kont1 : nat -> bq_impl_transition_state val -> Prop :=
  | deq_kont1_intro i : deq_kont1 i (deq_impl_state2 i).

  Inductive deq_kont2 : val -> bq_impl_transition_state val -> Prop :=
  | deq_kont2_intro v : deq_kont2 v (deq_impl_state3 v).

  Inductive bq_impl_call:
    forall m1 m2, bq_impl_transition_state m2 -> rb_sig m1 ->
    (m1 -> bq_impl_transition_state m2 -> Prop) -> Prop :=
  | bq_impl_enq_call1 v:
    bq_impl_call (enq_impl_state1 v) inc2 (enq_kont1 v)
  | bq_impl_enq_call2 v i:
    bq_impl_call (enq_impl_state2 v i) (set i v) enq_kont2
  | bq_impl_deq_call1:
    bq_impl_call deq_impl_state1 inc1 deq_kont1
  | bq_impl_deq_call2 i:
    bq_impl_call (deq_impl_state2 i) (get i) deq_kont2.

  Inductive bq_impl_return: forall m, bq_impl_transition_state m -> m -> Prop :=
  | bq_impl_enq_return : bq_impl_return (enq_impl_state3) tt
  | bq_impl_deq_return v : bq_impl_return (deq_impl_state3 v) v.

  Definition M_bq : semantics rb_sig bq_sig := {|
    transition_state := bq_impl_transition_state;
    init := bq_impl_init;
    call := bq_impl_call;
    return_ := bq_impl_return;
  |}.

End BoundedQueue.
