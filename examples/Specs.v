Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.

(* IMPORTANT *)
(*    
    It turns out Coq is more stupid than this. Doing the following cannot solve all similar problems.

    When a single thread event could have multiple transitions,
    must defined transitions in the following way:
    Variant Step : ... :=
    | rule_name params e:
        e = {| te_tid := t; te_ev := ev |} ->
        Step e s1 s2
    ...
    The event should not appear in the conclusion,
    otherwise inversion on the relation will not work.
    Doing so also make sure it will work with the current automation.
*)

Module AtomicLTS.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  
  Section AtomicLTS.
    Context {E : Op.t}.
    Context {StateE : Type}.
    Context (StepE : @ThreadEvent E -> StateE -> StateE -> Prop).

    Variant AState : Type :=
    | Idle (s : StateE) | Pending (s : StateE) (t : tid) (op : Sig.op E).

    Definition state (s : AState) : StateE := 
      match s with
      | Idle s => s
      | Pending s _ _ => s
      end.

    Variant AStep : ThreadEvent -> AState -> AState -> Prop :=
    | step_inv t op s1 s2
        (Hstep : StepE {| te_tid := t; te_ev := InvEv op |} s1 s2):
        AStep {| te_tid := t; te_ev := InvEv op |} (Idle s1) (Pending s2 t op)
    | step_res t op r s1 s2
        (Hstep : StepE {| te_tid := t; te_ev := ResEv op r |} s1 s2):
        AStep {| te_tid := t; te_ev := ResEv op r |} (Pending s1 t op) (Idle s2).

    (* atomic error *)
    Variant AError (error : @ThreadEvent E -> StateE -> Prop) : ThreadEvent -> AState -> Prop :=
    | aerror ev s
        (Herror : error ev s):
        AError error ev (Idle s).

    Definition VAE (error : ThreadEvent -> AState -> Prop) : @LTS E := {|
      State := AState;
      Step := AStep;
      Error := error;
    |}.
    
  End AtomicLTS.
  
End AtomicLTS.


Module FAISpec.
  Import LinCCALBase.
  Import LTSSpec.
  Import AtomicLTS.

  Variant EFAI_op :=
    | fai.

  Canonical Structure EFAI :=
  {|
    Sig.op := EFAI_op;
    Sig.ar _ := nat;
  |}.

  Definition SFAI : Type := nat.
  
  Variant StepFAI : ThreadEvent -> SFAI -> SFAI -> Prop :=
  | step_fai_inv t n : StepFAI {| te_tid := t; te_ev := InvEv fai |} n n
  | step_fai_res t n : StepFAI {| te_tid := t; te_ev := ResEv fai n |} n (S n)
  .

  Definition VFAI : @LTS EFAI := VAE StepFAI NoError.
  
End FAISpec.

Module LockSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant ELock_op :=
    | acq
    | rel.

  Canonical Structure ELock :=
  {|
    Sig.op := ELock_op;
    Sig.ar _ := unit;
  |}.

  Variant SLock : Type :=
  | Locked (t : tid) | Unlocked.
  
  Variant StepLock : ThreadEvent -> SLock -> SLock -> Prop :=
  | step_acq_inv t : StepLock {| te_tid := t; te_ev := InvEv acq |} Unlocked Unlocked
  | step_acq_res t : StepLock {| te_tid := t; te_ev := ResEv acq tt |} Unlocked (Locked t)
  | step_rel_inv t : StepLock {| te_tid := t; te_ev := InvEv rel |} (Locked t) (Locked t)
  | step_rel_res t : StepLock {| te_tid := t; te_ev := ResEv rel tt |} (Locked t) Unlocked
  .

  Variant ErrorLock : ThreadEvent -> SLock -> Prop :=
  | error_rel_rel t : ErrorLock {| te_tid := t; te_ev := InvEv rel |} Unlocked
  | error_rel_race t t' : t <> t' ->
      ErrorLock {| te_tid := t; te_ev := InvEv rel |} (Locked t').
  (* | error_acq_acq t : ErrorLock {| te_tid := t; te_ev := InvEv acq |} Locked. *)

  Definition VLock : @LTS ELock := VAE StepLock (AError ErrorLock).

End LockSpec.

Module RegSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant EReg_op {A} :=
  | get
  | set (v : A).
  Arguments EReg_op : clear implicits.

  Definition EReg_ar {A} (m : EReg_op A) :=
    match m with
      | get => A
      | set _ => unit
    end.
  
  Canonical Structure EReg A :=
  {|
    Sig.op := EReg_op A;
    Sig.ar := EReg_ar
  |}.

  Variant StepReg {A} : @ThreadEvent (EReg A) -> A -> A -> Prop :=
  | step_get_inv t v : StepReg {| te_tid := t; te_ev := InvEv get |} v v
  | step_get_res t v : StepReg {| te_tid := t; te_ev := ResEv get v |} v v
  | step_set_inv t v w : StepReg {| te_tid := t; te_ev := InvEv (set w) |} v v
  | step_set_res t v w: StepReg {| te_tid := t; te_ev := ResEv (set w) tt |} v w
  .

  Variant ErrorReg {A} : @ThreadEvent (EReg A) -> @AState (EReg A) A -> Prop :=
  | error_set_racy t t' v u w :
      (* non-sequetial-consisten steps stuck *)
      t <> t' ->
      ErrorReg {| te_tid := t; te_ev := InvEv (set w) |} (Pending v t' (set u)).
  
  Definition VReg {A} : @LTS (EReg A) := VAE StepReg ErrorReg.

End RegSpec.

(* race-free register *)
Module Reg'Spec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant EReg_op {A} :=
  | get
  | set (v : A).
  Arguments EReg_op : clear implicits.

  Definition EReg_ar {A} (m : EReg_op A) :=
    match m with
      | get => A
      | set _ => unit
    end.
  
  Canonical Structure EReg A :=
  {|
    Sig.op := EReg_op A;
    Sig.ar := EReg_ar
  |}.

  Variant StepReg {A} : @ThreadEvent (EReg A) -> A -> A -> Prop :=
  | step_get_inv t v : StepReg {| te_tid := t; te_ev := InvEv get |} v v
  | step_get_res t v : StepReg {| te_tid := t; te_ev := ResEv get v |} v v
  | step_set_inv t v w : StepReg {| te_tid := t; te_ev := InvEv (set w) |} v v
  | step_set_res t v w: StepReg {| te_tid := t; te_ev := ResEv (set w) tt |} v w
  .

  Definition VReg {A} : @LTS (EReg A) := VAE StepReg NoError.

End Reg'Spec.

Module TryStackSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant ETryStack_op {A} :=
  | push (v : A)
  | pop.
  Arguments ETryStack_op : clear implicits.

  Variant TryResult {A} : Type :=
  | OK (v : A)
  | FAIL.
  Arguments TryResult : clear implicits.

  Definition ETryStack_ar {A} (m : ETryStack_op A) : Type :=
    match m with
      | push _ => TryResult unit
      | pop => TryResult (option A)
    end.
  
  Canonical Structure ETryStack A :=
  {|
    Sig.op := ETryStack_op A;
    Sig.ar := ETryStack_ar
  |}.

  Variant StepTryStack {A} : @ThreadEvent (ETryStack A) -> list A -> list A -> Prop :=
  | step_push_inv t stk v e:
      e = {| te_tid := t; te_ev := InvEv (push v) |} ->
      StepTryStack e stk stk
  | step_push_ok t stk v e : 
      e = {| te_tid := t; te_ev := ResEv (push v) (OK tt) |} ->
      StepTryStack e stk (v :: stk)
  | step_push_fail t stk v e :
      e = {| te_tid := t; te_ev := ResEv (push v) FAIL |} ->
      StepTryStack e stk stk

  | step_pop_inv t stk e:
      e = {| te_tid := t; te_ev := InvEv pop |} ->
      StepTryStack e stk stk
  | step_pop_emp t e:
      e = {| te_tid := t; te_ev := ResEv pop (OK None) |} ->
      StepTryStack e nil nil
  | step_pop_ok t v stk e :
      e = {| te_tid := t; te_ev := ResEv pop (OK (Some v)) |} ->
      StepTryStack e (v :: stk) stk
  | step_pop_fail t stk e:
      e = {| te_tid := t; te_ev := ResEv pop FAIL |} ->
      StepTryStack e stk stk.
  
  Definition VTryStack {A} : @LTS (ETryStack A) := VAE StepTryStack NoError.

End TryStackSpec.



Module StackSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant EStack_op {A} :=
  | push (v : A)
  | pop.
  Arguments EStack_op : clear implicits.

  Definition EStack_ar {A} (m : EStack_op A) : Type :=
    match m with
      | push _ => unit
      | pop => option A
    end.
  
  Canonical Structure EStack A :=
  {|
    Sig.op := EStack_op A;
    Sig.ar := EStack_ar
  |}.

  Variant StepStack {A} : @ThreadEvent (EStack A) -> list A -> list A -> Prop :=
  | step_push_inv t stk v : StepStack {| te_tid := t; te_ev := InvEv (push v) |} stk stk
  | step_push_res t stk v : StepStack {| te_tid := t; te_ev := ResEv (push v) tt |} stk (v :: stk)

  | step_pop_inv t stk : StepStack {| te_tid := t; te_ev := InvEv pop |} stk stk
  | step_pop_emp t : StepStack {| te_tid := t; te_ev := ResEv pop None |} nil nil
  | step_pop_res t v stk : StepStack {| te_tid := t; te_ev := ResEv pop (Some v) |} (v :: stk) stk.
  
  Definition VStack {A} : @LTS (EStack A) := VAE StepStack NoError.

End StackSpec.


Module TicketSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Open Scope list.

  Variant ETicket_op :=
  | acq_ticket
  | cmp_ticket (t : nat)
  | rel_ticket.

  Definition ETicket_ar (m : ETicket_op) : Type :=
    match m with
    | acq_ticket => nat
    | cmp_ticket t => bool
    | rel_ticket => unit
    end.
  
  Canonical Structure ETicket :=
  {|
    Sig.op := ETicket_op;
    Sig.ar := ETicket_ar
  |}.

  Record TicketState : Type := TKS {
    ts_hd : nat;
    ts_q : list tid;
    ts_tl : nat
  }.

  Variant StepTicket : @ThreadEvent ETicket -> TicketState -> TicketState -> Prop :=
  | step_acq_inv e tks t :
      e = {| te_tid := t; te_ev := InvEv acq_ticket |} ->
      StepTicket e tks tks
  | step_acq_res e hd q tl t tks1 tks2 :
      e = {| te_tid := t; te_ev := ResEv acq_ticket tl |} ->
      tks1 = TKS hd q tl ->
      tks2 = TKS hd (q ++ t :: nil) (S tl) ->
      StepTicket e tks1 tks2

  | step_cmp_inv e tks t tk :
      e = {| te_tid := t; te_ev := InvEv (cmp_ticket tk) |} ->
      StepTicket e tks tks
  | step_cmp_res e t tk tks:
      e = {| te_tid := t; te_ev := ResEv (cmp_ticket tk) (tk =? (ts_hd tks))%bool |} ->
      StepTicket e tks tks
  
  | step_rel_inv e tks t :
      e = {| te_tid := t; te_ev := InvEv rel_ticket |} ->
      StepTicket e tks tks
  | step_rel_res e hd q tl t tks1 tks2:
      e = {| te_tid := t; te_ev := ResEv rel_ticket tt |} ->
      tks1 = TKS hd (t :: q) tl ->
      tks2 = TKS (S hd) q tl ->
      StepTicket e tks1 tks2
  .

  Variant ErrorTicket : @ThreadEvent ETicket -> TicketState -> Prop :=
  | error_jump_queue e hd q tl t t' tks:
      t <> t' ->
      e = {| te_tid := t; te_ev := InvEv rel_ticket |} ->
      tks = TKS hd (t' :: q) tl ->
      ErrorTicket e tks
  | error_empty_queue e hd tl t tks:
      e = {| te_tid := t; te_ev := InvEv rel_ticket |} ->
      tks = TKS hd nil tl ->
      ErrorTicket e tks.
  
  Definition VTicket : @LTS ETicket := VAE StepTicket (AError ErrorTicket).
End TicketSpec.

Module CoinSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Variant ECoin_op :=
  | flip
  | read.

  Definition ECoin_ar (m : ECoin_op) : Type :=
    match m with
    | flip => unit
    | read => bool
    end.
  
  Canonical Structure ECoin :=
  {|
    Sig.op := ECoin_op;
    Sig.ar := ECoin_ar
  |}.

  Variant StepCoin : @ThreadEvent ECoin -> bool -> bool -> Prop :=
  | step_flip_inv e b t:
      e = {| te_tid := t; te_ev := InvEv flip |} ->
      StepCoin e b b
  | step_flip_res e t b b':
      e = {| te_tid := t; te_ev := ResEv flip tt |} ->
      StepCoin e b b'
  | step_read_inv b t:
      StepCoin {| te_tid := t; te_ev := InvEv read |} b b
  | step_read_res t b:
      StepCoin {| te_tid := t; te_ev := ResEv read b |} b b
  (* | step_read_inv e b t:
      e = {| te_tid := t; te_ev := InvEv read |} ->
      StepCoin e b b
  | step_read_res e t b:
      e = {| te_tid := t; te_ev := ResEv read b |} ->
      StepCoin e b b *)
  .

  Variant ErrorCoin : @ThreadEvent ECoin -> AState -> Prop :=
  | error_flip_racy t t' (b:bool) e:
      t <> t' ->
      e = {| te_tid := t; te_ev := InvEv flip |} ->
      ErrorCoin e (Pending b t' flip).

  Definition VCoin : @LTS ECoin := VAE StepCoin ErrorCoin.

End CoinSpec.


Module CASRegSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Variant ECASReg_op {A} :=
  | get
  | set (v : A)
  | cas (v w : A).
  Arguments ECASReg_op : clear implicits.

  Definition ECASReg_ar {A} (m : ECASReg_op A) : Type :=
    match m with
    | get => A
    | set _ => unit
    | cas _ _ => bool
    end.
  
  Canonical Structure ECASReg A :=
  {|
    Sig.op := ECASReg_op A;
    Sig.ar := ECASReg_ar
  |}.

  Variant StepCASReg {A} : @ThreadEvent (ECASReg A) -> A -> A -> Prop :=
  | step_get_inv t v : StepCASReg {| te_tid := t; te_ev := InvEv get |} v v
  | step_get_res t v : StepCASReg {| te_tid := t; te_ev := ResEv get v |} v v
  | step_set_inv t v w : StepCASReg {| te_tid := t; te_ev := InvEv (set w) |} v v
  | step_set_res t v w: StepCASReg {| te_tid := t; te_ev := ResEv (set w) tt |} v w
  | step_cas_inv t u v w:
      StepCASReg {| te_tid := t; te_ev := InvEv (cas v w) |} u u
  | step_cas_res_succ t v w b:
      b = true ->
      StepCASReg {| te_tid := t; te_ev := ResEv (cas v w) b |} v w
  | step_cas_res_fail t u v w b:
      b = false ->
      u <> v ->
      StepCASReg {| te_tid := t; te_ev := ResEv (cas v w) b |} u u
  .

  Variant ErrorCASReg {A} : @ThreadEvent (ECASReg A) -> AState -> Prop :=
  | error_set_racy t t' (v u w : A) e:
      t <> t' ->
      e = {| te_tid := t; te_ev := InvEv (set u) |} ->
      ErrorCASReg e (Pending v t' (set w)).

  Definition VCASReg {A} : @LTS (ECASReg A) := VAE StepCASReg ErrorCASReg.
  
  End CASRegSpec.


Module CAS'Spec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Variant ECAS'_op {A} :=
  | get
  | cas (v w : A).
  Arguments ECAS'_op : clear implicits.

  Definition ECAS'_ar {A} (m : ECAS'_op A) : Type :=
    match m with
    | get => A
    | cas _ _ => A
    end.
  
  Canonical Structure ECAS' A :=
  {|
    Sig.op := ECAS'_op A;
    Sig.ar := ECAS'_ar
  |}.

  Variant StepCAS' {A} : @ThreadEvent (ECAS' A) -> A -> A -> Prop :=
  | step_get_inv t v : StepCAS' {| te_tid := t; te_ev := InvEv get |} v v
  | step_get_res t v : StepCAS' {| te_tid := t; te_ev := ResEv get v |} v v
  | step_cas_inv t u v w:
      StepCAS' {| te_tid := t; te_ev := InvEv (cas v w) |} u u
  | step_cas_res_succ t v w b:
      b = true ->
      StepCAS' {| te_tid := t; te_ev := ResEv (cas v w) v |} v w
  | step_cas_res_fail t u v w b:
      b = false ->
      u <> v ->
      StepCAS' {| te_tid := t; te_ev := ResEv (cas v w) u |} u u
  .

  Definition VCAS' {A} : @LTS (ECAS' A) := VAE StepCAS' NoError.
  
End CAS'Spec.

Module CCASSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Variant ECCAS_op {A} :=
  | setFlag (b : bool)
  | cas (o n : A).
  Arguments ECCAS_op : clear implicits.

  Definition ECCAS_ar {A} (m : ECCAS_op A) : Type :=
    match m with
    | setFlag _ => unit
    | cas _ _ => A
    end.
  
  Canonical Structure ECCAS A :=
  {|
    Sig.op := ECCAS_op A;
    Sig.ar := ECCAS_ar
  |}.

  Definition CCASState (A : Type) : Type := A * bool.

  Variant StepCCAS {A} : @ThreadEvent (ECCAS A) -> CCASState A -> CCASState A -> Prop :=
  | step_setFlag_inv t b s:
    StepCCAS {| te_tid := t; te_ev := InvEv (setFlag b) |} s s
  | step_setFlag_res t b b' (v : A):
    StepCCAS {| te_tid := t; te_ev := ResEv (setFlag b) tt |} (v, b') (v, b)
  | step_cas_inv t o n s:
      StepCCAS {| te_tid := t; te_ev := InvEv (cas o n) |} s s
  | step_cas_res_succ t o n b:
      StepCCAS {| te_tid := t; te_ev := ResEv (cas o n) o |} (o, b) (if b then n else o, b)
  | step_cas_res_fail t v o n b:
      v <> o ->
      StepCCAS {| te_tid := t; te_ev := ResEv (cas o n) v |} (v, b) (v, b)
  .
  
  Variant ErrorCCAS {T} : @ThreadEvent (ECCAS T) -> (@AState (ECCAS T) (CCASState T)) -> Prop :=
  | error_set_racy t t' (s : CCASState T) b b':
      t <> t' ->
      ErrorCCAS {| te_tid := t; te_ev := InvEv (setFlag b) |} (Pending s t' (setFlag b')).

  (* MARK: for simplicity, use race-free version *)
  Definition VCCAS {A} : @LTS (ECCAS A) := VAE StepCCAS NoError.
  

End CCASSpec.


Module CASTaskSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Section CASTaskSpec.
    Context {A : Type}.

    Variant CASTask : Type := CTask (t : tid) (o n : A) (i : nat).

    Variant ECASTask_op :=
    | allocTask (o n : A)
    | tryPlaceTask (o n : A) (i : nat)
    | tryResolveTask (tsk : CASTask) (v : A).

    Definition ECASTask_ar (m : ECASTask_op) : Type :=
      match m with
      | allocTask _ _ => nat
      | tryPlaceTask _ _ _ => CASTask + A
      | tryResolveTask _ _ => unit
      end.
    
    Canonical Structure ECASTask :=
    {|
      Sig.op := ECASTask_op;
      Sig.ar := ECASTask_ar
    |}.

    Variant ticket_state : Type :=
      Inactive | Owned (t : tid) | Expired.

    Record CASTaskState : Type := cts {
      current : CASTask + A;
      ticket : nat;
      owner : nat -> ticket_state;
      (* ired : list nat; *)
    }.


    Definition owner_upd (o : nat -> ticket_state) i t : nat -> ticket_state :=
      fun i' => if (i =? i')%nat then t else (o i').

    Variant StepCASTask : @ThreadEvent ECASTask -> CASTaskState -> CASTaskState -> Prop :=
    (* alloc *)
    | step_allocTask_inv cid o n s:
      StepCASTask {| te_tid := cid; te_ev := InvEv (allocTask o n) |} s s
    | step_allocTask_res cid o n c tk  owner:
      StepCASTask {| te_tid := cid; te_ev := ResEv (allocTask o n) tk |}
                  (* increase ticket *)
                  (cts c tk owner ) (cts c (S tk) (owner_upd owner tk (Owned cid)) )
    (* try place *)
    | step_tryPlaceTask_inv cid o n i s:
      StepCASTask {| te_tid := cid; te_ev := InvEv (tryPlaceTask o n i) |} s s
    (* succeed if no task placed *)
    | step_tryPlaceTask_succ cid o n i tk owner e:
      e = {| te_tid := cid; te_ev := ResEv (tryPlaceTask o n i) (inr o) |} ->
      StepCASTask e
                  (* replace with the task *)
                  (cts (inr o) tk owner ) (cts (inl (CTask cid o n i)) tk owner )
    (* blocked if have task placed *)
    | step_tryPlaceTask_block cid o n i tk tsk owner e:
      e = {| te_tid := cid; te_ev := ResEv (tryPlaceTask o n i) (inl tsk) |} ->
      StepCASTask e
                  (* do nothing *)
                  (cts (inl tsk) tk owner ) (cts (inl tsk) tk owner )
    (* fail if o[ld] value does not match *)
    | step_tryPlaceTask_fail cid v o n i tk owner e:
      e = {| te_tid := cid; te_ev := ResEv (tryPlaceTask o n i) (inr v) |} ->
      v <> o ->
      StepCASTask e
                  (* replace with the task *)
                  (cts (inr v) tk owner ) (cts (inr v) tk owner )
    (* try resolve *)
    | step_tryResolveTask_inv cid tsk v s:
      StepCASTask {| te_tid := cid; te_ev := InvEv (tryResolveTask tsk v) |} s s
    | step_tryResolveTask_succ cid v t o n i tk owner:
      StepCASTask {| te_tid := cid; te_ev := ResEv (tryResolveTask (CTask t o n i) v) tt |}
                  (* resolve to the given value *)
                  (* ticket ires *)
                  (cts (inl (CTask t o n i)) tk owner) (cts (inr v) tk (owner_upd owner i Expired))
    | step_tryResolveTask_fail cid c tsk v tk owner:
      c <> (inl tsk) ->
      StepCASTask {| te_tid := cid; te_ev := ResEv (tryResolveTask tsk v) tt |}
                  (* do nothing *)
                  (cts c tk owner) (cts c tk owner)
    .

    Definition VCASTask : @LTS ECASTask := @VAE _ CASTaskState StepCASTask NoError.
    
  End CASTaskSpec.

  Arguments CASTask : clear implicits.
  Arguments ECASTask : clear implicits.
End CASTaskSpec.


(* START WITH THE FOLLOWING TEMPLATE *)
(* Module TemplateSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Variant ETemplate_op :=
  | acq_ticket.

  Definition ETemplate_ar (m : ETemplate_op) : Type :=
    match m with
    | acq_ticket => nat
    end.
  
  Canonical Structure ETemplate :=
  {|
    Sig.op := ETemplate_op;
    Sig.ar := ETemplate_ar
  |}.

  Record TemplateState : Type := TKS {
    ts_hd : nat;
    ts_q : list tid;
    ts_tl : nat
  }.

  Variant StepTemplate : @ThreadEvent ETemplate -> TemplateState -> TemplateState -> Prop :=
  | step_acq_inv e tks t :
      e = {| te_tid := t; te_ev := InvEv acq_ticket |} ->
      StepTemplate e tks tks
  .

  (* Atomic Error *)
  Variant ErrorTemplate : @ThreadEvent ETemplate -> TemplateState -> Prop :=
  | error_jump_queue e t tks:
      e = {| te_tid := t; te_ev := InvEv acq_ticket |} ->
      ErrorTemplate e tks.
  Definition VTemplate : @LTS ETemplate := VAE StepTemplate (AError ErrorTemplate).

  (* Custom Error *)
  (* Variant ErrorTemplate : @ThreadEvent ETemplate -> @AState ETemplate TemplateState -> Prop :=
  | error_set_racy t t' v u w :
      t <> t' ->
      e = {| te_tid := t; te_ev := InvEv acq_ticket |} ->
      ErrorReg  (Pending v t' acq_ticket).
  Definition VTemplate : @LTS ETemplate := VAE StepTemplate ErrorTemplate. *)

  (* No Error *)
  (* Definition VTemplate : @LTS ETemplate := VAE StepTemplate NoError. *)
  
End TemplateSpec. *)
