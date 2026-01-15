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
  | step_read_inv e b t:
      e = {| te_tid := t; te_ev := InvEv read |} ->
      StepCoin e b b
  | step_read_res e t b:
      e = {| te_tid := t; te_ev := ResEv read b |} ->
      StepCoin e b b
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
  | step_cas_res_succ e t v w:
      e = {| te_tid := t; te_ev := ResEv (cas v w) true |} ->
      StepCASReg e v w
  | step_cas_res_fail e t u v w:
      u <> v ->
      e = {| te_tid := t; te_ev := ResEv (cas v w) false |} ->
      StepCASReg e u u
  .

  Variant ErrorCASReg {A} : @ThreadEvent (ECASReg A) -> AState -> Prop :=
  | error_set_racy t t' (v u w : A) e:
      t <> t' ->
      e = {| te_tid := t; te_ev := InvEv (set u) |} ->
      ErrorCASReg e (Pending v t' (set w)).

  Definition VCASReg {A} : @LTS (ECASReg A) := VAE StepCASReg ErrorCASReg.
  
End CASRegSpec.



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

