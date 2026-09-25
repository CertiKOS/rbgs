Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical.
Require Import Coq.Relations.Relation_Operators.
Require Import Lia.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGILogicSet.
Require Import SingletonPossibility.
Require Import CompLinLayer.

Require Import examples.Common.AtomicLTS.
Require Import examples.Common.Heap.
Require Import examples.Common.OwnerMemSpec.
Require Import examples.Common.OwnerMemProof.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.NodeMemSpec.
Require Import examples.TSStack.NodeMem.


Module NodeMemProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSingle SingletonPossibility.
  Import TPSimulationSet.TPSimulation CompLinLayer.
  Import AtomicLTS OwnerMemSpec OwnerMem OwnerMemProof TimestampSpec NodeMemSpec NodeMemImpl.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {A : Type}.

    Definition E : layer_interface := @NodeMemImpl.E A.
    Definition F : layer_interface := @NodeMemImpl.F A.

    Definition single_state :=
      @SinglePossState.ProofStateSingle _ _ (li_lts E) (li_lts F).
    Definition assertion := @Assertion single_state.
    Definition rg_relation :=
      @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F).

    (** * Views of the concrete state *)

    Definition rec_control := @AState (EOMem (@NodeRec)) (OMemState (@NodeRec)).
    Definition val_control := @AState (EOMem A) (OMemState A).
    Definition ts_control := @AState (EOMem TS) (OMemState TS).
    Definition next_control := @AState (EOMem Ptr) (OMemState Ptr).
    Definition taken_control := @AState (EOMem bool) (OMemState bool).

    Definition rec_c (c : State (li_lts E)) : rec_control := fst (fst (fst (fst c))).
    Definition val_c (c : State (li_lts E)) : val_control := snd (fst (fst (fst c))).
    Definition ts_c (c : State (li_lts E)) : ts_control := snd (fst (fst c)).
    Definition next_c (c : State (li_lts E)) : next_control := snd (fst c).
    Definition taken_c (c : State (li_lts E)) : taken_control := snd c.

    Definition rec_h (c : State (li_lts E)) : @Heap (@NodeRec) :=
      om_heap (state (rec_c c)).
    Definition val_h (c : State (li_lts E)) : @Heap A := om_heap (state (val_c c)).
    Definition val_o (c : State (li_lts E)) : @Heap tid := om_owner (state (val_c c)).
    Definition ts_h (c : State (li_lts E)) : @Heap TS := om_heap (state (ts_c c)).
    Definition ts_o (c : State (li_lts E)) : @Heap tid := om_owner (state (ts_c c)).
    Definition next_h (c : State (li_lts E)) : @Heap Ptr := om_heap (state (next_c c)).
    Definition next_o (c : State (li_lts E)) : @Heap tid := om_owner (state (next_c c)).
    Definition taken_h (c : State (li_lts E)) : @Heap bool := om_heap (state (taken_c c)).
    Definition taken_o (c : State (li_lts E)) : @Heap tid := om_owner (state (taken_c c)).

    Definition mk (rc : rec_control) (vc : val_control) (tc : ts_control)
        (nc : next_control) (kc : taken_control) : State (li_lts E) :=
      pair (pair (pair (pair rc vc) tc) nc) kc.

    Lemma state_mk (c : State (li_lts E)) :
      c = mk (rec_c c) (val_c c) (ts_c c) (next_c c) (taken_c c).
    Proof.
      destruct c as [[[[rc vc] tc] nc] kc]. reflexivity.
    Qed.

    (** Projections of the record. *)
    Definition rec_val (r : @NodeRec) : Addr := fst (fst (fst r)).
    Definition rec_ts (r : @NodeRec) : Addr := snd (fst (fst r)).
    Definition rec_taken (r : @NodeRec) : Addr := snd (fst r).
    Definition rec_next (r : @NodeRec) : Addr := snd r.

    Definition node_val (n : @Node A) : A := fst (fst (fst n)).
    Definition node_ts (n : @Node A) : TS := snd (fst (fst n)).
    Definition node_taken (n : @Node A) : bool := snd (fst n).
    Definition node_next (n : @Node A) : Ptr := snd n.

    (** * Steps of one component memory *)

    Section OneMemory.
      Context {X : Type}.

      Definition oread_result (ev : @ThreadEvent (EOMem X)) : option X :=
        match te_ev ev with
        | ResEv op ret =>
            match op return (Sig.ar op -> option X) with
            | oread _ => fun v => Some v
            | _ => fun _ => None
            end ret
        | InvEv _ => None
        end.

      Definition omalloc_result (ev : @ThreadEvent (EOMem X)) : option Addr :=
        match te_ev ev with
        | ResEv op ret =>
            match op return (Sig.ar op -> option Addr) with
            | omalloc _ => fun l => Some l
            | _ => fun _ => None
            end ret
        | InvEv _ => None
        end.

      Definition ocas_result (ev : @ThreadEvent (EOMem X)) : option bool :=
        match te_ev ev with
        | ResEv op ret =>
            match op return (Sig.ar op -> option bool) with
            | ocas _ _ _ => fun b => Some b
            | _ => fun _ => None
            end ret
        | InvEv _ => None
        end.

      Ltac crush_omem_step :=
        repeat match goal with
        | H : {| te_tid := _; te_ev := _ |} = {| te_tid := _; te_ev := _ |} |- _ =>
            first [ apply (f_equal oread_result) in H; discriminate H
                  | apply (f_equal omalloc_result) in H; discriminate H
                  | apply (f_equal ocas_result) in H; discriminate H
                  | injection H; clear H; intros ]
        | H : InvEv _ = ResEv _ _ |- _ => discriminate H
        | H : ResEv _ _ = InvEv _ |- _ => discriminate H
        | H : InvEv _ = InvEv _ |- _ => injection H; clear H; intros
        | H : ResEv _ _ = ResEv _ _ |- _ => injection H; clear H; intros
        | H : omalloc _ = omalloc _ |- _ => injection H; clear H; intros
        | H : oread _ = oread _ |- _ => injection H; clear H; intros
        | H : owrite _ _ = owrite _ _ |- _ => injection H; clear H; intros
        | H : ocas _ _ _ = ocas _ _ _ |- _ => injection H; clear H; intros
        | H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H
        | H : ?x = ?x |- _ => clear H
        | H : ?x = ?y |- _ => is_var y; subst y
        | H : ?x = ?y |- _ => is_var x; subst x
        end;
        try discriminate; try congruence.

      Lemma omem_inv_shape t op (c c' : @AState (EOMem X) (OMemState X)) :
        Step (@VOMem X) {| te_tid := t; te_ev := InvEv op |} c c' ->
        exists s, c = Idle s /\ c' = Pending s t op.
      Proof.
        intros Hstep. inversion Hstep; subst; crush_omem_step.
        inversion Hstep0; subst; crush_omem_step; eauto.
      Qed.

      Lemma omem_alloc_res_shape t v l (c c' : @AState (EOMem X) (OMemState X)) :
        Step (@VOMem X) {| te_tid := t; te_ev := ResEv (omalloc v) l |} c c' ->
        exists s, c = Pending s t (omalloc v) /\ om_heap s l = None /\
          c' = Idle (om_alloc t l v s).
      Proof.
        intros Hstep. inversion Hstep; subst; crush_omem_step.
        inversion Hstep0; subst; crush_omem_step. eauto.
      Qed.

      Lemma omem_read_res_shape t l v (c c' : @AState (EOMem X) (OMemState X)) :
        Step (@VOMem X) {| te_tid := t; te_ev := ResEv (oread l) v |} c c' ->
        exists s, c = Pending s t (oread l) /\ om_heap s l = Some v /\ c' = Idle s.
      Proof.
        intros Hstep. inversion Hstep; subst; crush_omem_step.
        inversion Hstep0; subst; crush_omem_step. eauto.
      Qed.

      Lemma omem_write_res_shape t l v (c c' : @AState (EOMem X) (OMemState X)) :
        Step (@VOMem X) {| te_tid := t; te_ev := ResEv (owrite l v) tt |} c c' ->
        exists s, c = Pending s t (owrite l v) /\ om_heap s l <> None /\
          c' = Idle (om_write l v s).
      Proof.
        intros Hstep. inversion Hstep; subst; crush_omem_step.
        inversion Hstep0; subst; crush_omem_step. eauto.
      Qed.

      Lemma omem_cas_true_shape t l v w (c c' : @AState (EOMem X) (OMemState X)) :
        Step (@VOMem X) {| te_tid := t; te_ev := ResEv (ocas l v w) true |} c c' ->
        exists s, c = Pending s t (ocas l v w) /\ om_heap s l = Some v /\
          c' = Idle (om_write l w s).
      Proof.
        intros Hstep. inversion Hstep; subst; crush_omem_step.
        inversion Hstep0; subst; crush_omem_step. eauto.
      Qed.

      Lemma omem_cas_false_shape t l v w (c c' : @AState (EOMem X) (OMemState X)) :
        Step (@VOMem X) {| te_tid := t; te_ev := ResEv (ocas l v w) false |} c c' ->
        exists s u, c = Pending s t (ocas l v w) /\ om_heap s l = Some u /\
          u <> v /\ c' = Idle s.
      Proof.
        intros Hstep. inversion Hstep; subst; crush_omem_step.
        inversion Hstep0; subst; crush_omem_step. eauto 10.
      Qed.

      (** Errors of one memory. *)
      Lemma omem_alloc_no_error t v (c : @AState (EOMem X) (OMemState X)) :
        ~ Error (@VOMem X) {| te_tid := t; te_ev := InvEv (omalloc v) |} c.
      Proof.
        intros Herr. inversion Herr; subst; crush_omem_step.
      Qed.

      Lemma omem_read_no_error t l (c : @AState (EOMem X) (OMemState X)) :
        om_heap (state c) l <> None ->
        ~ Error (@VOMem X) {| te_tid := t; te_ev := InvEv (oread l) |} c.
      Proof.
        intros Hdef Herr. inversion Herr; subst; crush_omem_step;
        simpl in Hdef; congruence.
      Qed.

      Lemma omem_cas_no_error t l v w (c : @AState (EOMem X) (OMemState X)) :
        om_heap (state c) l <> None ->
        ~ Error (@VOMem X) {| te_tid := t; te_ev := InvEv (ocas l v w) |} c.
      Proof.
        intros Hdef Herr. inversion Herr; subst; crush_omem_step;
        simpl in Hdef; congruence.
      Qed.

      Lemma omem_write_no_error t l v (c : @AState (EOMem X) (OMemState X)) :
        om_heap (state c) l <> None ->
        (forall s t' v', c = Pending s t' (owrite l v') -> t = t') ->
        ~ Error (@VOMem X) {| te_tid := t; te_ev := InvEv (owrite l v) |} c.
      Proof.
        intros Hdef Hrace Herr. inversion Herr; subst; crush_omem_step;
        simpl in Hdef; try congruence.
        match goal with
        | Hne : ?t <> ?t' |- False => apply Hne; eapply Hrace; reflexivity
        end.
      Qed.
    End OneMemory.

    (** * Projecting tensor steps to one component *)

    Definition rec_ev (ev : @Event (EOMem (@NodeRec))) : @Event (li_sig E) :=
      match ev with
      | InvEv m => InvEv (in_rec m)
      | ResEv m r => ResEv (in_rec m) r
      end.
    Definition val_ev (ev : @Event (EOMem A)) : @Event (li_sig E) :=
      match ev with
      | InvEv m => InvEv (in_val m)
      | ResEv m r => ResEv (in_val m) r
      end.
    Definition ts_ev (ev : @Event (EOMem TS)) : @Event (li_sig E) :=
      match ev with
      | InvEv m => InvEv (in_ts m)
      | ResEv m r => ResEv (in_ts m) r
      end.
    Definition next_ev (ev : @Event (EOMem Ptr)) : @Event (li_sig E) :=
      match ev with
      | InvEv m => InvEv (in_next m)
      | ResEv m r => ResEv (in_next m) r
      end.
    Definition taken_ev (ev : @Event (EOMem bool)) : @Event (li_sig E) :=
      match ev with
      | InvEv m => InvEv (in_taken m)
      | ResEv m r => ResEv (in_taken m) r
      end.

    Lemma step_rec t ev c c' :
      Step (li_lts E) {| te_tid := t; te_ev := rec_ev ev |} c c' ->
      Step (@VOMem (@NodeRec)) {| te_tid := t; te_ev := ev |} (rec_c c) (rec_c c') /\
      val_c c' = val_c c /\ ts_c c' = ts_c c /\ next_c c' = next_c c /\
      taken_c c' = taken_c c.
    Proof.
      destruct c as [[[[rc vc] tc] nc] kc], c' as [[[[rc' vc'] tc'] nc'] kc'].
      destruct ev; simpl; unfold in_rec; simpl; intros H;
      decompose [and] H;
      repeat match goal with
      | H : pair _ _ = pair _ _ |- _ => injection H; clear H; intros
      end; subst; auto.
    Qed.

    Lemma step_val t ev c c' :
      Step (li_lts E) {| te_tid := t; te_ev := val_ev ev |} c c' ->
      Step (@VOMem A) {| te_tid := t; te_ev := ev |} (val_c c) (val_c c') /\
      rec_c c' = rec_c c /\ ts_c c' = ts_c c /\ next_c c' = next_c c /\
      taken_c c' = taken_c c.
    Proof.
      destruct c as [[[[rc vc] tc] nc] kc], c' as [[[[rc' vc'] tc'] nc'] kc'].
      destruct ev; simpl; unfold in_val; simpl; intros H;
      decompose [and] H;
      repeat match goal with
      | H : pair _ _ = pair _ _ |- _ => injection H; clear H; intros
      end; subst; auto.
    Qed.

    Lemma step_ts t ev c c' :
      Step (li_lts E) {| te_tid := t; te_ev := ts_ev ev |} c c' ->
      Step (@VOMem TS) {| te_tid := t; te_ev := ev |} (ts_c c) (ts_c c') /\
      rec_c c' = rec_c c /\ val_c c' = val_c c /\ next_c c' = next_c c /\
      taken_c c' = taken_c c.
    Proof.
      destruct c as [[[[rc vc] tc] nc] kc], c' as [[[[rc' vc'] tc'] nc'] kc'].
      destruct ev; simpl; unfold in_ts; simpl; intros H;
      decompose [and] H;
      repeat match goal with
      | H : pair _ _ = pair _ _ |- _ => injection H; clear H; intros
      end; subst; auto.
    Qed.

    Lemma step_next t ev c c' :
      Step (li_lts E) {| te_tid := t; te_ev := next_ev ev |} c c' ->
      Step (@VOMem Ptr) {| te_tid := t; te_ev := ev |} (next_c c) (next_c c') /\
      rec_c c' = rec_c c /\ val_c c' = val_c c /\ ts_c c' = ts_c c /\
      taken_c c' = taken_c c.
    Proof.
      destruct c as [[[[rc vc] tc] nc] kc], c' as [[[[rc' vc'] tc'] nc'] kc'].
      destruct ev; simpl; unfold in_next; simpl; intros H;
      decompose [and] H;
      repeat match goal with
      | H : pair _ _ = pair _ _ |- _ => injection H; clear H; intros
      end; subst; auto.
    Qed.

    Lemma step_taken t ev c c' :
      Step (li_lts E) {| te_tid := t; te_ev := taken_ev ev |} c c' ->
      Step (@VOMem bool) {| te_tid := t; te_ev := ev |} (taken_c c) (taken_c c') /\
      rec_c c' = rec_c c /\ val_c c' = val_c c /\ ts_c c' = ts_c c /\
      next_c c' = next_c c.
    Proof.
      destruct c as [[[[rc vc] tc] nc] kc], c' as [[[[rc' vc'] tc'] nc'] kc'].
      destruct ev; simpl; unfold in_taken; simpl; intros H;
      decompose [and] H;
      repeat match goal with
      | H : pair _ _ = pair _ _ |- _ => injection H; clear H; intros
      end; subst; auto.
    Qed.

    Lemma error_rec t ev c :
      Error (li_lts E) {| te_tid := t; te_ev := rec_ev ev |} c ->
      Error (@VOMem (@NodeRec)) {| te_tid := t; te_ev := ev |} (rec_c c).
    Proof.
      destruct c as [[[[rc vc] tc] nc] kc]. destruct ev; simpl; unfold in_rec; auto.
    Qed.

    Lemma error_val t ev c :
      Error (li_lts E) {| te_tid := t; te_ev := val_ev ev |} c ->
      Error (@VOMem A) {| te_tid := t; te_ev := ev |} (val_c c).
    Proof.
      destruct c as [[[[rc vc] tc] nc] kc]. destruct ev; simpl; unfold in_val; auto.
    Qed.

    Lemma error_ts t ev c :
      Error (li_lts E) {| te_tid := t; te_ev := ts_ev ev |} c ->
      Error (@VOMem TS) {| te_tid := t; te_ev := ev |} (ts_c c).
    Proof.
      destruct c as [[[[rc vc] tc] nc] kc]. destruct ev; simpl; unfold in_ts; auto.
    Qed.

    Lemma error_next t ev c :
      Error (li_lts E) {| te_tid := t; te_ev := next_ev ev |} c ->
      Error (@VOMem Ptr) {| te_tid := t; te_ev := ev |} (next_c c).
    Proof.
      destruct c as [[[[rc vc] tc] nc] kc]. destruct ev; simpl; unfold in_next; auto.
    Qed.

    Lemma error_taken t ev c :
      Error (li_lts E) {| te_tid := t; te_ev := taken_ev ev |} c ->
      Error (@VOMem bool) {| te_tid := t; te_ev := ev |} (taken_c c).
    Proof.
      destruct c as [[[[rc vc] tc] nc] kc]. destruct ev; simpl; unfold in_taken; auto.
    Qed.

    (** * The invariant *)

    Definition abs (s : single_state) : @Heap (@Node A) := state (ρ s).

    Definition mknode (v : A) (ts : TS) (tk : bool) (nx : Ptr) : @Node A :=
      pair (pair (pair v ts) tk) nx.
    Definition mkrec (lv lts lt ln : Addr) : @NodeRec :=
      pair (pair (pair lv lts) lt) ln.

    Ltac simpl_fields H :=
      cbn [rec_val rec_ts rec_taken rec_next mkrec node_val node_ts node_taken
           node_next mknode fst snd] in H.
    Ltac simpl_fields_goal :=
      cbn [rec_val rec_ts rec_taken rec_next mkrec node_val node_ts node_taken
           node_next mknode fst snd].


    Definition fields_defined (c : State (li_lts E)) (r : @NodeRec) : Prop :=
      val_h c (rec_val r) <> None /\ ts_h c (rec_ts r) <> None /\
      taken_h c (rec_taken r) <> None /\ next_h c (rec_next r) <> None.

    Definition represents (c : State (li_lts E)) (r : @NodeRec) (n : @Node A) : Prop :=
      val_h c (rec_val r) = Some (node_val n) /\
      ts_h c (rec_ts r) = Some (node_ts n) /\
      taken_h c (rec_taken r) = Some (node_taken n) /\
      next_h c (rec_next r) = Some (node_next n).

    Definition referenced_val (c : State (li_lts E)) (a : Addr) : Prop :=
      exists l r, rec_h c l = Some r /\ rec_val r = a.
    Definition referenced_ts (c : State (li_lts E)) (a : Addr) : Prop :=
      exists l r, rec_h c l = Some r /\ rec_ts r = a.
    Definition referenced_taken (c : State (li_lts E)) (a : Addr) : Prop :=
      exists l r, rec_h c l = Some r /\ rec_taken r = a.
    Definition referenced_next (c : State (li_lts E)) (a : Addr) : Prop :=
      exists l r, rec_h c l = Some r /\ rec_next r = a.

    (** Facts about the concrete heaps alone.  They hold in every reachable
        state: the fields of a record are allocated, and distinct records
        never share a timestamp or a taken cell. *)
    Definition IConcrete (c : State (li_lts E)) : Prop :=
      (forall l r, rec_h c l = Some r -> fields_defined c r) /\
      (forall l1 l2 r1 r2, rec_h c l1 = Some r1 -> rec_h c l2 = Some r2 ->
        l1 <> l2 -> rec_ts r1 <> rec_ts r2 /\ rec_taken r1 <> rec_taken r2).

    (** The thread [t] is inside [nmsetTS l _] and has not linearized. *)
    Definition AtSetTS (s : single_state) (t : tid) (l : Addr) : Prop :=
      exists ts, TMap.find t (π s) = Some (ls_inv (nmsetTS l ts)).

    Definition OtherAtSetTS (s : single_state) (t : tid) (l : Addr) : Prop :=
      exists t', t <> t' /\ AtSetTS s t' l.

    (** A pending store to a timestamp cell belongs to a [setTS] on the node
        that owns the cell. *)
    Definition PendingTSWrite (s : single_state) : Prop :=
      forall st t' a v, ts_c (σ s) = Pending st t' (owrite a v) ->
        exists l r, rec_h (σ s) l = Some r /\ rec_ts r = a /\ AtSetTS s t' l.

    (** Two unlinearized [setTS] on the same node: the specification's racy
        error is reachable, and nothing further is owed. *)
    Definition Err : assertion := fun s =>
      exists l t1 t2, t1 <> t2 /\ AtSetTS s t1 l /\ AtSetTS s t2 l.

    (** The abstract heap is represented by the record and field memories. *)
    Definition Rep (s : single_state) : Prop :=
      (forall l, abs s l = None <-> rec_h (σ s) l = None) /\
      (forall l r, rec_h (σ s) l = Some r ->
        exists n, abs s l = Some n /\ represents (σ s) r n).

    Definition I : assertion := fun s =>
      (exists h, ρ s = Idle h) /\ IConcrete (σ s) /\ PendingTSWrite s /\
      (Err s \/ Rep s).

    (** * Thread-local assertions *)

    Definition Defined (l : Addr) : assertion := fun s => rec_h (σ s) l <> None.
    Definition RecIs (l : Addr) (r : @NodeRec) : assertion :=
      fun s => rec_h (σ s) l = Some r.

    Definition FreshVal (t : tid) (a : Addr) (v : A) : assertion := fun s =>
      val_h (σ s) a = Some v /\ val_o (σ s) a = Some t /\ ~ referenced_val (σ s) a.
    Definition FreshTS (t : tid) (a : Addr) : assertion := fun s =>
      ts_h (σ s) a = Some TSTop /\ ts_o (σ s) a = Some t /\ ~ referenced_ts (σ s) a.
    Definition FreshTaken (t : tid) (a : Addr) : assertion := fun s =>
      taken_h (σ s) a = Some false /\ taken_o (σ s) a = Some t /\
      ~ referenced_taken (σ s) a.
    Definition FreshNext (t : tid) (a : Addr) (nx : Ptr) : assertion := fun s =>
      next_h (σ s) a = Some nx /\ next_o (σ s) a = Some t /\
      ~ referenced_next (σ s) a.

    Definition AbsTSTop (l : Addr) : assertion :=
      fun s => exists n, abs s l = Some n /\ node_ts n = TSTop.

    (** [setTS] has read [TSTop]: the abstract timestamp is still [TSTop]
        (unless the racy error is already reachable), and it stays so while
        the actor is unlinearized. *)
    Definition TSTopSeen (t : tid) (l : Addr) (ts : TS) : assertion := fun s =>
      TMap.find t (π s) = Some (ls_inv (nmsetTS l ts)) /\ (Err s \/ AbsTSTop l s).

    (** * Rely and guarantee *)

    Definition HeapRely (c c' : State (li_lts E)) : Prop :=
      (forall l r, rec_h c l = Some r -> rec_h c' l = Some r) /\
      (forall a o, val_h c a <> None -> val_o c a = Some o -> val_o c' a = Some o) /\
      (forall a o, ts_h c a <> None -> ts_o c a = Some o -> ts_o c' a = Some o) /\
      (forall a o, taken_h c a <> None -> taken_o c a = Some o ->
        taken_o c' a = Some o) /\
      (forall a o, next_h c a <> None -> next_o c a = Some o -> next_o c' a = Some o) /\
      (forall a v, val_h c a = Some v -> val_h c' a = Some v) /\
      (forall a v, next_h c a = Some v -> next_h c' a = Some v) /\
      (forall a v, ts_h c a = Some v -> ~ referenced_ts c a -> ts_h c' a = Some v) /\
      (forall a v, taken_h c a = Some v -> ~ referenced_taken c a ->
        taken_h c' a = Some v).

    Definition NewRecOwner (P : option tid -> Prop) (c c' : State (li_lts E)) : Prop :=
      forall l r, rec_h c l = None -> rec_h c' l = Some r ->
        P (val_o c' (rec_val r)) /\ P (ts_o c' (rec_ts r)) /\
        P (taken_o c' (rec_taken r)) /\ P (next_o c' (rec_next r)).

    (** Guarantee of [t]: other threads' linearization tokens are untouched;
        records are immutable and a new record owns its fields; unreferenced
        cells never change; the abstract timestamp of a node changes only
        when no other thread is inside an unlinearized [setTS] on it; and a
        thread inside a racing [setTS] does not linearize. *)
    Definition G (t : tid) : rg_relation := fun s s' =>
      (forall t', t <> t' -> TMap.find t' (π s) = TMap.find t' (π s')) /\
      HeapRely (σ s) (σ s') /\
      NewRecOwner (fun o => o = Some t) (σ s) (σ s') /\
      (forall l n, abs s l = Some n -> exists n', abs s' l = Some n' /\
        (node_ts n' <> node_ts n -> ~ OtherAtSetTS s t l)) /\
      (forall l, AtSetTS s t l -> OtherAtSetTS s t l ->
        TMap.find t (π s) = TMap.find t (π s')).

    Definition R (t : tid) : rg_relation := fun s s' =>
      TMap.find t (π s) = TMap.find t (π s') /\
      HeapRely (σ s) (σ s') /\
      NewRecOwner (fun o => o <> Some t) (σ s) (σ s') /\
      (forall l n, abs s l = Some n -> exists n', abs s' l = Some n' /\
        (node_ts n' <> node_ts n -> ~ AtSetTS s t l)) /\
      (Err s -> Err s').

    Lemma HeapRely_refl c : HeapRely c c.
    Proof. unfold HeapRely. repeat split; auto. Qed.

    (** * Stability *)

    Lemma I_stable t : Stable (R t) I I.
    Proof. apply Stable_invariant. Qed.

    Lemma ALin_stable t ls : Stable (R t) I (ALin t ls).
    Proof.
      intros s [[pre [Hlin [Hπ _]]] _]. unfold ALin in *. congruence.
    Qed.

    Lemma Pure_stable t (P : Prop) : Stable (R t) I (⌜P⌝).
    Proof. apply APureStable. Qed.

    Lemma Err_stable t : Stable (R t) I Err.
    Proof.
      intros s [[pre [Herr [_ [_ [_ [_ HR]]]]]] _]. exact (HR Herr).
    Qed.

    Lemma Defined_stable t l : Stable (R t) I (Defined l).
    Proof.
      intros s [[pre [Hdef [_ [[Hrec _] _]]]] _].
      unfold Defined in *. destruct (rec_h (σ pre) l) as [r|] eqn:Hr;
        [|contradiction].
      rewrite (Hrec _ _ Hr). discriminate.
    Qed.

    Lemma RecIs_stable t l r : Stable (R t) I (RecIs l r).
    Proof.
      intros s [[pre [Hr [_ [[Hrec _] _]]]] _]. unfold RecIs in *. auto.
    Qed.

    Lemma FreshVal_stable t a v : Stable (R t) I (FreshVal t a v).
    Proof.
      intros s [[pre [[Hh [Ho Hnr]] [_ [HH [Hnew _]]]]] _].
      destruct HH as [Hrec [Hown [_ [_ [_ [Hvh _]]]]]].
      split; [auto|]. split; [eapply Hown; [congruence|exact Ho]|].
      intros [l [r [Hl Hr]]]. subst a.
      destruct (rec_h (σ pre) l) as [r0|] eqn:Hr0.
      - pose proof (Hrec _ _ Hr0) as Hr1. rewrite Hr1 in Hl. injection Hl as ->.
        apply Hnr. exists l, r. auto.
      - destruct (Hnew _ _ Hr0 Hl) as [Hnewo _]. apply Hnewo.
        apply Hown; [congruence|exact Ho].
    Qed.

    Lemma FreshTS_stable t a : Stable (R t) I (FreshTS t a).
    Proof.
      intros s [[pre [[Hh [Ho Hnr]] [_ [HH [Hnew _]]]]] _].
      destruct HH as [Hrec [_ [Hown [_ [_ [_ [_ [Hth _]]]]]]]].
      split; [auto|]. split; [eapply Hown; [congruence|exact Ho]|].
      intros [l [r [Hl Hr]]]. subst a.
      destruct (rec_h (σ pre) l) as [r0|] eqn:Hr0.
      - pose proof (Hrec _ _ Hr0) as Hr1. rewrite Hr1 in Hl. injection Hl as ->.
        apply Hnr. exists l, r. auto.
      - destruct (Hnew _ _ Hr0 Hl) as [_ [Hnewo _]]. apply Hnewo.
        apply Hown; [congruence|exact Ho].
    Qed.

    Lemma FreshTaken_stable t a : Stable (R t) I (FreshTaken t a).
    Proof.
      intros s [[pre [[Hh [Ho Hnr]] [_ [HH [Hnew _]]]]] _].
      destruct HH as [Hrec [_ [_ [Hown [_ [_ [_ [_ Hkh]]]]]]]].
      split; [auto|]. split; [eapply Hown; [congruence|exact Ho]|].
      intros [l [r [Hl Hr]]]. subst a.
      destruct (rec_h (σ pre) l) as [r0|] eqn:Hr0.
      - pose proof (Hrec _ _ Hr0) as Hr1. rewrite Hr1 in Hl. injection Hl as ->.
        apply Hnr. exists l, r. auto.
      - destruct (Hnew _ _ Hr0 Hl) as [_ [_ [Hnewo _]]]. apply Hnewo.
        apply Hown; [congruence|exact Ho].
    Qed.

    Lemma FreshNext_stable t a nx : Stable (R t) I (FreshNext t a nx).
    Proof.
      intros s [[pre [[Hh [Ho Hnr]] [_ [HH [Hnew _]]]]] _].
      destruct HH as [Hrec [_ [_ [_ [Hown [_ [Hnh _]]]]]]].
      split; [auto|]. split; [eapply Hown; [congruence|exact Ho]|].
      intros [l [r [Hl Hr]]]. subst a.
      destruct (rec_h (σ pre) l) as [r0|] eqn:Hr0.
      - pose proof (Hrec _ _ Hr0) as Hr1. rewrite Hr1 in Hl. injection Hl as ->.
        apply Hnr. exists l, r. auto.
      - destruct (Hnew _ _ Hr0 Hl) as [_ [_ [_ Hnewo]]]. apply Hnewo.
        apply Hown; [congruence|exact Ho].
    Qed.

    Lemma TSTopSeen_stable t l ts : Stable (R t) I (TSTopSeen t l ts).
    Proof.
      intros s [[pre [[Hlin Habs] [Hπ [_ [_ [Hts HErr]]]]]] _].
      split; [congruence|].
      destruct Habs as [Herr | [n [Hn Htop]]].
      - left. exact (HErr Herr).
      - right. destruct (Hts _ _ Hn) as [n' [Hn' Hchange]].
        exists n'. split; [exact Hn'|].
        destruct (classic (node_ts n' = node_ts n)) as [Heq|Hneq].
        + congruence.
        + exfalso. apply (Hchange Hneq). exists ts. exact Hlin.
    Qed.

    Create HintDb stableDB.
    #[local] Hint Resolve I_stable ALin_stable Pure_stable Err_stable
      Defined_stable RecIs_stable FreshVal_stable FreshTS_stable
      FreshTaken_stable FreshNext_stable TSTopSeen_stable : stableDB.

    (** * Rely/guarantee side conditions *)

    Lemma source_valid_rg t : forall s s', R t s s' -> I s' ->
      TMap.find t (π s) = None <-> TMap.find t (π s') = None.
    Proof. intros s s' [Hπ _] _. rewrite Hπ. tauto. Qed.

    Lemma R_refl t s : R t s s.
    Proof.
      split; [reflexivity|]. split; [apply HeapRely_refl|].
      split; [intros l r H1 H2; congruence|].
      split; [|auto].
      intros l n Hn. exists n. split; [exact Hn|]. intros Hc. contradiction.
    Qed.

    Lemma source_rg_compatible t1 t2 : t1 <> t2 -> forall s s',
      (G t1 s s' \/ (GINV t1 s s' \/ GRET t1 s s') \/ GId s s') ->
      R t2 s s'.
    Proof.
      intros Hneq s s' [HG | [[Hinv | Hret] | Hid]].
      - destruct HG as [Hπ [HH [Hnew [Habs Hprot]]]].
        split; [apply Hπ; exact Hneq|]. split; [exact HH|]. split.
        + intros l r Hnone Hsome.
          destruct (Hnew _ _ Hnone Hsome) as [H1 [H2 [H3 H4]]].
          rewrite H1, H2, H3, H4.
          repeat split; intros Heq; injection Heq; intros; congruence.
        + split.
          * intros l n Hn. destruct (Habs _ _ Hn) as [n' [Hn' Hch]].
            exists n'. split; [exact Hn'|].
            intros Hts Hat. apply (Hch Hts). exists t2. split; auto.
          * intros [l [ta [tb [Hab [Ha Hb]]]]]. exists l, ta, tb.
            split; [exact Hab|].
            assert (Hkeep : forall tx ty, tx <> ty ->
              AtSetTS s tx l -> AtSetTS s ty l -> AtSetTS s' tx l).
            { intros tx ty Hxy [ts Hx] Hy. exists ts.
              destruct (Pos.eq_dec t1 tx) as [->|Hne].
              - rewrite <- (Hprot l); [exact Hx|exists ts; exact Hx|].
                exists ty. split; auto.
              - rewrite <- Hπ; auto. }
            split; [eapply Hkeep; eauto|eapply Hkeep; eauto].
      - destruct Hinv as [f [Hσ [Hρ [Hnone Hπ]]]].
        unfold R, abs. rewrite <- Hσ, <- Hρ, Hπ.
        split; [rewrite TMap.gso; auto|].
        split; [apply HeapRely_refl|].
        split; [intros l r H1 H2; congruence|].
        split; [intros l n Hn; exists n; split; [exact Hn|intros Hc; contradiction]|].
        intros [l [ta [tb [Hab [[tsa Ha] [tsb Hb]]]]]].
        exists l, ta, tb. split; [exact Hab|].
        split; [exists tsa|exists tsb]; rewrite Hπ, TMap.gso; auto; congruence.
      - destruct Hret as [f [ret [Hσ [Hρ [Hsome Hπ]]]]].
        unfold R, abs. rewrite <- Hσ, <- Hρ, Hπ.
        split; [rewrite TMap.gro; auto|].
        split; [apply HeapRely_refl|].
        split; [intros l r H1 H2; congruence|].
        split; [intros l n Hn; exists n; split; [exact Hn|intros Hc; contradiction]|].
        intros [l [ta [tb [Hab [[tsa Ha] [tsb Hb]]]]]].
        exists l, ta, tb. split; [exact Hab|].
        split; [exists tsa|exists tsb]; rewrite Hπ, TMap.gro; auto; congruence.
      - unfold GId in Hid. subst. apply R_refl.
    Qed.

    (** * Reaching the specification's errors *)

    Lemma Err_APError : ⊨ I //\\ Err ==>> APError.
    Proof.
      intros s [[[h Hρ] _] [l [t1 [t2 [Hneq [[ts1 H1] [ts2 H2]]]]]]].
      unfold APError. rewrite Hρ.
      destruct (h l) eqn:Hl.
      - eapply rt_trans.
        + apply rt_step. apply (ps_inv t1 (nmsetTS l ts1)); [|exact H1].
          apply step_inv. eapply step_setTS_inv; [reflexivity|].
          rewrite Hl. discriminate.
        + apply rt_step. eapply (ps_error t2 (nmsetTS l ts2)).
          * eapply error_setTS_racy; [| |reflexivity]; [congruence|reflexivity].
          * rewrite TMap.gso; [exact H2|congruence].
      - apply rt_step. eapply (ps_error t1 (nmsetTS l ts1)); [|exact H1].
        eapply error_setTS_undefined; [reflexivity|exact Hl].
    Qed.

    Lemma undefined_APError t (f : Sig.op (li_sig F)) l s :
      I s -> TMap.find t (π s) = Some (ls_inv f) -> abs s l = None ->
      (forall h, h l = None ->
        ErrorNodeMem {| te_tid := t; te_ev := InvEv f |} (Idle h)) ->
      APError s.
    Proof.
      intros [[h Hρ] _] Hlin Habs Herr. unfold APError. rewrite Hρ.
      unfold abs in Habs. rewrite Hρ in Habs. simpl in Habs.
      apply rt_step. eapply (ps_error t f); [|exact Hlin].
      apply Herr. exact Habs.
    Qed.

    (** Every method except allocation starts by reading the record cell.
        Either the node is allocated, or the specification is in error. *)
    Lemma defined_or_error t (f : Sig.op (li_sig F)) l :
      (forall h, h l = None ->
        ErrorNodeMem {| te_tid := t; te_ev := InvEv f |} (Idle h)) ->
      ⊨ I //\\ ALin t (ls_inv f) ==>>
        (I //\\ ALin t (ls_inv f) //\\ Defined l) \\// APError.
    Proof.
      intros Herr s [HI Hlin]. pose proof HI as [Hρ [Hc [Hp Hor]]].
      destruct Hor as [HErr | [Hnone Hsome]].
      - right. apply Err_APError. split; assumption.
      - destruct (abs s l) as [n|] eqn:Hl.
        + left. split; [exact HI|]. split; [exact Hlin|].
          unfold Defined. intros Hrec. apply Hnone in Hrec.
          rewrite Hl in Hrec. discriminate.
        + right. eapply undefined_APError; eauto.
    Qed.

    (** * Underlay steps never error *)

    Lemma alloc_val_no_error t v (P : assertion) :
      ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv (in_val (omalloc v)) |}.
    Proof.
      intros s _ Herr. apply (error_val t (InvEv (omalloc v))) in Herr.
      eapply omem_alloc_no_error; exact Herr.
    Qed.

    Lemma alloc_ts_no_error t v (P : assertion) :
      ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv (in_ts (omalloc v)) |}.
    Proof.
      intros s _ Herr. apply (error_ts t (InvEv (omalloc v))) in Herr.
      eapply omem_alloc_no_error; exact Herr.
    Qed.

    Lemma alloc_next_no_error t v (P : assertion) :
      ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv (in_next (omalloc v)) |}.
    Proof.
      intros s _ Herr. apply (error_next t (InvEv (omalloc v))) in Herr.
      eapply omem_alloc_no_error; exact Herr.
    Qed.

    Lemma alloc_taken_no_error t v (P : assertion) :
      ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv (in_taken (omalloc v)) |}.
    Proof.
      intros s _ Herr. apply (error_taken t (InvEv (omalloc v))) in Herr.
      eapply omem_alloc_no_error; exact Herr.
    Qed.

    Lemma alloc_rec_no_error t v (P : assertion) :
      ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv (in_rec (omalloc v)) |}.
    Proof.
      intros s _ Herr. apply (error_rec t (InvEv (omalloc v))) in Herr.
      eapply omem_alloc_no_error; exact Herr.
    Qed.

    Lemma read_rec_no_error t l (P : assertion) :
      (⊨ P ==>> Defined l) ->
      ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv (in_rec (oread l)) |}.
    Proof.
      intros HP s HPs Herr. pose proof (HP s HPs) as Hdef. apply (error_rec t (InvEv (oread l))) in Herr.
      eapply omem_read_no_error; [exact Hdef|exact Herr].
    Qed.

    Lemma I_fields_defined l r s :
      I s -> RecIs l r s -> fields_defined (σ s) r.
    Proof. intros [_ [[Hf _] _]] Hr. apply (Hf _ _ Hr). Qed.

    Lemma read_val_no_error t l r (P : assertion) :
      (⊨ P ==>> I //\\ RecIs l r) ->
      ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv (in_val (oread (rec_val r))) |}.
    Proof.
      intros HP s HPs Herr. destruct (HP s HPs) as [HI Hr]. apply (error_val t (InvEv (oread (rec_val r)))) in Herr.
      destruct (I_fields_defined _ _ _ HI Hr) as [Hdef _].
      eapply omem_read_no_error; [exact Hdef|exact Herr].
    Qed.

    Lemma read_ts_no_error t l r (P : assertion) :
      (⊨ P ==>> I //\\ RecIs l r) ->
      ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv (in_ts (oread (rec_ts r))) |}.
    Proof.
      intros HP s HPs Herr. destruct (HP s HPs) as [HI Hr]. apply (error_ts t (InvEv (oread (rec_ts r)))) in Herr.
      destruct (I_fields_defined _ _ _ HI Hr) as [_ [Hdef _]].
      eapply omem_read_no_error; [exact Hdef|exact Herr].
    Qed.

    Lemma read_taken_no_error t l r (P : assertion) :
      (⊨ P ==>> I //\\ RecIs l r) ->
      ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv (in_taken (oread (rec_taken r))) |}.
    Proof.
      intros HP s HPs Herr. destruct (HP s HPs) as [HI Hr].
      apply (error_taken t (InvEv (oread (rec_taken r)))) in Herr.
      destruct (I_fields_defined _ _ _ HI Hr) as [_ [_ [Hdef _]]].
      eapply omem_read_no_error; [exact Hdef|exact Herr].
    Qed.

    Lemma read_next_no_error t l r (P : assertion) :
      (⊨ P ==>> I //\\ RecIs l r) ->
      ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv (in_next (oread (rec_next r))) |}.
    Proof.
      intros HP s HPs Herr. destruct (HP s HPs) as [HI Hr].
      apply (error_next t (InvEv (oread (rec_next r)))) in Herr.
      destruct (I_fields_defined _ _ _ HI Hr) as [_ [_ [_ Hdef]]].
      eapply omem_read_no_error; [exact Hdef|exact Herr].
    Qed.

    Lemma cas_taken_no_error t l r v w (P : assertion) :
      (⊨ P ==>> I //\\ RecIs l r) ->
      ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv (in_taken (ocas (rec_taken r) v w)) |}.
    Proof.
      intros HP s HPs Herr. destruct (HP s HPs) as [HI Hr].
      apply (error_taken t (InvEv (ocas (rec_taken r) v w))) in Herr.
      destruct (I_fields_defined _ _ _ HI Hr) as [_ [_ [Hdef _]]].
      eapply omem_cas_no_error; [exact Hdef|exact Herr].
    Qed.

    (** No other thread has a pending store to the timestamp cell [a]. *)
    Definition NoOtherTSWrite (t : tid) (a : Addr) : assertion := fun s =>
      forall st t' v, ts_c (σ s) = Pending st t' (owrite a v) -> t = t'.

    (** Before storing the timestamp: either the store is race free, or the
        other writer is inside a [setTS] on the same node and the
        specification's racy error is reachable. *)
    Lemma ts_write_race_or_error t l r ts :
      ⊨ I //\\ TSTopSeen t l ts //\\ RecIs l r ==>>
        (I //\\ TSTopSeen t l ts //\\ RecIs l r //\\ NoOtherTSWrite t (rec_ts r))
        \\// APError.
    Proof.
      intros s [HI [Hseen Hr]].
      destruct (classic (exists st t' v,
        ts_c (σ s) = Pending st t' (owrite (rec_ts r) v) /\ t <> t'))
        as [[st [t' [v [Hpend Hneq]]]] | Hno].
      - right. apply Err_APError. split; [exact HI|].
        destruct HI as [_ [[_ Hinj] [Hp _]]].
        destruct (Hp _ _ _ _ Hpend) as [l' [r' [Hr' [Hts' Hat']]]].
        destruct (Nat.eq_dec l l') as [<-|Hll].
        + exists l, t, t'. split; [exact Hneq|]. split; [|exact Hat'].
          exists ts. apply Hseen.
        + exfalso. destruct (Hinj _ _ _ _ Hr Hr' Hll) as [Hne _]. congruence.
      - left. split; [exact HI|]. split; [exact Hseen|]. split; [exact Hr|].
        intros st t' v Hpend. destruct (Pos.eq_dec t t') as [Heq|Hneq]; [exact Heq|].
        exfalso. apply Hno. exists st, t', v. auto.
    Qed.

    Lemma write_ts_no_error t l r ts :
      ⊨ I //\\ TSTopSeen t l ts //\\ RecIs l r //\\ NoOtherTSWrite t (rec_ts r) ==>>
        ANoError {| te_tid := t; te_ev := InvEv (in_ts (owrite (rec_ts r) ts)) |}.
    Proof.
      intros s [HI [_ [Hr Hno]]] Herr.
      apply (error_ts t (InvEv (owrite (rec_ts r) ts))) in Herr.
      destruct (I_fields_defined _ _ _ HI Hr) as [_ [Hdef _]].
      eapply omem_write_no_error; [exact Hdef| |exact Herr].
      intros st t' v' Hpend. apply (Hno st t' v'). exact Hpend.
    Qed.

    (** * Building blocks for possibility updates *)

    Definition st (c : State (li_lts E)) (a : State (li_lts F))
        (p : tmap (@LinState (li_sig F))) : single_state :=
      @SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F) c a p.

    Ltac simpl_abs := unfold abs; cbn [st SinglePossState.ρ state].

    (** Facts about the linearization map alone. *)
    Definition AtSetTSPi (p : tmap (@LinState (li_sig F))) (t : tid) (l : Addr) :=
      exists ts, TMap.find t p = Some (ls_inv (nmsetTS l ts)).

    Lemma AtSetTS_pi s t l : AtSetTS s t l <-> AtSetTSPi (π s) t l.
    Proof. reflexivity. Qed.

    (** Two facts about the same entry.  Stated with [eq_trans] because the
        implicit signature of the entries differs up to unfolding
        ([@ENodeMem A] versus [li_sig F]), which defeats [rewrite]. *)
    Lemma AtSetTS_self t (f : Sig.op (li_sig F)) (p : tmap (@LinState (li_sig F))) l :
      TMap.find t p = Some (ls_inv f) -> AtSetTSPi p t l ->
      exists ts, f = nmsetTS l ts.
    Proof.
      intros Hlin [ts Hts]. exists ts.
      pose proof (eq_trans (eq_sym Hlin) Hts) as Heq. injection Heq as Heq. exact Heq.
    Qed.

    Lemma AtSetTS_self_setTS t l ts (p : tmap (@LinState (li_sig F))) l0 :
      TMap.find t p = Some (ls_inv (nmsetTS l ts)) -> AtSetTSPi p t l0 -> l0 = l.
    Proof.
      intros Hlin Hat. destruct (AtSetTS_self _ _ _ _ Hlin Hat) as [ts' Heq].
      injection Heq as Heq _. symmetry. exact Heq.
    Qed.

    Definition lin_π t (f : Sig.op (li_sig F)) (ret : Sig.ar f)
        (p : tmap (@LinState (li_sig F))) :=
      TMap.add t (ls_linr f ret) (TMap.add t (ls_lini f) p).

    Lemma lin_π_self t (f : Sig.op (li_sig F)) ret (p : tmap (@LinState (li_sig F))) :
      TMap.find t (lin_π t f ret p) = Some (ls_linr f ret).
    Proof. unfold lin_π. apply TMap.gss. Qed.

    Lemma lin_π_other t t' (f : Sig.op (li_sig F)) ret (p : tmap (@LinState (li_sig F))) :
      t <> t' -> TMap.find t' (lin_π t f ret p) = TMap.find t' p.
    Proof. intros Hne. unfold lin_π. rewrite !TMap.gso; auto. Qed.

    (** Linearizing an entire abstract operation at once. *)
    Lemma lin_steps t (f : Sig.op (li_sig F)) (ret : Sig.ar f) h h'
        (p : tmap (@LinState (li_sig F))) :
      TMap.find t p = Some (ls_inv f) ->
      StepNodeMem {| te_tid := t; te_ev := InvEv f |} h h ->
      StepNodeMem {| te_tid := t; te_ev := ResEv f ret |} h h' ->
      @poss_steps _ (li_lts F) (@PossOk _ (li_lts F) (Idle h) p)
        (@PossOk _ (li_lts F) (Idle h') (lin_π t f ret p)).
    Proof.
      intros Hlin Hinv Hres. eapply rt_trans.
      - apply rt_step. apply (ps_inv t f); [|exact Hlin].
        apply step_inv. exact Hinv.
      - apply rt_step. apply (ps_ret t f ret).
        + apply step_res. exact Hres.
        + apply TMap.gss.
    Qed.

    (** Every other thread's entry, and every [AtSetTS] fact, survives the
        actor's linearization of an operation that is not [nmsetTS]. *)
    Lemma AtSetTS_lin t (f : Sig.op (li_sig F)) ret (p : tmap (@LinState (li_sig F))) :
      TMap.find t p = Some (ls_inv f) ->
      (forall l ts, f <> nmsetTS l ts) ->
      forall t' l, AtSetTSPi p t' l -> AtSetTSPi (lin_π t f ret p) t' l.
    Proof.
      intros Hlin Hf t' l Hat.
      destruct (Pos.eq_dec t t') as [<-|Hne].
      - exfalso. destruct (AtSetTS_self _ _ _ _ Hlin Hat) as [ts Heq]. eapply Hf; exact Heq.
      - destruct Hat as [ts Hts]. exists ts. rewrite lin_π_other; auto.
    Qed.

    (** Heap facts. *)
    Lemma heap_update_defined {V} (h : @Heap V) l v a :
      h a <> None -> heap_update l v h a <> None.
    Proof.
      intros Hdef. unfold heap_update. destruct (Nat.eqb l a); [discriminate|exact Hdef].
    Qed.

    Lemma heap_update_fresh {V} (h : @Heap V) l v a x :
      h l = None -> h a = Some x -> heap_update l v h a = Some x.
    Proof.
      intros Hl Ha. rewrite HeapUpdateOther; [exact Ha|]. congruence.
    Qed.

    Lemma heap_update_none_iff {V} (h : @Heap V) l v a n :
      h l = Some n -> (heap_update l v h a = None <-> h a = None).
    Proof.
      intros Hl. unfold heap_update. destruct (Nat.eqb l a) eqn:Heq.
      - apply Nat.eqb_eq in Heq. subst. rewrite Hl. split; discriminate.
      - tauto.
    Qed.

    Lemma heap_update_same {V} (h : @Heap V) l n :
      h l = Some n -> heap_update l n h = h.
    Proof.
      intros Hl. apply functional_extensionality. intros a.
      unfold heap_update. destruct (Nat.eqb l a) eqn:Heq; [|reflexivity].
      apply Nat.eqb_eq in Heq. subst. auto.
    Qed.

    Lemma node_eta (n : @Node A) :
      n = mknode (node_val n) (node_ts n) (node_taken n) (node_next n).
    Proof. destruct n as [[[v ts] tk] nx]. reflexivity. Qed.

    (** Invariant pieces that only depend on unchanged heaps. *)
    Definition same_heaps (c c' : State (li_lts E)) : Prop :=
      rec_h c' = rec_h c /\ val_h c' = val_h c /\ val_o c' = val_o c /\
      ts_h c' = ts_h c /\ ts_o c' = ts_o c /\ taken_h c' = taken_h c /\
      taken_o c' = taken_o c /\ next_h c' = next_h c /\ next_o c' = next_o c.

    Lemma IConcrete_same c c' :
      same_heaps c c' -> IConcrete c -> IConcrete c'.
    Proof.
      intros (Hr & Hv & _ & Ht & _ & Hk & _ & Hn & _) [Hf Hinj].
      unfold IConcrete, fields_defined. rewrite Hr, Hv, Ht, Hk, Hn. auto.
    Qed.

    Lemma Rep_same c c' a p p' :
      same_heaps c c' -> Rep (st c a p) -> Rep (st c' a p').
    Proof.
      intros (Hr & Hv & _ & Ht & _ & Hk & _ & Hn & _) [H1 H2].
      unfold Rep, represents, abs in *. simpl in *. rewrite Hr, Hv, Ht, Hk, Hn. auto.
    Qed.

    Lemma HeapRely_same c c' : same_heaps c c' -> HeapRely c c'.
    Proof.
      intros (Hr & Hv & Hvo & Ht & Hto & Hk & Hko & Hn & Hno).
      unfold HeapRely. rewrite Hr, Hv, Hvo, Ht, Hto, Hk, Hko, Hn, Hno.
      repeat split; auto.
    Qed.

    (** The timestamp control of [c'] carries no pending store that [c] did
        not already carry. *)
    Definition no_new_ts_write (c c' : State (li_lts E)) : Prop :=
      forall st0 t' x v, ts_c c' = Pending st0 t' (owrite x v) ->
        ts_c c = Pending st0 t' (owrite x v).

    Lemma no_new_ts_write_eq c c' : ts_c c' = ts_c c -> no_new_ts_write c c'.
    Proof. intros Heq st0 t' x v H. rewrite <- Heq. exact H. Qed.

    Lemma no_new_ts_write_idle c c' s : ts_c c' = Idle s -> no_new_ts_write c c'.
    Proof. intros Heq st0 t' x v H. rewrite Heq in H. discriminate. Qed.

    Lemma PendingTSWrite_grow c c' a a' p p' :
      no_new_ts_write c c' ->
      (forall l r, rec_h c l = Some r -> rec_h c' l = Some r) ->
      (forall t' l, AtSetTSPi p t' l -> AtSetTSPi p' t' l) ->
      PendingTSWrite (st c a p) -> PendingTSWrite (st c' a' p').
    Proof.
      intros Hts Hr Hpi Hp st0 t' x v Hpend. simpl in Hpend. apply Hts in Hpend.
      destruct (Hp _ _ _ _ Hpend) as [l [r [Hl [Hx Hat]]]].
      exists l, r. simpl. split; [apply Hr; exact Hl|]. split; [exact Hx|].
      apply Hpi. exact Hat.
    Qed.

    Lemma PendingTSWrite_same c c' a a' p p' :
      no_new_ts_write c c' -> rec_h c' = rec_h c ->
      (forall t' l, AtSetTSPi p t' l -> AtSetTSPi p' t' l) ->
      PendingTSWrite (st c a p) -> PendingTSWrite (st c' a' p').
    Proof.
      intros Hts Hr. apply PendingTSWrite_grow; [exact Hts|].
      intros l r Hl. rewrite Hr. exact Hl.
    Qed.

    Lemma Err_pi c c' a a' p p' :
      (forall t' l, AtSetTSPi p t' l -> AtSetTSPi p' t' l) ->
      Err (st c a p) -> Err (st c' a' p').
    Proof.
      intros Hpi [l [t1 [t2 [Hne [H1 H2]]]]]. exists l, t1, t2.
      split; [exact Hne|]. split; apply Hpi; assumption.
    Qed.

    Lemma I_same c c' a p p' :
      same_heaps c c' -> no_new_ts_write c c' ->
      (forall t' l, AtSetTSPi p t' l -> AtSetTSPi p' t' l) ->
      I (st c a p) -> I (st c' a p').
    Proof.
      intros Hsame Hts Hpi [Hρ [Hc [Hp Hor]]].
      split; [exact Hρ|]. split; [eapply IConcrete_same; eauto|].
      split; [eapply PendingTSWrite_same; eauto; apply Hsame|].
      destruct Hor as [Herr|Hrep].
      - left. eapply Err_pi; eauto.
      - right. eapply Rep_same; eauto.
    Qed.

    (** A guarantee step that changes no heap and no abstract state. *)
    Lemma G_same t c c' a p p' :
      same_heaps c c' ->
      (forall t', t <> t' -> TMap.find t' p = TMap.find t' p') ->
      (forall l, AtSetTSPi p t l -> (exists t', t <> t' /\ AtSetTSPi p t' l) ->
        TMap.find t p = TMap.find t p') ->
      G t (st c a p) (st c' a p').
    Proof.
      intros Hsame Hπ Hprot. split; [exact Hπ|].
      split; [apply HeapRely_same; exact Hsame|].
      split; [intros l r H1 H2; simpl in H1, H2; destruct Hsame as [Hr _];
              rewrite Hr in H2; congruence|].
      split.
      - intros l n Hn. exists n. split; [exact Hn|]. intros Hc. contradiction.
      - exact Hprot.
    Qed.

    Lemma same_heaps_control c c' :
      state (rec_c c') = state (rec_c c) -> state (val_c c') = state (val_c c) ->
      state (ts_c c') = state (ts_c c) -> state (next_c c') = state (next_c c) ->
      state (taken_c c') = state (taken_c c) ->
      same_heaps c c'.
    Proof.
      intros H1 H2 H3 H4 H5. unfold same_heaps, rec_h, val_h, val_o, ts_h, ts_o,
        taken_h, taken_o, next_h, next_o.
      rewrite H1, H2, H3, H4, H5. repeat split.
    Qed.

    (** Lifting the error escape to the set logic. *)
    Lemma lift_perror (P P' : assertion) :
      (⊨ P ==>> P' \\// APError) ->
      ⊨ lift_assert P ==>> lift_assert P' \\// AssertionsSet.APError.
    Proof.
      intros Himpl s [x [Hview HP]].
      destruct (Himpl x HP) as [HP'|Herr].
      - left. exists x. auto.
      - right. eapply AssertionsSet.APErrorSome.
        + apply singleton_view_member. exact Hview.
        + exact Herr.
    Qed.

    Lemma done_or_err (P : assertion) :
      ⊨ P \\// (I //\\ Err) ==>> P \\// APError.
    Proof.
      intros s [HP | HErr]; [left; exact HP|right; apply Err_APError; exact HErr].
    Qed.

    Lemma disj_I (P : assertion) :
      (⊨ P ==>> I) -> ⊨ P \\// (I //\\ Err) ==>> I.
    Proof. intros HP s [H | [HI _]]; [apply HP; exact H|exact HI]. Qed.

    (** * Method-level assertions *)

    Definition Active t (f : Sig.op (li_sig F)) : assertion :=
      I //\\ ALin t (ls_inv f).
    Definition Done t (f : Sig.op (li_sig F)) (ret : Sig.ar f) : assertion :=
      I //\\ ALin t (ls_linr f ret).
    Definition DoneOrErr t (f : Sig.op (li_sig F)) (ret : Sig.ar f) : assertion :=
      Done t f ret \\// (I //\\ Err).

    Lemma Active_I t f : ⊨ Active t f ==>> I.
    Proof. intros s [HI _]. exact HI. Qed.
    Lemma Done_I t f ret : ⊨ Done t f ret ==>> I.
    Proof. intros s [HI _]. exact HI. Qed.
    Lemma DoneOrErr_I t f ret : ⊨ DoneOrErr t f ret ==>> I.
    Proof. apply disj_I. apply Done_I. Qed.
    Lemma Active_stable t f : Stable (R t) I (Active t f).
    Proof. apply ConjStable; auto with stableDB. Qed.
    Lemma Done_stable t f ret : Stable (R t) I (Done t f ret).
    Proof. apply ConjStable; auto with stableDB. Qed.
    Lemma DoneOrErr_stable t f ret : Stable (R t) I (DoneOrErr t f ret).
    Proof.
      apply DisjStable; [apply Done_stable|apply ConjStable; auto with stableDB].
    Qed.
    #[local] Hint Resolve Active_stable Done_stable DoneOrErr_stable : stableDB.

    Lemma DoneOrErr_perror t f ret :
      ⊨ lift_assert (DoneOrErr t f ret) ==>>
        lift_assert (Done t f ret) \\// AssertionsSet.APError.
    Proof. apply lift_perror. apply done_or_err. Qed.

    (** Heaps only gain cells; records never change. *)
    Definition heaps_grow (c c' : State (li_lts E)) : Prop :=
      rec_h c' = rec_h c /\
      (forall a v, val_h c a = Some v -> val_h c' a = Some v) /\
      (forall a o, val_h c a <> None -> val_o c a = Some o -> val_o c' a = Some o) /\
      (forall a v, ts_h c a = Some v -> ts_h c' a = Some v) /\
      (forall a o, ts_h c a <> None -> ts_o c a = Some o -> ts_o c' a = Some o) /\
      (forall a v, taken_h c a = Some v -> taken_h c' a = Some v) /\
      (forall a o, taken_h c a <> None -> taken_o c a = Some o ->
        taken_o c' a = Some o) /\
      (forall a v, next_h c a = Some v -> next_h c' a = Some v) /\
      (forall a o, next_h c a <> None -> next_o c a = Some o -> next_o c' a = Some o).

    Lemma same_heaps_grow c c' : same_heaps c c' -> heaps_grow c c'.
    Proof.
      intros (Hr & Hv & Hvo & Ht & Hto & Hk & Hko & Hn & Hno).
      unfold heaps_grow. rewrite Hr, Hv, Hvo, Ht, Hto, Hk, Hko, Hn, Hno.
      repeat split; auto.
    Qed.

    (** Assertions that do not look at the control components and survive
        allocation. *)
    Definition CI (P : assertion) : Prop :=
      forall c c' a p, heaps_grow c c' -> P (st c a p) -> P (st c' a p).

    Lemma ALin_ci t ls : CI (ALin t ls).
    Proof. intros c c' a p _ H. exact H. Qed.
    Lemma Err_ci : CI Err.
    Proof. intros c c' a p _ H. exact H. Qed.
    Lemma Defined_ci l : CI (Defined l).
    Proof. intros c c' a p [Hr _] H. unfold Defined in *. simpl in *. rewrite Hr. exact H. Qed.
    Lemma RecIs_ci l r : CI (RecIs l r).
    Proof. intros c c' a p [Hr _] H. unfold RecIs in *. simpl in *. rewrite Hr. exact H. Qed.
    Lemma FreshVal_ci t x v : CI (FreshVal t x v).
    Proof.
      intros c c' a p (Hr & Hv & Hvo & _) [H1 [H2 H3]]. unfold FreshVal, referenced_val in *.
      simpl in *. rewrite Hr. split; [apply Hv; exact H1|].
      split; [apply Hvo; [rewrite H1; discriminate|exact H2]|exact H3].
    Qed.
    Lemma FreshTS_ci t x : CI (FreshTS t x).
    Proof.
      intros c c' a p (Hr & _ & _ & Ht & Hto & _) [H1 [H2 H3]].
      unfold FreshTS, referenced_ts in *. simpl in *. rewrite Hr.
      split; [apply Ht; exact H1|].
      split; [apply Hto; [rewrite H1; discriminate|exact H2]|exact H3].
    Qed.
    Lemma FreshTaken_ci t x : CI (FreshTaken t x).
    Proof.
      intros c c' a p (Hr & _ & _ & _ & _ & Hk & Hko & _) [H1 [H2 H3]].
      unfold FreshTaken, referenced_taken in *. simpl in *. rewrite Hr.
      split; [apply Hk; exact H1|].
      split; [apply Hko; [rewrite H1; discriminate|exact H2]|exact H3].
    Qed.
    Lemma FreshNext_ci t x nx : CI (FreshNext t x nx).
    Proof.
      intros c c' a p (Hr & _ & _ & _ & _ & _ & _ & Hn & Hno) [H1 [H2 H3]].
      unfold FreshNext, referenced_next in *. simpl in *. rewrite Hr.
      split; [apply Hn; exact H1|].
      split; [apply Hno; [rewrite H1; discriminate|exact H2]|exact H3].
    Qed.
    Lemma TSTopSeen_ci t l ts : CI (TSTopSeen t l ts).
    Proof. intros c c' a p _ H. exact H. Qed.
    Lemma Conj_ci (P Q : assertion) : CI P -> CI Q -> CI (P //\\ Q).
    Proof. intros HP HQ c c' a p Hs [H1 H2]. split; [eapply HP|eapply HQ]; eauto. Qed.
    Lemma Disj_ci (P Q : assertion) : CI P -> CI Q -> CI (P \\// Q).
    Proof.
      intros HP HQ c c' a p Hs [H1 | H2]; [left; eapply HP|right; eapply HQ]; eauto.
    Qed.

    Create HintDb ciDB.
    #[local] Hint Resolve ALin_ci Err_ci Defined_ci RecIs_ci FreshVal_ci FreshTS_ci
      FreshTaken_ci FreshNext_ci TSTopSeen_ci Conj_ci Disj_ci : ciDB.

    (** * Generic possibility updates *)

    (** An invocation on any component memory other than a timestamp store
        changes only the control state. *)
    Lemma inv_update t (m : Sig.op (li_sig E)) (P : assertion) :
      CI P ->
      (forall x v, m <> in_ts (owrite x v)) ->
      PUpdate (G t) {| te_tid := t; te_ev := InvEv m |} (I //\\ P) (I //\\ P).
    Proof.
      intros HP Hnw σ1 ρ1 π1 [HI Hpre] σ2 Hstep.
      exists ρ1, π1. split; [apply rt_refl|].
      assert (Hfacts : same_heaps σ1 σ2 /\
        (forall st0 t' x v, ts_c σ2 = Pending st0 t' (owrite x v) ->
          ts_c σ1 = Pending st0 t' (owrite x v))).
      { destruct m as [[[[m0|m0]|m0]|m0]|m0].
        - apply (step_rec t (InvEv m0)) in Hstep.
          destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
          destruct (omem_inv_shape _ _ _ _ Hs) as [s [Hc Hc']].
          split; [|rewrite H2; auto].
          apply same_heaps_control; [rewrite Hc, Hc'|rewrite H1|rewrite H2|rewrite H3|rewrite H4];
            reflexivity.
        - apply (step_val t (InvEv m0)) in Hstep.
          destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
          destruct (omem_inv_shape _ _ _ _ Hs) as [s [Hc Hc']].
          split; [|rewrite H2; auto].
          apply same_heaps_control; [rewrite H1|rewrite Hc, Hc'|rewrite H2|rewrite H3|rewrite H4];
            reflexivity.
        - apply (step_ts t (InvEv m0)) in Hstep.
          destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
          destruct (omem_inv_shape _ _ _ _ Hs) as [s [Hc Hc']].
          split.
          + apply same_heaps_control; [rewrite H1|rewrite H2|rewrite Hc, Hc'|rewrite H3|rewrite H4];
              reflexivity.
          + intros st0 t' x v Heq. rewrite Hc' in Heq. injection Heq as _ _ Hm.
            exfalso. apply (Hnw x v). rewrite Hm. reflexivity.
        - apply (step_next t (InvEv m0)) in Hstep.
          destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
          destruct (omem_inv_shape _ _ _ _ Hs) as [s [Hc Hc']].
          split; [|rewrite H3; auto].
          apply same_heaps_control; [rewrite H1|rewrite H2|rewrite H3|rewrite Hc, Hc'|rewrite H4];
            reflexivity.
        - apply (step_taken t (InvEv m0)) in Hstep.
          destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
          destruct (omem_inv_shape _ _ _ _ Hs) as [s [Hc Hc']].
          split; [|rewrite H3; auto].
          apply same_heaps_control; [rewrite H1|rewrite H2|rewrite H3|rewrite H4|rewrite Hc, Hc'];
            reflexivity. }
      destruct Hfacts as [Hsame Hts].
      split; [split|].
      - destruct HI as [Hρ [Hc [Hp Hor]]].
        split; [exact Hρ|]. split; [eapply IConcrete_same; eauto|]. split.
        + intros st0 t' x v Heq. apply Hts in Heq.
          destruct (Hp _ _ _ _ Heq) as [l [r [Hl [Hx Hat]]]].
          exists l, r. simpl. destruct Hsame as [Hr _]. rewrite Hr. auto.
        + destruct Hor as [He|Hr]; [left; exact He|right; eapply Rep_same; eauto].
      - apply (HP σ1 σ2 ρ1 π1); [apply same_heaps_grow; exact Hsame|exact Hpre].
      - apply G_same; auto.
    Qed.

    (** Reading the record cell. *)
    Lemma rec_read_res_update t l r (P : assertion) :
      CI P ->
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_rec (oread l)) r |}
        (I //\\ P) (I //\\ P //\\ RecIs l r).
    Proof.
      intros HP σ1 ρ1 π1 [HI Hpre] σ2 Hstep.
      apply (step_rec t (ResEv (oread l) r)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_read_res_shape _ _ _ _ _ Hs) as [s [Hc [Hr Hc']]].
      assert (Hsame : same_heaps σ1 σ2).
      { apply same_heaps_control; [rewrite Hc, Hc'|rewrite H1|rewrite H2|rewrite H3|rewrite H4];
          reflexivity. }
      exists ρ1, π1. split; [apply rt_refl|]. split.
      - split; [eapply I_same; eauto; apply no_new_ts_write_eq; exact H2|].
        split; [apply (HP σ1 σ2 ρ1 π1); [apply same_heaps_grow; exact Hsame|exact Hpre]|].
        unfold RecIs, rec_h. simpl. rewrite Hc'. exact Hr.
      - apply G_same; auto.
    Qed.

    (** Linearizing an operation other than [nmsetTS] without touching the
        heaps. *)
    Lemma G_lin_same t (f : Sig.op (li_sig F)) (ret : Sig.ar f) c c' a
        (p : tmap (@LinState (li_sig F))) :
      same_heaps c c' -> TMap.find t p = Some (ls_inv f) ->
      (forall l ts, f <> nmsetTS l ts) ->
      G t (st c a p) (st c' a (lin_π t f ret p)).
    Proof.
      intros Hsame Hlin Hf. apply G_same; auto.
      - intros t' Hne. rewrite lin_π_other; auto.
      - intros l Hat _. exfalso.
        destruct (AtSetTS_self _ _ _ _ Hlin Hat) as [ts Heq]. eapply Hf. exact Heq.
    Qed.

    Lemma I_lin_same t (f : Sig.op (li_sig F)) (ret : Sig.ar f) c c' a
        (p : tmap (@LinState (li_sig F))) :
      same_heaps c c' -> no_new_ts_write c c' -> TMap.find t p = Some (ls_inv f) ->
      (forall l ts, f <> nmsetTS l ts) ->
      I (st c a p) -> I (st c' a (lin_π t f ret p)).
    Proof.
      intros Hsame Hts Hlin Hf HI.
      eapply I_same; [exact Hsame|exact Hts|apply AtSetTS_lin; auto|exact HI].
    Qed.

    (** Reading a field is the linearization point of the corresponding
        [nmget*] operation: either the representation holds and the value read
        is the abstract one, or the racy error is already reachable. *)
    Lemma field_read_lin t (f : Sig.op (li_sig F)) (ret : Sig.ar f) l r σ1 σ2 h π1 :
      same_heaps σ1 σ2 -> no_new_ts_write σ1 σ2 ->
      I (st σ1 (Idle h) π1) -> TMap.find t π1 = Some (ls_inv f) ->
      (forall l' ts, f <> nmsetTS l' ts) ->
      rec_h σ1 l = Some r ->
      (forall n, h l = Some n -> represents σ1 r n ->
        StepNodeMem {| te_tid := t; te_ev := InvEv f |} h h /\
        StepNodeMem {| te_tid := t; te_ev := ResEv f ret |} h h) ->
      exists ρ' π', @poss_steps _ (li_lts F) (@PossOk _ (li_lts F) (Idle h) π1) (@PossOk _ (li_lts F) ρ' π') /\
        DoneOrErr t f ret (st σ2 ρ' π') /\ G t (st σ1 (Idle h) π1) (st σ2 ρ' π').
    Proof.
      intros Hsame Hts HI Hlin Hf Hr Hstep.
      pose proof HI as [_ [_ [_ Hor]]].
      destruct Hor as [Herr | [_ Hsome]].
      - exists (Idle h), π1. split; [apply rt_refl|]. split.
        + right. split; [eapply I_same; eauto|exact Herr].
        + apply G_same; auto.
      - destruct (Hsome _ _ Hr) as [n [Hn Hrep]]. unfold abs in Hn. simpl in Hn.
        destruct (Hstep _ Hn Hrep) as [Hinv Hres].
        exists (Idle h), (lin_π t f ret π1). split.
        + apply lin_steps; auto.
        + split.
          * left. split; [eapply I_lin_same; eauto|]. unfold ALin. simpl. apply lin_π_self.
          * apply G_lin_same; auto.
    Qed.

    (** * Method: getValue *)

    Lemma getValue_res_update t l lv lts lt ln v :
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_val (oread lv)) v |}
        (Active t (nmgetValue l) //\\ RecIs l (mkrec lv lts lt ln))
        (DoneOrErr t (nmgetValue l) v).
    Proof.
      intros σ1 ρ1 π1 [[HI Hlin] Hr] σ2 Hstep.
      apply (step_val t (ResEv (oread lv) v)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_read_res_shape _ _ _ _ _ Hs) as [s [Hc [Hv Hc']]].
      assert (Hsame : same_heaps σ1 σ2).
      { apply same_heaps_control; [rewrite H1|rewrite Hc, Hc'|rewrite H2|rewrite H3|rewrite H4];
          reflexivity. }
      pose proof HI as [[h Hρ] _]. simpl in Hρ. subst ρ1.
      eapply field_read_lin; eauto;
        [apply no_new_ts_write_eq; exact H2|discriminate|].
      intros [[[v0 ts0] tk0] nx0] Hn [Hval _]. simpl_fields Hval; simpl in Hval.
      unfold val_h in Hval. rewrite Hc in Hval. simpl_fields Hval; simpl in Hval.
      rewrite Hv in Hval. injection Hval as <-.
      split.
      - eapply step_getValue_inv; [reflexivity|rewrite Hn; discriminate].
      - eapply step_getValue_res; [reflexivity|exact Hn].
    Qed.

    Lemma getValue_triple t l :
      [li_lts E, li_lts F, lift_relation (R t), lift_relation (G t), lift_assert I, t] ⊢
        {{ lift_assert (Active t (nmgetValue l)) }}
          (@getValue_impl A l t)
        {{ fun v => lift_assert (Done t (nmgetValue l) v) }}.
    Proof.
      eapply SetLogic.provable_perror.
      { apply lift_perror. apply (defined_or_error t (nmgetValue l) l).
        intros h Hnone. eapply error_getValue_undefined; [reflexivity|exact Hnone]. }
      unfold getValue_impl.
      eapply singleton_provable_vis_safe with
        (P' := I //\\ (ALin t (ls_inv (nmgetValue l)) //\\ Defined l))
        (Q' := fun r => I //\\ (ALin t (ls_inv (nmgetValue l)) //\\ Defined l) //\\ RecIs l r).
      - apply read_rec_no_error. intros s [_ [_ H]]. exact H.
      - intros s [HI _]. exact HI.
      - intros r s [HI _]. exact HI.
      - solve_conj_stable stableDB.
      - intros r. solve_conj_stable stableDB.
      - apply inv_update; [auto with ciDB|discriminate].
      - intros r. apply rec_read_res_update. auto with ciDB.
      - intros [[[lv lts] lt] ln]. cbn.
        eapply singleton_provable_vis_safe with
          (P' := Active t (nmgetValue l) //\\ RecIs l (mkrec lv lts lt ln))
          (Q' := fun v => DoneOrErr t (nmgetValue l) v).
        + apply (read_val_no_error t l (mkrec lv lts lt ln)).
          intros s [HI [_ Hr]]. split; [exact HI|exact Hr].
        + intros s [[HI _] _]. exact HI.
        + intros v. apply DoneOrErr_I.
        + solve_conj_stable stableDB.
        + intros v. apply DoneOrErr_stable.
        + eapply PUpdateConseq;
            [apply ImplRefl| |apply inv_update; [auto with ciDB|discriminate]].
          intros s [HI [[Hlin _] Hr]]. split; [split; [exact HI|exact Hlin]|exact Hr].
        + intros v. apply getValue_res_update.
        + intros v. eapply SetLogic.provable_perror; [apply DoneOrErr_perror|].
          singleton_ret_safe; [apply ImplRefl|apply Done_I|apply Done_stable].
    Qed.

    (** * Methods: getTS, getTaken, getNext *)

    Lemma getTS_res_update t l lv lts lt ln ts :
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_ts (oread lts)) ts |}
        (Active t (nmgetTS l) //\\ RecIs l (mkrec lv lts lt ln))
        (DoneOrErr t (nmgetTS l) ts).
    Proof.
      intros σ1 ρ1 π1 [[HI Hlin] Hr] σ2 Hstep.
      apply (step_ts t (ResEv (oread lts) ts)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_read_res_shape _ _ _ _ _ Hs) as [s [Hc [Hv Hc']]].
      assert (Hsame : same_heaps σ1 σ2).
      { apply same_heaps_control; [rewrite H1|rewrite H2|rewrite Hc, Hc'|rewrite H3|rewrite H4];
          reflexivity. }
      pose proof HI as [[h Hρ] _]. simpl in Hρ. subst ρ1.
      eapply field_read_lin; eauto;
        [eapply no_new_ts_write_idle; exact Hc'|discriminate|].
      intros [[[v0 ts0] tk0] nx0] Hn [_ [Hval _]]. simpl_fields Hval; simpl in Hval.
      unfold ts_h in Hval. rewrite Hc in Hval. simpl_fields Hval; simpl in Hval.
      rewrite Hv in Hval. injection Hval as <-.
      split.
      - eapply step_getTS_inv; [reflexivity|rewrite Hn; discriminate].
      - eapply step_getTS_res; [reflexivity|exact Hn].
    Qed.

    Lemma getTS_triple t l :
      [li_lts E, li_lts F, lift_relation (R t), lift_relation (G t), lift_assert I, t] ⊢
        {{ lift_assert (Active t (nmgetTS l)) }}
          (@getTS_impl A l t)
        {{ fun v => lift_assert (Done t (nmgetTS l) v) }}.
    Proof.
      eapply SetLogic.provable_perror.
      { apply lift_perror. apply (defined_or_error t (nmgetTS l) l).
        intros h Hnone. eapply error_getTS_undefined; [reflexivity|exact Hnone]. }
      unfold getTS_impl.
      eapply singleton_provable_vis_safe with
        (P' := I //\\ (ALin t (ls_inv (nmgetTS l)) //\\ Defined l))
        (Q' := fun r => I //\\ (ALin t (ls_inv (nmgetTS l)) //\\ Defined l) //\\ RecIs l r).
      - apply read_rec_no_error. intros s [_ [_ H]]. exact H.
      - intros s [HI _]. exact HI.
      - intros r s [HI _]. exact HI.
      - solve_conj_stable stableDB.
      - intros r. solve_conj_stable stableDB.
      - apply inv_update; [auto with ciDB|discriminate].
      - intros r. apply rec_read_res_update. auto with ciDB.
      - intros [[[lv lts] lt] ln]. cbn.
        eapply singleton_provable_vis_safe with
          (P' := Active t (nmgetTS l) //\\ RecIs l (mkrec lv lts lt ln))
          (Q' := fun v => DoneOrErr t (nmgetTS l) v).
        + apply (read_ts_no_error t l (mkrec lv lts lt ln)).
          intros s [HI [_ Hr]]. split; [exact HI|exact Hr].
        + intros s [[HI _] _]. exact HI.
        + intros v. apply DoneOrErr_I.
        + solve_conj_stable stableDB.
        + intros v. apply DoneOrErr_stable.
        + eapply PUpdateConseq;
            [apply ImplRefl| |apply inv_update; [auto with ciDB|discriminate]].
          intros s [HI [[Hlin _] Hr]]. split; [split; [exact HI|exact Hlin]|exact Hr].
        + intros v. apply getTS_res_update.
        + intros v. eapply SetLogic.provable_perror; [apply DoneOrErr_perror|].
          singleton_ret_safe; [apply ImplRefl|apply Done_I|apply Done_stable].
    Qed.

    Lemma getTaken_res_update t l lv lts lt ln tk :
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_taken (oread lt)) tk |}
        (Active t (nmgetTaken l) //\\ RecIs l (mkrec lv lts lt ln))
        (DoneOrErr t (nmgetTaken l) tk).
    Proof.
      intros σ1 ρ1 π1 [[HI Hlin] Hr] σ2 Hstep.
      apply (step_taken t (ResEv (oread lt) tk)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_read_res_shape _ _ _ _ _ Hs) as [s [Hc [Hv Hc']]].
      assert (Hsame : same_heaps σ1 σ2).
      { apply same_heaps_control; [rewrite H1|rewrite H2|rewrite H3|rewrite H4|rewrite Hc, Hc'];
          reflexivity. }
      pose proof HI as [[h Hρ] _]. simpl in Hρ. subst ρ1.
      eapply field_read_lin; eauto;
        [apply no_new_ts_write_eq; exact H3|discriminate|].
      intros [[[v0 ts0] tk0] nx0] Hn [_ [_ [Hval _]]]. simpl_fields Hval; simpl in Hval.
      unfold taken_h in Hval. rewrite Hc in Hval. simpl_fields Hval; simpl in Hval.
      rewrite Hv in Hval. injection Hval as <-.
      split.
      - eapply step_getTaken_inv; [reflexivity|rewrite Hn; discriminate].
      - eapply step_getTaken_res; [reflexivity|exact Hn].
    Qed.

    Lemma getTaken_triple t l :
      [li_lts E, li_lts F, lift_relation (R t), lift_relation (G t), lift_assert I, t] ⊢
        {{ lift_assert (Active t (nmgetTaken l)) }}
          (@getTaken_impl A l t)
        {{ fun v => lift_assert (Done t (nmgetTaken l) v) }}.
    Proof.
      eapply SetLogic.provable_perror.
      { apply lift_perror. apply (defined_or_error t (nmgetTaken l) l).
        intros h Hnone. eapply error_getTaken_undefined; [reflexivity|exact Hnone]. }
      unfold getTaken_impl.
      eapply singleton_provable_vis_safe with
        (P' := I //\\ (ALin t (ls_inv (nmgetTaken l)) //\\ Defined l))
        (Q' := fun r => I //\\ (ALin t (ls_inv (nmgetTaken l)) //\\ Defined l) //\\ RecIs l r).
      - apply read_rec_no_error. intros s [_ [_ H]]. exact H.
      - intros s [HI _]. exact HI.
      - intros r s [HI _]. exact HI.
      - solve_conj_stable stableDB.
      - intros r. solve_conj_stable stableDB.
      - apply inv_update; [auto with ciDB|discriminate].
      - intros r. apply rec_read_res_update. auto with ciDB.
      - intros [[[lv lts] lt] ln]. cbn.
        eapply singleton_provable_vis_safe with
          (P' := Active t (nmgetTaken l) //\\ RecIs l (mkrec lv lts lt ln))
          (Q' := fun v => DoneOrErr t (nmgetTaken l) v).
        + apply (read_taken_no_error t l (mkrec lv lts lt ln)).
          intros s [HI [_ Hr]]. split; [exact HI|exact Hr].
        + intros s [[HI _] _]. exact HI.
        + intros v. apply DoneOrErr_I.
        + solve_conj_stable stableDB.
        + intros v. apply DoneOrErr_stable.
        + eapply PUpdateConseq;
            [apply ImplRefl| |apply inv_update; [auto with ciDB|discriminate]].
          intros s [HI [[Hlin _] Hr]]. split; [split; [exact HI|exact Hlin]|exact Hr].
        + intros v. apply getTaken_res_update.
        + intros v. eapply SetLogic.provable_perror; [apply DoneOrErr_perror|].
          singleton_ret_safe; [apply ImplRefl|apply Done_I|apply Done_stable].
    Qed.

    Lemma getNext_res_update t l lv lts lt ln nx :
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_next (oread ln)) nx |}
        (Active t (nmgetNext l) //\\ RecIs l (mkrec lv lts lt ln))
        (DoneOrErr t (nmgetNext l) nx).
    Proof.
      intros σ1 ρ1 π1 [[HI Hlin] Hr] σ2 Hstep.
      apply (step_next t (ResEv (oread ln) nx)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_read_res_shape _ _ _ _ _ Hs) as [s [Hc [Hv Hc']]].
      assert (Hsame : same_heaps σ1 σ2).
      { apply same_heaps_control; [rewrite H1|rewrite H2|rewrite H3|rewrite Hc, Hc'|rewrite H4];
          reflexivity. }
      pose proof HI as [[h Hρ] _]. simpl in Hρ. subst ρ1.
      eapply field_read_lin; eauto;
        [apply no_new_ts_write_eq; exact H3|discriminate|].
      intros [[[v0 ts0] tk0] nx0] Hn [_ [_ [_ Hval]]]. simpl_fields Hval; simpl in Hval.
      unfold next_h in Hval. rewrite Hc in Hval. simpl_fields Hval; simpl in Hval.
      rewrite Hv in Hval. injection Hval as <-.
      split.
      - eapply step_getNext_inv; [reflexivity|rewrite Hn; discriminate].
      - eapply step_getNext_res; [reflexivity|exact Hn].
    Qed.

    Lemma getNext_triple t l :
      [li_lts E, li_lts F, lift_relation (R t), lift_relation (G t), lift_assert I, t] ⊢
        {{ lift_assert (Active t (nmgetNext l)) }}
          (@getNext_impl A l t)
        {{ fun v => lift_assert (Done t (nmgetNext l) v) }}.
    Proof.
      eapply SetLogic.provable_perror.
      { apply lift_perror. apply (defined_or_error t (nmgetNext l) l).
        intros h Hnone. eapply error_getNext_undefined; [reflexivity|exact Hnone]. }
      unfold getNext_impl.
      eapply singleton_provable_vis_safe with
        (P' := I //\\ (ALin t (ls_inv (nmgetNext l)) //\\ Defined l))
        (Q' := fun r => I //\\ (ALin t (ls_inv (nmgetNext l)) //\\ Defined l) //\\ RecIs l r).
      - apply read_rec_no_error. intros s [_ [_ H]]. exact H.
      - intros s [HI _]. exact HI.
      - intros r s [HI _]. exact HI.
      - solve_conj_stable stableDB.
      - intros r. solve_conj_stable stableDB.
      - apply inv_update; [auto with ciDB|discriminate].
      - intros r. apply rec_read_res_update. auto with ciDB.
      - intros [[[lv lts] lt] ln]. cbn.
        eapply singleton_provable_vis_safe with
          (P' := Active t (nmgetNext l) //\\ RecIs l (mkrec lv lts lt ln))
          (Q' := fun v => DoneOrErr t (nmgetNext l) v).
        + apply (read_next_no_error t l (mkrec lv lts lt ln)).
          intros s [HI [_ Hr]]. split; [exact HI|exact Hr].
        + intros s [[HI _] _]. exact HI.
        + intros v. apply DoneOrErr_I.
        + solve_conj_stable stableDB.
        + intros v. apply DoneOrErr_stable.
        + eapply PUpdateConseq;
            [apply ImplRefl| |apply inv_update; [auto with ciDB|discriminate]].
          intros s [HI [[Hlin _] Hr]]. split; [split; [exact HI|exact Hlin]|exact Hr].
        + intros v. apply getNext_res_update.
        + intros v. eapply SetLogic.provable_perror; [apply DoneOrErr_perror|].
          singleton_ret_safe; [apply ImplRefl|apply Done_I|apply Done_stable].
    Qed.

    (** * Updating one field cell of a published node *)

    Lemma IConcrete_grow c c' :
      rec_h c' = rec_h c ->
      (forall a, val_h c a <> None -> val_h c' a <> None) ->
      (forall a, ts_h c a <> None -> ts_h c' a <> None) ->
      (forall a, taken_h c a <> None -> taken_h c' a <> None) ->
      (forall a, next_h c a <> None -> next_h c' a <> None) ->
      IConcrete c -> IConcrete c'.
    Proof.
      intros Hr Hv Ht Hk Hn [Hf Hinj]. split.
      - intros l r Hl. rewrite Hr in Hl. destruct (Hf _ _ Hl) as [H1 [H2 [H3 H4]]].
        unfold fields_defined. auto.
      - intros l1 l2 r1 r2 H1 H2. rewrite Hr in H1, H2. eapply Hinj; eauto.
    Qed.

    (** Representation after storing [b] into the taken cell of node [l]. *)
    Lemma Rep_update_taken c c' h p p' l r n b :
      IConcrete c -> Rep (st c (Idle h) p) ->
      rec_h c' = rec_h c -> val_h c' = val_h c -> ts_h c' = ts_h c ->
      next_h c' = next_h c ->
      taken_h c' = heap_update (rec_taken r) b (taken_h c) ->
      rec_h c l = Some r -> h l = Some n ->
      Rep (st c' (Idle (heap_update l
        (mknode (node_val n) (node_ts n) b (node_next n)) h)) p').
    Proof.
      intros [_ Hinj] [Hnone Hsome] Hr Hv Ht Hn Hk Hl Hh.
      unfold Rep, abs in *. simpl in *. rewrite Hr. split.
      - intros l'. rewrite (heap_update_none_iff _ _ _ _ _ Hh). auto.
      - intros l' r' Hl'. destruct (Nat.eq_dec l l') as [<-|Hne].
        + rewrite Hl in Hl'. injection Hl' as <-.
          destruct (Hsome _ _ Hl) as [n0 [Hn0 Hrep]]. rewrite Hh in Hn0.
          injection Hn0 as <-.
          eexists. split; [apply HeapUpdateSelf|].
          destruct Hrep as [H1 [H2 [H3 H4]]].
          unfold represents. rewrite Hv, Ht, Hn, Hk. simpl.
          split; [exact H1|]. split; [exact H2|]. split; [apply HeapUpdateSelf|exact H4].
        + destruct (Hsome _ _ Hl') as [n' [Hn' Hrep]].
          exists n'. split; [rewrite HeapUpdateOther; auto|].
          destruct Hrep as [H1 [H2 [H3 H4]]].
          unfold represents. rewrite Hv, Ht, Hn, Hk.
          split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
          rewrite HeapUpdateOther; [exact H3|].
          destruct (Hinj _ _ _ _ Hl Hl' Hne) as [_ Hk']. exact Hk'.
    Qed.

    (** Representation after storing [ts] into the timestamp cell of node [l]. *)
    Lemma Rep_update_ts c c' h p p' l r n ts :
      IConcrete c -> Rep (st c (Idle h) p) ->
      rec_h c' = rec_h c -> val_h c' = val_h c -> taken_h c' = taken_h c ->
      next_h c' = next_h c ->
      ts_h c' = heap_update (rec_ts r) ts (ts_h c) ->
      rec_h c l = Some r -> h l = Some n ->
      Rep (st c' (Idle (heap_update l
        (mknode (node_val n) ts (node_taken n) (node_next n)) h)) p').
    Proof.
      intros [_ Hinj] [Hnone Hsome] Hr Hv Hk Hn Ht Hl Hh.
      unfold Rep, abs in *. simpl in *. rewrite Hr. split.
      - intros l'. rewrite (heap_update_none_iff _ _ _ _ _ Hh). auto.
      - intros l' r' Hl'. destruct (Nat.eq_dec l l') as [<-|Hne].
        + rewrite Hl in Hl'. injection Hl' as <-.
          destruct (Hsome _ _ Hl) as [n0 [Hn0 Hrep]]. rewrite Hh in Hn0.
          injection Hn0 as <-.
          eexists. split; [apply HeapUpdateSelf|].
          destruct Hrep as [H1 [H2 [H3 H4]]].
          unfold represents. rewrite Hv, Hk, Hn, Ht. simpl.
          split; [exact H1|]. split; [apply HeapUpdateSelf|]. split; [exact H3|exact H4].
        + destruct (Hsome _ _ Hl') as [n' [Hn' Hrep]].
          exists n'. split; [rewrite HeapUpdateOther; auto|].
          destruct Hrep as [H1 [H2 [H3 H4]]].
          unfold represents. rewrite Hv, Hk, Hn, Ht.
          split; [exact H1|]. split; [|split; [exact H3|exact H4]].
          rewrite HeapUpdateOther; [exact H2|].
          destruct (Hinj _ _ _ _ Hl Hl' Hne) as [Ht' _]. exact Ht'.
    Qed.

    (** Heap rely after a store to a referenced taken cell. *)
    Lemma HeapRely_update_taken c c' a b :
      rec_h c' = rec_h c -> val_h c' = val_h c -> val_o c' = val_o c ->
      ts_h c' = ts_h c -> ts_o c' = ts_o c -> taken_o c' = taken_o c ->
      next_h c' = next_h c -> next_o c' = next_o c ->
      taken_h c' = heap_update a b (taken_h c) ->
      referenced_taken c a ->
      HeapRely c c'.
    Proof.
      intros Hr Hv Hvo Ht Hto Hko Hn Hno Hk Href.
      unfold HeapRely. rewrite Hr, Hv, Hvo, Ht, Hto, Hko, Hn, Hno, Hk.
      repeat split; auto.
      intros x v Hx Hnref. rewrite HeapUpdateOther; [exact Hx|].
      intros <-. apply Hnref. exact Href.
    Qed.

    Lemma HeapRely_update_ts c c' a ts :
      rec_h c' = rec_h c -> val_h c' = val_h c -> val_o c' = val_o c ->
      taken_h c' = taken_h c -> taken_o c' = taken_o c -> ts_o c' = ts_o c ->
      next_h c' = next_h c -> next_o c' = next_o c ->
      ts_h c' = heap_update a ts (ts_h c) ->
      referenced_ts c a ->
      HeapRely c c'.
    Proof.
      intros Hr Hv Hvo Hk Hko Hto Hn Hno Ht Href.
      unfold HeapRely. rewrite Hr, Hv, Hvo, Hk, Hko, Hto, Hn, Hno, Ht.
      repeat split; auto.
      intros x v Hx Hnref. rewrite HeapUpdateOther; [exact Hx|].
      intros <-. apply Hnref. exact Href.
    Qed.

    (** * Method: tryTake *)

    Lemma tryTake_read_res_update t l lv lts lt ln tk :
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_taken (oread lt)) tk |}
        (Active t (nmtryTake l) //\\ RecIs l (mkrec lv lts lt ln))
        (if tk then DoneOrErr t (nmtryTake l) false
         else Active t (nmtryTake l) //\\ RecIs l (mkrec lv lts lt ln)).
    Proof.
      intros σ1 ρ1 π1 [[HI Hlin] Hr] σ2 Hstep.
      apply (step_taken t (ResEv (oread lt) tk)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_read_res_shape _ _ _ _ _ Hs) as [s [Hc [Hv Hc']]].
      assert (Hsame : same_heaps σ1 σ2).
      { apply same_heaps_control; [rewrite H1|rewrite H2|rewrite H3|rewrite H4|rewrite Hc, Hc'];
          reflexivity. }
      destruct tk.
      - pose proof HI as [[h Hρ] _]. simpl in Hρ. subst ρ1.
        eapply field_read_lin; eauto;
          [apply no_new_ts_write_eq; exact H3|discriminate|].
        intros [[[v0 ts0] tk0] nx0] Hn [_ [_ [Hval _]]]. simpl_fields Hval; simpl in Hval.
        unfold taken_h in Hval. rewrite Hc in Hval. simpl_fields Hval; simpl in Hval.
        rewrite Hv in Hval. injection Hval as <-.
        split.
        + eapply step_tryTake_inv; [reflexivity|rewrite Hn; discriminate].
        + eapply step_tryTake_res_fail; [reflexivity|exact Hn].
      - exists ρ1, π1. split; [apply rt_refl|]. split.
        + split; [split; [eapply I_same; eauto; apply no_new_ts_write_eq; exact H3|exact Hlin]|].
          apply (RecIs_ci l (mkrec lv lts lt ln) σ1 σ2 ρ1 π1);
            [apply same_heaps_grow; exact Hsame|exact Hr].
        + apply G_same; auto.
    Qed.

    Lemma tryTake_cas_res_update t l lv lts lt ln b :
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_taken (ocas lt false true)) b |}
        (Active t (nmtryTake l) //\\ RecIs l (mkrec lv lts lt ln))
        (DoneOrErr t (nmtryTake l) b).
    Proof.
      intros σ1 ρ1 π1 [[HI Hlin] Hr] σ2 Hstep.
      apply (step_taken t (ResEv (ocas lt false true) b)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      pose proof HI as [[h Hρ] [Hcon [Hp Hor]]]. simpl in Hρ. subst ρ1.
      unfold RecIs in Hr. simpl in Hr.
      destruct b.
      - destruct (omem_cas_true_shape _ _ _ _ _ _ Hs) as [s [Hc [Hv Hc']]].
        assert (Hheaps : rec_h σ2 = rec_h σ1 /\ val_h σ2 = val_h σ1 /\
          val_o σ2 = val_o σ1 /\ ts_h σ2 = ts_h σ1 /\ ts_o σ2 = ts_o σ1 /\
          next_h σ2 = next_h σ1 /\ next_o σ2 = next_o σ1 /\
          taken_o σ2 = taken_o σ1 /\ taken_h σ2 = heap_update lt true (taken_h σ1)).
        { unfold rec_h, val_h, val_o, ts_h, ts_o, next_h, next_o, taken_o, taken_h.
          rewrite H1, H2, H3, H4, Hc, Hc'. simpl. repeat split. }
        destruct Hheaps as (Hr2 & Hv2 & Hvo2 & Ht2 & Hto2 & Hn2 & Hno2 & Hko2 & Hk2).
        assert (Href : referenced_taken σ1 lt) by (exists l, (mkrec lv lts lt ln); auto).
        assert (Hcon2 : IConcrete σ2).
        { eapply IConcrete_grow; eauto; try (intros; congruence).
          intros a Ha. rewrite Hk2. apply heap_update_defined. exact Ha. }
        assert (HHR : HeapRely σ1 σ2).
        { eapply HeapRely_update_taken; eauto. }
        destruct Hor as [Herr | Hrep].
        + exists (Idle h), π1. split; [apply rt_refl|]. split.
          * right. split; [|exact Herr].
            split; [eexists; reflexivity|]. split; [exact Hcon2|].
            split; [eapply PendingTSWrite_same; eauto; apply no_new_ts_write_eq; exact H3|].
            left. exact Herr.
          * split; [auto|]. split; [exact HHR|].
            split; [intros l0 r0 Ha Hb; simpl in Ha, Hb; rewrite Hr2 in Hb; congruence|]. split.
            -- intros l0 n0 Hn0. exists n0. split; [exact Hn0|]. intros Hc0. contradiction.
            -- auto.
        + pose proof Hrep as [_ Hsome].
          destruct (Hsome _ _ Hr) as [n [Hn Hrepn]]. unfold abs in Hn. simpl in Hn.
          destruct n as [[[v0 ts0] tk0] nx0].
          destruct Hrepn as [_ [_ [Hk _]]]. simpl_fields Hk; simpl in Hk.
          unfold taken_h in Hk. rewrite Hc in Hk. simpl_fields Hk; simpl in Hk.
          rewrite Hv in Hk. injection Hk as <-.
          exists (Idle (heap_update l (mknode v0 ts0 true nx0) h)),
            (lin_π t (nmtryTake l) true π1).
          split.
          * apply lin_steps; [exact Hlin| |].
            -- eapply step_tryTake_inv; [reflexivity|rewrite Hn; discriminate].
            -- eapply step_tryTake_res_succ; [reflexivity|exact Hn].
          * split.
            -- left. split; [|unfold ALin; simpl; apply lin_π_self].
               split; [eexists; reflexivity|]. split; [exact Hcon2|]. split.
               ++ eapply PendingTSWrite_same;
                    [apply no_new_ts_write_eq; exact H3|exact Hr2
                    |apply AtSetTS_lin; [exact Hlin|discriminate]|exact Hp].
               ++ right.
                  apply (Rep_update_taken σ1 σ2 h π1 _ l (mkrec lv lts lt ln)
                    (mknode v0 ts0 false nx0) true); auto.
            -- split; [intros t' Hne; simpl; rewrite lin_π_other; auto|].
               split; [exact HHR|].
               split; [intros l0 r0 Ha Hb; simpl in Ha, Hb; rewrite Hr2 in Hb; congruence|]. split.
               ++ intros l0 n0 Hn0. unfold abs in Hn0. simpl in Hn0.
                  destruct (Nat.eq_dec l l0) as [<-|Hne].
                  ** exists (mknode v0 ts0 true nx0). split; [apply HeapUpdateSelf|].
                     rewrite Hn in Hn0. injection Hn0 as <-. simpl. intros Hc0. contradiction.
                  ** exists n0. split; [simpl_abs; rewrite HeapUpdateOther; auto|].
                     intros Hc0. contradiction.
               ++ intros l0 Hat _. exfalso.
                  destruct (AtSetTS_self _ _ _ _ Hlin Hat) as [ts1 Heq]. discriminate Heq.
      - destruct (omem_cas_false_shape _ _ _ _ _ _ Hs) as [s [u [Hc [Hu [Hne Hc']]]]].
        destruct u; [|exfalso; apply Hne; reflexivity].
        assert (Hsame : same_heaps σ1 σ2).
        { apply same_heaps_control; [rewrite H1|rewrite H2|rewrite H3|rewrite H4|rewrite Hc, Hc'];
            reflexivity. }
        eapply field_read_lin; eauto;
          [apply no_new_ts_write_eq; exact H3|discriminate|].
        intros [[[v0 ts0] tk0] nx0] Hn [_ [_ [Hval _]]]. simpl_fields Hval; simpl in Hval.
        unfold taken_h in Hval. rewrite Hc in Hval. simpl_fields Hval; simpl in Hval.
        rewrite Hu in Hval. injection Hval as <-.
        split.
        + eapply step_tryTake_inv; [reflexivity|rewrite Hn; discriminate].
        + eapply step_tryTake_res_fail; [reflexivity|exact Hn].
    Qed.

    Lemma tryTake_triple t l :
      [li_lts E, li_lts F, lift_relation (R t), lift_relation (G t), lift_assert I, t] ⊢
        {{ lift_assert (Active t (nmtryTake l)) }}
          (@tryTake_impl A l t)
        {{ fun b => lift_assert (Done t (nmtryTake l) b) }}.
    Proof.
      eapply SetLogic.provable_perror.
      { apply lift_perror. apply (defined_or_error t (nmtryTake l) l).
        intros h Hnone. eapply error_tryTake_undefined; [reflexivity|exact Hnone]. }
      unfold tryTake_impl.
      eapply singleton_provable_vis_safe with
        (P' := I //\\ (ALin t (ls_inv (nmtryTake l)) //\\ Defined l))
        (Q' := fun r => I //\\ (ALin t (ls_inv (nmtryTake l)) //\\ Defined l) //\\ RecIs l r).
      - apply read_rec_no_error. intros s [_ [_ H]]. exact H.
      - intros s [HI _]. exact HI.
      - intros r s [HI _]. exact HI.
      - solve_conj_stable stableDB.
      - intros r. solve_conj_stable stableDB.
      - apply inv_update; [auto with ciDB|discriminate].
      - intros r. apply rec_read_res_update. auto with ciDB.
      - intros [[[lv lts] lt] ln]. cbn.
        eapply singleton_provable_vis_safe with
          (P' := Active t (nmtryTake l) //\\ RecIs l (mkrec lv lts lt ln))
          (Q' := fun tk : bool => if tk then DoneOrErr t (nmtryTake l) false
                  else Active t (nmtryTake l) //\\ RecIs l (mkrec lv lts lt ln)).
        + apply (read_taken_no_error t l (mkrec lv lts lt ln)).
          intros s [HI [_ Hr]]. split; [exact HI|exact Hr].
        + intros s [[HI _] _]. exact HI.
        + intros [|]; [apply DoneOrErr_I|intros s [[HI _] _]; exact HI].
        + solve_conj_stable stableDB.
        + intros [|]; [apply DoneOrErr_stable|solve_conj_stable stableDB].
        + eapply PUpdateConseq;
            [apply ImplRefl| |apply inv_update; [auto with ciDB|discriminate]].
          intros s [HI [[Hlin _] Hr]]. split; [split; [exact HI|exact Hlin]|exact Hr].
        + intros tk. apply tryTake_read_res_update.
        + intros [|].
          * eapply SetLogic.provable_perror; [apply DoneOrErr_perror|].
            singleton_ret_safe; [apply ImplRefl|apply Done_I|apply Done_stable].
          * eapply singleton_provable_vis_safe with
              (P' := Active t (nmtryTake l) //\\ RecIs l (mkrec lv lts lt ln))
              (Q' := fun b => DoneOrErr t (nmtryTake l) b).
            -- apply (cas_taken_no_error t l (mkrec lv lts lt ln)).
               intros s [[HI _] Hr]. split; [exact HI|exact Hr].
            -- intros s [[HI _] _]. exact HI.
            -- intros b. apply DoneOrErr_I.
            -- solve_conj_stable stableDB.
            -- intros b. apply DoneOrErr_stable.
            -- eapply PUpdateConseq;
                 [| |apply (inv_update t _ (ALin t (ls_inv (nmtryTake l)) //\\
                                            RecIs l (mkrec lv lts lt ln)));
                     [auto with ciDB|discriminate]].
               ++ intros s [[HI Hlin] Hr]. split; [exact HI|split; [exact Hlin|exact Hr]].
               ++ intros s [HI [Hlin Hr]]. split; [split; [exact HI|exact Hlin]|exact Hr].
            -- intros b. apply tryTake_cas_res_update.
            -- intros b. eapply SetLogic.provable_perror; [apply DoneOrErr_perror|].
               singleton_ret_safe; [apply ImplRefl|apply Done_I|apply Done_stable].
    Qed.

    (** * Method: setTS *)

    (** Reading the timestamp cell.  [TSTop] records that the abstract
        timestamp is still unset; an interval is the (no-op) linearization
        point, unless another [setTS] on the node is in flight, in which case
        the racy error is reachable and nothing is linearized. *)
    Lemma setTS_read_res_update t l ts lv lts lt ln old :
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_ts (oread lts)) old |}
        (Active t (nmsetTS l ts) //\\ RecIs l (mkrec lv lts lt ln))
        (match old with
         | TSTop => I //\\ TSTopSeen t l ts //\\ RecIs l (mkrec lv lts lt ln)
         | TSInterval _ _ => DoneOrErr t (nmsetTS l ts) tt
         end).
    Proof.
      intros σ1 ρ1 π1 [[HI Hlin] Hr] σ2 Hstep.
      apply (step_ts t (ResEv (oread lts) old)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_read_res_shape _ _ _ _ _ Hs) as [s [Hc [Hv Hc']]].
      assert (Hsame : same_heaps σ1 σ2).
      { apply same_heaps_control; [rewrite H1|rewrite H2|rewrite Hc, Hc'|rewrite H3|rewrite H4];
          reflexivity. }
      assert (Hnw : no_new_ts_write σ1 σ2) by (eapply no_new_ts_write_idle; exact Hc').
      pose proof HI as [[h Hρ] [Hcon [Hp Hor]]]. simpl in Hρ. subst ρ1.
      unfold ALin in Hlin. simpl in Hlin. unfold RecIs in Hr. simpl in Hr.
      assert (Hval : ts_h σ1 lts = Some old).
      { unfold ts_h. rewrite Hc. simpl. exact Hv. }
      destruct old as [|a b].
      - (* TSTop *)
        exists (Idle h), π1. split; [apply rt_refl|]. split.
        + split; [eapply I_same; eauto|]. split; [|unfold RecIs; simpl; destruct Hsame as [Hr2 _]; rewrite Hr2; exact Hr].
          split; [exact Hlin|].
          destruct Hor as [Herr|[_ Hsome]]; [left; exact Herr|right].
          destruct (Hsome _ _ Hr) as [n [Hn Hrep]]. exists n. split; [exact Hn|].
          destruct Hrep as [_ [Ht _]]. simpl_fields Ht; simpl in Ht. rewrite Hval in Ht.
          injection Ht as Ht. symmetry. exact Ht.
        + apply G_same; auto.
      - (* interval *)
        destruct Hor as [Herr|Hrep].
        + exists (Idle h), π1. split; [apply rt_refl|]. split.
          * right. split; [eapply I_same; eauto|exact Herr].
          * apply G_same; auto.
        + destruct (classic (OtherAtSetTS (st σ1 (Idle h) π1) t l)) as [Hother|Hno].
          * (* racing: the error is reachable, do not linearize *)
            assert (Herr : Err (st σ1 (Idle h) π1)).
            { destruct Hother as [t' [Hne Hat]]. exists l, t, t'. split; [exact Hne|].
              split; [exists ts; exact Hlin|exact Hat]. }
            exists (Idle h), π1. split; [apply rt_refl|]. split.
            -- right. split; [eapply I_same; eauto|exact Herr].
            -- apply G_same; auto.
          * (* no-op linearization *)
            pose proof Hrep as [_ Hsome].
            destruct (Hsome _ _ Hr) as [n [Hn Hrep']]. unfold abs in Hn. simpl in Hn.
            destruct n as [[[v0 ts0] tk0] nx0].
            destruct Hrep' as [_ [Ht _]]. simpl_fields Ht; simpl in Ht. rewrite Hval in Ht.
            injection Ht as <-.
            change (h l = Some (mknode v0 (TSInterval a b) tk0 nx0)) in Hn.
            exists (Idle (heap_update l (mknode v0 (TSInterval a b) tk0 nx0) h)),
              (lin_π t (nmsetTS l ts) tt π1).
            split.
            { apply lin_steps; [exact Hlin| |].
              - eapply step_setTS_inv; [reflexivity|rewrite Hn; discriminate].
              - apply (step_setTS_res t h l v0 (TSInterval a b) tk0 nx0 ts);
                  [reflexivity|exact Hn]. }
            rewrite (heap_update_same h l _ Hn).
            split.
            -- left. split; [|unfold ALin; simpl; apply lin_π_self].
               split; [eexists; reflexivity|]. split; [eapply IConcrete_same; eauto|].
               split.
               ++ intros st0 t' x v Hpend. simpl in Hpend. rewrite Hc' in Hpend. discriminate.
               ++ right. eapply Rep_same; eauto.
            -- apply G_same; auto.
               ++ intros t' Hne. rewrite lin_π_other; auto.
               ++ intros l0 Hat [t' [Hne Hat']]. exfalso. apply Hno.
                  pose proof (AtSetTS_self_setTS _ _ _ _ _ Hlin Hat) as ->.
                  exists t'. split; [exact Hne|exact Hat'].
    Qed.

    (** Invoking the store: the new pending store belongs to this [setTS]. *)
    Lemma setTS_write_inv_update t l ts lv lts lt ln :
      PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_ts (owrite lts ts)) |}
        (I //\\ TSTopSeen t l ts //\\ RecIs l (mkrec lv lts lt ln) //\\
           NoOtherTSWrite t lts)
        (I //\\ TSTopSeen t l ts //\\ RecIs l (mkrec lv lts lt ln)).
    Proof.
      intros σ1 ρ1 π1 [HI [Hseen [Hr _]]] σ2 Hstep.
      apply (step_ts t (InvEv (owrite lts ts))) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_inv_shape _ _ _ _ Hs) as [s [Hc Hc']].
      assert (Hsame : same_heaps σ1 σ2).
      { apply same_heaps_control; [rewrite H1|rewrite H2|rewrite Hc, Hc'|rewrite H3|rewrite H4];
          reflexivity. }
      exists ρ1, π1. split; [apply rt_refl|]. split.
      - destruct HI as [Hρ [Hcon [Hp Hor]]].
        split; [|split; [exact Hseen|apply (RecIs_ci l (mkrec lv lts lt ln) σ1 σ2 ρ1 π1);
                                      [apply same_heaps_grow; exact Hsame|exact Hr]]].
        split; [exact Hρ|]. split; [eapply IConcrete_same; eauto|]. split.
        + intros st0 t' x v Hpend. simpl in Hpend. rewrite Hc' in Hpend.
          injection Hpend as <- <- <- <-.
          exists l, (mkrec lv lts lt ln). simpl.
          destruct Hsame as [Hr2 _]. rewrite Hr2.
          split; [exact Hr|]. split; [reflexivity|]. exists ts. apply Hseen.
        + destruct Hor as [He|Hrep]; [left; exact He|right; eapply Rep_same; eauto].
      - apply G_same; auto.
    Qed.

    (** The store's response: the linearization point of a [setTS] that found
        [TSTop], unless another [setTS] on the node is in flight. *)
    Lemma setTS_write_res_update t l ts lv lts lt ln :
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_ts (owrite lts ts)) tt |}
        (I //\\ TSTopSeen t l ts //\\ RecIs l (mkrec lv lts lt ln))
        (DoneOrErr t (nmsetTS l ts) tt).
    Proof.
      intros σ1 ρ1 π1 [HI [[Hlin Hseen] Hr]] σ2 Hstep.
      apply (step_ts t (ResEv (owrite lts ts) tt)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_write_res_shape _ _ _ _ _ Hs) as [s [Hc [Hdef Hc']]].
      pose proof HI as [[h Hρ] [Hcon [Hp Hor]]]. simpl in Hρ. subst ρ1.
      simpl in Hlin. unfold RecIs in Hr. simpl in Hr.
      assert (Hheaps : rec_h σ2 = rec_h σ1 /\ val_h σ2 = val_h σ1 /\
        val_o σ2 = val_o σ1 /\ taken_h σ2 = taken_h σ1 /\ taken_o σ2 = taken_o σ1 /\
        next_h σ2 = next_h σ1 /\ next_o σ2 = next_o σ1 /\
        ts_o σ2 = ts_o σ1 /\ ts_h σ2 = heap_update lts ts (ts_h σ1)).
      { unfold rec_h, val_h, val_o, ts_h, ts_o, next_h, next_o, taken_o, taken_h.
        rewrite H1, H2, H3, H4, Hc, Hc'. simpl. repeat split. }
      destruct Hheaps as (Hr2 & Hv2 & Hvo2 & Hk2 & Hko2 & Hn2 & Hno2 & Hto2 & Ht2).
      assert (Href : referenced_ts σ1 lts) by (exists l, (mkrec lv lts lt ln); auto).
      assert (Hcon2 : IConcrete σ2).
      { eapply IConcrete_grow; eauto; try (intros; congruence).
        intros a Ha. rewrite Ht2. apply heap_update_defined. exact Ha. }
      assert (HHR : HeapRely σ1 σ2) by (eapply HeapRely_update_ts; eauto).
      assert (Hnw : no_new_ts_write σ1 σ2) by (eapply no_new_ts_write_idle; exact Hc').
      (* the branch that does not linearize *)
      assert (Hstay : Err (st σ1 (Idle h) π1) ->
        exists ρ' π', @poss_steps _ (li_lts F) (@PossOk _ (li_lts F) (Idle h) π1) (@PossOk _ (li_lts F) ρ' π') /\
          DoneOrErr t (nmsetTS l ts) tt (st σ2 ρ' π') /\
          G t (st σ1 (Idle h) π1) (st σ2 ρ' π')).
      { intros Herr. exists (Idle h), π1. split; [apply rt_refl|]. split.
        - right. split; [|exact Herr].
          split; [eexists; reflexivity|]. split; [exact Hcon2|].
          split; [eapply PendingTSWrite_same; eauto|left; exact Herr].
        - split; [auto|]. split; [exact HHR|].
          split; [intros l0 r0 Ha Hb; simpl in Ha, Hb; rewrite Hr2 in Hb; congruence|]. split.
          + intros l0 n0 Hn0. exists n0. split; [exact Hn0|]. intros Hc0. contradiction.
          + auto. }
      destruct Hor as [Herr|Hrep]; [apply Hstay; exact Herr|].
      destruct Hseen as [Herr|[n [Hn Htop]]]; [apply Hstay; exact Herr|].
      destruct (classic (OtherAtSetTS (st σ1 (Idle h) π1) t l)) as [Hother|Hno].
      { apply Hstay. destruct Hother as [t' [Hne Hat]]. exists l, t, t'.
        split; [exact Hne|]. split; [exists ts; exact Hlin|exact Hat]. }
      unfold abs in Hn. simpl in Hn.
      destruct n as [[[v0 ts0] tk0] nx0]. simpl_fields Htop; simpl in Htop. subst ts0.
      change (h l = Some (mknode v0 TSTop tk0 nx0)) in Hn.
      exists (Idle (heap_update l (mknode v0 ts tk0 nx0) h)),
        (lin_π t (nmsetTS l ts) tt π1).
      split.
      { apply lin_steps; [exact Hlin| |].
        - eapply step_setTS_inv; [reflexivity|rewrite Hn; discriminate].
        - apply (step_setTS_res t h l v0 TSTop tk0 nx0 ts); [reflexivity|exact Hn]. }
      split.
      - left. split; [|unfold ALin; simpl; apply lin_π_self].
        split; [eexists; reflexivity|]. split; [exact Hcon2|]. split.
        + intros st0 t' x v Hpend. simpl in Hpend. rewrite Hc' in Hpend. discriminate.
        + right.
          apply (Rep_update_ts σ1 σ2 h π1 _ l (mkrec lv lts lt ln)
            (mknode v0 TSTop tk0 nx0) ts); auto.
      - split; [intros t' Hne; simpl; rewrite lin_π_other; auto|].
        split; [exact HHR|].
        split; [intros l0 r0 Ha Hb; simpl in Ha, Hb; rewrite Hr2 in Hb; congruence|]. split.
        + intros l0 n0 Hn0. unfold abs in Hn0. simpl in Hn0.
          destruct (Nat.eq_dec l l0) as [<-|Hne].
          * exists (mknode v0 ts tk0 nx0). split; [apply HeapUpdateSelf|].
            intros _. exact Hno.
          * exists n0. split; [simpl_abs; rewrite HeapUpdateOther; auto|].
            intros Hc0. contradiction.
        + intros l0 Hat [t' [Hne Hat']]. exfalso. apply Hno.
          pose proof (AtSetTS_self_setTS _ _ _ _ _ Hlin Hat) as ->.
          exists t'. split; [exact Hne|exact Hat'].
    Qed.

    Lemma setTS_triple t l ts :
      [li_lts E, li_lts F, lift_relation (R t), lift_relation (G t), lift_assert I, t] ⊢
        {{ lift_assert (Active t (nmsetTS l ts)) }}
          (@setTS_impl A l ts t)
        {{ fun u => lift_assert (Done t (nmsetTS l ts) u) }}.
    Proof.
      eapply SetLogic.provable_perror.
      { apply lift_perror. apply (defined_or_error t (nmsetTS l ts) l).
        intros h Hnone. eapply error_setTS_undefined; [reflexivity|exact Hnone]. }
      unfold setTS_impl.
      eapply singleton_provable_vis_safe with
        (P' := I //\\ (ALin t (ls_inv (nmsetTS l ts)) //\\ Defined l))
        (Q' := fun r => I //\\ (ALin t (ls_inv (nmsetTS l ts)) //\\ Defined l) //\\ RecIs l r).
      - apply read_rec_no_error. intros s [_ [_ H]]. exact H.
      - intros s [HI _]. exact HI.
      - intros r s [HI _]. exact HI.
      - solve_conj_stable stableDB.
      - intros r. solve_conj_stable stableDB.
      - apply inv_update; [auto with ciDB|discriminate].
      - intros r. apply rec_read_res_update. auto with ciDB.
      - intros [[[lv lts] lt] ln]. cbn.
        eapply singleton_provable_vis_safe with
          (P' := Active t (nmsetTS l ts) //\\ RecIs l (mkrec lv lts lt ln))
          (Q' := fun old => match old with
                  | TSTop => I //\\ TSTopSeen t l ts //\\ RecIs l (mkrec lv lts lt ln)
                  | TSInterval _ _ => DoneOrErr t (nmsetTS l ts) tt
                  end).
        + apply (read_ts_no_error t l (mkrec lv lts lt ln)).
          intros s [HI [_ Hr]]. split; [exact HI|exact Hr].
        + intros s [[HI _] _]. exact HI.
        + intros [|a b]; cbn beta iota; [intros s [HI _]; exact HI|apply DoneOrErr_I].
        + solve_conj_stable stableDB.
        + intros [|a b]; cbn beta iota; [solve_conj_stable stableDB|apply DoneOrErr_stable].
        + eapply PUpdateConseq;
            [apply ImplRefl| |apply inv_update; [auto with ciDB|discriminate]].
          intros s [HI [[Hlin _] Hr]]. split; [split; [exact HI|exact Hlin]|exact Hr].
        + intros old. apply setTS_read_res_update.
        + intros [|a b]; cbn beta iota.
          * (* TSTop: store the timestamp *)
            eapply SetLogic.provable_perror.
            { apply lift_perror. apply ts_write_race_or_error. }
            eapply singleton_provable_vis_safe with
              (P' := I //\\ TSTopSeen t l ts //\\ RecIs l (mkrec lv lts lt ln))
              (Q' := fun _ => DoneOrErr t (nmsetTS l ts) tt).
            -- apply (write_ts_no_error t l (mkrec lv lts lt ln)).
            -- intros s [HI _]. exact HI.
            -- intros u. apply DoneOrErr_I.
            -- solve_conj_stable stableDB.
            -- intros u. apply DoneOrErr_stable.
            -- apply setTS_write_inv_update.
            -- intros []. apply setTS_write_res_update.
            -- intros []. eapply SetLogic.provable_perror; [apply DoneOrErr_perror|].
               singleton_ret_safe; [apply ImplRefl|apply Done_I|apply Done_stable].
          * eapply SetLogic.provable_perror; [apply DoneOrErr_perror|].
            singleton_ret_safe; [apply ImplRefl|apply Done_I|apply Done_stable].
    Qed.

    (** * Method: malloc *)

    Lemma Rep_grow c c' a p p' :
      heaps_grow c c' -> Rep (st c a p) -> Rep (st c' a p').
    Proof.
      intros (Hr & Hv & _ & Ht & _ & Hk & _ & Hn & _) [H1 H2].
      unfold Rep, represents, abs in *. simpl in *. rewrite Hr. split; [exact H1|].
      intros l r Hl. destruct (H2 _ _ Hl) as [n [Hn' [Hv' [Ht' [Hk' Hn'']]]]].
      exists n. split; [exact Hn'|]. split; [apply Hv; exact Hv'|].
      split; [apply Ht; exact Ht'|]. split; [apply Hk; exact Hk'|apply Hn; exact Hn''].
    Qed.

    Lemma I_grow c c' a p :
      heaps_grow c c' -> no_new_ts_write c c' -> I (st c a p) -> I (st c' a p).
    Proof.
      intros Hg Hnw [Hρ [Hc [Hp Hor]]].
      split; [exact Hρ|]. split.
      { cbn [st SinglePossState.σ] in Hc |- *.
        destruct Hg as (Hr & Hv & _ & Ht & _ & Hk & _ & Hn & _).
        eapply IConcrete_grow; eauto.
        - intros x Hx. destruct (val_h c x) eqn:Hx'; [|contradiction]. rewrite (Hv _ _ Hx'). discriminate.
        - intros x Hx. destruct (ts_h c x) eqn:Hx'; [|contradiction]. rewrite (Ht _ _ Hx'). discriminate.
        - intros x Hx. destruct (taken_h c x) eqn:Hx'; [|contradiction]. rewrite (Hk _ _ Hx'). discriminate.
        - intros x Hx. destruct (next_h c x) eqn:Hx'; [|contradiction]. rewrite (Hn _ _ Hx'). discriminate. }
      split; [eapply PendingTSWrite_grow; eauto; destruct Hg as [Hr _]; intros l r; rewrite Hr; auto|].
      destruct Hor as [He|Hrep]; [left; exact He|right; eapply Rep_grow; eauto].
    Qed.

    (** Allocating one field cell: the new cell is fresh and owned. *)
    Lemma malloc_val_res_update t v lv (P : assertion) :
      CI P ->
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_val (omalloc v)) lv |}
        (I //\\ P) (I //\\ P //\\ FreshVal t lv v).
    Proof.
      intros HP σ1 ρ1 π1 [HI Hpre] σ2 Hstep.
      apply (step_val t (ResEv (omalloc v) lv)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_alloc_res_shape _ _ _ _ _ Hs) as [s [Hc [Hnone Hc']]].
      assert (Hheaps : rec_h σ2 = rec_h σ1 /\ ts_h σ2 = ts_h σ1 /\ ts_o σ2 = ts_o σ1 /\
        taken_h σ2 = taken_h σ1 /\ taken_o σ2 = taken_o σ1 /\
        next_h σ2 = next_h σ1 /\ next_o σ2 = next_o σ1 /\
        val_h σ2 = heap_update lv v (val_h σ1) /\ val_o σ2 = heap_update lv t (val_o σ1) /\
        val_h σ1 lv = None).
      { unfold rec_h, val_h, val_o, ts_h, ts_o, next_h, next_o, taken_o, taken_h.
        rewrite H1, H2, H3, H4, Hc, Hc'. simpl. repeat split. exact Hnone. }
      destruct Hheaps as (Hr2 & Ht2 & Hto2 & Hk2 & Hko2 & Hn2 & Hno2 & Hv2 & Hvo2 & Hfresh).
      assert (Hg : heaps_grow σ1 σ2).
      { unfold heaps_grow. rewrite Hr2, Ht2, Hto2, Hk2, Hko2, Hn2, Hno2, Hv2, Hvo2.
        split; [reflexivity|].
        split; [intros a x Hx; apply heap_update_fresh; [exact Hfresh|exact Hx]|].
        split; [intros a o Ha Ho; rewrite HeapUpdateOther; [exact Ho|];
                intros <-; exact (Ha Hfresh)|].
        repeat split; auto. }
      exists ρ1, π1. split; [apply rt_refl|]. split.
      - split; [eapply I_grow; eauto; apply no_new_ts_write_eq; exact H2|].
        split; [apply (HP σ1 σ2 ρ1 π1); [exact Hg|exact Hpre]|].
        unfold FreshVal. cbn [SinglePossState.σ].
        split; [rewrite Hv2; apply HeapUpdateSelf|].
        split; [rewrite Hvo2; apply HeapUpdateSelf|].
        intros [l [r [Hl Hx]]]. rewrite Hr2 in Hl.
        destruct HI as [_ [[Hf _] _]]. destruct (Hf _ _ Hl) as [Hd _].
        cbn [SinglePossState.σ] in Hd. rewrite Hx in Hd. exact (Hd Hfresh).
      - split; [auto|]. split.
        { cbn [SinglePossState.σ]. unfold HeapRely. rewrite Hr2, Ht2, Hto2, Hk2, Hko2, Hn2, Hno2, Hv2, Hvo2.
          repeat split; auto.
          - intros a o Ha Ho. rewrite HeapUpdateOther; [exact Ho|]. intros <-. auto.
          - intros a x Hx. apply heap_update_fresh; auto. }
        split; [intros l0 r0 Ha Hb; simpl in Ha, Hb; rewrite Hr2 in Hb; congruence|]. split.
        + intros l0 n0 Hn0. exists n0. split; [exact Hn0|]. intros Hc0. contradiction.
        + auto.
    Qed.

    Lemma malloc_ts_res_update t lts (P : assertion) :
      CI P ->
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_ts (omalloc TSTop)) lts |}
        (I //\\ P) (I //\\ P //\\ FreshTS t lts).
    Proof.
      intros HP σ1 ρ1 π1 [HI Hpre] σ2 Hstep.
      apply (step_ts t (ResEv (omalloc TSTop) lts)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_alloc_res_shape _ _ _ _ _ Hs) as [s [Hc [Hnone Hc']]].
      assert (Hheaps : rec_h σ2 = rec_h σ1 /\ val_h σ2 = val_h σ1 /\ val_o σ2 = val_o σ1 /\
        taken_h σ2 = taken_h σ1 /\ taken_o σ2 = taken_o σ1 /\
        next_h σ2 = next_h σ1 /\ next_o σ2 = next_o σ1 /\
        ts_h σ2 = heap_update lts TSTop (ts_h σ1) /\ ts_o σ2 = heap_update lts t (ts_o σ1) /\
        ts_h σ1 lts = None).
      { unfold rec_h, val_h, val_o, ts_h, ts_o, next_h, next_o, taken_o, taken_h.
        rewrite H1, H2, H3, H4, Hc, Hc'. simpl. repeat split. exact Hnone. }
      destruct Hheaps as (Hr2 & Hv2 & Hvo2 & Hk2 & Hko2 & Hn2 & Hno2 & Ht2 & Hto2 & Hfresh).
      assert (Hg : heaps_grow σ1 σ2).
      { unfold heaps_grow. rewrite Hr2, Hv2, Hvo2, Hk2, Hko2, Hn2, Hno2, Ht2, Hto2.
        split; [reflexivity|]. split; [auto|]. split; [auto|].
        split; [intros a x Hx; apply heap_update_fresh; [exact Hfresh|exact Hx]|].
        split; [intros a o Ha Ho; rewrite HeapUpdateOther; [exact Ho|];
                intros <-; exact (Ha Hfresh)|].
        repeat split; auto. }
      exists ρ1, π1. split; [apply rt_refl|]. split.
      - split; [eapply I_grow; eauto; eapply no_new_ts_write_idle; exact Hc'|].
        split; [apply (HP σ1 σ2 ρ1 π1); [exact Hg|exact Hpre]|].
        unfold FreshTS. cbn [SinglePossState.σ].
        split; [rewrite Ht2; apply HeapUpdateSelf|].
        split; [rewrite Hto2; apply HeapUpdateSelf|].
        intros [l [r [Hl Hx]]]. rewrite Hr2 in Hl.
        destruct HI as [_ [[Hf _] _]]. destruct (Hf _ _ Hl) as [_ [Hd _]].
        cbn [SinglePossState.σ] in Hd. rewrite Hx in Hd. exact (Hd Hfresh).
      - split; [auto|]. split.
        { cbn [SinglePossState.σ]. unfold HeapRely. rewrite Hr2, Hv2, Hvo2, Hk2, Hko2, Hn2, Hno2, Ht2, Hto2.
          repeat split; auto.
          - intros a o Ha Ho. rewrite HeapUpdateOther; [exact Ho|]. intros <-. auto.
          - intros a x Hx _. apply heap_update_fresh; auto. }
        split; [intros l0 r0 Ha Hb; simpl in Ha, Hb; rewrite Hr2 in Hb; congruence|]. split.
        + intros l0 n0 Hn0. exists n0. split; [exact Hn0|]. intros Hc0. contradiction.
        + auto.
    Qed.

    Lemma malloc_next_res_update t nx ln (P : assertion) :
      CI P ->
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_next (omalloc nx)) ln |}
        (I //\\ P) (I //\\ P //\\ FreshNext t ln nx).
    Proof.
      intros HP σ1 ρ1 π1 [HI Hpre] σ2 Hstep.
      apply (step_next t (ResEv (omalloc nx) ln)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_alloc_res_shape _ _ _ _ _ Hs) as [s [Hc [Hnone Hc']]].
      assert (Hheaps : rec_h σ2 = rec_h σ1 /\ val_h σ2 = val_h σ1 /\ val_o σ2 = val_o σ1 /\
        taken_h σ2 = taken_h σ1 /\ taken_o σ2 = taken_o σ1 /\
        ts_h σ2 = ts_h σ1 /\ ts_o σ2 = ts_o σ1 /\
        next_h σ2 = heap_update ln nx (next_h σ1) /\ next_o σ2 = heap_update ln t (next_o σ1) /\
        next_h σ1 ln = None).
      { unfold rec_h, val_h, val_o, ts_h, ts_o, next_h, next_o, taken_o, taken_h.
        rewrite H1, H2, H3, H4, Hc, Hc'. simpl. repeat split. exact Hnone. }
      destruct Hheaps as (Hr2 & Hv2 & Hvo2 & Hk2 & Hko2 & Ht2 & Hto2 & Hn2 & Hno2 & Hfresh).
      assert (Hg : heaps_grow σ1 σ2).
      { unfold heaps_grow. rewrite Hr2, Hv2, Hvo2, Hk2, Hko2, Ht2, Hto2, Hn2, Hno2.
        split; [reflexivity|]. split; [auto|]. split; [auto|]. split; [auto|].
        split; [auto|]. split; [auto|]. split; [auto|].
        split; [intros a x Hx; apply heap_update_fresh; [exact Hfresh|exact Hx]|].
        intros a o Ha Ho; rewrite HeapUpdateOther; [exact Ho|];
        intros <-; exact (Ha Hfresh). }
      exists ρ1, π1. split; [apply rt_refl|]. split.
      - split; [eapply I_grow; eauto; apply no_new_ts_write_eq; exact H3|].
        split; [apply (HP σ1 σ2 ρ1 π1); [exact Hg|exact Hpre]|].
        unfold FreshNext. cbn [SinglePossState.σ].
        split; [rewrite Hn2; apply HeapUpdateSelf|].
        split; [rewrite Hno2; apply HeapUpdateSelf|].
        intros [l [r [Hl Hx]]]. rewrite Hr2 in Hl.
        destruct HI as [_ [[Hf _] _]]. destruct (Hf _ _ Hl) as [_ [_ [_ Hd]]].
        cbn [SinglePossState.σ] in Hd. rewrite Hx in Hd. exact (Hd Hfresh).
      - split; [auto|]. split.
        { cbn [SinglePossState.σ]. unfold HeapRely. rewrite Hr2, Hv2, Hvo2, Hk2, Hko2, Ht2, Hto2, Hn2, Hno2.
          repeat split; auto.
          - intros a o Ha Ho. rewrite HeapUpdateOther; [exact Ho|]. intros <-. auto.
          - intros a x Hx. apply heap_update_fresh; auto. }
        split; [intros l0 r0 Ha Hb; simpl in Ha, Hb; rewrite Hr2 in Hb; congruence|]. split.
        + intros l0 n0 Hn0. exists n0. split; [exact Hn0|]. intros Hc0. contradiction.
        + auto.
    Qed.

    Lemma malloc_taken_res_update t lt (P : assertion) :
      CI P ->
      PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_taken (omalloc false)) lt |}
        (I //\\ P) (I //\\ P //\\ FreshTaken t lt).
    Proof.
      intros HP σ1 ρ1 π1 [HI Hpre] σ2 Hstep.
      apply (step_taken t (ResEv (omalloc false) lt)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_alloc_res_shape _ _ _ _ _ Hs) as [s [Hc [Hnone Hc']]].
      assert (Hheaps : rec_h σ2 = rec_h σ1 /\ val_h σ2 = val_h σ1 /\ val_o σ2 = val_o σ1 /\
        ts_h σ2 = ts_h σ1 /\ ts_o σ2 = ts_o σ1 /\
        next_h σ2 = next_h σ1 /\ next_o σ2 = next_o σ1 /\
        taken_h σ2 = heap_update lt false (taken_h σ1) /\
        taken_o σ2 = heap_update lt t (taken_o σ1) /\
        taken_h σ1 lt = None).
      { unfold rec_h, val_h, val_o, ts_h, ts_o, next_h, next_o, taken_o, taken_h.
        rewrite H1, H2, H3, H4, Hc, Hc'. simpl. repeat split. exact Hnone. }
      destruct Hheaps as (Hr2 & Hv2 & Hvo2 & Ht2 & Hto2 & Hn2 & Hno2 & Hk2 & Hko2 & Hfresh).
      assert (Hg : heaps_grow σ1 σ2).
      { unfold heaps_grow. rewrite Hr2, Hv2, Hvo2, Ht2, Hto2, Hn2, Hno2, Hk2, Hko2.
        split; [reflexivity|]. split; [auto|]. split; [auto|]. split; [auto|].
        split; [auto|].
        split; [intros a x Hx; apply heap_update_fresh; [exact Hfresh|exact Hx]|].
        split; [intros a o Ha Ho; rewrite HeapUpdateOther; [exact Ho|];
                intros <-; exact (Ha Hfresh)|].
        split; auto. }
      exists ρ1, π1. split; [apply rt_refl|]. split.
      - split; [eapply I_grow; eauto; apply no_new_ts_write_eq; exact H3|].
        split; [apply (HP σ1 σ2 ρ1 π1); [exact Hg|exact Hpre]|].
        unfold FreshTaken. cbn [SinglePossState.σ].
        split; [rewrite Hk2; apply HeapUpdateSelf|].
        split; [rewrite Hko2; apply HeapUpdateSelf|].
        intros [l [r [Hl Hx]]]. rewrite Hr2 in Hl.
        destruct HI as [_ [[Hf _] _]]. destruct (Hf _ _ Hl) as [_ [_ [Hd _]]].
        cbn [SinglePossState.σ] in Hd. rewrite Hx in Hd. exact (Hd Hfresh).
      - split; [auto|]. split.
        { cbn [SinglePossState.σ]. unfold HeapRely. rewrite Hr2, Hv2, Hvo2, Ht2, Hto2, Hn2, Hno2, Hk2, Hko2.
          repeat split; auto.
          - intros a o Ha Ho. rewrite HeapUpdateOther; [exact Ho|]. intros <-. auto.
          - intros a x Hx _. apply heap_update_fresh; auto. }
        split; [intros l0 r0 Ha Hb; simpl in Ha, Hb; rewrite Hr2 in Hb; congruence|]. split.
        + intros l0 n0 Hn0. exists n0. split; [exact Hn0|]. intros Hc0. contradiction.
        + auto.
    Qed.

    (** Representation after publishing a fresh record. *)
    Lemma Rep_alloc c c' h p p' l r n :
      Rep (st c (Idle h) p) ->
      rec_h c' = heap_update l r (rec_h c) -> rec_h c l = None -> h l = None ->
      val_h c' = val_h c -> ts_h c' = ts_h c -> taken_h c' = taken_h c ->
      next_h c' = next_h c ->
      represents c' r n ->
      Rep (st c' (Idle (heap_update l n h)) p').
    Proof.
      intros [Hnone Hsome] Hr Hrl Hhl Hv Ht Hk Hn Hrep.
      unfold Rep, abs in *. simpl in *. rewrite Hr. split.
      - intros l'. destruct (Nat.eq_dec l l') as [<-|Hne].
        + rewrite !HeapUpdateSelf. split; discriminate.
        + rewrite !HeapUpdateOther; auto.
      - intros l' r' Hl'. destruct (Nat.eq_dec l l') as [<-|Hne].
        + rewrite HeapUpdateSelf in Hl'. injection Hl' as <-.
          exists n. split; [apply HeapUpdateSelf|exact Hrep].
        + rewrite HeapUpdateOther in Hl'; auto.
          destruct (Hsome _ _ Hl') as [n' [Hn' Hrep']].
          exists n'. split; [rewrite HeapUpdateOther; auto|].
          unfold represents in *. rewrite Hv, Ht, Hk, Hn. exact Hrep'.
    Qed.

    Lemma malloc_rec_res_update t v nx lv lts lt ln l :
      PUpdate (G t)
        {| te_tid := t; te_ev := ResEv (in_rec (omalloc (mkrec lv lts lt ln))) l |}
        (I //\\ ALin t (ls_inv (nmalloc v nx)) //\\ FreshVal t lv v //\\ FreshTS t lts
           //\\ FreshNext t ln nx //\\ FreshTaken t lt)
        (DoneOrErr t (nmalloc v nx) l).
    Proof.
      intros σ1 ρ1 π1 [HI [Hlin [Hfv [Hft [Hfn Hfk]]]]] σ2 Hstep.
      apply (step_rec t (ResEv (omalloc (mkrec lv lts lt ln)) l)) in Hstep.
      destruct Hstep as [Hs [H1 [H2 [H3 H4]]]].
      destruct (omem_alloc_res_shape _ _ _ _ _ Hs) as [s [Hc [Hnone Hc']]].
      pose proof HI as [[h Hρ] [Hcon [Hp Hor]]]. simpl in Hρ. subst ρ1.
      simpl in Hlin.
      destruct Hfv as [Hv1 [Hv2 Hv3]]. destruct Hft as [Ht1 [Ht2 Ht3]].
      destruct Hfn as [Hn1 [Hn2 Hn3]]. destruct Hfk as [Hk1 [Hk2 Hk3]].
      simpl in Hv1, Hv2, Hv3, Ht1, Ht2, Ht3, Hn1, Hn2, Hn3, Hk1, Hk2, Hk3.
      assert (Hheaps : val_h σ2 = val_h σ1 /\ val_o σ2 = val_o σ1 /\
        ts_h σ2 = ts_h σ1 /\ ts_o σ2 = ts_o σ1 /\
        taken_h σ2 = taken_h σ1 /\ taken_o σ2 = taken_o σ1 /\
        next_h σ2 = next_h σ1 /\ next_o σ2 = next_o σ1 /\
        rec_h σ2 = heap_update l (mkrec lv lts lt ln) (rec_h σ1) /\ rec_h σ1 l = None).
      { unfold rec_h, val_h, val_o, ts_h, ts_o, next_h, next_o, taken_o, taken_h.
        rewrite H1, H2, H3, H4, Hc, Hc'. simpl. repeat split. exact Hnone. }
      destruct Hheaps as (Hv2' & Hvo2 & Ht2' & Hto2 & Hk2' & Hko2 & Hn2' & Hno2 & Hr2 & Hrl).
      assert (Hrec_old : forall l' r', rec_h σ1 l' = Some r' -> rec_h σ2 l' = Some r').
      { intros l' r' Hl'. rewrite Hr2. apply heap_update_fresh; auto. }
      assert (Hrec_new : forall l' r', rec_h σ2 l' = Some r' ->
        (l' = l /\ r' = mkrec lv lts lt ln) \/ (l' <> l /\ rec_h σ1 l' = Some r')).
      { intros l' r' Hl'. rewrite Hr2 in Hl'. destruct (Nat.eq_dec l l') as [<-|Hne].
        - rewrite HeapUpdateSelf in Hl'. injection Hl' as <-. auto.
        - rewrite HeapUpdateOther in Hl'; auto. }
      assert (Hcon2 : IConcrete σ2).
      { destruct Hcon as [Hf Hinj]. split.
        - intros l' r' Hl'. destruct (Hrec_new _ _ Hl') as [[-> ->]|[_ Hold]].
          + unfold fields_defined. rewrite Hv2', Ht2', Hk2', Hn2'. simpl_fields_goal.
            repeat split; [rewrite Hv1|rewrite Ht1|rewrite Hk1|rewrite Hn1]; discriminate.
          + destruct (Hf _ _ Hold) as [Ha [Hb [Hc0 Hd]]]. unfold fields_defined.
            rewrite Hv2', Ht2', Hk2', Hn2'. auto.
        - intros l1 l2 r1 r2 Hl1 Hl2 Hne.
          destruct (Hrec_new _ _ Hl1) as [[-> ->]|[Hne1 Hold1]];
          destruct (Hrec_new _ _ Hl2) as [[-> ->]|[Hne2 Hold2]].
          + contradiction.
          + simpl_fields_goal. split; intros Heq.
            * apply Ht3. exists l2, r2. split; [exact Hold2|symmetry; exact Heq].
            * apply Hk3. exists l2, r2. split; [exact Hold2|symmetry; exact Heq].
          + simpl_fields_goal. split; intros Heq.
            * apply Ht3. exists l1, r1. split; [exact Hold1|exact Heq].
            * apply Hk3. exists l1, r1. split; [exact Hold1|exact Heq].
          + eapply Hinj; eauto. }
      assert (HHR : HeapRely σ1 σ2).
      { unfold HeapRely. rewrite Hv2', Hvo2, Ht2', Hto2, Hk2', Hko2, Hn2', Hno2.
        repeat split; auto. }
      assert (Hnew : NewRecOwner (fun o => o = Some t) σ1 σ2).
      { intros l' r' Hl1 Hl2. destruct (Hrec_new _ _ Hl2) as [[-> ->]|[_ Hold]];
          [|congruence].
        simpl_fields_goal. rewrite Hvo2, Hto2, Hko2, Hno2.
        split; [exact Hv2|]. split; [exact Ht2|]. split; [exact Hk2|exact Hn2]. }
      assert (Hpw : no_new_ts_write σ1 σ2) by (apply no_new_ts_write_eq; exact H2).
      destruct Hor as [Herr|Hrep].
      - exists (Idle h), π1. split; [apply rt_refl|]. split.
        + right. split; [|exact Herr].
          split; [eexists; reflexivity|]. split; [exact Hcon2|].
          split; [eapply PendingTSWrite_grow; eauto|left; exact Herr].
        + split; [auto|]. split; [exact HHR|]. split; [exact Hnew|]. split.
          * intros l0 n0 Hn0. exists n0. split; [exact Hn0|]. intros Hc0. contradiction.
          * auto.
      - pose proof Hrep as [Hnone' _].
        assert (Hhl : h l = None).
        { apply Hnone'. exact Hrl. }
        exists (Idle (heap_update l (mknode v TSTop false nx) h)),
          (lin_π t (nmalloc v nx) l π1).
        split.
        { apply lin_steps; [exact Hlin| |].
          - eapply step_malloc_inv; reflexivity.
          - eapply step_malloc_res; [reflexivity|exact Hhl]. }
        split.
        + left. split; [|unfold ALin; simpl; apply lin_π_self].
          split; [eexists; reflexivity|]. split; [exact Hcon2|]. split.
          * eapply PendingTSWrite_grow;
              [exact Hpw|exact Hrec_old|apply AtSetTS_lin; [exact Hlin|discriminate]|exact Hp].
          * right. eapply Rep_alloc; eauto.
            unfold represents. rewrite Hv2', Ht2', Hk2', Hn2'. simpl_fields_goal.
            split; [exact Hv1|]. split; [exact Ht1|]. split; [exact Hk1|exact Hn1].
        + split; [intros t' Hne; simpl; rewrite lin_π_other; auto|].
          split; [exact HHR|]. split; [exact Hnew|]. split.
          * intros l0 n0 Hn0. unfold abs in Hn0. simpl in Hn0.
            exists n0. split; [|intros Hc0; contradiction].
            simpl_abs. rewrite HeapUpdateOther; [exact Hn0|]. intros <-. congruence.
          * intros l0 Hat _. exfalso.
            destruct (AtSetTS_self _ _ _ _ Hlin Hat) as [ts' Heq]. discriminate Heq.
    Qed.

    Lemma malloc_triple t v nx :
      [li_lts E, li_lts F, lift_relation (R t), lift_relation (G t), lift_assert I, t] ⊢
        {{ lift_assert (Active t (nmalloc v nx)) }}
          (@malloc_impl A v nx t)
        {{ fun l => lift_assert (Done t (nmalloc v nx) l) }}.
    Proof.
      unfold malloc_impl.
      eapply singleton_provable_vis_safe with
        (P' := I //\\ ALin t (ls_inv (nmalloc v nx)))
        (Q' := fun lv => I //\\ ALin t (ls_inv (nmalloc v nx)) //\\ FreshVal t lv v).
      - apply alloc_val_no_error.
      - intros s [HI _]. exact HI.
      - intros lv s [HI _]. exact HI.
      - solve_conj_stable stableDB.
      - intros lv. solve_conj_stable stableDB.
      - apply inv_update; [auto with ciDB|discriminate].
      - intros lv. apply malloc_val_res_update. auto with ciDB.
      - intros lv.
        eapply singleton_provable_vis_safe with
          (P' := I //\\ (ALin t (ls_inv (nmalloc v nx)) //\\ FreshVal t lv v))
          (Q' := fun lts => I //\\ (ALin t (ls_inv (nmalloc v nx)) //\\ FreshVal t lv v)
                           //\\ FreshTS t lts).
        + apply alloc_ts_no_error.
        + intros s [HI _]. exact HI.
        + intros lts s [HI _]. exact HI.
        + solve_conj_stable stableDB.
        + intros lts. solve_conj_stable stableDB.
        + apply inv_update; [auto with ciDB|discriminate].
        + intros lts. apply malloc_ts_res_update. auto with ciDB.
        + intros lts.
          eapply singleton_provable_vis_safe with
            (P' := I //\\ ((ALin t (ls_inv (nmalloc v nx)) //\\ FreshVal t lv v)
                          //\\ FreshTS t lts))
            (Q' := fun ln => I //\\ ((ALin t (ls_inv (nmalloc v nx)) //\\ FreshVal t lv v)
                          //\\ FreshTS t lts) //\\ FreshNext t ln nx).
          * apply alloc_next_no_error.
          * intros s [HI _]. exact HI.
          * intros ln s [HI _]. exact HI.
          * solve_conj_stable stableDB.
          * intros ln. solve_conj_stable stableDB.
          * apply inv_update; [auto with ciDB|discriminate].
          * intros ln. apply malloc_next_res_update. auto with ciDB.
          * intros ln.
            eapply singleton_provable_vis_safe with
              (P' := I //\\ (((ALin t (ls_inv (nmalloc v nx)) //\\ FreshVal t lv v)
                          //\\ FreshTS t lts) //\\ FreshNext t ln nx))
              (Q' := fun lt => I //\\ (((ALin t (ls_inv (nmalloc v nx)) //\\ FreshVal t lv v)
                          //\\ FreshTS t lts) //\\ FreshNext t ln nx) //\\ FreshTaken t lt).
            -- apply alloc_taken_no_error.
            -- intros s [HI _]. exact HI.
            -- intros lt s [HI _]. exact HI.
            -- solve_conj_stable stableDB.
            -- intros lt. solve_conj_stable stableDB.
            -- apply inv_update; [auto with ciDB|discriminate].
            -- intros lt. apply malloc_taken_res_update. auto with ciDB.
            -- intros lt.
               eapply singleton_provable_vis_safe with
                 (P' := I //\\ ALin t (ls_inv (nmalloc v nx)) //\\ FreshVal t lv v
                          //\\ FreshTS t lts //\\ FreshNext t ln nx //\\ FreshTaken t lt)
                 (Q' := fun l => DoneOrErr t (nmalloc v nx) l).
               ++ apply alloc_rec_no_error.
               ++ intros s [HI _]. exact HI.
               ++ intros l. apply DoneOrErr_I.
               ++ solve_conj_stable stableDB.
               ++ intros l. apply DoneOrErr_stable.
               ++ eapply PUpdateConseq; [|apply ImplRefl|apply inv_update; [auto with ciDB|discriminate]].
                  intros s [HI [[[[Hlin Hfv] Hft] Hfn] Hfk]].
                  split; [exact HI|]. split; [exact Hlin|]. split; [exact Hfv|].
                  split; [exact Hft|]. split; [exact Hfn|exact Hfk].
               ++ intros l. apply malloc_rec_res_update.
               ++ intros l. eapply SetLogic.provable_perror; [apply DoneOrErr_perror|].
                  singleton_ret_safe; [apply ImplRefl|apply Done_I|apply Done_stable].
    Qed.

    (** * The layer *)

    Lemma I_ginv t f σ0 ρ0 π0 :
      I (st σ0 ρ0 π0) -> TMap.find t π0 = None ->
      I (st σ0 ρ0 (TMap.add t (ls_inv f) π0)).
    Proof.
      intros HI Hnone. eapply I_same; [| | |exact HI].
      - unfold same_heaps. repeat split.
      - apply no_new_ts_write_eq. reflexivity.
      - intros t' l [ts Hat]. exists ts. rewrite TMap.gso; [exact Hat|].
        intros <-. congruence.
    Qed.

    Lemma I_gret t f ret σ0 ρ0 π0 :
      I (st σ0 ρ0 π0) -> TMap.find t π0 = Some (ls_linr f ret) ->
      I (st σ0 ρ0 (TMap.remove t π0)).
    Proof.
      intros HI Hsome. eapply I_same; [| | |exact HI].
      - unfold same_heaps. repeat split.
      - apply no_new_ts_write_eq. reflexivity.
      - intros t' l [ts Hat]. exists ts. rewrite TMap.gro; [exact Hat|].
        intros <-. pose proof (eq_trans (eq_sym Hsome) Hat) as Heq. discriminate Heq.
    Qed.

    Lemma I_init :
      I (st (li_init E) (li_init F) (TMap.empty _)).
    Proof.
      split; [eexists; reflexivity|]. split.
      - split.
        + intros l r Hl. discriminate.
        + intros l1 l2 r1 r2 Hl. discriminate.
      - split.
        + intros st0 t' x v Hpend. discriminate.
        + right. split.
          * intros l. simpl. tauto.
          * intros l r Hl. discriminate.
    Qed.

    Program Definition MNodeMem : layer_implementation_simulation E F :=
    {| li_impl := @nodemem_impl A |}.
    Next Obligation.
      eapply SetLogic.soundness
        with (R := fun t => lift_relation (R t))
             (G := fun t => lift_relation (G t))
             (I := lift_assert I).
      (* valid RG *)
      { intros t. eapply lift_valid_rgi. apply source_valid_rg. }
      (* cross-thread compatibility *)
      {
        intros t1 t2 Hneq s s' Hrel.
        eapply lift_parallel_compat; [exact Hneq| |exact Hrel].
        apply source_rg_compatible; exact Hneq.
      }
      (* method provable *)
      {
        intros t f.
        exists (lift_assert (Active t f)).
        exists (fun ret => lift_assert (Done t f ret)).
        constructor.
        (* invocation *)
        - intros s Hcompose.
          eapply (lift_ginv_compose t f I (Active t f)); [|exact Hcompose].
          intros out [pre [HI [Hσ [Hρ [Hnone Hπ]]]]].
          destruct pre as [σp ρp πp], out as [σo ρo πo]. simpl in *. subst.
          split.
          + apply I_ginv; assumption.
          + unfold ALin. simpl. apply PositiveMap.gss.
        (* precondition entails invariant *)
        - intros s Hlift. eapply lift_impl; [|exact Hlift]. apply Active_I.
        (* precondition stable *)
        - apply lift_stable. apply Active_stable.
        (* return *)
        - intros ret s Hcompose.
          eapply (lift_gret_compose t f ret (Done t f ret) I); [|exact Hcompose].
          intros out [pre [[HI Hlin] [Hσ [Hρ [Hsome Hπ]]]]].
          destruct pre as [σp ρp πp], out as [σo ρo πo]. simpl in *. subst.
          eapply I_gret; eassumption.
        (* postcondition carries the linearized response *)
        - intros ret σ0 Δ0 Hpost ρ0 π0 Hposs.
          eapply (lift_post_lin (Done t f ret) t (ls_linr f ret));
            [|exact Hpost|exact Hposs].
          intros x [_ Hlin]. exact Hlin.
        (* the method bodies *)
        - destruct f; simpl.
          + apply malloc_triple.
          + apply setTS_triple.
          + apply getValue_triple.
          + apply getTS_triple.
          + apply getTaken_triple.
          + apply getNext_triple.
          + apply tryTake_triple.
      }
      (* initial singleton *)
      { apply lift_initial. apply I_init. }
    Defined.

    Definition MNodeMemLinearizable := LISim2LILin MNodeMem.

    (** * Down to the concrete memories *)

    (** The owner maps are ghost: [OwnerMemProof.MOwnerMem] realises each
        [OwnerMem] over the plain memory with the same operations, so NodeMem
        is linearizable from five concrete memories. *)
    Definition EPlain : layer_interface :=
      @PlainMemLayer.L (@NodeRec) ⊗ₗ @PlainMemLayer.L A ⊗ₗ @PlainMemLayer.L TS
      ⊗ₗ @PlainMemLayer.L Ptr ⊗ₗ @PlainMemLayer.L bool.

    Definition MNodeMemOverPlain :
        layer_implementation_linearizability EPlain F :=
      (⟦ @MOwnerMem (@NodeRec) ⟧ₗ ⊗ ⟦ @MOwnerMem A ⟧ₗ ⊗ ⟦ @MOwnerMem TS ⟧ₗ
        ⊗ ⟦ @MOwnerMem Ptr ⟧ₗ ⊗ ⟦ @MOwnerMem bool ⟧ₗ) ▶ MNodeMemLinearizable.

  End Proof.

  Print Assumptions MNodeMem.
  Print Assumptions MNodeMemOverPlain.

End NodeMemProof.
