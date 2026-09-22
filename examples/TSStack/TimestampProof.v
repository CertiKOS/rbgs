Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep.
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
Require Import examples.CAS.CASRegSpec.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.Timestamp.


(** Correctness of the interval timestamp implementation (Fig. 15) with
    respect to the [(t, p)] specification of Appendix A.1.

    The proof keeps a single abstract possibility.  The invariant ties the
    abstract clock [t] to the value of the CAS register.  The abstract
    invocation is linearized at the first [get]: the pending entry then
    records exactly the value read.  The response is linearized either at
    a successful [cas] (which advances both the register and the clock) or,
    in the two branches that return [[t1, n - 1]] for a later read [n], by
    an abstract-only step, since [n] is at most the current register value
    so [max t n = t] keeps the invariant. *)
Module TimestampProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSingle SingletonPossibility.
  Import TPSimulationSet.TPSimulation CompLinLayer.
  Import AtomicLTS CASRegSpec TimestampSpec TimestampImpl.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Definition single_state :=
    @SinglePossState.ProofStateSingle _ _ (li_lts E) (li_lts F).
  Definition assertion := @Assertion single_state.
  Definition rg_relation :=
    @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F).

  (** Views of the proof state. *)
  Definition counter (s : single_state) : nat := AtomicLTS.state (σ s).
  Definition clock (s : single_state) : nat := ts_clock (ρ s).
  Definition pending_of (actor : tid) (s : single_state) : option nat :=
    TMap.find actor (ts_pending (ρ s)).

  (** Invariant: the abstract clock is the register value. *)
  Definition I : assertion := fun s => clock s = counter s.

  (** [n] has been observed in the register, hence is a lower bound. *)
  Definition Observed (n : nat) : assertion := fun s => n <= counter s.

  (** The actor's pending invocation recorded [lower]. *)
  Definition Stamped (actor : tid) (lower : nat) : assertion :=
    fun s => pending_of actor s = Some lower.

  (** Guarantee: the register never decreases, and nothing owned by another
      thread (its pending entry, its linearization token) changes. *)
  Definition G (actor : tid) : rg_relation :=
    fun s s' =>
      counter s <= counter s' /\
      (forall other, actor <> other -> pending_of other s = pending_of other s') /\
      (forall other, actor <> other -> TMap.find other (π s) = TMap.find other (π s')).

  Definition R (actor : tid) : rg_relation :=
    fun s s' =>
      counter s <= counter s' /\
      pending_of actor s = pending_of actor s' /\
      TMap.find actor (π s) = TMap.find actor (π s').

  (** Introduction form of the guarantee on explicit proof states. *)
  Lemma G_intro actor σ σ' ρ ρ' π π' :
    AtomicLTS.state σ <= AtomicLTS.state σ' ->
    (forall other, actor <> other ->
      TMap.find other (ts_pending ρ) = TMap.find other (ts_pending ρ')) ->
    (forall other, actor <> other ->
      TMap.find other π = TMap.find other π') ->
    G actor
      (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F) σ ρ π)
      (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F) σ' ρ' π').
  Proof. intros Hmono Hpend Hπ. repeat split; auto. Qed.

  (** * Stability *)

  Lemma I_stable actor : Stable (R actor) I I.
  Proof. apply Stable_invariant. Qed.

  Lemma Observed_stable actor n : Stable (R actor) I (Observed n).
  Proof.
    intros s [[pre [Hobs [Hmono _]]] _]. unfold Observed in *. lia.
  Qed.

  Lemma Stamped_stable actor lower : Stable (R actor) I (Stamped actor lower).
  Proof.
    intros s [[pre [Hstamp [_ [Hpend _]]]] _]. unfold Stamped in *. congruence.
  Qed.

  Lemma ALin_stable actor ls : Stable (R actor) I (ALin actor ls).
  Proof.
    intros s [[pre [Hlin [_ [_ Hπ]]]] _]. unfold ALin in *. congruence.
  Qed.

  Lemma Pure_stable actor (P : Prop) : Stable (R actor) I (⌜P⌝).
  Proof. apply APureStable. Qed.

  Create HintDb stableDB.
  #[local] Hint Resolve I_stable Observed_stable Stamped_stable ALin_stable
    Pure_stable : stableDB.

  (** * Rely/guarantee side conditions *)

  Lemma source_valid_rg actor : forall s s', R actor s s' -> I s' ->
    TMap.find actor (π s) = None <-> TMap.find actor (π s') = None.
  Proof. intros s s' [_ [_ Hπ]] _. rewrite Hπ. tauto. Qed.

  Lemma source_rg_compatible t1 t2 : t1 <> t2 -> forall s s',
    (G t1 s s' \/ (GINV t1 s s' \/ GRET t1 s s') \/ GId s s') ->
    R t2 s s'.
  Proof.
    intros Hneq s s' [HG | [[Hinv | Hret] | Hid]].
    - destruct HG as [Hmono [Hpend Hπ]]. repeat split; auto.
    - destruct Hinv as [f [Hσ [Hρ [_ Hπ]]]].
      unfold R, counter, pending_of. rewrite Hσ, Hρ, Hπ.
      repeat split; auto. rewrite PositiveMap.gso; auto.
    - destruct Hret as [f [ret [Hσ [Hρ [_ Hπ]]]]].
      unfold R, counter, pending_of. rewrite Hσ, Hρ, Hπ.
      repeat split; auto. rewrite PositiveMap.gro; auto.
    - unfold GId in Hid. subst. repeat split; auto.
  Qed.

  (** * Steps of the CAS register *)

  Lemma cas_no_error actor op (P : assertion) :
    (forall v, op <> set v) ->
    ⊨ P ==>> ANoError {| te_tid := actor; te_ev := InvEv op |}.
  Proof.
    intros Hnotset s _ Herr. inversion Herr; subst;
    repeat match goal with
    | H : {| te_tid := _; te_ev := _ |} = {| te_tid := _; te_ev := _ |} |- _ =>
        inversion H; subst; clear H
    end;
    eapply Hnotset; reflexivity.
  Qed.

  Lemma get_no_error actor (P : assertion) :
    ⊨ P ==>> ANoError {| te_tid := actor; te_ev := InvEv get |}.
  Proof. apply cas_no_error. discriminate. Qed.

  Lemma cas_op_no_error actor v w (P : assertion) :
    ⊨ P ==>> ANoError {| te_tid := actor; te_ev := InvEv (cas v w) |}.
  Proof. apply cas_no_error. discriminate. Qed.

  (** Thread events carry dependent arguments; [injection] drops the
      dependent result component, so the boolean outcome of a [cas] is read
      back through an explicit projection. *)
  Definition cas_result (ev : @ThreadEvent (ECASReg nat)) : option bool :=
    match te_ev ev with
    | ResEv op ret =>
        match op return (Sig.ar op -> option bool) with
        | cas _ _ => fun b => Some b
        | _ => fun _ => None
        end ret
    | InvEv _ => None
    end.

  Ltac crush_cas_step :=
    repeat match goal with
    | H : {| te_tid := _; te_ev := _ |} = {| te_tid := _; te_ev := _ |} |- _ =>
        first [ apply (f_equal cas_result) in H; discriminate H
              | injection H; clear H; intros ]
    | H : InvEv _ = ResEv _ _ |- _ => discriminate H
    | H : ResEv _ _ = InvEv _ |- _ => discriminate H
    | H : InvEv _ = InvEv _ |- _ => injection H; clear H; intros
    | H : ResEv _ _ = ResEv _ _ |- _ => injection H; clear H; intros
    | H : cas _ _ = cas _ _ |- _ => injection H; clear H; intros
    | H : set _ = set _ |- _ => injection H; clear H; intros
    | H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H
    | H : ?x = ?x |- _ => clear H
    | H : ?x = ?y |- _ => is_var y; subst y
    | H : ?x = ?y |- _ => is_var x; subst x
    end;
    try discriminate; try congruence.

  Lemma step_inv_shape actor op σ σ' :
    Step (li_lts E) {| te_tid := actor; te_ev := InvEv op |} σ σ' ->
    exists c, σ = Idle c /\ σ' = Pending c actor op.
  Proof.
    intros Hstep. inversion Hstep; subst; crush_cas_step.
    inversion Hstep0; subst; crush_cas_step; eauto.
  Qed.

  Lemma step_get_res_shape actor r σ σ' :
    Step (li_lts E) {| te_tid := actor; te_ev := ResEv get r |} σ σ' ->
    σ = Pending r actor get /\ σ' = Idle r.
  Proof.
    intros Hstep. inversion Hstep; subst; crush_cas_step.
    inversion Hstep0; subst; crush_cas_step; auto.
  Qed.

  Lemma step_cas_true_shape actor v w σ σ' :
    Step (li_lts E) {| te_tid := actor; te_ev := ResEv (cas v w) true |} σ σ' ->
    σ = Pending v actor (cas v w) /\ σ' = Idle w.
  Proof.
    intros Hstep. inversion Hstep; subst; crush_cas_step.
    inversion Hstep0; subst; crush_cas_step; auto.
  Qed.

  Lemma step_cas_false_shape actor v w σ σ' :
    Step (li_lts E) {| te_tid := actor; te_ev := ResEv (cas v w) false |} σ σ' ->
    exists c, c <> v /\ σ = Pending c actor (cas v w) /\ σ' = Idle c.
  Proof.
    intros Hstep. inversion Hstep; subst; crush_cas_step.
    inversion Hstep0; subst; crush_cas_step; eauto.
  Qed.

  (** * The layer *)

  Program Definition MTimestamp : layer_implementation_simulation E F :=
  {| li_impl := timestamp_impl |}.
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
      intros t f. destruct f.
      exists (lift_assert (I //\\ ALin t (ls_inv newTS))).
      exists (fun ret => lift_assert (I //\\ ALin t (ls_linr newTS ret))).
      constructor.
      (* invocation *)
      - intros s Hcompose.
        eapply (lift_ginv_compose t newTS I
          (I //\\ ALin t (ls_inv newTS))); [|exact Hcompose].
        intros out [pre [HI [Hσ [Hρ [Hnone Hπ]]]]].
        destruct pre as [σp ρp πp], out as [σo ρo πo]. simpl in *. subst.
        split.
        + exact HI.
        + unfold ALin. simpl. apply PositiveMap.gss.
      (* precondition entails invariant *)
      - intros s Hlift. eapply lift_impl; [|exact Hlift].
        apply ConjLeftImpl. apply ImplRefl.
      (* precondition stable *)
      - apply lift_stable. solve_conj_stable stableDB.
      (* return *)
      - intros ret s Hcompose.
        eapply (lift_gret_compose t newTS ret
          (I //\\ ALin t (ls_linr newTS ret)) I); [|exact Hcompose].
        intros out [pre [[HI _] [Hσ [Hρ _]]]].
        destruct pre as [σp ρp πp], out as [σo ρo πo]. simpl in *. subst.
        exact HI.
      (* postcondition carries the linearized response *)
      - intros ret σ0 Δ0 Hpost ρ0 π0 Hposs.
        eapply (lift_post_lin
          (I //\\ ALin t (ls_linr newTS ret)) t
          (ls_linr newTS ret)); [|exact Hpost|exact Hposs].
        intros x [_ Hlin]. exact Hlin.
      (* the method body *)
      - simpl. unfold newTS_impl.

        (* [t1 ← get]: linearize the invocation at the response. *)
        singleton_vis_safe
          (I //\\ ALin t (ls_inv newTS))
          (fun t1 => I //\\ ALin t (ls_lini newTS)
                       //\\ Stamped t t1 //\\ Observed t1)
          using stableDB;
          [apply get_no_error| | |intros t1].
        {
          intros σ1 ρ1 π1 Hpre σ2 Hstep.
          destruct (step_inv_shape _ _ _ _ Hstep) as [c [-> ->]].
          exists ρ1, π1. split; [apply rt_refl|].
          split; [exact Hpre|]. apply G_intro; auto.
        }
        {
          intros t1 σ1 ρ1 π1 [HI Hlin] σ2 Hstep.
          destruct (step_get_res_shape _ _ _ _ Hstep) as [-> ->].
          unfold I, clock, counter in HI. simpl in HI.
          exists (start_newTS t ρ1), (TMap.add t (ls_lini newTS) π1).
          split.
          { apply rt_step. apply (ps_inv t newTS); [|exact Hlin].
            apply step_newTS_inv. reflexivity. }
          split.
          - split; [|split; [|split]].
            + unfold I, clock, counter. simpl. exact HI.
            + unfold ALin. simpl. apply PositiveMap.gss.
            + unfold Stamped, pending_of. simpl.
              rewrite PositiveMap.gss. congruence.
            + unfold Observed, counter. simpl. lia.
          - apply G_intro; [simpl; lia| |].
            + intros other Hneq. simpl. rewrite PositiveMap.gso; auto.
            + intros other Hneq. rewrite PositiveMap.gso; auto.
        }

        (* [t2 ← get]: the register is monotone, so [t1 <= t2]. *)
        singleton_vis_safe
          (I //\\ ALin t (ls_lini newTS) //\\ Stamped t t1 //\\ Observed t1)
          (fun t2 => I //\\ ALin t (ls_lini newTS) //\\ Stamped t t1
                       //\\ Observed t2 //\\ ⌜t1 <= t2⌝)
          using stableDB;
          [apply get_no_error| | |intros t2].
        {
          intros σ1 ρ1 π1 Hpre σ2 Hstep.
          destruct (step_inv_shape _ _ _ _ Hstep) as [c [-> ->]].
          exists ρ1, π1. split; [apply rt_refl|].
          split; [exact Hpre|]. apply G_intro; auto.
        }
        {
          intros t2 σ1 ρ1 π1 [HI [Hlin [Hstamp Hobs]]] σ2 Hstep.
          destruct (step_get_res_shape _ _ _ _ Hstep) as [-> ->].
          unfold Observed, counter in Hobs. simpl in Hobs.
          exists ρ1, π1. split; [apply rt_refl|]. split.
          - split; [exact HI|]. split; [exact Hlin|]. split; [exact Hstamp|].
            split; [unfold Observed, counter; simpl; lia|].
            unfold APure. lia.
          - apply G_intro; auto.
        }

        destruct (Nat.eqb t1 t2) eqn:Hcmp.
        + (* Both reads agree: try to advance the register. *)
          apply Nat.eqb_eq in Hcmp. subst t2.
          singleton_vis_safe
            (I //\\ ALin t (ls_lini newTS) //\\ Stamped t t1
               //\\ Observed t1 //\\ ⌜t1 <= t1⌝)
            (fun b : bool =>
              if b
              then I //\\ ALin t (ls_linr newTS (TSInterval t1 t1))
              else I //\\ ALin t (ls_lini newTS) //\\ Stamped t t1
                     //\\ Observed (S t1));
            [apply cas_op_no_error
            |solve_conj_impl
            |intros [|]; solve_conj_impl
            |solve_conj_stable stableDB
            |intros [|]; solve_conj_stable stableDB
            | |
            |intros [|]].
          {
            intros σ1 ρ1 π1 Hpre σ2 Hstep.
            destruct (step_inv_shape _ _ _ _ Hstep) as [c [-> ->]].
            exists ρ1, π1. split; [apply rt_refl|].
            split; [exact Hpre|]. apply G_intro; auto.
          }
          {
            intros [|] σ1 ρ1 π1 [HI [Hlin [Hstamp [Hobs _]]]] σ2 Hstep.
            - (* [cas] succeeded: this is the response linearization point. *)
              destruct (step_cas_true_shape _ _ _ _ _ Hstep) as [-> ->].
              unfold I, clock, counter in HI. simpl in HI.
              unfold Stamped, pending_of in Hstamp. simpl in Hstamp.
              exists (finish_newTS t t1 ρ1),
                (TMap.add t (ls_linr newTS (TSInterval t1 t1)) π1).
              split.
              { apply rt_step. apply (ps_ret t newTS (TSInterval t1 t1));
                  [|exact Hlin].
                apply (step_newTS_res t ρ1 t1 t1); auto. }
              split.
              + split.
                * unfold I, clock, counter, finish_newTS. simpl. lia.
                * unfold ALin. simpl. apply PositiveMap.gss.
              + apply G_intro; [simpl; lia| |].
                * intros other Hneq. unfold finish_newTS. simpl.
                  rewrite PositiveMap.gro; auto.
                * intros other Hneq. rewrite PositiveMap.gso; auto.
            - (* [cas] failed: someone else advanced past [t1]. *)
              destruct (step_cas_false_shape _ _ _ _ _ Hstep)
                as [c [Hneq [-> ->]]].
              unfold Observed, counter in Hobs. simpl in Hobs.
              exists ρ1, π1. split; [apply rt_refl|]. split.
              + split; [exact HI|]. split; [exact Hlin|]. split; [exact Hstamp|].
                unfold Observed, counter. simpl. lia.
              + apply G_intro; auto.
          }
          * (* success: return the point interval *)
            singleton_ret_safe using stableDB.
          * (* failure: [t3 ← get], then linearize [[t1, t3 - 1]]. *)
            singleton_vis_safe
              (I //\\ ALin t (ls_lini newTS) //\\ Stamped t t1
                 //\\ Observed (S t1))
              (fun t3 => I //\\ ALin t (ls_lini newTS) //\\ Stamped t t1
                           //\\ Observed t3 //\\ ⌜S t1 <= t3⌝)
              using stableDB;
              [apply get_no_error| | |intros t3].
            {
              intros σ1 ρ1 π1 Hpre σ2 Hstep.
              destruct (step_inv_shape _ _ _ _ Hstep) as [c [-> ->]].
              exists ρ1, π1. split; [apply rt_refl|].
              split; [exact Hpre|]. apply G_intro; auto.
            }
            {
              intros t3 σ1 ρ1 π1 [HI [Hlin [Hstamp Hobs]]] σ2 Hstep.
              destruct (step_get_res_shape _ _ _ _ Hstep) as [-> ->].
              unfold Observed, counter in Hobs. simpl in Hobs.
              exists ρ1, π1. split; [apply rt_refl|]. split.
              - split; [exact HI|]. split; [exact Hlin|]. split; [exact Hstamp|].
                split; [unfold Observed, counter; simpl; lia|].
                unfold APure. lia.
              - apply G_intro; auto.
            }
            singleton_linstep
              (I //\\ ALin t (ls_linr newTS (TSInterval t1 (t3 - 1))))
              using stableDB.
            {
              intros σ1 ρ1 π1 [HI [Hlin [Hstamp [Hobs Hle]]]].
              unfold I, clock, counter in HI.
              unfold Stamped, pending_of in Hstamp.
              unfold Observed, counter in Hobs. unfold APure in Hle.
              simpl in HI, Hstamp, Hobs.
              exists (finish_newTS t (t3 - 1) ρ1),
                (TMap.add t (ls_linr newTS (TSInterval t1 (t3 - 1))) π1).
              split.
              { apply rt_step. apply (ps_ret t newTS (TSInterval t1 (t3 - 1)));
                  [|exact Hlin].
                apply (step_newTS_res t ρ1 t1 (t3 - 1)); auto. lia. }
              split.
              - split.
                + unfold I, clock, counter, finish_newTS. simpl. lia.
                + unfold ALin. simpl. apply PositiveMap.gss.
              - apply G_intro; [simpl; lia| |].
                + intros other Hneq. unfold finish_newTS. simpl.
                  rewrite PositiveMap.gro; auto.
                + intros other Hneq. rewrite PositiveMap.gso; auto.
            }
            singleton_ret_safe using stableDB.
        + (* The reads differ, so [t1 < t2]: linearize [[t1, t2 - 1]]. *)
          apply Nat.eqb_neq in Hcmp.
          singleton_linstep
            (I //\\ ALin t (ls_linr newTS (TSInterval t1 (t2 - 1))))
            using stableDB.
          {
            intros σ1 ρ1 π1 [HI [Hlin [Hstamp [Hobs Hle]]]].
            unfold I, clock, counter in HI.
            unfold Stamped, pending_of in Hstamp.
            unfold Observed, counter in Hobs. unfold APure in Hle.
            simpl in HI, Hstamp, Hobs.
            exists (finish_newTS t (t2 - 1) ρ1),
              (TMap.add t (ls_linr newTS (TSInterval t1 (t2 - 1))) π1).
            split.
            { apply rt_step. apply (ps_ret t newTS (TSInterval t1 (t2 - 1)));
                [|exact Hlin].
              apply (step_newTS_res t ρ1 t1 (t2 - 1)); auto. lia. }
            split.
            - split.
              + unfold I, clock, counter, finish_newTS. simpl. lia.
              + unfold ALin. simpl. apply PositiveMap.gss.
            - apply G_intro; [simpl; lia| |].
              + intros other Hneq. unfold finish_newTS. simpl.
                rewrite PositiveMap.gro; auto.
              + intros other Hneq. rewrite PositiveMap.gso; auto.
          }
          singleton_ret_safe using stableDB.
    }
    (* initial singleton *)
    { apply lift_initial. unfold I, clock, counter. reflexivity. }
  Defined.

  Definition MTimestampLinearizable := LISim2LILin MTimestamp.

  Print Assumptions MTimestamp.

End TimestampProof.
