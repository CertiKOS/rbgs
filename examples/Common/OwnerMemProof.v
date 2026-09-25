Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.Classical.
Require Import Coq.Relations.Relation_Operators.

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


(** [OwnerMemSpec.OwnerMem] is linearizable from [OwnerMemSpec.PlainMem]
    with the identity implementation: the owner map is ghost state, so the
    only content of the proof is that the two memories take the same steps
    and raise the same errors.  A concrete error is answered by the same
    abstract error, which discharges the method. *)
Module OwnerMemProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSingle SingletonPossibility.
  Import TPSimulationSet.TPSimulation CompLinLayer.
  Import AtomicLTS OwnerMemSpec PlainMem OwnerMem.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {X : Type}.

    Definition E : layer_interface := @PlainMemLayer.L X.
    Definition F : layer_interface := @OwnerMemLayer.L X.

    Definition owner_mem_impl : ModuleImpl (li_sig E) (li_sig F) :=
      fun m _ => m >= r => Ret r.

    Definition single_state :=
      @SinglePossState.ProofStateSingle _ _ (li_lts E) (li_lts F).
    Definition assertion := @Assertion single_state.
    Definition rg_relation :=
      @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F).

    (** The abstract state is the concrete one plus the owner map. *)
    Definition state_rel (c : State (li_lts E)) (a : State (li_lts F)) : Prop :=
      match c, a with
      | Idle h, Idle om => om_heap om = h
      | Pending h t p, Pending om t' q => t = t' /\ p = q /\ om_heap om = h
      | _, _ => False
      end.

    Definition I : assertion := fun s => state_rel (σ s) (ρ s).

    Definition G (t : tid) : rg_relation := fun s s' =>
      forall t', t <> t' -> TMap.find t' (π s) = TMap.find t' (π s').
    Definition R (t : tid) : rg_relation := fun s s' =>
      TMap.find t (π s) = TMap.find t (π s').

    Lemma I_stable t : Stable (R t) I I.
    Proof. apply Stable_invariant. Qed.

    Lemma ALin_stable t ls : Stable (R t) I (ALin t ls).
    Proof. intros s [[pre [Hlin Hπ]] _]. unfold ALin in *. congruence. Qed.

    Create HintDb stableDB.
    #[local] Hint Resolve I_stable ALin_stable : stableDB.

    Lemma source_valid_rg t : forall s s', R t s s' -> I s' ->
      TMap.find t (π s) = None <-> TMap.find t (π s') = None.
    Proof. intros s s' Hπ _. unfold R in Hπ. rewrite Hπ. tauto. Qed.

    Lemma source_rg_compatible t1 t2 : t1 <> t2 -> forall s s',
      (G t1 s s' \/ (GINV t1 s s' \/ GRET t1 s s') \/ GId s s') ->
      R t2 s s'.
    Proof.
      intros Hneq s s' [HG | [[Hinv | Hret] | Hid]]; unfold R.
      - apply HG. exact Hneq.
      - destruct Hinv as [f [_ [_ [_ Hπ]]]]. rewrite Hπ, TMap.gso; auto.
      - destruct Hret as [f [ret [_ [_ [_ Hπ]]]]]. rewrite Hπ, TMap.gro; auto.
      - unfold GId in Hid. subst. reflexivity.
    Qed.

    (** * Steps of the two memories *)

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

    Ltac crush :=
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

    (** Precondition of an invocation, shared by both memories. *)
    Definition inv_ok (m : Sig.op (EOMem X)) (h : @Heap X) : Prop :=
      match m with
      | omalloc _ => True
      | oread l => h l <> None
      | owrite l _ => h l <> None
      | ocas l _ _ => h l <> None
      end.

    Lemma plain_inv_shape t m c c' :
      Step (li_lts E) {| te_tid := t; te_ev := InvEv m |} c c' ->
      exists h, c = Idle h /\ c' = Pending h t m /\ inv_ok m h.
    Proof.
      intros Hstep. inversion Hstep; subst; crush.
      inversion Hstep0; subst; crush; eexists; repeat split; simpl; auto.
    Qed.

    Lemma owner_inv_step t m (om : OMemState X) :
      inv_ok m (om_heap om) ->
      Step (li_lts F) {| te_tid := t; te_ev := InvEv m |} (Idle om) (Pending om t m).
    Proof.
      intros Hok. apply step_inv. destruct m; simpl in Hok.
      - eapply step_alloc_inv; reflexivity.
      - eapply step_read_inv; [reflexivity|exact Hok].
      - eapply step_write_inv; [reflexivity|exact Hok].
      - eapply step_cas_inv; [reflexivity|exact Hok].
    Qed.

    (** Every concrete response has an abstract counterpart with the same
        heap. *)
    Lemma plain_res_matches t m r (h h' : @Heap X) (om : OMemState X) :
      om_heap om = h ->
      StepPlain {| te_tid := t; te_ev := ResEv m r |} h h' ->
      exists om', om_heap om' = h' /\
        StepOMem {| te_tid := t; te_ev := ResEv m r |} om om'.
    Proof.
      intros Hh Hstep. subst h. inversion Hstep; subst; crush.
      - match goal with |- context [heap_update ?l ?v _] => exists (om_alloc t l v om) end.
        split; [reflexivity|]. eapply step_alloc_res; [reflexivity|assumption].
      - exists om. split; [reflexivity|]. eapply step_read_res; [reflexivity|assumption].
      - match goal with |- context [heap_update ?l ?v _] => exists (om_write l v om) end.
        split; [reflexivity|]. eapply step_write_res; [reflexivity|assumption].
      - match goal with |- context [heap_update ?l ?v _] => exists (om_write l v om) end.
        split; [reflexivity|]. eapply step_cas_res_succ; [reflexivity|assumption].
      - exists om. split; [reflexivity|].
        eapply step_cas_res_fail; [reflexivity|eassumption|assumption].
    Qed.

    Lemma plain_res_shape t m r c c' :
      Step (li_lts E) {| te_tid := t; te_ev := ResEv m r |} c c' ->
      exists h h', c = Pending h t m /\ c' = Idle h' /\
        StepPlain {| te_tid := t; te_ev := ResEv m r |} h h'.
    Proof.
      intros Hstep. inversion Hstep; subst; crush. eauto.
    Qed.

    (** * Errors *)

    Lemma concrete_error_refines t m c a :
      state_rel c a ->
      Error (li_lts E) {| te_tid := t; te_ev := InvEv m |} c ->
      Error (li_lts F) {| te_tid := t; te_ev := InvEv m |} a.
    Proof.
      unfold state_rel. destruct c as [h | h tp p], a as [om | om tq q];
        simpl; try contradiction.
      - intros Hh Herr. subst h. inversion Herr; subst; crush.
        + eapply error_read_undefined; eauto.
        + eapply error_write_undefined; eauto.
        + eapply error_cas_undefined; eauto.
      - intros [Ht [Hp Hh]] Herr. subst tq q h. inversion Herr; subst; crush.
        eapply error_write_racy; eauto.
    Qed.

    Lemma no_error_or_abstract_error t m :
      ⊨ I //\\ ALin t (ls_inv m) ==>>
        (I //\\ ALin t (ls_inv m) //\\ ANoError {| te_tid := t; te_ev := InvEv m |})
        \\// APError.
    Proof.
      intros s [HI Hlin].
      destruct (classic (Error (li_lts E) {| te_tid := t; te_ev := InvEv m |} (σ s)))
        as [Herr | Hno].
      - right. apply rt_step. eapply (ps_error t m); [|exact Hlin].
        apply concrete_error_refines with (c := σ s); assumption.
      - left. split; [exact HI|]. split; [exact Hlin|exact Hno].
    Qed.

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

    (** * Possibility updates *)

    Lemma inv_update t m :
      PUpdate (G t) {| te_tid := t; te_ev := InvEv m |}
        (I //\\ ALin t (ls_inv m) //\\ ANoError {| te_tid := t; te_ev := InvEv m |})
        (I //\\ ALin t (ls_lini m)).
    Proof.
      intros c a p [HI [Hlin _]] c' Hstep.
      destruct (plain_inv_shape _ _ _ _ Hstep) as [h [-> [-> Hok]]].
      unfold I, state_rel in HI. simpl in HI.
      destruct a as [om | om tq q]; [|contradiction]. subst h.
      exists (Pending om t m), (TMap.add t (ls_lini m) p). split.
      { apply rt_step. apply (ps_inv t m); [|exact Hlin].
        apply owner_inv_step. exact Hok. }
      split.
      - split; [unfold I, state_rel; simpl; auto|].
        unfold ALin. simpl. apply TMap.gss.
      - intros t' Hne. simpl. rewrite TMap.gso; auto.
    Qed.

    Lemma res_update t m r :
      PUpdate (G t) {| te_tid := t; te_ev := ResEv m r |}
        (I //\\ ALin t (ls_lini m))
        (I //\\ ALin t (ls_linr m r)).
    Proof.
      intros c a p [HI Hlin] c' Hstep.
      destruct (plain_res_shape _ _ _ _ _ Hstep) as [h [h' [-> [-> Hres]]]].
      unfold I, state_rel in HI. simpl in HI.
      destruct a as [om | om tq q]; [contradiction|].
      destruct HI as [<- [<- Hh]].
      destruct (plain_res_matches _ _ _ _ _ _ Hh Hres) as [om' [Hh' Hstep']].
      exists (Idle om'), (TMap.add t (ls_linr m r) p). split.
      { apply rt_step. apply (ps_ret t m r); [|exact Hlin].
        apply step_res. exact Hstep'. }
      split.
      - split; [unfold I, state_rel; simpl; exact Hh'|].
        unfold ALin. simpl. apply TMap.gss.
      - intros t' Hne. simpl. rewrite TMap.gso; auto.
    Qed.

    (** * The layer *)

    Program Definition MOwnerMem : layer_implementation_simulation E F :=
    {| li_impl := owner_mem_impl |}.
    Next Obligation.
      eapply SetLogic.soundness
        with (R := fun t => lift_relation (R t))
             (G := fun t => lift_relation (G t))
             (I := lift_assert I).
      { intros t. eapply lift_valid_rgi. apply source_valid_rg. }
      {
        intros t1 t2 Hneq s s' Hrel.
        eapply lift_parallel_compat; [exact Hneq| |exact Hrel].
        apply source_rg_compatible; exact Hneq.
      }
      {
        intros t m.
        exists (lift_assert (I //\\ ALin t (ls_inv m))).
        exists (fun r => lift_assert (I //\\ ALin t (ls_linr m r))).
        constructor.
        - intros s Hcompose.
          eapply (lift_ginv_compose t m I (I //\\ ALin t (ls_inv m)));
            [|exact Hcompose].
          intros out [pre [HI [Hσ [Hρ [Hnone Hπ]]]]].
          destruct pre as [σp ρp πp], out as [σo ρo πo]. simpl in *. subst.
          split; [exact HI|]. unfold ALin. simpl. apply TMap.gss.
        - intros s Hlift. eapply lift_impl; [|exact Hlift].
          apply ConjLeftImpl. apply ImplRefl.
        - apply lift_stable. solve_conj_stable stableDB.
        - intros r s Hcompose.
          eapply (lift_gret_compose t m r (I //\\ ALin t (ls_linr m r)) I);
            [|exact Hcompose].
          intros out [pre [[HI _] [Hσ [Hρ _]]]].
          destruct pre as [σp ρp πp], out as [σo ρo πo]. simpl in *. subst.
          exact HI.
        - intros r σ0 Δ0 Hpost ρ0 π0 Hposs.
          eapply (lift_post_lin (I //\\ ALin t (ls_linr m r)) t (ls_linr m r));
            [|exact Hpost|exact Hposs].
          intros x [_ Hlin]. exact Hlin.
        - simpl. unfold owner_mem_impl.
          eapply SetLogic.provable_perror.
          { apply lift_perror. apply no_error_or_abstract_error. }
          eapply singleton_provable_vis_safe with
            (P' := I //\\ ALin t (ls_lini m))
            (Q' := fun r => I //\\ ALin t (ls_linr m r)).
          + intros s [_ [_ H]]. exact H.
          + intros s [HI _]. exact HI.
          + intros r s [HI _]. exact HI.
          + solve_conj_stable stableDB.
          + intros r. solve_conj_stable stableDB.
          + apply inv_update.
          + intros r. apply res_update.
          + intros r. singleton_ret_safe;
              [apply ImplRefl|intros s [HI _]; exact HI|solve_conj_stable stableDB].
      }
      { apply lift_initial. unfold I, state_rel. reflexivity. }
    Defined.

    Definition MOwnerMemLinearizable := LISim2LILin MOwnerMem.
  End Proof.

  Print Assumptions MOwnerMem.
End OwnerMemProof.
