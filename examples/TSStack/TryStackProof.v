Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relation_Operators.
Require Import Lia.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import RGILogicSet.
Require Import CompLinLayer.

Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.TryStackAuxSpec.
Require Import examples.TSStack.TryStackAuxGhost.
Require Import examples.TSStack.ListPoolProof.
Require Import examples.TSStack.TryStackAuxProof.
Require Import examples.TSStack.TryStackSpec.
Require Import examples.TSStack.TryStack.
Require Import examples.TSStack.TryStackLinearization.
Require Import examples.TSStack.TryStackTrace.


(** Correctness proof of the TryStack layer over TryStackAux.

    The invariant states that the abstract configuration is exactly the
    set of configurations realisable by the consistent histories of the
    ghost-timed concrete state ([TryStackLinearization.Real]).  Every
    concrete event is simulated by the replay lemmas of that file.  The
    trace theorem [real_nonempty] (every well-formed ghost state admits a
    consistent history) is proved in [TryStackTrace]. *)
Module TryStackProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSet.
  Import TPSimulationSet.TPSimulation CompLinLayer.
  Import ListPoolSpec TryStackAuxSpec TryStackAuxGhost TryStackSpec TryStackImpl.
  Import TryStackLinearization.
  Import (coercions, canonicals, notations) Sig.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {A : Type} (D : ThreadDomain.t).

    Definition E : layer_interface := @TryStackImpl.E A D.
    Definition F : layer_interface := @TryStackImpl.F A D.

    Definition set_state :=
      @SetPossState.ProofStateSet _ _ (li_lts E) (li_lts F).
    Definition assertion := @Logics.Assertion set_state.
    Definition rg_relation :=
      @AssertionsSet.A.RGRelation _ _ (li_lts E) (li_lts F).

    (** The trace theorem. *)
    Lemma real_nonempty :
      forall s : @TryStackAuxState A, tsa_ghost_wf s -> exists h, consistent s h.
    Proof. intros s Hwf. exact (TryStackTrace.trace_theorem s Hwf). Qed.

    Definition J (c : @TryStackAuxControl A) (phi : @PhaseMap A)
        (Delta : @AbstractConfig _ (li_lts F)) : Prop :=
      control_wf c /\ phase_consistent c phi /\
      (forall rho pi, Delta rho pi -> Real c phi rho pi) /\
      (forall h, consistent (payload c) h ->
        exists rho pi, Delta rho pi /\
          represents_at (payload c) phi h (final_cut (payload c)) None rho pi).

    Definition I : assertion :=
      fun w => exists phi, J (SetPossState.σ w) phi (SetPossState.Δ w).

    (** * Tokens determined by phases *)

    Definition not_atomic_for (c : @TryStackAuxControl A) (t : tid) : Prop :=
      forall s op, c <> TSAAtomicPending s t op.

    Definition token_shape (c : @TryStackAuxControl A) (t : tid)
        (ph : option (@Phase A)) (tok : option (@LinState ETryStack)) : Prop :=
      match ph with
      | None => tok = None
      | Some (PhPushInvoked v) =>
          tok = Some (ls_inv (ts_push v)) /\
          TMap.find t (tsa_pending_pushes (payload c)) = None
      | Some (PhPushPending v loc) =>
          (tok = Some (ls_inv (ts_push v)) \/ tok = Some (ls_lini (ts_push v))) /\
          TMap.find t (tsa_pending_pushes (payload c)) = Some loc
      | Some (PhPushDone v) =>
          tok = Some (ls_linr (ts_push v) tt) /\
          TMap.find t (tsa_pending_pushes (payload c)) = None
      | Some PhPopInvoked =>
          tok = Some (ls_inv ts_trypop) /\
          TMap.find t (tsa_snapshots (payload c)) = None /\ not_atomic_for c t
      | Some PhPopSnapshot =>
          (tok = Some (ls_inv ts_trypop) \/
           exists v o l, tok = Some (ls_linr ts_trypop (TSuccNode v o l))) /\
          (exists N, TMap.find t (tsa_snapshots (payload c)) = Some N) /\
          not_atomic_for c t
      | Some PhPopEmptyPending =>
          tok = Some (ls_inv ts_trypop) /\
          exists s op, c = TSAAtomicPending s t op
      | Some (PhPopDone r) =>
          tok = Some (ls_linr ts_trypop r) /\
          TMap.find t (tsa_snapshots (payload c)) = None /\ not_atomic_for c t
      end.

    Lemma J_token_shape c phi Delta rho pi t :
      J c phi Delta -> Delta rho pi ->
      token_shape c t (phi t) (TMap.find t pi).
    Proof.
      intros (Hwf & Hpc & Hreal & _) Hposs.
      destruct (Hreal _ _ Hposs) as (h & Hc & Hrep).
      destruct Hrep as (st & _ & _ & _ & _ & _ & _ & Htok).
      specialize (Htok t). unfold token_at in Htok.
      destruct Hpc as (Hpc1 & Hpc2 & Hpc3 & Hpc4 & Hpc5 & Hpc6 & Hpc7).
      assert (Hwf' : tsa_ghost_wf (payload c)) by (destruct c; exact Hwf).
      unfold token_shape.
      destruct (phi t) as [ph|] eqn:Hph; [|exact Htok].
      destruct ph as [v|v loc|v| | | |r].
      - split; [exact Htok|].
        destruct (TMap.find t (tsa_pending_pushes (payload c))) as [loc|] eqn:Hf; [|reflexivity].
        exfalso. apply Hpc1 in Hf. destruct Hf as [v' Hf]. congruence.
      - split.
        + destruct Htok as [[_ H]|[_ H]]; auto.
        + apply Hpc1. eauto.
      - split.
        + destruct Htok as (loc0 & Hlat0 & Hcase).
          destruct (Hpc5 t v Hph) as (loc & r & Hr & Hv & Hlat).
          pose proof (latest_node_unique _ _ _ _ Hwf' Hlat0 Hlat) as ->.
          assert (Hrb : ret_before (payload c) (final_cut (payload c)) (pair t loc)).
          { exists r. split; [exact Hr|]. apply ret_pos_lt_gap. eapply wf_ret_now; eauto. }
          destruct Hcase as [[_ H]|[[Hn _]|[Hn _]]]; [exact H|contradiction|].
          exfalso. apply Hn. destruct (c_ret_forces_inv _ _ Hc _ _ Hr) as [p Hp].
          exists p. split; [exact Hp|]. destruct Hrb as (r' & Hr' & Hlt).
          eapply pos_lt_trans; [|exact Hlt]. eapply inv_before_ret; eauto. exists r'. auto.
        + destruct (TMap.find t (tsa_pending_pushes (payload c))) as [loc|] eqn:Hf; [|reflexivity].
          exfalso. apply Hpc1 in Hf. destruct Hf as [v' Hf]. congruence.
      - split; [exact Htok|]. split.
        + destruct (TMap.find t (tsa_snapshots (payload c))) as [N|] eqn:Hf; [|reflexivity].
          exfalso. assert (H : phi t = Some PhPopSnapshot) by (apply Hpc2; eauto). congruence.
        + intros s op Heq. assert (H : phi t = Some PhPopEmptyPending).
          { apply Hpc3. exists op. rewrite Heq. reflexivity. }
          congruence.
      - split.
        + destruct Htok as [H|[_ H]].
          * destruct H as (n & v & _ & _ & _ & H). right. eauto.
          * left. exact H.
        + split; [apply Hpc2; exact Hph|].
          intros s op Heq. assert (H : phi t = Some PhPopEmptyPending).
          { apply Hpc3. exists op. rewrite Heq. reflexivity. }
          congruence.
      - split; [exact Htok|]. destruct (proj1 (Hpc3 t) Hph) as [op Hat].
        exists (payload c), op. exact Hat.
      - split.
        + destruct r as [v o l| |].
          * destruct Htok as [[_ H]|[Hn _]]; [exact H|]. exfalso. apply Hn.
            destruct (Hpc6 t v o l Hph) as (_ & st0 & rt & Hrem).
            destruct (c_removal_popped _ _ Hc _ _ _ _ Hrem) as [p Hp].
            destruct (c_pop_placed _ _ Hc _ _ _ Hp) as (_ & Hnow & _).
            exists p. split; [exact Hp|]. apply final_cut_lt. exact Hnow.
          * destruct Htok as [[H _]|[_ H]]; [discriminate|exact H].
          * destruct Htok as [[H _]|[_ H]]; [discriminate|exact H].
        + split.
          * destruct (TMap.find t (tsa_snapshots (payload c))) as [N|] eqn:Hf; [|reflexivity].
            exfalso. assert (H : phi t = Some PhPopSnapshot) by (apply Hpc2; eauto). congruence.
          * intros s op Heq. assert (H : phi t = Some PhPopEmptyPending).
            { apply Hpc3. exists op. rewrite Heq. reflexivity. }
            congruence.
    Qed.

    Lemma ls_linr_inj (f : Sig.op (@ETryStack A)) (r1 r2 : Sig.ar f) :
      @ls_linr (@ETryStack A) f r1 = ls_linr f r2 -> r1 = r2.
    Proof. intros H. dependent destruction H. reflexivity. Qed.

    Lemma ls_linr_op_inj (f1 f2 : Sig.op (@ETryStack A)) (r1 : Sig.ar f1) (r2 : Sig.ar f2) :
      @ls_linr (@ETryStack A) f1 r1 = ls_linr f2 r2 -> f1 = f2.
    Proof. intros H. inversion H. reflexivity. Qed.

    Ltac shape_crush :=
      repeat match goal with
      | H : _ /\ _ |- _ => destruct H
      | H : exists _, _ |- _ => destruct H
      | H : _ \/ _ |- _ => destruct H
      end;
      try congruence;
      try match goal with
      | H1 : ?tok = Some (ls_linr _ _), H2 : ?tok = Some (ls_linr _ _) |- _ =>
          rewrite H1 in H2; inversion H2 as [Hx];
          apply ls_linr_op_inj in Hx; discriminate
      end;
      try match goal with
      | H1 : not_atomic_for ?c ?t, H2 : ?c = TSAAtomicPending _ ?t _ |- _ =>
          exfalso; eapply H1; exact H2
      end.

    (** Two phase maps consistent with the same concrete state and with
        configurations sharing a token agree on that thread. *)
    Lemma phase_from_token c phi Delta rho pi phi' Delta' rho' pi' t :
      J c phi Delta -> Delta rho pi ->
      J c phi' Delta' -> Delta' rho' pi' ->
      TMap.find t pi = TMap.find t pi' ->
      phi t = phi' t.
    Proof.
      intros HJ Hposs HJ' Hposs' Heq.
      pose proof (J_token_shape _ _ _ _ _ t HJ Hposs) as S1.
      pose proof (J_token_shape _ _ _ _ _ t HJ' Hposs') as S2.
      rewrite Heq in S1. unfold token_shape in S1, S2.
      destruct (phi t) as [ph|]; destruct (phi' t) as [ph'|];
        [|destruct ph|destruct ph'|reflexivity];
        try (destruct ph); try (destruct ph'); shape_crush.
      (* PopDone vs PopDone with equal result tokens *)
      match goal with
      | |- Some (PhPopDone ?r1) = Some (PhPopDone ?r2) =>
          assert (Hx : @ls_linr (@ETryStack A) ts_trypop r1 = ls_linr ts_trypop r2)
            by congruence;
          apply ls_linr_inj in Hx; rewrite Hx; reflexivity
      end.
    Qed.

    Lemma phase_unique c phi phi' Delta :
      J c phi Delta -> J c phi' Delta -> forall t, phi t = phi' t.
    Proof.
      intros HJ HJ' t. destruct (ac_nonempty Delta) as (rho & pi & Hposs).
      eapply phase_from_token; eauto.
    Qed.

    (** * Rely and guarantee *)

    Definition G (actor : tid) : rg_relation :=
      fun w w' =>
        I w /\ I w' /\
        forall phi phi',
          J (SetPossState.σ w) phi (SetPossState.Δ w) ->
          J (SetPossState.σ w') phi' (SetPossState.Δ w') ->
          forall t, t <> actor -> phi' t = phi t.

    Definition R (observer : tid) : rg_relation :=
      fun w w' =>
        I w /\
        forall phi phi',
          J (SetPossState.σ w) phi (SetPossState.Δ w) ->
          J (SetPossState.σ w') phi' (SetPossState.Δ w') ->
          phi' observer = phi observer.

    Lemma token_none_iff_phase_none c phi Delta rho pi t :
      J c phi Delta -> Delta rho pi ->
      (TMap.find t pi = None <-> phi t = None).
    Proof.
      intros HJ Hposs.
      pose proof (J_token_shape _ _ _ _ _ t HJ Hposs) as S. unfold token_shape in S.
      destruct (phi t) as [ph|]; [|tauto].
      split; [|discriminate]. intro Hn. exfalso.
      destruct ph; shape_crush.
    Qed.

    Lemma valid_rg observer :
      RGISimulationSet.RGISimulation.ValidRGI
        (R observer) (G observer) I observer.
    Proof.
      constructor. intros w w' (HI & Hphase) HI'.
      destruct HI as [phi HJ]. destruct HI' as [phi' HJ'].
      pose proof (Hphase _ _ HJ HJ') as Heq.
      split.
      - intros Hall rho' pi' Hposs'.
        rewrite (token_none_iff_phase_none _ _ _ _ _ observer HJ' Hposs'). rewrite Heq.
        destruct (ac_nonempty (SetPossState.Δ w)) as (rho & pi & Hposs).
        rewrite <- (token_none_iff_phase_none _ _ _ _ _ observer HJ Hposs).
        exact (Hall _ _ Hposs).
      - intros Hall rho pi Hposs.
        rewrite (token_none_iff_phase_none _ _ _ _ _ observer HJ Hposs). rewrite <- Heq.
        destruct (ac_nonempty (SetPossState.Δ w')) as (rho' & pi' & Hposs').
        rewrite <- (token_none_iff_phase_none _ _ _ _ _ observer HJ' Hposs').
        exact (Hall _ _ Hposs').
    Qed.

    (** Phase maps after the framework's invocation / return updates. *)

    Definition phi_remove (phi : @PhaseMap A) (t : tid) : @PhaseMap A :=
      fun t' => if Pos.eq_dec t' t then None else phi t'.

    Lemma token_at_upd_other (s : @TryStackAuxState A) (phi : @PhaseMap A) h P pd t ph t' tok :
      t' <> t ->
      token_at s phi h P pd t' tok -> token_at s (upd phi t ph) h P pd t' tok.
    Proof. intros Hneq. unfold token_at. rewrite upd_neq by exact Hneq. tauto. Qed.

    Lemma token_at_remove_other (s : @TryStackAuxState A) (phi : @PhaseMap A) h P pd t t' tok :
      t' <> t ->
      token_at s phi h P pd t' tok -> token_at s (phi_remove phi t) h P pd t' tok.
    Proof.
      intros Hneq. unfold token_at, phi_remove.
      destruct (Pos.eq_dec t' t); [congruence|tauto].
    Qed.

    Lemma represents_at_upd_token (s : @TryStackAuxState A) (phi : @PhaseMap A) h P pd t ph rho pi tok :
      represents_at s phi h P pd rho pi ->
      token_at s (upd phi t ph) h P pd t tok ->
      represents_at s (upd phi t ph) h P pd rho
        (match tok with Some ls => TMap.add t ls pi | None => TMap.remove t pi end).
    Proof.
      intros (st & -> & HV & HVn & HE & HP & HG & Htok) Ht.
      exists st. split; [reflexivity|].
      refine (conj HV (conj HVn (conj HE (conj HP (conj HG _))))).
      intros t'. destruct (Pos.eq_dec t' t) as [->|Hneq].
      - destruct tok as [ls|].
        + rewrite TMap.gss. exact Ht.
        + rewrite TMap.grs. exact Ht.
      - destruct tok as [ls|].
        + rewrite TMap.gso by exact Hneq. apply token_at_upd_other; auto.
        + rewrite TMap.gro by exact Hneq. apply token_at_upd_other; auto.
    Qed.

    Definition phase_of_inv (op : Sig.op (li_sig F)) : @Phase A :=
      match op with
      | ts_push v => PhPushInvoked v
      | ts_trypop => PhPopInvoked
      end.

    Definition no_footprint (ph : option (@Phase A)) : Prop :=
      match ph with
      | None | Some (PhPushInvoked _) | Some PhPopInvoked
      | Some (PhPushDone _) | Some (PhPopDone _) => True
      | _ => False
      end.

    Definition no_clause (ph : option (@Phase A)) : Prop :=
      match ph with
      | None | Some (PhPushInvoked _) | Some PhPopInvoked => True
      | _ => False
      end.

    Lemma phase_consistent_update c phi phi' :
      phase_consistent c phi ->
      (forall t, phi' t = phi t \/ (no_footprint (phi t) /\ no_clause (phi' t))) ->
      phase_consistent c phi'.
    Proof.
      intros (Hpc1 & Hpc2 & Hpc3 & Hpc4 & Hpc5 & Hpc6 & Hpc7) Hch.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      - intros t loc. destruct (Hch t) as [Heq|[Hfp Hcl]].
        + rewrite Heq. apply Hpc1.
        + split.
          * intro Hf. exfalso. apply Hpc1 in Hf. destruct Hf as [v Hf].
            rewrite Hf in Hfp. exact Hfp.
          * intros [v Hf]. rewrite Hf in Hcl. contradiction.
      - intros t. destruct (Hch t) as [Heq|[Hfp Hcl]].
        + rewrite Heq. apply Hpc2.
        + split.
          * intro HN. exfalso. apply Hpc2 in HN. rewrite HN in Hfp. exact Hfp.
          * intro Hf. rewrite Hf in Hcl. contradiction.
      - intros t. destruct (Hch t) as [Heq|[Hfp Hcl]].
        + rewrite Heq. apply Hpc3.
        + split.
          * intro Hf. rewrite Hf in Hcl. contradiction.
          * intro Hat. exfalso. apply Hpc3 in Hat. rewrite Hat in Hfp. exact Hfp.
      - intros t v loc Hf. destruct (Hch t) as [Heq|[Hfp Hcl]].
        + rewrite Heq in Hf. eapply Hpc4. exact Hf.
        + rewrite Hf in Hcl. contradiction.
      - intros t v Hf. destruct (Hch t) as [Heq|[Hfp Hcl]].
        + rewrite Heq in Hf. eapply Hpc5. exact Hf.
        + rewrite Hf in Hcl. contradiction.
      - intros t v owner loc Hf. destruct (Hch t) as [Heq|[Hfp Hcl]].
        + rewrite Heq in Hf. eapply Hpc6. exact Hf.
        + rewrite Hf in Hcl. contradiction.
      - intros t Hf. destruct (Hch t) as [Heq|[Hfp Hcl]].
        + rewrite Heq in Hf. eapply Hpc7. exact Hf.
        + rewrite Hf in Hcl. contradiction.
    Qed.

    Lemma J_ac_inv c phi Delta t op :
      J c phi Delta ->
      (forall rho pi, Delta rho pi -> TMap.find t pi = None) ->
      J c (upd phi t (phase_of_inv op)) (ac_inv Delta t op).
    Proof.
      intros HJ Hnone. pose proof HJ as (Hwf & Hpc & Hreal & Hcomplete).
      assert (Hphi_none : phi t = None).
      { destruct (ac_nonempty Delta) as (rho & pi & Hposs).
        apply (token_none_iff_phase_none _ _ _ _ _ t HJ Hposs). exact (Hnone _ _ Hposs). }
      split; [exact Hwf|]. split.
      - eapply phase_consistent_update; [exact Hpc|].
        intro t'. destruct (Pos.eq_dec t' t) as [->|Hneq].
        + right. rewrite upd_eq, Hphi_none. split; [constructor|]. destruct op; constructor.
        + left. apply upd_neq. exact Hneq.
      - split.
        + intros rho pi Hposs. inversion Hposs; subst.
          destruct (Hreal _ _ Hposs0) as (h & Hc & Hrep).
          exists h. split; [exact Hc|].
          pose proof (represents_at_upd_token (payload c) phi h (final_cut (payload c)) None t
            (phase_of_inv op) rho π (Some (ls_inv op)) Hrep) as Hrep'.
          apply Hrep'. unfold token_at. rewrite upd_eq. destruct op; reflexivity.
        + intros h Hc. destruct (Hcomplete h Hc) as (rho & pi & Hposs & Hrep).
          exists rho, (TMap.add t (ls_inv op) pi). split; [constructor; exact Hposs|].
          pose proof (represents_at_upd_token (payload c) phi h (final_cut (payload c)) None t
            (phase_of_inv op) rho pi (Some (ls_inv op)) Hrep) as Hrep'.
          apply Hrep'. unfold token_at. rewrite upd_eq. destruct op; reflexivity.
    Qed.

    Lemma represents_at_remove_token (s : @TryStackAuxState A) (phi : @PhaseMap A) h P pd t rho pi :
      represents_at s phi h P pd rho pi ->
      represents_at s (phi_remove phi t) h P pd rho (TMap.remove t pi).
    Proof.
      intros (st & -> & HV & HVn & HE & HP & HG & Htok).
      exists st. split; [reflexivity|].
      refine (conj HV (conj HVn (conj HE (conj HP (conj HG _))))).
      intros t'. destruct (Pos.eq_dec t' t) as [->|Hneq].
      - rewrite TMap.grs. unfold token_at, phi_remove.
        destruct (Pos.eq_dec t t); [reflexivity|congruence].
      - rewrite TMap.gro by exact Hneq. apply token_at_remove_other; auto.
    Qed.

    Lemma J_ac_res c phi Delta t :
      J c phi Delta -> no_footprint (phi t) ->
      J c (phi_remove phi t) (ac_res Delta t).
    Proof.
      intros HJ Hfp. pose proof HJ as (Hwf & Hpc & Hreal & Hcomplete).
      split; [exact Hwf|]. split.
      - eapply phase_consistent_update; [exact Hpc|].
        intro t'. unfold phi_remove. destruct (Pos.eq_dec t' t) as [->|Hneq].
        + right. split; [exact Hfp|constructor].
        + left. reflexivity.
      - split.
        + intros rho pi Hposs. inversion Hposs; subst.
          destruct (Hreal _ _ Hposs0) as (h & Hc & Hrep).
          exists h. split; [exact Hc|]. apply represents_at_remove_token. exact Hrep.
        + intros h Hc. destruct (Hcomplete h Hc) as (rho & pi & Hposs & Hrep).
          exists rho, (TMap.remove t pi). split; [constructor; exact Hposs|].
          apply represents_at_remove_token. exact Hrep.
    Qed.

    Lemma parallel_compatible actor observer :
      actor <> observer -> forall w w',
      (G actor w w' \/
       (AssertionsSet.GINV actor w w' \/
        AssertionsSet.GRET actor w w') \/
       AssertionsSet.A.GId w w') /\ I w ->
      R observer w w'.
    Proof.
      intros Hneq w w' [Hstep HI].
      destruct Hstep as [HG | [[Hinv|Hret]|Hid]].
      - destruct HG as (HIw & HIw' & Hph). split; [exact HIw|].
        intros phi phi' HJ HJ'. apply Hph; auto.
      - destruct Hinv as [op [Hsigma [Hnone Heq]]].
        split; [exact HI|]. intros phi phi' HJ HJ'.
        destruct (ac_nonempty (SetPossState.Δ w)) as (rho & pi & Hposs).
        assert (Hposs' : SetPossState.Δ w' rho (TMap.add actor (ls_inv op) pi)).
        { apply (proj2 (Heq _ _)). constructor. exact Hposs. }
        rewrite <- Hsigma in HJ'.
        symmetry. eapply phase_from_token; [exact HJ|exact Hposs|exact HJ'|exact Hposs'|].
        rewrite TMap.gso by congruence. reflexivity.
      - destruct Hret as [op [ret [Hsigma [Hlinr Heq]]]].
        split; [exact HI|]. intros phi phi' HJ HJ'.
        destruct (ac_nonempty (SetPossState.Δ w)) as (rho & pi & Hposs).
        assert (Hposs' : SetPossState.Δ w' rho (TMap.remove actor pi)).
        { apply (proj2 (Heq _ _)). constructor. exact Hposs. }
        rewrite <- Hsigma in HJ'.
        symmetry. eapply phase_from_token; [exact HJ|exact Hposs|exact HJ'|exact Hposs'|].
        rewrite TMap.gro by congruence. reflexivity.
      - unfold AssertionsSet.A.GId in Hid. subst w'.
        split; [exact HI|].
        intros phi phi' HJ HJ'. symmetry. apply (phase_unique _ _ _ _ HJ HJ').
    Qed.

    (** * The new configuration after a concrete event *)

    Lemma wf_payload (c : @TryStackAuxControl A) : control_wf c -> tsa_ghost_wf (payload c).
    Proof. destruct c; auto. Qed.

    Notation psteps := (@poss_steps (@ETryStack A) (li_lts F)).
    Notation Ok rho pi := (@PossOk (@ETryStack A) (li_lts F) rho pi).

    Lemma real_step_generic (c c' : @TryStackAuxControl A) phi phi'
        (Delta : @AbstractConfig _ (li_lts F)) :
      J c phi Delta -> control_wf c' -> phase_consistent c' phi' ->
      (forall h', consistent (payload c') h' ->
        consistent (payload c) (restrict h' (final_cut (payload c))) /\
        forall rho pi,
          represents_at (payload c) phi (restrict h' (final_cut (payload c)))
            (final_cut (payload c)) None rho pi ->
          exists rho' pi',
            psteps (Ok rho pi) (Ok rho' pi') /\
            represents_at (payload c') phi' h' (final_cut (payload c')) None rho' pi') ->
      exists Delta', ac_subset Delta' (ac_steps Delta) /\ J c' phi' Delta'.
    Proof.
      intros HJ Hwf' Hpc' Hev. pose proof HJ as (Hwf & Hpc & Hreal & Hcomplete).
      assert (Hbuild : forall h', consistent (payload c') h' ->
        exists rho' pi', ac_steps Delta rho' pi' /\
          represents_at (payload c') phi' h' (final_cut (payload c')) None rho' pi').
      { intros h' Hc'. destruct (Hev h' Hc') as [Hres Hrep].
        destruct (Hcomplete _ Hres) as (rho & pi & Hposs & Hrepr).
        destruct (Hrep _ _ Hrepr) as (rho' & pi' & Hsteps & Hrep').
        exists rho', pi'. split; [|exact Hrep']. econstructor; eauto. }
      assert (Hne : exists rho pi, real_step_prop D Delta c' phi' rho pi).
      { destruct (real_nonempty _ (wf_payload _ Hwf')) as [h' Hc'].
        destruct (Hbuild h' Hc') as (rho' & pi' & Hsteps & Hrep').
        exists rho', pi'. split; [exact Hsteps|]. exists h'. auto. }
      exists (ac_real_step D Delta c' phi' Hne).
      split; [apply ac_real_step_subset_steps|].
      split; [exact Hwf'|]. split; [exact Hpc'|]. split.
      - intros rho pi Hposs. eapply ac_real_step_real. exact Hposs.
      - intros h' Hc'. destruct (Hbuild h' Hc') as (rho' & pi' & Hsteps & Hrep').
        exists rho', pi'. split; [|exact Hrep'].
        apply ac_real_step_intro; [exact Hsteps|]. exists h'. auto.
    Qed.

    (** * Actor-local assertions *)

    Definition PhaseIs (actor : tid) (Pph : option (@Phase A) -> Prop) : assertion :=
      fun w => I w /\
        forall phi, J (SetPossState.σ w) phi (SetPossState.Δ w) -> Pph (phi actor).

    Lemma phase_is_entails_I actor Pph : ⊨ PhaseIs actor Pph ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma phase_is_stable actor Pph :
      AssertionsSet.A.Stable (R actor) I (PhaseIs actor Pph).
    Proof.
      unfold AssertionsSet.A.Stable. intros w' [[w [[HI Hph] HR]] HI'].
      split; [exact HI'|]. intros phi' HJ'.
      destruct HR as [_ Hphase]. destruct HI as [phi HJ].
      rewrite (Hphase _ _ HJ HJ'). apply Hph. exact HJ.
    Qed.

    (** The post-condition of a method: the thread is in its done phase. *)
    Definition done_phase (op : Sig.op (li_sig F)) : Sig.ar op -> @Phase A :=
      match op as o return Sig.ar o -> Phase with
      | ts_push v => fun _ => PhPushDone v
      | ts_trypop => fun r => PhPopDone r
      end.

    Definition Done (actor : tid) (op : Sig.op (li_sig F)) (ret : Sig.ar op) : assertion :=
      PhaseIs actor (fun ph => ph = Some (done_phase op ret)).

    Lemma done_has_return_token actor op ret :
      forall w, Done actor op ret w ->
      forall rho pi, SetPossState.Δ w rho pi ->
        TMap.find actor pi = Some (ls_linr op ret).
    Proof.
      intros w [HI Hph] rho pi Hposs.
      destruct HI as [phi HJ]. specialize (Hph _ HJ).
      pose proof (J_token_shape _ _ _ _ _ actor HJ Hposs) as S.
      rewrite Hph in S. unfold token_shape in S. destruct op; simpl in *.
      - destruct ret. tauto.
      - tauto.
    Qed.

    Lemma ginv_exposes_phase actor op :
      forall w, AssertionsSet.A.ComposeA I (AssertionsSet.Ginv actor op) w ->
      PhaseIs actor (fun ph => ph = Some (phase_of_inv op)) w.
    Proof.
      intros w [w0 [[phi HJ] Hginv]].
      destruct Hginv as [Hsigma [Hnone Heq]].
      assert (Hext : SetPossState.Δ w = ac_inv (SetPossState.Δ w0) actor op).
      { apply AbstractConfig_ext. exact Heq. }
      assert (HJ' : J (SetPossState.σ w) (upd phi actor (phase_of_inv op)) (SetPossState.Δ w)).
      { rewrite <- Hsigma, Hext. apply J_ac_inv; auto. }
      split; [eexists; exact HJ'|]. intros phi0 HJ0.
      rewrite (phase_unique _ _ _ _ HJ0 HJ' actor). apply upd_eq.
    Qed.

    Lemma gret_closes_done actor op ret :
      forall w, AssertionsSet.A.ComposeA (Done actor op ret)
        (AssertionsSet.Gret actor op ret) w -> I w.
    Proof.
      intros w [w0 [HD Hgret]].
      destruct Hgret as [Hsigma [Hlinr Heq]].
      assert (Hext : SetPossState.Δ w = ac_res (SetPossState.Δ w0) actor).
      { apply AbstractConfig_ext. exact Heq. }
      destruct HD as [[phi HJ] Hph]. specialize (Hph _ HJ).
      exists (phi_remove phi actor). rewrite <- Hsigma, Hext.
      apply J_ac_res; [exact HJ|]. rewrite Hph. destruct op; simpl; constructor.
    Qed.

    (** Guarantee of a step by [actor] whose only phase change is [actor]'s. *)
    Lemma G_intro actor (w w' : set_state) phi phi' :
      J (SetPossState.σ w) phi (SetPossState.Δ w) ->
      J (SetPossState.σ w') phi' (SetPossState.Δ w') ->
      (forall t, t <> actor -> phi' t = phi t) ->
      G actor w w'.
    Proof.
      intros HJ HJ' Hother. split; [eexists; exact HJ|]. split; [eexists; exact HJ'|].
      intros phi0 phi0' HJ0 HJ0' t Hneq.
      rewrite (phase_unique _ _ _ _ HJ0 HJ t), (phase_unique _ _ _ _ HJ0' HJ' t).
      apply Hother. exact Hneq.
    Qed.

    (** * Phase consistency after each concrete event *)

    Ltac pc_other :=
      match goal with
      | Hpc : phase_consistent _ ?phi |- _ =>
          destruct Hpc as (Hpc1 & Hpc2 & Hpc3 & Hpc4 & Hpc5 & Hpc6 & Hpc7); simpl in *
      end.

    Lemma pc_push_inv (s : @TryStackAuxState A) actor loc v (phi : @PhaseMap A) :
      tsa_ghost_wf s -> phase_consistent (TSAReady s) phi ->
      TMap.find actor (tsa_pending_pushes s) = None ->
      tsa_fresh_node s (pair actor loc) ->
      phi actor = Some (PhPushInvoked v) ->
      phase_consistent (TSAReady (tsa_start_push actor loc v s))
        (upd phi actor (PhPushPending v loc)).
    Proof.
      intros Hwf Hpc Hnone Hfresh Hph. pc_other.
      destruct Hfresh as [Hfresh _].
      unfold phase_consistent, tsa_start_push; simpl.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      - intros t l. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite TMap.gss, upd_eq. split.
          * intro H. inversion H; subst. eauto.
          * intros [v' H]. inversion H; subst. reflexivity.
        + rewrite TMap.gso, upd_neq by exact Hneq. apply Hpc1.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split.
          * intros HN. exfalso. assert (H : phi actor = Some PhPopSnapshot) by (apply Hpc2; exact HN).
            congruence.
          * discriminate.
        + rewrite upd_neq by exact Hneq. apply Hpc2.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split; [discriminate|]. intros [op H]. discriminate.
        + rewrite upd_neq by exact Hneq. split.
          * intro H. apply Hpc3 in H. destruct H as [op H]. discriminate.
          * intros [op H]. discriminate.
      - intros t v' l H. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq in H. inversion H; subst. unfold node_update.
          destruct (node_eq_dec (pair actor l) (pair actor l)); congruence.
        + rewrite upd_neq in H by exact Hneq. unfold node_update.
          destruct (node_eq_dec (pair actor loc) (pair t l)) as [Heq|Hne]; [inversion Heq; congruence|].
          apply Hpc4. exact H.
      - intros t v' H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq.
        destruct (Hpc5 t v' H) as (l & r & Hr & Hv & Hlat).
        exists l, r. split; [exact Hr|]. split.
        + unfold node_update. destruct (node_eq_dec (pair actor loc) (pair t l)) as [Heq|Hne];
            [inversion Heq; congruence|exact Hv].
        + unfold latest_node in *; simpl. destruct Hlat as (i & Hi & Hmax). exists i. split.
          * unfold node_update. destruct (node_eq_dec (pair actor loc) (pair t l)) as [Heq|Hne];
              [inversion Heq; congruence|exact Hi].
          * intros l' i' Hi'. unfold node_update in Hi'.
            destruct (node_eq_dec (pair actor loc) (pair t l')) as [Heq|Hne];
              [inversion Heq; congruence|]. eapply Hmax. exact Hi'.
      - intros t v' o l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq.
        destruct (Hpc6 t v' o l H) as [Hv Hrem]. split; [|exact Hrem].
        unfold node_update. destruct (node_eq_dec (pair actor loc) (pair o l)) as [Heq|Hne]; [|exact Hv].
        rewrite <- Heq in Hv. congruence.
      - intros t H. exfalso. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq in H. discriminate.
        + rewrite upd_neq in H by exact Hneq. apply Hpc3 in H. destruct H as [op H]. discriminate.
    Qed.

    Lemma pc_push_res (s : @TryStackAuxState A) actor loc v (phi : @PhaseMap A) :
      tsa_ghost_wf s -> phase_consistent (TSAReady s) phi ->
      TMap.find actor (tsa_pending_pushes s) = Some loc ->
      phi actor = Some (PhPushPending v loc) ->
      phase_consistent (TSAReady (tsa_finish_push actor s))
        (upd phi actor (PhPushDone v)).
    Proof.
      intros Hwf Hpc Hfind Hph. pc_other.
      destruct (wf_pending_node_ret s actor loc Hwf Hfind) as [Hret0 [i0 Hinv0]].
      unfold phase_consistent, tsa_finish_push; simpl. rewrite Hfind.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      - intros t l. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite TMap.grs, upd_eq. split; [discriminate|]. intros [v' H]. discriminate.
        + rewrite TMap.gro, upd_neq by exact Hneq. apply Hpc1.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split.
          * intros HN. exfalso. assert (H : phi actor = Some PhPopSnapshot) by (apply Hpc2; exact HN).
            congruence.
          * discriminate.
        + rewrite upd_neq by exact Hneq. apply Hpc2.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split; [discriminate|]. intros [op H]. discriminate.
        + rewrite upd_neq by exact Hneq. split.
          * intro H. apply Hpc3 in H. destruct H as [op H]. discriminate.
          * intros [op H]. discriminate.
      - intros t v' l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc4. exact H.
      - intros t v' H. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq in H. inversion H; subst v'.
          exists loc, (tsa_now s). split.
          * unfold node_update. destruct (node_eq_dec (pair actor loc) (pair actor loc)); congruence.
          * split; [apply Hpc4; exact Hph|].
            exists i0. split; [exact Hinv0|]. intros l' i' Hi'.
            destruct (le_lt_dec i' i0) as [Hle|Hlt]; [exact Hle|]. exfalso.
            destruct (wf_same_actor _ Hwf _ _ _ _ _ Hinv0 Hi' Hlt) as (r & Hr & _). congruence.
        + rewrite upd_neq in H by exact Hneq.
          destruct (Hpc5 t v' H) as (l & r & Hr & Hv & Hlat).
          exists l, r. split; [|split; assumption]. unfold node_update.
          destruct (node_eq_dec (pair actor loc) (pair t l)) as [Heq|Hne]; [inversion Heq; congruence|exact Hr].
      - intros t v' o l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc6. exact H.
      - intros t H. exfalso. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq in H. discriminate.
        + rewrite upd_neq in H by exact Hneq. apply Hpc3 in H. destruct H as [op H]. discriminate.
    Qed.


    (** * Inversion of the concrete steps *)

    Lemma step_push_inv_inv actor v (c c' : @TryStackAuxControl A) :
      StepTryStackAux (Build_ThreadEvent actor (InvEv (tsa_push v))) c c' ->
      exists s loc, c = TSAReady s /\ c' = TSAReady (tsa_start_push actor loc v s) /\
        TMap.find actor (tsa_pending_pushes s) = None /\
        tsa_fresh_node s (pair actor loc).
    Proof.
      intros Hstep. inversion Hstep; subst; try inversion_thread_event_eq;
        repeat match goal with
        | H : existT _ _ _ = existT _ _ _ |- _ => dependent destruction H
        end.
      eauto 6.
    Qed.

    Lemma step_push_res_inv actor v (c c' : @TryStackAuxControl A) :
      StepTryStackAux (Build_ThreadEvent actor (ResEv (tsa_push v) tt)) c c' ->
      exists s loc, c = TSAReady s /\ c' = TSAReady (tsa_finish_push actor s) /\
        TMap.find actor (tsa_pending_pushes s) = Some loc.
    Proof.
      intros Hstep. inversion Hstep; subst; try inversion_thread_event_eq;
        repeat match goal with
        | H : existT _ _ _ = existT _ _ _ |- _ => dependent destruction H
        end.
      eauto 6.
    Qed.

    Lemma step_trypop_inv_inv actor (c c' : @TryStackAuxControl A) :
      StepTryStackAux (Build_ThreadEvent actor (InvEv tsa_trypop)) c c' ->
      exists s, c = TSAReady s /\ TMap.find actor (tsa_snapshots s) = None /\
        ((c' = TSAAtomicPending s actor tsa_trypop /\ tsa_all_vertices_garbage s) \/
         c' = TSAReady (tsa_start_snapshot actor s)).
    Proof.
      intros Hstep. inversion Hstep; subst; try inversion_thread_event_eq;
        repeat match goal with
        | H : existT _ _ _ = existT _ _ _ |- _ => dependent destruction H
        end.
      - exists s. split; [reflexivity|]. split; [assumption|]. left. auto.
      - exists s. split; [reflexivity|]. split; [assumption|]. right. reflexivity.
    Qed.

    Lemma step_trypop_res_inv actor r (c c' : @TryStackAuxControl A) :
      StepTryStackAux (Build_ThreadEvent actor (ResEv tsa_trypop r)) c c' ->
      exists s,
        (c = TSAAtomicPending s actor tsa_trypop /\ c' = TSAReady s /\ r = TSuccEmpty) \/
        (c = TSAReady s /\ exists N, TMap.find actor (tsa_snapshots s) = Some N /\
           ((exists n v, lp_top (fun n' => N n' /\ ~ tsa_garbage s n') (tsa_edges s) n /\
               tsa_vertices s n = Some v /\ r = TSuccNode v (fst n) (snd n) /\
               c' = TSAReady (tsa_remove_node actor n s)) \/
            (r = TFail /\ c' = TSAReady (tsa_clear_snapshot actor s)))).
    Proof.
      intros Hstep. inversion Hstep; subst; try inversion_thread_event_eq;
        repeat match goal with
        | H : existT _ _ _ = existT _ _ _ |- _ => dependent destruction H
        end.
      - exists s. left. auto.
      - exists s. right. split; [reflexivity|]. exists N. split; [assumption|].
        left. exists n, v. auto.
      - exists s. right. split; [reflexivity|]. exists N. split; [assumption|].
        right. auto.
    Qed.

    (** * Possibility updates for the push events *)

    Definition state_of (sigma : @TryStackAuxControl A)
        (Delta : @AbstractConfig _ (li_lts F)) : set_state :=
      @SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F) sigma Delta.

    Lemma push_inv_update actor (v : A) :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (InvEv (tsa_push v)))
        (PhaseIs actor (fun ph => ph = Some (PhPushInvoked v)))
        (PhaseIs actor (fun ph => exists loc, ph = Some (PhPushPending v loc))).
    Proof.
      intros sigma Delta [[phi HJ] Hph] sigma' Hstep.
      specialize (Hph _ HJ).
      destruct (step_push_inv_inv actor v sigma sigma' Hstep)
        as (s & loc & -> & -> & Hnone & Hfresh).
      pose proof HJ as (Hwf & Hpc & _ & _). simpl in Hwf.
      set (phi' := upd phi actor (PhPushPending v loc)).
      destruct (real_step_generic (TSAReady s) (TSAReady (tsa_start_push actor loc v s))
        phi phi' Delta HJ) as (Delta' & Hsub & HJ').
      - simpl. apply start_push_wf; auto.
      - apply pc_push_inv; auto.
      - intros h' Hc'. apply (real_step_push_inv D s actor loc v phi h'); auto.
      - exists Delta'. split; [exact Hsub|]. split.
        + split; [eexists; exact HJ'|]. intros phi0 HJ0.
          rewrite (phase_unique _ _ _ _ HJ0 HJ' actor). exists loc. apply upd_eq.
        + eapply (G_intro actor (state_of _ Delta) (state_of _ Delta') phi phi'); auto.
          intros t Hneq. apply upd_neq. exact Hneq.
    Qed.

    Lemma push_res_update actor (v : A) :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (ResEv (tsa_push v) tt))
        (PhaseIs actor (fun ph => exists loc, ph = Some (PhPushPending v loc)))
        (PhaseIs actor (fun ph => ph = Some (PhPushDone v))).
    Proof.
      intros sigma Delta [[phi HJ] Hph] sigma' Hstep.
      destruct (Hph _ HJ) as [loc0 Hph0].
      destruct (step_push_res_inv actor v sigma sigma' Hstep)
        as (s & loc & -> & -> & Hfind).
      pose proof HJ as (Hwf & Hpc & _ & _). simpl in Hwf.
      assert (Hloc : loc = loc0).
      { destruct Hpc as (Hpc1 & _). apply Hpc1 in Hfind. destruct Hfind as [v' Hf].
        rewrite Hph0 in Hf. inversion Hf. reflexivity. }
      subst loc0.
      set (phi' := upd phi actor (PhPushDone v)).
      destruct (real_step_generic (TSAReady s) (TSAReady (tsa_finish_push actor s))
        phi phi' Delta HJ) as (Delta' & Hsub & HJ').
      - simpl. apply (finish_push_wf s actor loc); auto.
      - apply (pc_push_res s actor loc v); auto.
      - intros h' Hc'. apply (real_step_push_res D s actor loc v phi h'); auto.
      - exists Delta'. split; [exact Hsub|]. split.
        + split; [eexists; exact HJ'|]. intros phi0 HJ0.
          rewrite (phase_unique _ _ _ _ HJ0 HJ' actor). apply upd_eq.
        + eapply (G_intro actor (state_of _ Delta) (state_of _ Delta') phi phi'); auto.
          intros t Hneq. apply upd_neq. exact Hneq.
    Qed.

    Lemma inside_no_error actor (op : Sig.op (li_sig E)) :
      ThreadDomain.contains D actor ->
      forall w : set_state,
        @AssertionsSet.A.ANoError _ _ (li_lts E) (li_lts F)
          (Build_ThreadEvent actor (InvEv op)) w.
    Proof.
      intros Hin w Herr. simpl in Herr.
      inversion Herr; subst. inversion_thread_event_eq. contradiction.
    Qed.

    Definition Inside (actor : tid) (P : assertion) : assertion :=
      fun w => P w /\ ThreadDomain.contains D actor.

    Lemma inside_entails actor P : ⊨ Inside actor P ==>> P.
    Proof. intros w [H _]. exact H. Qed.

    Lemma inside_stable actor P :
      AssertionsSet.A.Stable (R actor) I P ->
      AssertionsSet.A.Stable (R actor) I (Inside actor P).
    Proof.
      intros Hst w' [[w [[HP Hin] HR]] HI']. split; [|exact Hin].
      apply Hst. split; [exists w; auto|exact HI'].
    Qed.

    Lemma phase_or_error actor op w :
      PhaseIs actor (fun ph => ph = Some (phase_of_inv op)) w ->
      Inside actor (PhaseIs actor (fun ph => ph = Some (phase_of_inv op))) w \/
      AssertionsSet.APError w.
    Proof.
      intros HP.
      destruct (ThreadDomain.contains_dec D actor) as [Hin|Hout].
      - left. split; [exact HP|exact Hin].
      - right. destruct w as [sigma Delta]. destruct HP as [[phi HJ] Hph].
        specialize (Hph _ HJ).
        destruct (ac_nonempty Delta) as (rho & pi & Hposs).
        pose proof (J_token_shape _ _ _ _ _ actor HJ Hposs) as S.
        rewrite Hph in S. unfold token_shape in S.
        assert (Htok : TMap.find actor pi = Some (ls_inv op)).
        { destruct op; simpl in S; tauto. }
        destruct HJ as (_ & _ & Hreal & _).
        destruct (Hreal _ _ Hposs) as (h & _ & (st & Hrho & _)).
        econstructor; [exact Hposs|]. apply rt_step. eapply ps_error.
        + simpl. rewrite Hrho. eapply error_ts_actor_outside; [exact Hout|reflexivity].
        + exact Htok.
    Qed.

    Lemma push_method_triple actor (v : A) :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (PhaseIs actor (fun ph => ph = Some (PhPushInvoked v)))
        (push_impl D v actor)
        (fun ret => Done actor (ts_push v) ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := Inside actor (PhaseIs actor (fun ph => ph = Some (PhPushInvoked v)))).
      - intros w HA. apply (phase_or_error actor (ts_push v) w HA).
      - unfold push_impl.
        eapply SetLogic.provable_vis_safe with
          (P' := PhaseIs actor (fun ph => exists loc, ph = Some (PhPushPending v loc)))
          (Q' := fun _ => PhaseIs actor (fun ph => ph = Some (PhPushDone v))).
        + intros w [_ Hin]. apply inside_no_error. exact Hin.
        + apply phase_is_entails_I.
        + intros _. apply phase_is_entails_I.
        + apply phase_is_stable.
        + intros _. apply phase_is_stable.
        + intros sigma Delta [HP Hin] sigma' Hstep.
          apply (push_inv_update actor v sigma Delta HP sigma' Hstep).
        + intros []. apply push_res_update.
        + intros []. eapply SetLogic.provable_ret_safe.
          * intros w HP. exact HP.
          * apply phase_is_entails_I.
          * apply phase_is_stable.
    Qed.

    (** * Phase consistency after the trypop events *)

    Lemma pc_snapshot (s : @TryStackAuxState A) actor (phi : @PhaseMap A) :
      tsa_ghost_wf s -> phase_consistent (TSAReady s) phi ->
      TMap.find actor (tsa_snapshots s) = None ->
      phi actor = Some PhPopInvoked ->
      phase_consistent (TSAReady (tsa_start_snapshot actor s))
        (upd phi actor PhPopSnapshot).
    Proof.
      intros Hwf Hpc Hnone Hph. pc_other.
      unfold phase_consistent, tsa_start_snapshot; simpl.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      - intros t l. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split.
          * intro Hf. exfalso. apply Hpc1 in Hf. destruct Hf as [v Hf]. congruence.
          * intros [v Hf]. discriminate.
        + rewrite upd_neq by exact Hneq. apply Hpc1.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite TMap.gss, upd_eq. split; [reflexivity|]. intros _. eauto.
        + rewrite TMap.gso, upd_neq by exact Hneq. apply Hpc2.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split; [discriminate|]. intros [op H]. discriminate.
        + rewrite upd_neq by exact Hneq. split.
          * intro H. apply Hpc3 in H. destruct H as [op H]. discriminate.
          * intros [op H]. discriminate.
      - intros t v l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc4. exact H.
      - intros t v H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc5. exact H.
      - intros t v o l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc6. exact H.
      - intros t H. exfalso. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq in H. discriminate.
        + rewrite upd_neq in H by exact Hneq. apply Hpc3 in H. destruct H as [op H]. discriminate.
    Qed.

    Lemma pc_empty_inv (s : @TryStackAuxState A) actor (phi : @PhaseMap A) :
      phase_consistent (TSAReady s) phi ->
      tsa_all_vertices_garbage s ->
      phi actor = Some PhPopInvoked ->
      phase_consistent (TSAAtomicPending s actor tsa_trypop)
        (upd phi actor PhPopEmptyPending).
    Proof.
      intros Hpc Hall Hph. pc_other.
      unfold phase_consistent; simpl.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      - intros t l. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split.
          * intro Hf. exfalso. apply Hpc1 in Hf. destruct Hf as [v Hf]. congruence.
          * intros [v Hf]. discriminate.
        + rewrite upd_neq by exact Hneq. apply Hpc1.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split.
          * intro HN. exfalso. assert (H : phi actor = Some PhPopSnapshot) by (apply Hpc2; exact HN).
            congruence.
          * discriminate.
        + rewrite upd_neq by exact Hneq. apply Hpc2.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split; [intros _; eexists; reflexivity|reflexivity].
        + rewrite upd_neq by exact Hneq. split.
          * intro H. apply Hpc3 in H. destruct H as [op H]. discriminate.
          * intros [op H]. inversion H. congruence.
      - intros t v l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc4. exact H.
      - intros t v H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc5. exact H.
      - intros t v o l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc6. exact H.
      - intros t H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [exact Hall|].
        rewrite upd_neq in H by exact Hneq. exfalso.
        apply Hpc3 in H. destruct H as [op H]. discriminate.
    Qed.

    Lemma pc_remove (s : @TryStackAuxState A) actor n N v (phi : @PhaseMap A) :
      tsa_ghost_wf s -> phase_consistent (TSAReady s) phi ->
      TMap.find actor (tsa_snapshots s) = Some N ->
      lp_top (fun n' => N n' /\ ~ tsa_garbage s n') (tsa_edges s) n ->
      tsa_vertices s n = Some v ->
      phi actor = Some PhPopSnapshot ->
      phase_consistent (TSAReady (tsa_remove_node actor n s))
        (upd phi actor (PhPopDone (TSuccNode v (fst n) (snd n)))).
    Proof.
      intros Hwf Hpc HN Htop Hv Hph. pc_other.
      destruct (wf_snapshot _ Hwf _ _ HN) as (st & Hst & _).
      destruct Htop as [[_ Hnog] _].
      unfold phase_consistent, tsa_remove_node; simpl. rewrite Hst.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      - intros t l. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split.
          * intro Hf. exfalso. apply Hpc1 in Hf. destruct Hf as [v' Hf]. congruence.
          * intros [v' Hf]. discriminate.
        + rewrite upd_neq by exact Hneq. apply Hpc1.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite TMap.grs, upd_eq. split; [intros [N' H]; discriminate|discriminate].
        + rewrite TMap.gro, upd_neq by exact Hneq. apply Hpc2.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split; [discriminate|]. intros [op H]. discriminate.
        + rewrite upd_neq by exact Hneq. split.
          * intro H. apply Hpc3 in H. destruct H as [op H]. discriminate.
          * intros [op H]. discriminate.
      - intros t v' l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc4. exact H.
      - intros t v' H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc5. exact H.
      - intros t v' o l H. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq in H. inversion H; subst v' o l. destruct n as [on ln]. simpl.
          split; [exact Hv|]. exists st, (tsa_now s). unfold node_update.
          destruct (node_eq_dec (pair on ln) (pair on ln)); congruence.
        + rewrite upd_neq in H by exact Hneq.
          destruct (Hpc6 t v' o l H) as [Hv' Hrem]. split; [exact Hv'|].
          unfold node_update. destruct (node_eq_dec n (pair o l)) as [Heq|Hne]; [|exact Hrem].
          exfalso. apply Hnog. apply (wf_garbage _ Hwf). rewrite Heq.
          destruct Hrem as (st' & rt' & Hrem). eauto.
      - intros t H. exfalso. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq in H. discriminate.
        + rewrite upd_neq in H by exact Hneq. apply Hpc3 in H. destruct H as [op H]. discriminate.
    Qed.

    Lemma pc_fail (s : @TryStackAuxState A) actor N (phi : @PhaseMap A) :
      phase_consistent (TSAReady s) phi ->
      TMap.find actor (tsa_snapshots s) = Some N ->
      phi actor = Some PhPopSnapshot ->
      phase_consistent (TSAReady (tsa_clear_snapshot actor s))
        (upd phi actor (PhPopDone TFail)).
    Proof.
      intros Hpc HN Hph. pc_other.
      unfold phase_consistent, tsa_clear_snapshot; simpl.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      - intros t l. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split.
          * intro Hf. exfalso. apply Hpc1 in Hf. destruct Hf as [v' Hf]. congruence.
          * intros [v' Hf]. discriminate.
        + rewrite upd_neq by exact Hneq. apply Hpc1.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite TMap.grs, upd_eq. split; [intros [N' H]; discriminate|discriminate].
        + rewrite TMap.gro, upd_neq by exact Hneq. apply Hpc2.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split; [discriminate|]. intros [op H]. discriminate.
        + rewrite upd_neq by exact Hneq. split.
          * intro H. apply Hpc3 in H. destruct H as [op H]. discriminate.
          * intros [op H]. discriminate.
      - intros t v' l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc4. exact H.
      - intros t v' H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc5. exact H.
      - intros t v' o l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc6. exact H.
      - intros t H. exfalso. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq in H. discriminate.
        + rewrite upd_neq in H by exact Hneq. apply Hpc3 in H. destruct H as [op H]. discriminate.
    Qed.

    Lemma pc_empty_res (s : @TryStackAuxState A) actor (phi : @PhaseMap A) :
      phase_consistent (TSAAtomicPending s actor tsa_trypop) phi ->
      phi actor = Some PhPopEmptyPending ->
      phase_consistent (TSAReady s) (upd phi actor (PhPopDone TSuccEmpty)).
    Proof.
      intros Hpc Hph. pc_other.
      unfold phase_consistent; simpl.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      - intros t l. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split.
          * intro Hf. exfalso. apply Hpc1 in Hf. destruct Hf as [v' Hf]. congruence.
          * intros [v' Hf]. discriminate.
        + rewrite upd_neq by exact Hneq. apply Hpc1.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split.
          * intro HN. exfalso. assert (H : phi actor = Some PhPopSnapshot) by (apply Hpc2; exact HN).
            congruence.
          * discriminate.
        + rewrite upd_neq by exact Hneq. apply Hpc2.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq. split; [discriminate|]. intros [op H]. discriminate.
        + rewrite upd_neq by exact Hneq. split.
          * intro H. apply Hpc3 in H. destruct H as [op H]. inversion H. congruence.
          * intros [op H]. discriminate.
      - intros t v' l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc4. exact H.
      - intros t v' H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc5. exact H.
      - intros t v' o l H. destruct (Pos.eq_dec t actor) as [->|Hneq]; [rewrite upd_eq in H; discriminate|].
        rewrite upd_neq in H by exact Hneq. apply Hpc6. exact H.
      - intros t H. exfalso. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite upd_eq in H. discriminate.
        + rewrite upd_neq in H by exact Hneq. apply Hpc3 in H. destruct H as [op H].
          inversion H. congruence.
    Qed.

    (** A consistent history restricted to the current final cut is
        unchanged in every respect that matters. *)
    Lemma restrict_final_consistent (s : @TryStackAuxState A) h :
      tsa_ghost_wf s -> consistent s h -> consistent s (restrict h (final_cut s)).
    Proof.
      intros Hwf Hc. apply (restrict_consistent s s h Hwf Hwf); [|exact Hc|].
      - constructor.
        + lia.
        + intros m i Hi _. exact Hi.
        + intros m i Hi. exact Hi.
        + intros m r Hr _. exact Hr.
        + intros m r Hr. split; [exact Hr|]. eapply wf_ret_now; eauto.
        + intros m rec Hrec. exact Hrec.
        + intros m a st rt Hrem. split; [intros _; exact Hrem|].
          intro Hn. exfalso. apply Hn. eapply wf_removal; eauto.
        + intros m Hm. exact Hm.
        + intros a st Hst _. exact Hst.
      - intros n m p q a Hp Hq _ _ Hn Hm. eapply c_spec_unique; eauto.
    Qed.

    (** * Possibility updates for the trypop events *)

    Lemma trypop_inv_update actor :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (InvEv tsa_trypop))
        (PhaseIs actor (fun ph => ph = Some PhPopInvoked))
        (PhaseIs actor (fun ph => ph = Some PhPopSnapshot \/ ph = Some PhPopEmptyPending)).
    Proof.
      intros sigma Delta [[phi HJ] Hph] sigma' Hstep.
      specialize (Hph _ HJ).
      destruct (step_trypop_inv_inv actor sigma sigma' Hstep)
        as (s & -> & Hnone & Hcase).
      destruct Hcase as [[-> Hall]| ->].
      - (* empty branch *)
        pose proof HJ as (Hwf & Hpc & _ & _). simpl in Hwf.
        set (phi' := upd phi actor PhPopEmptyPending).
        destruct (real_step_generic (TSAReady s) (TSAAtomicPending s actor tsa_trypop)
          phi phi' Delta HJ) as (Delta' & Hsub & HJ').
        + simpl. exact Hwf.
        + apply pc_empty_inv; auto.
        + intros h' Hc'. simpl in *. split; [apply restrict_final_consistent; auto|].
          intros rho pi Hrep. exists rho, pi. split; [apply rt_refl|].
          rewrite represents_at_restrict in Hrep.
          apply real_step_empty_inv; auto.
        + exists Delta'. split; [exact Hsub|]. split.
          * split; [eexists; exact HJ'|]. intros phi0 HJ0.
            rewrite (phase_unique _ _ _ _ HJ0 HJ' actor). right. apply upd_eq.
          * eapply (G_intro actor (state_of _ Delta) (state_of _ Delta') phi phi'); auto.
            intros t Hneq. apply upd_neq. exact Hneq.
      - (* snapshot branch *)
        pose proof HJ as (Hwf & Hpc & _ & _). simpl in Hwf.
        set (phi' := upd phi actor PhPopSnapshot).
        destruct (real_step_generic (TSAReady s) (TSAReady (tsa_start_snapshot actor s))
          phi phi' Delta HJ) as (Delta' & Hsub & HJ').
        + simpl. apply start_snapshot_wf; auto.
        + apply pc_snapshot; auto.
        + intros h' Hc'. apply (real_step_snapshot D s actor phi h'); auto.
        + exists Delta'. split; [exact Hsub|]. split.
          * split; [eexists; exact HJ'|]. intros phi0 HJ0.
            rewrite (phase_unique _ _ _ _ HJ0 HJ' actor). left. apply upd_eq.
          * eapply (G_intro actor (state_of _ Delta) (state_of _ Delta') phi phi'); auto.
            intros t Hneq. apply upd_neq. exact Hneq.
    Qed.

    Lemma trypop_res_update actor (r : @TResult A) :
      AssertionsSet.PUpdate (G actor)
        (Build_ThreadEvent actor (ResEv tsa_trypop r))
        (PhaseIs actor (fun ph => ph = Some PhPopSnapshot \/ ph = Some PhPopEmptyPending))
        (Done actor ts_trypop r).
    Proof.
      intros sigma Delta [[phi HJ] Hph] sigma' Hstep.
      specialize (Hph _ HJ).
      destruct (step_trypop_res_inv actor r sigma sigma' Hstep) as (s & Hcase).
      pose proof HJ as (Hwf & Hpc & _ & _).
      destruct Hcase as [Hcase|Hcase];
        [destruct Hcase as [-> [-> Hr]]|destruct Hcase as [-> [N [HN Hcase]]]].
      - (* empty response *)
        simpl in Hwf.
        assert (Hph' : phi actor = Some PhPopEmptyPending).
        { destruct Hpc as (_ & _ & Hpc3 & _). apply Hpc3. exists tsa_trypop. reflexivity. }
        assert (Hall : tsa_all_vertices_garbage s).
        { destruct Hpc as (_ & _ & _ & _ & _ & _ & Hpc7). apply (Hpc7 actor Hph'). }
        set (phi' := upd phi actor (PhPopDone TSuccEmpty)).
        destruct (real_step_generic (TSAAtomicPending s actor tsa_trypop) (TSAReady s)
          phi phi' Delta HJ) as (Delta' & Hsub & HJ').
        + simpl. exact Hwf.
        + apply pc_empty_res; auto.
        + intros h' Hc'. simpl in *. split; [apply restrict_final_consistent; auto|].
          intros rho pi Hrep. rewrite represents_at_restrict in Hrep.
          apply (real_step_empty_res D s actor phi h' rho pi); auto.
        + exists Delta'. split; [exact Hsub|]. split.
          * split; [eexists; exact HJ'|]. intros phi0 HJ0.
            rewrite (phase_unique _ _ _ _ HJ0 HJ' actor). rewrite Hr. apply upd_eq.
          * eapply (G_intro actor (state_of _ Delta) (state_of _ Delta') phi phi'); auto.
            intros t Hneq. apply upd_neq. exact Hneq.
      - simpl in Hwf.
        assert (Hph' : phi actor = Some PhPopSnapshot).
        { destruct Hpc as (_ & Hpc2 & _). apply Hpc2. eauto. }
        destruct Hcase as [Hcase|Hcase];
          [destruct Hcase as [n [v [Htop [Hv [Hr ->]]]]]|destruct Hcase as [Hr ->]].
        + (* successful removal *)
          set (phi' := upd phi actor (PhPopDone (TSuccNode v (fst n) (snd n)))).
          destruct (real_step_generic (TSAReady s) (TSAReady (tsa_remove_node actor n s))
            phi phi' Delta HJ) as (Delta' & Hsub & HJ').
          * simpl. eapply remove_node_wf; eauto.
          * apply (pc_remove s actor n N v); auto.
          * intros h' Hc'. apply (real_step_remove D s actor n N v phi h'); auto.
          * exists Delta'. split; [exact Hsub|]. split.
            -- split; [eexists; exact HJ'|]. intros phi0 HJ0.
               rewrite (phase_unique _ _ _ _ HJ0 HJ' actor). rewrite Hr. apply upd_eq.
            -- eapply (G_intro actor (state_of _ Delta) (state_of _ Delta') phi phi'); auto.
               intros t Hneq. apply upd_neq. exact Hneq.
        + (* failure *)
          set (phi' := upd phi actor (PhPopDone TFail)).
          destruct (real_step_generic (TSAReady s) (TSAReady (tsa_clear_snapshot actor s))
            phi phi' Delta HJ) as (Delta' & Hsub & HJ').
          * simpl. apply clear_snapshot_wf; auto.
          * apply (pc_fail s actor N); auto.
          * intros h' Hc'. apply (real_step_fail D s actor N phi h'); auto.
          * exists Delta'. split; [exact Hsub|]. split.
            -- split; [eexists; exact HJ'|]. intros phi0 HJ0.
               rewrite (phase_unique _ _ _ _ HJ0 HJ' actor). rewrite Hr. apply upd_eq.
            -- eapply (G_intro actor (state_of _ Delta) (state_of _ Delta') phi phi'); auto.
               intros t Hneq. apply upd_neq. exact Hneq.
    Qed.

    Lemma trypop_method_triple actor :
      SetLogic.HTripleProvable (R actor) (G actor) I actor
        (PhaseIs actor (fun ph => ph = Some PhPopInvoked))
        (trypop_impl D actor)
        (fun ret => Done actor ts_trypop ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := Inside actor (PhaseIs actor (fun ph => ph = Some PhPopInvoked))).
      - intros w HA. apply (phase_or_error actor ts_trypop w HA).
      - unfold trypop_impl.
        eapply SetLogic.provable_vis_safe with
          (P' := PhaseIs actor (fun ph => ph = Some PhPopSnapshot \/ ph = Some PhPopEmptyPending))
          (Q' := fun r => Done actor ts_trypop r).
        + intros w [_ Hin]. apply inside_no_error. exact Hin.
        + apply phase_is_entails_I.
        + intros r. apply phase_is_entails_I.
        + apply phase_is_stable.
        + intros r. apply phase_is_stable.
        + intros sigma Delta [HP Hin] sigma' Hstep.
          apply (trypop_inv_update actor sigma Delta HP sigma' Hstep).
        + intros r. apply trypop_res_update.
        + intros r. eapply SetLogic.provable_ret_safe.
          * intros w HP. exact HP.
          * apply phase_is_entails_I.
          * apply phase_is_stable.
    Qed.

    (** * The initial state *)

    Definition empty_history : History :=
      {| h_inv := fun _ => None; h_pop := fun _ => None |}.

    Lemma initial_consistent :
      consistent (@empty_try_stack_aux_state A) empty_history.
    Proof.
      constructor; simpl; intros; try discriminate; try congruence.
    Qed.

    Lemma represents_initial (h : History) :
      (forall n q, h_inv h n <> Some q) ->
      (forall n qa, h_pop h n <> Some qa) ->
      represents_at (@empty_try_stack_aux_state A) (fun _ => None) h
        (final_cut (@empty_try_stack_aux_state A)) None
        (TSReady (@empty_try_stack_state A)) (TMap.empty _).
    Proof.
      intros Hinv Hpop.
      assert (Hnpl : forall n, ~ placed_before h (final_cut (@empty_try_stack_aux_state A)) n).
      { intros n (q & Hq & _). eapply Hinv. exact Hq. }
      assert (Hnpo : forall n, ~ popped_before h (final_cut (@empty_try_stack_aux_state A)) n).
      { intros n (q & a & Hq & _). eapply Hpop. exact Hq. }
      exists empty_try_stack_state. split; [reflexivity|].
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      - intros n Hn. exfalso. eapply Hnpl. exact Hn.
      - intros n _. reflexivity.
      - intros x y. simpl. split; [contradiction|]. intros [Hx _]. exfalso. eapply Hnpl. exact Hx.
      - intros t loc. simpl. rewrite TMap.gempty. split; [discriminate|].
        intros [Hx _]. exfalso. eapply Hnpl. exact Hx.
      - intros n. simpl. split; [contradiction|]. intro Hn. exfalso. eapply Hnpo. exact Hn.
      - intros t. unfold token_at. simpl. apply TMap.gempty.
    Qed.

    Lemma initial_I :
      I (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (li_init E)
          (ac_singleton (li_init F) (@TMap.empty (@LinState (li_sig F))))).
    Proof.
      exists (fun _ => None). simpl.
      split; [exact initial_ghost_wf|]. split.
      - unfold phase_consistent; simpl.
        refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
        + intros t loc. rewrite TMap.gempty. split; [discriminate|]. intros [v H]. discriminate.
        + intros t. rewrite TMap.gempty. split; [intros [N H]; discriminate|discriminate].
        + intros t. split; [discriminate|]. intros [op H]. discriminate.
        + intros t v loc H. discriminate.
        + intros t v H. discriminate.
        + intros t v o l H. discriminate.
        + intros t H. discriminate.
      - split.
        + intros rho pi Hposs. inversion Hposs; subst.
          exists empty_history. split; [exact initial_consistent|].
          apply represents_initial; intros; discriminate.
        + intros h Hc. exists (li_init F), (TMap.empty _). split; [constructor|].
          apply represents_initial.
          * intros n q Hq. destruct (c_inv_placed _ _ Hc _ _ Hq) as (_ & Hnow & _).
            simpl in Hnow. lia.
          * intros n [q a] Hq. destruct (c_pop_placed _ _ Hc _ _ _ Hq) as (_ & Hnow & _).
            simpl in Hnow. lia.
    Qed.

    (** * Soundness *)

    Program Definition MTryStack : layer_implementation_simulation E F :=
      {| li_impl := try_stack_impl D |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := I).
      - exact valid_rg.
      - exact parallel_compatible.
      - intros actor op. destruct op as [v|].
        + exists (PhaseIs actor (fun ph => ph = Some (PhPushInvoked v))).
          exists (fun ret => Done actor (ts_push v) ret).
          constructor.
          * intros w Hcompose. apply (ginv_exposes_phase actor (ts_push v) w Hcompose).
          * apply phase_is_entails_I.
          * apply phase_is_stable.
          * intros ret w Hcompose. apply (gret_closes_done actor (ts_push v) ret w Hcompose).
          * intros ret sigma Delta Hdone rho pi Hposs.
            apply (done_has_return_token actor (ts_push v) ret (state_of sigma Delta) Hdone rho pi Hposs).
          * apply push_method_triple.
        + exists (PhaseIs actor (fun ph => ph = Some PhPopInvoked)).
          exists (fun ret => Done actor ts_trypop ret).
          constructor.
          * intros w Hcompose. apply (ginv_exposes_phase actor ts_trypop w Hcompose).
          * apply phase_is_entails_I.
          * apply phase_is_stable.
          * intros ret w Hcompose. apply (gret_closes_done actor ts_trypop ret w Hcompose).
          * intros ret sigma Delta Hdone rho pi Hposs.
            apply (done_has_return_token actor ts_trypop ret (state_of sigma Delta) Hdone rho pi Hposs).
          * apply trypop_method_triple.
      - exact initial_I.
    Qed.

    Definition MTryStackLinearizable :
        layer_implementation_linearizability E F :=
      LISim2LILin MTryStack.

    Definition MListPoolTryStack :
        layer_implementation_linearizability (@ListPoolProof.E A D) F :=
      LIVComp (@TryStackAuxProof.MListPoolTryStackAux A D) MTryStackLinearizable.
  End Proof.
End TryStackProof.
