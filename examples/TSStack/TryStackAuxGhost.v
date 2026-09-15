Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Lia.
Require Import Coq.Logic.Classical_Prop.

Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.TryStackAuxSpec.
Require Import LinCCAL.
Require Import LTS.


(** Well-formedness of the ghost timing data of [TryStackAuxSpec].

    The ghost fields are deterministic functions of the pre-state and the
    event, so they never restrict the TryStackAux transitions.  This file
    states what they record and proves that every transition preserves it.
    The TryStack layer proof uses these facts to reconstruct, from the
    current state alone, which speculative linearisations are realisable. *)
Module TryStackAuxGhost.
  Import LTSSpec.
  Import LinCCALBase.
  Import ListPoolSpec.
  Import TryStackAuxSpec.

  Section Ghost.
    Context {A : Type}.

    (** Each clock value is used by at most one recorded event. *)
    Variant GhostEvent : Type :=
    | GInv (n : LPNodeId)
    | GRet (n : LPNodeId)
    | GSnap (actor : tid)
    | GRem (n : LPNodeId)
    | GSnapOf (n : LPNodeId).

    Definition ghost_event_at
        (s : @TryStackAuxState A) (t : nat) (ev : GhostEvent) : Prop :=
      match ev with
      | GInv n => tsa_node_inv s n = Some t
      | GRet n => tsa_node_ret s n = Some t
      | GSnap actor => TMap.find actor (tsa_snap_time s) = Some t
      | GRem n => exists actor st, tsa_removals s n = Some (actor, st, t)
      | GSnapOf n => exists actor rt, tsa_removals s n = Some (actor, t, rt)
      end.

    Record tsa_ghost_wf (s : @TryStackAuxState A) : Prop := {
      wf_vertex_inv : forall n,
        tsa_is_vertex s n <-> exists i, tsa_node_inv s n = Some i;
      wf_inv_now : forall n i,
        tsa_node_inv s n = Some i -> i < tsa_now s;
      wf_ret_inv : forall n r,
        tsa_node_ret s n = Some r ->
        exists i, tsa_node_inv s n = Some i /\ i < r;
      wf_ret_now : forall n r,
        tsa_node_ret s n = Some r -> r < tsa_now s;
      wf_pending : forall n,
        tsa_is_pending s n <->
        (exists i, tsa_node_inv s n = Some i) /\ tsa_node_ret s n = None;
      wf_edges : forall x y,
        tsa_edges s x y <->
        exists r i, tsa_node_ret s y = Some r /\
          tsa_node_inv s x = Some i /\ r < i;
      wf_snapshot : forall actor N,
        TMap.find actor (tsa_snapshots s) = Some N ->
        exists t, TMap.find actor (tsa_snap_time s) = Some t /\
          forall n, N n <-> exists i, tsa_node_inv s n = Some i /\ i < t;
      wf_snap_time : forall actor t,
        TMap.find actor (tsa_snap_time s) = Some t ->
        t < tsa_now s /\
        exists N, TMap.find actor (tsa_snapshots s) = Some N;
      wf_garbage : forall n,
        tsa_garbage s n <-> exists rec, tsa_removals s n = Some rec;
      wf_removal : forall n actor st rt,
        tsa_removals s n = Some (actor, st, rt) ->
        st < rt /\ rt < tsa_now s /\
        (exists i, tsa_node_inv s n = Some i /\ i < st) /\
        (forall y i, tsa_node_inv s y = Some i -> i < st ->
          tsa_edges s y n ->
          exists actor' st' rt',
            tsa_removals s y = Some (actor', st', rt') /\ rt' < rt);
      wf_unique : forall t ev1 ev2,
        ghost_event_at s t ev1 -> ghost_event_at s t ev2 -> ev1 = ev2;
      (** A thread pushes sequentially: an earlier push of the same
          thread completed before the later push started. *)
      wf_same_actor : forall actor l1 l2 i1 i2,
        tsa_node_inv s (actor, l1) = Some i1 ->
        tsa_node_inv s (actor, l2) = Some i2 ->
        i1 < i2 ->
        exists r1, tsa_node_ret s (actor, l1) = Some r1 /\ r1 < i2
    }.

    Definition control_wf (c : @TryStackAuxControl A) : Prop :=
      match c with
      | TSAReady s => tsa_ghost_wf s
      | TSAAtomicPending s _ _ => tsa_ghost_wf s
      end.

    (** Every recorded time is below the clock. *)
    Lemma ghost_event_now s t ev :
      tsa_ghost_wf s -> ghost_event_at s t ev -> t < tsa_now s.
    Proof.
      intros Hwf Hev. destruct ev; simpl in Hev.
      - eapply wf_inv_now; eauto.
      - eapply wf_ret_now; eauto.
      - eapply wf_snap_time; eauto.
      - destruct Hev as (a & st & Hrem).
        eapply wf_removal; eauto.
      - destruct Hev as (a & rt & Hrem).
        destruct (wf_removal _ Hwf _ _ _ _ Hrem) as [Hlt [Hrt _]]. lia.
    Qed.

    Lemma initial_ghost_wf :
      tsa_ghost_wf (@empty_try_stack_aux_state A).
    Proof.
      unfold empty_try_stack_aux_state, empty_node_map, empty_node_set,
        empty_edges; constructor; simpl.
      - intro n. unfold tsa_is_vertex; simpl. split.
        + intro H. exfalso. now apply H.
        + intros [i H]. discriminate.
      - intros n i H. discriminate.
      - intros n r H. discriminate.
      - intros n r H. discriminate.
      - intro n. unfold tsa_is_pending; simpl. rewrite TMap.gempty.
        split; [discriminate|]. intros [[i H] _]. discriminate.
      - intros x y. split; [contradiction|].
        intros (r & i & H & _). discriminate.
      - intros actor N H. rewrite TMap.gempty in H. discriminate.
      - intros actor t H. rewrite TMap.gempty in H. discriminate.
      - intro n. split; [contradiction|]. intros [rec H]. discriminate.
      - intros n actor st rt H. discriminate.
      - intros t ev1 ev2 H1 H2.
        destruct ev1; simpl in H1; try discriminate;
          try (rewrite TMap.gempty in H1; discriminate);
          destruct H1 as (? & ? & H1); discriminate.
      - intros actor l1 l2 i1 i2 H. discriminate.
    Qed.

    (** Auxiliary facts about the ghost data. *)

    Lemma node_update_some {B} n (v : B) (f : LPNodeMap B) n' w :
      node_update n v f n' = Some w ->
      (n' = n /\ w = v) \/ (n' <> n /\ f n' = Some w).
    Proof.
      unfold node_update. destruct (node_eq_dec n n') as [->|Hneq].
      - intro H. inversion H; subst. now left.
      - intro H. right. split; [congruence|exact H].
    Qed.

    Lemma wf_inv_unique s n1 n2 t :
      tsa_ghost_wf s ->
      tsa_node_inv s n1 = Some t -> tsa_node_inv s n2 = Some t -> n1 = n2.
    Proof.
      intros Hwf H1 H2.
      pose proof (wf_unique _ Hwf t (GInv n1) (GInv n2) H1 H2) as Heq.
      now inversion Heq.
    Qed.

    Lemma wf_ret_unique s n1 n2 t :
      tsa_ghost_wf s ->
      tsa_node_ret s n1 = Some t -> tsa_node_ret s n2 = Some t -> n1 = n2.
    Proof.
      intros Hwf H1 H2.
      pose proof (wf_unique _ Hwf t (GRet n1) (GRet n2) H1 H2) as Heq.
      now inversion Heq.
    Qed.

    Lemma wf_pending_node_ret s actor loc :
      tsa_ghost_wf s ->
      TMap.find actor (tsa_pending_pushes s) = Some loc ->
      tsa_node_ret s (actor, loc) = None /\
      exists i, tsa_node_inv s (actor, loc) = Some i.
    Proof.
      intros Hwf Hfind.
      assert (Hpend : tsa_is_pending s (actor, loc)).
      { unfold tsa_is_pending; simpl. exact Hfind. }
      apply (wf_pending _ Hwf) in Hpend. tauto.
    Qed.

    Lemma wf_vertex_inv_some s n v :
      tsa_ghost_wf s -> tsa_vertices s n = Some v ->
      exists i, tsa_node_inv s n = Some i.
    Proof.
      intros Hwf Hv. apply (wf_vertex_inv _ Hwf).
      unfold tsa_is_vertex. rewrite Hv. discriminate.
    Qed.

    Lemma wf_inv_vertex s n i :
      tsa_ghost_wf s -> tsa_node_inv s n = Some i -> tsa_is_vertex s n.
    Proof. intros Hwf Hi. apply (wf_vertex_inv _ Hwf). eauto. Qed.

    (** Preservation. *)

    Ltac ghost_simpl :=
      unfold tsa_start_push, tsa_finish_push, tsa_start_snapshot,
        tsa_clear_snapshot, tsa_remove_node, tsa_is_vertex, tsa_is_pending,
        ghost_event_at in *; simpl in *.

    Lemma start_push_event s actor loc (v : A) t ev :
      ghost_event_at (tsa_start_push actor loc v s) t ev ->
      (ev = GInv (actor, loc) /\ t = tsa_now s) \/ ghost_event_at s t ev.
    Proof.
      unfold ghost_event_at, tsa_start_push; simpl.
      destruct ev; intro H; try (right; exact H).
      apply node_update_some in H. destruct H as [[-> ->]|[_ H]].
      - left. auto.
      - right. exact H.
    Qed.

    Lemma start_push_wf s actor loc (v : A) :
      tsa_ghost_wf s ->
      TMap.find actor (tsa_pending_pushes s) = None ->
      tsa_fresh_node s (actor, loc) ->
      tsa_ghost_wf (tsa_start_push actor loc v s).
    Proof.
      intros Hwf Hnone [Hfresh Hnog].
      assert (Hinv_none : tsa_node_inv s (actor, loc) = None).
      { destruct (tsa_node_inv s (actor, loc)) as [i|] eqn:Hi; [|reflexivity].
        exfalso. apply (wf_inv_vertex _ _ _ Hwf) in Hi.
        unfold tsa_is_vertex in Hi. congruence. }
      assert (Hret_none : tsa_node_ret s (actor, loc) = None).
      { destruct (tsa_node_ret s (actor, loc)) as [r|] eqn:Hr; [|reflexivity].
        destruct (wf_ret_inv _ Hwf _ _ Hr) as (i & Hi & _). congruence. }
      assert (Hrem_none : tsa_removals s (actor, loc) = None).
      { destruct (tsa_removals s (actor, loc)) as [rec|] eqn:Hrec; [|reflexivity].
        exfalso. apply Hnog. apply (wf_garbage _ Hwf). eauto. }
      constructor; ghost_simpl.
      - intro m. unfold node_update.
        destruct (node_eq_dec (actor, loc) m) as [Heq|Hneq].
        + split; [eauto|]. intros _ Hc. discriminate Hc.
        + apply (wf_vertex_inv _ Hwf).
      - intros m i. unfold node_update.
        destruct (node_eq_dec (actor, loc) m) as [<-|Hneq].
        + intro H. inversion H. lia.
        + intro H. pose proof (wf_inv_now _ Hwf _ _ H). lia.
      - intros m r Hr. destruct (wf_ret_inv _ Hwf _ _ Hr) as (i & Hi & Hlt).
        exists i. split; [|exact Hlt]. unfold node_update.
        destruct (node_eq_dec (actor, loc) m) as [<-|Hneq]; [congruence|exact Hi].
      - intros m r Hr. pose proof (wf_ret_now _ Hwf _ _ Hr). lia.
      - intro m. destruct m as [t l]. simpl.
        destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite TMap.gss. unfold node_update.
          destruct (node_eq_dec (actor, loc) (actor, l)) as [Heq|Hneq'].
          * inversion Heq; subst l. split.
            -- intros _. split; [eauto|exact Hret_none].
            -- intros _. reflexivity.
          * split.
            -- intro H. inversion H; subst. exfalso. apply Hneq'. reflexivity.
            -- intros Hp'. exfalso.
               assert (Hpend : tsa_is_pending s (actor, l)).
               { apply (wf_pending _ Hwf). exact Hp'. }
               unfold tsa_is_pending in Hpend; simpl in Hpend. congruence.
        + rewrite TMap.gso by exact Hneq. unfold node_update.
          destruct (node_eq_dec (actor, loc) (t, l)) as [Heq|Hneq'].
          * inversion Heq; subst. congruence.
          * exact (wf_pending _ Hwf (t, l)).
      - intros x y. split.
        + intros [Hedge|[-> [Hvert Hnp]]].
          * destruct (proj1 (wf_edges _ Hwf x y) Hedge) as (r & i & Hr & Hi & Hlt).
            exists r, i. repeat split; try assumption.
            unfold node_update.
            destruct (node_eq_dec (actor, loc) x) as [<-|Hneq]; [congruence|exact Hi].
          * destruct (proj1 (wf_vertex_inv _ Hwf y) Hvert) as [i Hi].
            assert (Hr : exists r, tsa_node_ret s y = Some r).
            { destruct (tsa_node_ret s y) as [r|] eqn:Hr; [eauto|].
              exfalso. apply Hnp. apply (wf_pending _ Hwf). eauto. }
            destruct Hr as [r Hr].
            exists r, (tsa_now s). repeat split; try assumption.
            -- unfold node_update. destruct (node_eq_dec (actor, loc) (actor, loc)); congruence.
            -- eapply wf_ret_now; eauto.
        + intros (r & i & Hr & Hi & Hlt).
          apply node_update_some in Hi.
          destruct Hi as [[-> ->]|[Hneq Hi]].
          * right. split; [reflexivity|].
            destruct (wf_ret_inv _ Hwf _ _ Hr) as (iy & Hiy & _).
            split.
            -- eapply wf_inv_vertex; eauto.
            -- intro Hp. apply (wf_pending _ Hwf) in Hp. destruct Hp as [_ Hp].
               congruence.
          * left. apply (wf_edges _ Hwf). eauto.
      - intros a N HN.
        destruct (wf_snapshot _ Hwf _ _ HN) as (t & Ht & Hmem).
        exists t. split; [exact Ht|]. intro m. rewrite Hmem.
        pose proof (proj1 (wf_snap_time _ Hwf _ _ Ht)) as Htnow.
        unfold node_update. destruct (node_eq_dec (actor, loc) m) as [<-|Hneq].
        + split.
          * intros (i & Hi & _). congruence.
          * intros (i & Hi & Hlt). inversion Hi; subst. lia.
        + reflexivity.
      - intros a t Ht. destruct (wf_snap_time _ Hwf _ _ Ht) as [Hlt HN].
        split; [lia|exact HN].
      - exact (wf_garbage _ Hwf).
      - intros m a st rt Hrem.
        destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (H1 & H2 & (i & Hi & Hlt) & Hblock).
        repeat split; try lia.
        + exists i. split; [|exact Hlt]. unfold node_update.
          destruct (node_eq_dec (actor, loc) m) as [<-|Hneq]; [congruence|exact Hi].
        + intros y iy Hiy Hlty Hedge.
          apply node_update_some in Hiy.
          destruct Hiy as [[-> ->]|[Hneq Hiy]].
          * exfalso. lia.
          * destruct Hedge as [Hedge|[-> _]]; [|congruence].
            eapply Hblock; eauto.
      - intros t ev1 ev2 H1 H2.
        pose proof (start_push_event s actor loc v t ev1 H1) as H1'.
        pose proof (start_push_event s actor loc v t ev2 H2) as H2'.
        clear H1 H2.
        destruct H1' as [[-> ->]|H1]; destruct H2' as [[-> Heq]|H2].
        + reflexivity.
        + exfalso. apply ghost_event_now in H2; [lia|exact Hwf].
        + exfalso. apply ghost_event_now in H1; [lia|exact Hwf].
        + eapply wf_unique; eauto.
      - intros a l1 l2 i1 i2 H1 H2 Hlt.
        apply node_update_some in H1. apply node_update_some in H2.
        destruct H2 as [[Heq2 ->]|[Hneq2 H2]].
        + inversion Heq2; subst a l2. clear Heq2.
          destruct H1 as [[Heq1 ->]|[Hneq1 H1]]; [lia|].
          assert (Hnp : ~ tsa_is_pending s (actor, l1)).
          { unfold tsa_is_pending; simpl. rewrite Hnone. discriminate. }
          destruct (tsa_node_ret s (actor, l1)) as [r1|] eqn:Hr1.
          * exists r1. split; [reflexivity|]. eapply wf_ret_now; eauto.
          * exfalso. apply Hnp. apply (wf_pending _ Hwf). eauto.
        + destruct H1 as [[Heq1 ->]|[Hneq1 H1]].
          * inversion Heq1; subst. exfalso.
            pose proof (wf_inv_now _ Hwf _ _ H2). lia.
          * eapply wf_same_actor; eauto.
    Qed.

    (** finish_push *)

    Lemma finish_push_event s actor loc t ev :
      TMap.find actor (tsa_pending_pushes s) = Some loc ->
      ghost_event_at (tsa_finish_push actor s) t ev ->
      (ev = GRet (actor, loc) /\ t = tsa_now s) \/ ghost_event_at s t ev.
    Proof.
      intros Hfind. unfold ghost_event_at, tsa_finish_push; simpl.
      rewrite Hfind.
      destruct ev; intro H; try (right; exact H).
      apply node_update_some in H. destruct H as [[-> ->]|[_ H]].
      - left. auto.
      - right. exact H.
    Qed.

    Lemma finish_push_wf s actor loc :
      tsa_ghost_wf s ->
      TMap.find actor (tsa_pending_pushes s) = Some loc ->
      tsa_ghost_wf (tsa_finish_push actor s).
    Proof.
      intros Hwf Hfind.
      destruct (wf_pending_node_ret s actor loc Hwf Hfind)
        as [Hret_none [i0 Hinv0]].
      pose proof (wf_inv_now _ Hwf _ _ Hinv0) as Hi0now.
      constructor; ghost_simpl.
      - exact (wf_vertex_inv _ Hwf).
      - intros m i H. pose proof (wf_inv_now _ Hwf _ _ H). lia.
      - intros m r Hr. rewrite Hfind in Hr. apply node_update_some in Hr.
        destruct Hr as [[-> ->]|[Hneq Hr]].
        + exists i0. split; [exact Hinv0|exact Hi0now].
        + exact (wf_ret_inv _ Hwf _ _ Hr).
      - intros m r Hr. rewrite Hfind in Hr. apply node_update_some in Hr.
        destruct Hr as [[-> ->]|[Hneq Hr]]; [lia|].
        pose proof (wf_ret_now _ Hwf _ _ Hr). lia.
      - intros [t l]. simpl. rewrite Hfind.
        destruct (Pos.eq_dec t actor) as [->|Hneq].
        + rewrite TMap.grs. unfold node_update.
          destruct (node_eq_dec (actor, loc) (actor, l)) as [Heq|Hneq'].
          * split; [discriminate|]. intros [_ Hbad]. discriminate.
          * split; [discriminate|]. intros Hp'.
            assert (Hpend : tsa_is_pending s (actor, l)).
            { apply (wf_pending _ Hwf). exact Hp'. }
            unfold tsa_is_pending in Hpend; simpl in Hpend.
            rewrite Hfind in Hpend. inversion Hpend; subst.
            exfalso. apply Hneq'. reflexivity.
        + rewrite TMap.gro by exact Hneq. unfold node_update.
          destruct (node_eq_dec (actor, loc) (t, l)) as [Heq|Hneq'].
          * inversion Heq; subst. congruence.
          * exact (wf_pending _ Hwf (t, l)).
      - intros x y. rewrite Hfind. rewrite (wf_edges _ Hwf x y). split.
        + intros (r & i & Hr & Hi & Hlt). exists r, i.
          repeat split; try assumption. unfold node_update.
          destruct (node_eq_dec (actor, loc) y) as [<-|Hneq];
            [congruence|exact Hr].
        + intros (r & i & Hr & Hi & Hlt). apply node_update_some in Hr.
          destruct Hr as [[-> ->]|[Hneq Hr]].
          * exfalso. pose proof (wf_inv_now _ Hwf _ _ Hi). lia.
          * eauto.
      - exact (wf_snapshot _ Hwf).
      - intros a t Ht. destruct (wf_snap_time _ Hwf _ _ Ht) as [Hlt HN].
        split; [lia|exact HN].
      - exact (wf_garbage _ Hwf).
      - intros m a st rt Hrem.
        destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (H1 & H2 & H3 & Hblock).
        repeat split; try lia; try assumption.
      - intros t ev1 ev2 H1 H2.
        pose proof (finish_push_event s actor loc t ev1 Hfind H1) as H1'.
        pose proof (finish_push_event s actor loc t ev2 Hfind H2) as H2'.
        clear H1 H2.
        destruct H1' as [[-> ->]|H1]; destruct H2' as [[-> Heq]|H2].
        + reflexivity.
        + exfalso. apply ghost_event_now in H2; [lia|exact Hwf].
        + exfalso. apply ghost_event_now in H1; [lia|exact Hwf].
        + eapply wf_unique; eauto.
      - intros a l1 l2 i1 i2 H1 H2 Hlt. rewrite Hfind.
        destruct (wf_same_actor _ Hwf _ _ _ _ _ H1 H2 Hlt) as (r1 & Hr1 & Hlt1).
        exists r1. split; [|exact Hlt1]. unfold node_update.
        destruct (node_eq_dec (actor, loc) (a, l1)) as [Heq|Hneq]; [|exact Hr1].
        inversion Heq; subst. congruence.
    Qed.

    (** start_snapshot *)

    Lemma start_snapshot_event s actor t ev :
      ghost_event_at (tsa_start_snapshot actor s) t ev ->
      (ev = GSnap actor /\ t = tsa_now s) \/ ghost_event_at s t ev.
    Proof.
      unfold ghost_event_at, tsa_start_snapshot; simpl.
      destruct ev; intro H; try (right; exact H).
      destruct (Pos.eq_dec actor0 actor) as [->|Hneq].
      - rewrite TMap.gss in H. inversion H. left. auto.
      - rewrite TMap.gso in H by exact Hneq. right. exact H.
    Qed.

    Lemma start_snapshot_wf s actor :
      tsa_ghost_wf s ->
      TMap.find actor (tsa_snapshots s) = None ->
      tsa_ghost_wf (tsa_start_snapshot actor s).
    Proof.
      intros Hwf Hnone.
      constructor; ghost_simpl.
      - exact (wf_vertex_inv _ Hwf).
      - intros m i H. pose proof (wf_inv_now _ Hwf _ _ H). lia.
      - exact (wf_ret_inv _ Hwf).
      - intros m r Hr. pose proof (wf_ret_now _ Hwf _ _ Hr). lia.
      - exact (wf_pending _ Hwf).
      - exact (wf_edges _ Hwf).
      - intros a N HN.
        destruct (Pos.eq_dec a actor) as [->|Hneq].
        + rewrite TMap.gss in HN. inversion HN; subst N.
          exists (tsa_now s). rewrite TMap.gss. split; [reflexivity|].
          intro m. unfold tsa_is_vertex. rewrite (wf_vertex_inv _ Hwf m).
          split.
          * intros [i Hi]. exists i. split; [exact Hi|].
            eapply wf_inv_now; eauto.
          * intros (i & Hi & _). eauto.
        + rewrite TMap.gso in HN by exact Hneq. rewrite TMap.gso by exact Hneq.
          exact (wf_snapshot _ Hwf a N HN).
      - intros a t Ht.
        destruct (Pos.eq_dec a actor) as [->|Hneq].
        + rewrite TMap.gss in Ht. inversion Ht; subst t. split; [lia|].
          rewrite TMap.gss. eauto.
        + rewrite TMap.gso in Ht by exact Hneq. rewrite TMap.gso by exact Hneq.
          destruct (wf_snap_time _ Hwf _ _ Ht) as [Hlt HN]. split; [lia|exact HN].
      - exact (wf_garbage _ Hwf).
      - intros m a st rt Hrem.
        destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (H1 & H2 & H3 & Hblock).
        repeat split; try lia; try assumption.
      - intros t ev1 ev2 H1 H2.
        pose proof (start_snapshot_event s actor t ev1 H1) as H1'.
        pose proof (start_snapshot_event s actor t ev2 H2) as H2'.
        clear H1 H2.
        destruct H1' as [[-> ->]|H1]; destruct H2' as [[-> Heq]|H2].
        + reflexivity.
        + exfalso. apply ghost_event_now in H2; [lia|exact Hwf].
        + exfalso. apply ghost_event_now in H1; [lia|exact Hwf].
        + eapply wf_unique; eauto.
      - exact (wf_same_actor _ Hwf).
    Qed.

    (** clear_snapshot (failed trypop) *)

    Lemma clear_snapshot_event s actor t ev :
      ghost_event_at (tsa_clear_snapshot actor s) t ev ->
      ghost_event_at s t ev.
    Proof.
      unfold ghost_event_at, tsa_clear_snapshot; simpl.
      destruct ev; intro H; try exact H.
      destruct (Pos.eq_dec actor0 actor) as [->|Hneq].
      - rewrite TMap.grs in H. discriminate.
      - rewrite TMap.gro in H by exact Hneq. exact H.
    Qed.

    Lemma clear_snapshot_wf s actor :
      tsa_ghost_wf s ->
      tsa_ghost_wf (tsa_clear_snapshot actor s).
    Proof.
      intros Hwf.
      constructor; ghost_simpl.
      - exact (wf_vertex_inv _ Hwf).
      - intros m i H. pose proof (wf_inv_now _ Hwf _ _ H). lia.
      - exact (wf_ret_inv _ Hwf).
      - intros m r Hr. pose proof (wf_ret_now _ Hwf _ _ Hr). lia.
      - exact (wf_pending _ Hwf).
      - exact (wf_edges _ Hwf).
      - intros a N HN.
        destruct (Pos.eq_dec a actor) as [->|Hneq].
        + rewrite TMap.grs in HN. discriminate.
        + rewrite TMap.gro in HN by exact Hneq. rewrite TMap.gro by exact Hneq.
          exact (wf_snapshot _ Hwf a N HN).
      - intros a t Ht.
        destruct (Pos.eq_dec a actor) as [->|Hneq].
        + rewrite TMap.grs in Ht. discriminate.
        + rewrite TMap.gro in Ht by exact Hneq. rewrite TMap.gro by exact Hneq.
          destruct (wf_snap_time _ Hwf _ _ Ht) as [Hlt HN]. split; [lia|exact HN].
      - exact (wf_garbage _ Hwf).
      - intros m a st rt Hrem.
        destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (H1 & H2 & H3 & Hblock).
        repeat split; try lia; try assumption.
      - intros t ev1 ev2 H1 H2.
        apply clear_snapshot_event in H1. apply clear_snapshot_event in H2.
        eapply wf_unique; eauto.
      - exact (wf_same_actor _ Hwf).
    Qed.

    (** remove_node (successful trypop) *)

    Lemma remove_node_event s actor n st t ev :
      TMap.find actor (tsa_snap_time s) = Some st ->
      ghost_event_at (tsa_remove_node actor n s) t ev ->
      (ev = GRem n /\ t = tsa_now s) \/
      (ev = GSnapOf n /\ t = st) \/
      (ghost_event_at s t ev /\ ev <> GSnap actor).
    Proof.
      intros Hst. unfold ghost_event_at, tsa_remove_node; simpl.
      rewrite Hst.
      destruct ev; intro H.
      - right; right. split; [exact H|discriminate].
      - right; right. split; [exact H|discriminate].
      - destruct (Pos.eq_dec actor0 actor) as [->|Hneq].
        + rewrite TMap.grs in H. discriminate.
        + rewrite TMap.gro in H by exact Hneq. right; right.
          split; [exact H|]. intro Heq. inversion Heq. congruence.
      - destruct H as (a & st' & H). apply node_update_some in H.
        destruct H as [[-> Heq]|[Hneq H]].
        + inversion Heq; subst. left. auto.
        + right; right. split; [|discriminate]. eauto.
      - destruct H as (a & rt & H). apply node_update_some in H.
        destruct H as [[-> Heq]|[Hneq H]].
        + inversion Heq; subst. right; left. auto.
        + right; right. split; [|discriminate]. eauto.
    Qed.

    Lemma remove_node_wf s actor n N (v : A) :
      tsa_ghost_wf s ->
      TMap.find actor (tsa_snapshots s) = Some N ->
      lp_top (fun n' => N n' /\ ~ tsa_garbage s n') (tsa_edges s) n ->
      tsa_vertices s n = Some v ->
      tsa_ghost_wf (tsa_remove_node actor n s).
    Proof.
      intros Hwf HN Htop Hv.
      destruct (wf_snapshot _ Hwf _ _ HN) as (st & Hst & Hmem).
      destruct (wf_snap_time _ Hwf _ _ Hst) as [Hstnow _].
      destruct Htop as [[HNn Hnog] Htop].
      assert (Hrem_none : tsa_removals s n = None).
      { destruct (tsa_removals s n) as [rec|] eqn:Hrec; [|reflexivity].
        exfalso. apply Hnog. apply (wf_garbage _ Hwf). eauto. }
      constructor; ghost_simpl.
      - exact (wf_vertex_inv _ Hwf).
      - intros m i H. pose proof (wf_inv_now _ Hwf _ _ H). lia.
      - exact (wf_ret_inv _ Hwf).
      - intros m r Hr. pose proof (wf_ret_now _ Hwf _ _ Hr). lia.
      - exact (wf_pending _ Hwf).
      - exact (wf_edges _ Hwf).
      - intros a N' HN'.
        destruct (Pos.eq_dec a actor) as [->|Hneq].
        + rewrite TMap.grs in HN'. discriminate.
        + rewrite TMap.gro in HN' by exact Hneq. rewrite TMap.gro by exact Hneq.
          exact (wf_snapshot _ Hwf a N' HN').
      - intros a t Ht.
        destruct (Pos.eq_dec a actor) as [->|Hneq].
        + rewrite TMap.grs in Ht. discriminate.
        + rewrite TMap.gro in Ht by exact Hneq. rewrite TMap.gro by exact Hneq.
          destruct (wf_snap_time _ Hwf _ _ Ht) as [Hlt HN']. split; [lia|exact HN'].
      - intro m. rewrite Hst. unfold set_add. rewrite (wf_garbage _ Hwf m).
        unfold node_update. destruct (node_eq_dec n m) as [<-|Hneq].
        + split; [intros _; eauto|]. intros _. now left.
        + split.
          * intros [Heq|H]; [congruence|exact H].
          * intros H. right. exact H.
      - intros m a st' rt Hrem. rewrite Hst in Hrem. rewrite Hst.
        apply node_update_some in Hrem.
        destruct Hrem as [[-> Heq]|[Hneq Hrem]].
        + inversion Heq; subst a st' rt. clear Heq.
          repeat split; try lia.
          * apply Hmem. exact HNn.
          * intros y i Hiy Hlty Hedge.
            assert (HNy : N y). { apply Hmem. eauto. }
            assert (Hgy : tsa_garbage s y).
            { destruct (classic (tsa_garbage s y)) as [Hg|Hng]; [exact Hg|].
              exfalso. apply (Htop y (conj HNy Hng) Hedge). }
            apply (wf_garbage _ Hwf) in Hgy. destruct Hgy as [[[a' st'] rt'] Hrec].
            destruct (wf_removal _ Hwf _ _ _ _ Hrec) as (_ & Hrtnow & _).
            exists a', st', rt'. split; [|exact Hrtnow].
            unfold node_update. destruct (node_eq_dec n y) as [<-|Hneq].
            -- exfalso. apply Hnog. apply (wf_garbage _ Hwf). eauto.
            -- exact Hrec.
        + destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (H1 & H2 & H3 & Hblock).
          repeat split; try lia; try assumption.
          intros y i Hiy Hlty Hedge.
          destruct (Hblock y i Hiy Hlty Hedge) as (a' & st'' & rt' & Hrec & Hlt).
          exists a', st'', rt'. split; [|exact Hlt].
          unfold node_update. destruct (node_eq_dec n y) as [<-|Hneq'].
          -- congruence.
          -- exact Hrec.
      - intros t ev1 ev2 H1 H2.
        pose proof (remove_node_event s actor n st t ev1 Hst H1) as H1'.
        pose proof (remove_node_event s actor n st t ev2 Hst H2) as H2'.
        clear H1 H2.
        assert (Hsnap_unique : forall ev, ghost_event_at s st ev -> ev = GSnap actor).
        { intros ev Hev. eapply wf_unique; [exact Hwf|exact Hev|exact Hst]. }
        destruct H1' as [[-> ->]|[[-> ->]|[H1 Hne1]]];
          destruct H2' as [[-> Heq]|[[-> Heq]|[H2 Hne2]]];
          subst; try reflexivity; try lia;
          try (exfalso; apply ghost_event_now in H2; [lia|exact Hwf]);
          try (exfalso; apply ghost_event_now in H1; [lia|exact Hwf]);
          try (exfalso; apply Hne2; apply Hsnap_unique; exact H2);
          try (exfalso; apply Hne1; apply Hsnap_unique; exact H1).
        eapply wf_unique; eauto.
      - exact (wf_same_actor _ Hwf).
    Qed.

    (** The step relation preserves well-formedness. *)

    Lemma step_preserves_wf e c c' :
      @StepTryStackAux A e c c' -> control_wf c -> control_wf c'.
    Proof.
      intros Hstep Hwf. inversion Hstep; subst; simpl in *.
      - eapply start_push_wf; eauto.
      - eapply finish_push_wf; eauto.
      - exact Hwf.
      - exact Hwf.
      - eapply start_snapshot_wf; eauto.
      - eapply remove_node_wf; eauto.
      - eapply clear_snapshot_wf; eauto.
    Qed.

  End Ghost.
End TryStackAuxGhost.
