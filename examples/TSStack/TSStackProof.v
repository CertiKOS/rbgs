Require Import FMapPositive.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Equality.
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
Require Import CompLinLayer.

Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.Common.AtomicLTS.
Require Import examples.Stacks.StackSpec.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.TryStackAuxSpec.
Require Import examples.TSStack.TryStackSpec.
Require Import examples.TSStack.TSStackSpec.
Require Import examples.TSStack.TSStack.
Require Import examples.TSStack.ListPoolProof.
Require Import examples.TSStack.TryStackProof.


(** Correctness proof for the TSStack layer over TryStack (Section 7.2 and
    Appendix A.4 of the paper).

    The abstract configuration is a set of atomic-stack linearizations of
    the concrete DAG.  Following the paper, the invariant is stated as a
    completeness property: for every topological order of the live
    vertices, and every choice of which pending pushes have already been
    linearized, a matching possibility is present.  Soundness is only
    tracked for linearization tokens; the paper's [I_stack] is not needed
    (see the verification plan for why it is not even preserved). *)
Module TSStackProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSet.
  Import TPSimulationSet.TPSimulation CompLinLayer.
  Import AtomicLTS.
  Import ListPoolSpec TryStackAuxSpec TryStackSpec TSStackSpec TSStackImpl.
  Import (coercions, canonicals, notations) Sig.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {A : Type} (D : ThreadDomain.t).

    Definition E : layer_interface := @TSStackImpl.E A D.
    Definition F : layer_interface := @TSStackImpl.F A D.

    Definition concrete_state := State (li_lts E).
    Definition abstract_state := State (li_lts F).
    Definition lin_state := @LinState (li_sig F).
    Definition proof_state :=
      @SetPossState.ProofStateSet _ _ (li_lts E) (li_lts F).
    Definition assertion := @Logics.Assertion proof_state.
    Definition rg_relation :=
      @AssertionsSet.A.RGRelation _ _ (li_lts E) (li_lts F).
    Definition config := @AbstractConfig _ (li_lts F).

    Definition st_push (v : A) : Sig.op (li_sig F) := StackSpec.push v.
    Definition st_pop : Sig.op (li_sig F) := StackSpec.pop.

    Implicit Types (s : @TryStackState A).
    Implicit Types (π : tmap lin_state).
    Implicit Types (N ms order : list LPNodeId).
    Implicit Types (stk vals : list A).

    Definition push_inv_token (v : A) : lin_state := ls_inv (st_push v).
    Definition push_lini_token (v : A) : lin_state := ls_lini (st_push v).
    Definition push_ret_token (v : A) : lin_state := ls_linr (st_push v) tt.

    (** * Concrete payload *)

    Definition payload (c : @TryStackControl A) : @TryStackState A :=
      match c with
      | TSReady s => s
      | TSAtomicPending s _ _ => s
      end.

    Definition control_owned (actor : tid) (c : @TryStackControl A) : Prop :=
      match c with
      | TSReady _ => True
      | TSAtomicPending _ owner _ => owner = actor
      end.

    Definition graph_of (w : proof_state) : @TryStackState A :=
      payload (SetPossState.σ w).

    (** * Graph vocabulary (Appendix A.4) *)

    Definition live s (n : LPNodeId) : Prop := ts_is_live s n.

    (** The paper's [pending(π, P)]: a pending vertex whose thread has not
        linearized its push in the token map [π]. *)
    Definition omitted s π (n : LPNodeId) : Prop :=
      ts_is_pending s n /\
      exists v, TMap.find (fst n) π = Some (push_inv_token v).

    (** Newest-first lists compatible with the edge relation: no later
        element has an edge to an earlier one. *)
    Fixpoint ecompat (Ed : LPEdges) N : Prop :=
      match N with
      | nil => True
      | n :: N' => (forall m, In m N' -> ~ Ed m n) /\ ecompat Ed N'
      end.

    (** The paper's [perm(X, E)]. *)
    Definition perm s (X : LPNodeSet) N : Prop :=
      NoDup N /\ ecompat (ts_edges s) N /\ forall n, In n N <-> X n.

    Definition values_of s N stk : Prop :=
      Forall2 (fun n v => ts_vertices s n = Some v) N stk.

    (** [dom(V) \ g \ pending(π, P)]. *)
    Definition stack_domain s π : LPNodeSet :=
      fun n => live s n /\ ~ omitted s π n.

    (** [N ∈ perm(dom(V) \ g \ pending(π,P), E)] and [ρ = map(V, N)]. *)
    Definition justified s (ρ : abstract_state) π N : Prop :=
      perm s (stack_domain s π) N /\
      exists stk, values_of s N stk /\ ρ = Idle stk.

    (** * The paper's invariants *)

    Definition I_stack s (Δ : config) : Prop :=
      forall ρ π, Δ ρ π -> exists N, justified s ρ π N.

    Definition pending_set s (P' : LPNodeSet) : Prop :=
      forall n, P' n -> ts_is_pending s n.

    (** The token clauses of [I_graph]: threads whose pending vertex is
        outside [P'] have linearized, those inside [P'] (and live) have
        not. *)
    Definition graph_tokens s (P' : LPNodeSet) π : Prop :=
      forall β l, TMap.find β (ts_pending_pushes s) = Some l ->
        exists v, ts_vertices s (pair β l) = Some v /\
          (~ P' (pair β l) -> TMap.find β π = Some (push_ret_token v)) /\
          (P' (pair β l) -> live s (pair β l) ->
            TMap.find β π = Some (push_inv_token v)).

    Definition I_graph s (Δ : config) : Prop :=
      forall P', pending_set s P' ->
      forall N, perm s (fun n => live s n /\ ~ P' n) N ->
      forall stk, values_of s N stk ->
      exists π, Δ (Idle stk) π /\ graph_tokens s P' π.

    (** [I_pending] without its edge clause, which is kept in [graph_wf].
        The nonempty halves of the paper's [◦ ⊕ •] are consequences of
        [I_graph] ([pending_live_both_tokens]). *)
    Definition I_pending s (Δ : config) : Prop :=
      forall β l, TMap.find β (ts_pending_pushes s) = Some l ->
        exists v, ts_vertices s (pair β l) = Some v /\
          (ts_garbage s (pair β l) ->
            forall ρ π, Δ ρ π -> TMap.find β π = Some (push_ret_token v)) /\
          (~ ts_garbage s (pair β l) ->
            forall ρ π, Δ ρ π ->
              TMap.find β π = Some (push_inv_token v) \/
              TMap.find β π = Some (push_ret_token v)).

    (** Concrete facts the paper leaves implicit, including the finiteness
        witness for [perm] and [I_pending]'s edge clause. *)
    Definition graph_wf s : Prop :=
      (exists order, NoDup order /\ ecompat (ts_edges s) order /\
        forall n, In n order <-> ts_is_vertex s n) /\
      (forall n, ts_garbage s n -> ts_is_vertex s n) /\
      (forall β l, TMap.find β (ts_pending_pushes s) = Some l ->
        ts_is_vertex s (pair β l)) /\
      (forall n m, ts_edges s n m -> ts_is_vertex s n /\ ts_is_vertex s m) /\
      (forall n m, ts_edges s n m -> ~ ts_is_pending s m).

    Definition I_state s (Δ : config) : Prop :=
      graph_wf s /\ I_stack s Δ /\ I_graph s Δ /\ I_pending s Δ.

    Definition I : assertion :=
      fun w => I_state (graph_of w) (SetPossState.Δ w).

    (** * The paper's [push] relation *)

    (** One pending live push is linearized by an abstract atomic push. *)
    Variant lin_step s :
        abstract_state -> tmap lin_state ->
        abstract_state -> tmap lin_state -> Prop :=
    | lin_push β l v stk π :
        TMap.find β (ts_pending_pushes s) = Some l ->
        ts_vertices s (pair β l) = Some v ->
        ~ ts_garbage s (pair β l) ->
        TMap.find β π = Some (push_inv_token v) ->
        lin_step s (Idle stk) π
          (Idle (v :: stk))
          (TMap.add β (push_ret_token v) (TMap.add β (push_lini_token v) π)).

    Inductive lin_closure s :
        abstract_state -> tmap lin_state ->
        abstract_state -> tmap lin_state -> Prop :=
    | lin_refl ρ π : lin_closure s ρ π ρ π
    | lin_trans ρ π ρ' π' ρ'' π'' :
        lin_step s ρ π ρ' π' ->
        lin_closure s ρ' π' ρ'' π'' ->
        lin_closure s ρ π ρ'' π''.

    (** * Guarantees (paper's [G_push-inv], [G_push-ret], [G_pop],
        [G_pop-emp]) *)

    Definition pop_ret_token (r : option A) : lin_state :=
      ls_linr st_pop r.
    Definition pop_lini_token : lin_state := ls_lini st_pop.

    Variant G_push_inv (α : tid) : rg_relation :=
    | g_push_inv s l v (w w' : proof_state) :
        SetPossState.σ w = TSReady s ->
        TMap.find α (ts_pending_pushes s) = None ->
        ts_fresh_node s (pair α l) ->
        (forall ρ π, SetPossState.Δ w ρ π ->
          TMap.find α π = Some (push_inv_token v)) ->
        SetPossState.σ w' = TSReady (ts_start_push α l v s) ->
        (forall ρ' π', SetPossState.Δ w' ρ' π' <->
          exists ρ π, SetPossState.Δ w ρ π /\
            lin_closure (ts_start_push α l v s) ρ π ρ' π') ->
        G_push_inv α w w'.

    Variant G_push_ret (α : tid) : rg_relation :=
    | g_push_ret s l v (w w' : proof_state) :
        SetPossState.σ w = TSReady s ->
        TMap.find α (ts_pending_pushes s) = Some l ->
        ts_vertices s (pair α l) = Some v ->
        SetPossState.σ w' = TSReady (ts_finish_push α s) ->
        (forall ρ π, SetPossState.Δ w' ρ π <->
          SetPossState.Δ w ρ π /\ TMap.find α π = Some (push_ret_token v)) ->
        G_push_ret α w w'.

    (** The retained possibilities are those justified by a permutation
        headed by the popped vertex [n]; see the verification plan. *)
    Variant G_pop (α : tid) : rg_relation :=
    | g_pop s n v (w w' : proof_state) :
        SetPossState.σ w = TSAtomicPending s α ts_trypop ->
        lp_top (fun m => ts_is_live s m) (ts_edges s) n ->
        ts_vertices s n = Some v ->
        (forall ρ π, SetPossState.Δ w ρ π ->
          TMap.find α π = Some (ls_inv st_pop)) ->
        SetPossState.σ w' = TSReady (ts_mark_garbage n s) ->
        (forall ρ' π', SetPossState.Δ w' ρ' π' <->
          exists stk π,
            SetPossState.Δ w (Idle (v :: stk)) π /\
            (ts_is_pending s n ->
              TMap.find (fst n) π = Some (push_ret_token v)) /\
            (exists N', justified s (Idle (v :: stk)) π (n :: N')) /\
            ρ' = Idle stk /\
            π' = TMap.add α (pop_ret_token (Some v))
                   (TMap.add α pop_lini_token π)) ->
        G_pop α w w'.

    Variant G_pop_emp (α : tid) : rg_relation :=
    | g_pop_emp s (w w' : proof_state) :
        SetPossState.σ w = TSAtomicPending s α ts_trypop ->
        ts_all_vertices_garbage s ->
        (forall ρ π, SetPossState.Δ w ρ π ->
          TMap.find α π = Some (ls_inv st_pop)) ->
        SetPossState.σ w' = TSReady s ->
        (forall ρ' π', SetPossState.Δ w' ρ' π' <->
          exists π, SetPossState.Δ w (Idle nil) π /\
            ρ' = Idle nil /\
            π' = TMap.add α (pop_ret_token None)
                   (TMap.add α pop_lini_token π)) ->
        G_pop_emp α w w'.

    (** The Coq two-event encoding of the atomic [trypop]: entering and
        leaving the actor-owned atomic control state without an abstract
        step. *)
    Variant G_control (α : tid) : rg_relation :=
    | g_control_enter s (w w' : proof_state) :
        SetPossState.σ w = TSReady s ->
        SetPossState.σ w' = TSAtomicPending s α ts_trypop ->
        SetPossState.Δ w' = SetPossState.Δ w ->
        G_control α w w'
    | g_control_leave s (w w' : proof_state) :
        SetPossState.σ w = TSAtomicPending s α ts_trypop ->
        SetPossState.σ w' = TSReady s ->
        SetPossState.Δ w' = SetPossState.Δ w ->
        G_control α w w'.

    Definition G (α : tid) : rg_relation :=
      fun w w' =>
        G_push_inv α w w' \/ G_push_ret α w w' \/
        G_pop α w w' \/ G_pop_emp α w w' \/ G_control α w w'.

    Definition R (observer : tid) : rg_relation :=
      fun w w' =>
        (exists actor, actor <> observer /\ G actor w w') \/
        (exists actor, actor <> observer /\ GINV actor w w') \/
        (exists actor, actor <> observer /\ GRET actor w w') \/
        w = w'.

    (** * Assertions of the proof outlines (Fig. 34, Fig. 35) *)

    Definition Active (actor : tid) (op : Sig.op (li_sig F)) : assertion :=
      I //\\ ALin actor (ls_inv op).

    Definition NoPending (actor : tid) : assertion :=
      fun w => TMap.find actor (ts_pending_pushes (graph_of w)) = None.

    Definition Completed (actor : tid) (op : Sig.op (li_sig F))
        (ret : Sig.ar op) : assertion :=
      I //\\ ALin actor (ls_linr op ret) //\\ NoPending actor.

    Definition Inside (actor : tid) (op : Sig.op (li_sig F)) : assertion :=
      Active actor op //\\ ⌜ThreadDomain.contains D actor⌝.

    (** [I ∧ P[α] ≠ ⊥] of Fig. 34. *)
    Definition PushPending (actor : tid) (v : A) : assertion :=
      I //\\ ⌜ThreadDomain.contains D actor⌝ //\\
      (fun w => exists l,
        TMap.find actor (ts_pending_pushes (graph_of w)) = Some l /\
        ts_vertices (graph_of w) (pair actor l) = Some v).

    Definition PopAtomic (actor : tid) : assertion :=
      Inside actor st_pop //\\
      (fun w => exists s,
        SetPossState.σ w = TSAtomicPending s actor ts_trypop).

    Definition PopPost (actor : tid) (ret : @TResult A) : assertion :=
      match ret with
      | TSuccNode v _ _ => Completed actor st_pop (Some v)
      | TSuccEmpty => Completed actor st_pop None
      | TFail => Inside actor st_pop
      end.

    (** * List utilities *)

    Lemma ecompat_mono (E1 E2 : LPEdges) N :
      (forall x y, E1 x y -> E2 x y) ->
      ecompat E2 N -> ecompat E1 N.
    Proof.
      intros Hsub. induction N as [|n N IH]; simpl.
      - trivial.
      - intros [Hhead Htail]. split; [|now apply IH].
        intros m Hin HE. apply (Hhead m Hin). now apply Hsub.
    Qed.

    Lemma ecompat_app_inv_r Ed N1 N2 :
      ecompat Ed (N1 ++ N2) -> ecompat Ed N2.
    Proof.
      induction N1 as [|n N1 IH]; simpl; intros H.
      - exact H.
      - apply IH. exact (proj2 H).
    Qed.

    Lemma ecompat_app_later Ed N1 n N2 :
      ecompat Ed (N1 ++ n :: N2) ->
      forall m, In m N1 -> ~ Ed n m.
    Proof.
      induction N1 as [|x N1 IH]; simpl; intros H m Hin.
      - contradiction.
      - destruct H as [Hhead Htail]. destruct Hin as [->|Hin].
        + apply Hhead. apply in_or_app. right. left. reflexivity.
        + now apply IH.
    Qed.

    Lemma ecompat_cons_iff Ed n N :
      ecompat Ed (n :: N) <->
      (forall m, In m N -> ~ Ed m n) /\ ecompat Ed N.
    Proof. reflexivity. Qed.

    (** Selecting a sublist by an arbitrary (classically decided)
        predicate preserves duplicate-freeness and compatibility. *)
    Lemma select_sublist (Keep : LPNodeId -> Prop) Ed order :
      NoDup order -> ecompat Ed order ->
      exists N, NoDup N /\ ecompat Ed N /\
        forall n, In n N <-> (In n order /\ Keep n).
    Proof.
      induction order as [|h order IH]; intros Hnodup Hcompat.
      - exists nil. repeat split; try constructor; simpl; tauto.
      - apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hnotin Hnodup'].
        destruct Hcompat as [Hhead Hcompat'].
        destruct (IH Hnodup' Hcompat') as [N [HnodupN [HcompatN Hmem]]].
        destruct (classic (Keep h)) as [Hkeep|Hdrop].
        + exists (h :: N). split; [|split].
          * constructor; [|exact HnodupN].
            intro Hin. apply Hmem in Hin as [Hin _]. contradiction.
          * split; [|exact HcompatN].
            intros m Hin. apply Hmem in Hin as [Hin _]. now apply Hhead.
          * intros n. simpl. rewrite Hmem. split.
            -- intros [->|[Hin Hk]]; tauto.
            -- intros [[->|Hin] Hk]; tauto.
        + exists N. split; [exact HnodupN|]. split; [exact HcompatN|].
          intros n. simpl. rewrite Hmem. split.
          * intros [Hin Hk]; tauto.
          * intros [[->|Hin] Hk]; [contradiction|tauto].
    Qed.

    Lemma NoDup_app_left (l1 l2 : list LPNodeId) :
      NoDup (l1 ++ l2) -> NoDup l1.
    Proof.
      induction l1 as [|x l1 IH]; intros H; simpl in *; [constructor|].
      apply NoDup_cons_iff in H. destruct H as [Hnotin H].
      constructor; [|now apply IH].
      intro Hin. apply Hnotin. apply in_or_app. now left.
    Qed.

    Lemma NoDup_app_right (l1 l2 : list LPNodeId) :
      NoDup (l1 ++ l2) -> NoDup l2.
    Proof.
      induction l1 as [|x l1 IH]; intros H; simpl in *; [exact H|].
      apply NoDup_cons_iff in H. now apply IH.
    Qed.

    Lemma NoDup_app_disjoint (l1 l2 : list LPNodeId) x :
      NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
    Proof.
      induction l1 as [|y l1 IH]; intros H Hin1 Hin2; simpl in *; [contradiction|].
      apply NoDup_cons_iff in H. destruct H as [Hnotin H].
      destruct Hin1 as [Heq|Hin1].
      - subst y. apply Hnotin. apply in_or_app. now right.
      - now apply IH.
    Qed.

    Lemma values_exist s N :
      (forall n, In n N -> ts_is_vertex s n) ->
      exists stk, values_of s N stk.
    Proof.
      induction N as [|n N IH]; intros Hvertex.
      - exists nil. constructor.
      - destruct (IH (fun m Hm => Hvertex m (or_intror Hm))) as [stk Hstk].
        assert (Hn : ts_is_vertex s n) by (apply Hvertex; now left).
        unfold ts_is_vertex in Hn.
        destruct (ts_vertices s n) as [v|] eqn:Hv; [|congruence].
        exists (v :: stk). constructor; assumption.
    Qed.

    Lemma values_of_vertex s N stk n :
      values_of s N stk -> In n N -> ts_is_vertex s n.
    Proof.
      intros Hvals Hin. induction Hvals as [|m v N stk Hm Hvals IH].
      - contradiction.
      - destruct Hin as [->|Hin].
        + unfold ts_is_vertex. congruence.
        + now apply IH.
    Qed.

    Lemma values_of_same_vertices s s' N stk :
      (forall n, In n N -> ts_vertices s n = ts_vertices s' n) ->
      values_of s N stk -> values_of s' N stk.
    Proof.
      intros Hsame Hvals. induction Hvals as [|n v N stk Hn Hvals IH].
      - constructor.
      - constructor.
        + rewrite <- Hsame; [exact Hn|now left].
        + apply IH. intros m Hm. apply Hsame. now right.
    Qed.

    Lemma pending_unique s m m' :
      ts_is_pending s m -> ts_is_pending s m' -> fst m = fst m' -> m = m'.
    Proof.
      unfold ts_is_pending. intros Hm Hm' Hfst.
      destruct m as [β l], m' as [β' l']. simpl in *. subst β'.
      rewrite Hm in Hm'. injection Hm' as ->. reflexivity.
    Qed.

    (** * Token-map utilities *)

    Lemma find_add_add k x y π β :
      TMap.find β (TMap.add k x (TMap.add k y π)) =
      TMap.find β (TMap.add k x π).
    Proof.
      destruct (Pos.eq_dec β k) as [->|Hneq].
      - now rewrite !TMap.gss.
      - now rewrite !TMap.gso by congruence.
    Qed.

    Lemma push_tokens_distinct (v v' : A) :
      push_inv_token v <> push_ret_token v'.
    Proof. discriminate. Qed.

    Lemma perm_exists s (X : LPNodeSet) :
      graph_wf s -> (forall n, X n -> ts_is_vertex s n) ->
      exists N, perm s X N.
    Proof.
      intros [[order [Hnodup [Hcompat Hall]]] _] Hsub.
      destruct (select_sublist X (ts_edges s) order Hnodup Hcompat)
        as [N [HnodupN [HcompatN Hmem]]].
      exists N. split; [exact HnodupN|]. split; [exact HcompatN|].
      intros n. rewrite Hmem. split.
      - intros [_ Hk]. exact Hk.
      - intros Hk. split; [|exact Hk]. apply Hall. now apply Hsub.
    Qed.

    Lemma perm_vertices s (X : LPNodeSet) N n :
      (forall m, X m -> ts_is_vertex s m) ->
      perm s X N -> In n N -> ts_is_vertex s n.
    Proof.
      intros Hsub [_ [_ Hmem]] Hin. apply Hsub. now apply Hmem.
    Qed.

    Lemma perm_ext s (X X' : LPNodeSet) N :
      (forall n, X n <-> X' n) -> perm s X N -> perm s X' N.
    Proof.
      intros Hext [Hnodup [Hcompat Hmem]].
      split; [exact Hnodup|]. split; [exact Hcompat|].
      intros n. rewrite Hmem. apply Hext.
    Qed.

    Lemma perm_edges_ext s s' (X : LPNodeSet) N :
      ts_edges s = ts_edges s' -> perm s X N -> perm s' X N.
    Proof.
      intros Heq [Hnodup [Hcompat Hmem]].
      split; [exact Hnodup|]. split; [|exact Hmem]. now rewrite <- Heq.
    Qed.

    Lemma ecompat_edges_ext (E1 E2 : LPEdges) N :
      (forall x y, In x N -> In y N -> (E1 x y <-> E2 x y)) ->
      ecompat E1 N -> ecompat E2 N.
    Proof.
      induction N as [|n N IH]; simpl; intros Hext.
      - trivial.
      - intros [Hhead Htail]. split.
        + intros m Hin HE. apply (Hhead m Hin). apply Hext; auto.
        + apply IH; [|exact Htail]. intros x y Hx Hy. apply Hext; auto.
    Qed.

    Lemma live_vertex s n : live s n -> ts_is_vertex s n.
    Proof. intros [Hv _]. exact Hv. Qed.

    (** * Linearizing pending pushes inside a possibility *)

    Lemma lin_closure_snoc s ρ π ρ' π' ρ'' π'' :
      lin_closure s ρ π ρ' π' ->
      lin_step s ρ' π' ρ'' π'' ->
      lin_closure s ρ π ρ'' π''.
    Proof.
      intros Hclos Hstep. induction Hclos.
      - eapply lin_trans; [exact Hstep|constructor].
      - eapply lin_trans; [exact H|now apply IHHclos].
    Qed.

    Lemma lin_closure_app s ρ π ρ' π' ρ'' π'' :
      lin_closure s ρ π ρ' π' ->
      lin_closure s ρ' π' ρ'' π'' ->
      lin_closure s ρ π ρ'' π''.
    Proof.
      intros H1 H2. induction H1; [exact H2|].
      eapply lin_trans; eauto.
    Qed.

    Lemma stack_push_inv_step β (v : A) stk :
      Step (li_lts F) (Build_ThreadEvent β (InvEv (st_push v)))
        (Idle stk) (Pending stk β (st_push v)).
    Proof.
      eapply AtomicLTS.step_inv. apply StackSpec.step_push_inv.
    Qed.

    Lemma stack_push_res_step β (v : A) stk :
      Step (li_lts F) (Build_ThreadEvent β (ResEv (st_push v) tt))
        (Pending stk β (st_push v)) (Idle (v :: stk)).
    Proof.
      eapply AtomicLTS.step_res. apply StackSpec.step_push_res.
    Qed.

    Lemma stack_pop_inv_step β stk :
      Step (li_lts F) (Build_ThreadEvent β (InvEv st_pop))
        (Idle stk) (Pending stk β st_pop).
    Proof.
      eapply AtomicLTS.step_inv. apply StackSpec.step_pop_inv.
    Qed.

    Lemma stack_pop_emp_step β :
      Step (li_lts F) (Build_ThreadEvent β (ResEv st_pop None))
        (Pending nil β st_pop) (Idle nil).
    Proof.
      eapply AtomicLTS.step_res. apply StackSpec.step_pop_emp.
    Qed.

    Lemma stack_pop_res_step β (v : A) stk :
      Step (li_lts F) (Build_ThreadEvent β (ResEv st_pop (Some v)))
        (Pending (v :: stk) β st_pop) (Idle stk).
    Proof.
      eapply AtomicLTS.step_res. apply StackSpec.step_pop_res.
    Qed.

    Lemma lin_step_poss_steps s ρ π ρ' π' :
      lin_step s ρ π ρ' π' ->
      poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof.
      intros Hstep. inversion Hstep; subst.
      eapply rt_trans.
      - apply rt_step.
        eapply (@ps_inv _ (li_lts F) β (st_push v) (Idle stk)
          (Pending stk β (st_push v)) π).
        + apply stack_push_inv_step.
        + exact H2.
      - apply rt_step.
        eapply (@ps_ret _ (li_lts F) β (st_push v) tt (Pending stk β (st_push v))
          (Idle (v :: stk))).
        + apply stack_push_res_step.
        + apply TMap.gss.
    Qed.

    Lemma lin_closure_poss_steps s ρ π ρ' π' :
      lin_closure s ρ π ρ' π' ->
      poss_steps (PossOk ρ π) (PossOk ρ' π').
    Proof.
      intros Hclos. induction Hclos.
      - apply rt_refl.
      - eapply rt_trans; [eapply lin_step_poss_steps; eauto|exact IHHclos].
    Qed.

    Lemma lin_step_idle s ρ π ρ' π' :
      lin_step s ρ π ρ' π' -> exists stk, ρ' = Idle stk.
    Proof. intros Hstep. inversion Hstep; subst. eauto. Qed.

    Lemma lin_closure_idle s ρ π ρ' π' :
      lin_closure s ρ π ρ' π' -> (exists stk, ρ = Idle stk) ->
      exists stk, ρ' = Idle stk.
    Proof.
      intros Hclos Hidle. induction Hclos; [exact Hidle|].
      apply IHHclos. eapply lin_step_idle; eauto.
    Qed.

    (** Linearizing a list of pending vertices, the last one first, puts
        their values on top of the stack in list order. *)
    Fixpoint lin_tokens (s : @TryStackState A) (ms : list LPNodeId)
        (π : tmap lin_state) : tmap lin_state :=
      match ms with
      | nil => π
      | m :: ms' =>
          match ts_vertices s m with
          | Some v =>
              TMap.add (fst m) (push_ret_token v)
                (TMap.add (fst m) (push_lini_token v) (lin_tokens s ms' π))
          | None => lin_tokens s ms' π
          end
      end.

    Lemma lin_tokens_find_other s ms π β :
      ~ In β (map fst ms) ->
      TMap.find β (lin_tokens s ms π) = TMap.find β π.
    Proof.
      induction ms as [|m ms IH]; intros Hnotin; simpl.
      - reflexivity.
      - simpl in Hnotin.
        assert (Hβ : β <> fst m) by (intro; apply Hnotin; now left).
        assert (Hrest : ~ In β (map fst ms)) by (intro; apply Hnotin; now right).
        destruct (ts_vertices s m).
        + rewrite find_add_add, TMap.gso by congruence. now apply IH.
        + now apply IH.
    Qed.

    Lemma lin_tokens_find_in s ms π m v :
      NoDup (map fst ms) -> In m ms -> ts_vertices s m = Some v ->
      TMap.find (fst m) (lin_tokens s ms π) = Some (push_ret_token v).
    Proof.
      induction ms as [|m' ms IH]; intros Hnodup Hin Hv; simpl.
      - contradiction.
      - simpl in Hnodup. apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hnotin Hnodup'].
        destruct Hin as [->|Hin].
        + rewrite Hv. rewrite find_add_add, TMap.gss. reflexivity.
        + assert (Hneq : fst m <> fst m').
          { intro Heq. apply Hnotin. rewrite <- Heq. now apply in_map. }
          destruct (ts_vertices s m').
          * rewrite find_add_add, TMap.gso by congruence. now apply IH.
          * now apply IH.
    Qed.

    Lemma lin_all s ms vals stk π :
      values_of s ms vals ->
      NoDup (map fst ms) ->
      (forall m, In m ms ->
        ts_is_pending s m /\ ~ ts_garbage s m /\
        exists v, ts_vertices s m = Some v /\
          TMap.find (fst m) π = Some (push_inv_token v)) ->
      lin_closure s (Idle stk) π (Idle (vals ++ stk)) (lin_tokens s ms π).
    Proof.
      intros Hvals. revert stk.
      induction Hvals as [|m v ms vals Hv Hvals IH]; intros stk Hnodup Hall.
      - simpl. constructor.
      - simpl in Hnodup. apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hnotin Hnodup'].
        assert (Hrest : forall m', In m' ms ->
          ts_is_pending s m' /\ ~ ts_garbage s m' /\
          exists v', ts_vertices s m' = Some v' /\
            TMap.find (fst m') π = Some (push_inv_token v')).
        { intros m' Hm'. apply Hall. now right. }
        specialize (IH stk Hnodup' Hrest).
        destruct (Hall m (or_introl eq_refl)) as (Hpend & Hng & v' & Hv' & Hfind).
        rewrite Hv in Hv'. injection Hv' as <-.
        simpl. rewrite Hv.
        eapply lin_closure_snoc; [exact IH|].
        destruct m as [β l]. simpl in *.
        apply (lin_push s β l v (vals ++ stk) (lin_tokens s ms π)).
        + exact Hpend.
        + exact Hv.
        + exact Hng.
        + rewrite lin_tokens_find_other; assumption.
    Qed.


    (** * Facts about the concrete transformers *)

    Lemma sp_vertices s α l v m :
      m <> pair α l ->
      ts_vertices (ts_start_push α l v s) m = ts_vertices s m.
    Proof. intros Hneq. unfold ts_start_push. simpl. apply node_update_neq. congruence. Qed.

    Lemma sp_vertex_new s α l v :
      ts_vertices (ts_start_push α l v s) (pair α l) = Some v.
    Proof. unfold ts_start_push. simpl. apply node_update_eq. Qed.

    Lemma sp_is_vertex s α l v m :
      ts_is_vertex (ts_start_push α l v s) m <->
      ts_is_vertex s m \/ m = pair α l.
    Proof.
      unfold ts_is_vertex. destruct (node_eq_dec m (pair α l)) as [->|Hneq].
      - rewrite sp_vertex_new. split; [auto|discriminate].
      - rewrite sp_vertices by exact Hneq. tauto.
    Qed.

    Lemma sp_garbage s α l v m :
      ts_garbage (ts_start_push α l v s) m <-> ts_garbage s m.
    Proof. reflexivity. Qed.

    Lemma sp_live s α l v m :
      ts_fresh_node s (pair α l) ->
      (live (ts_start_push α l v s) m <-> live s m \/ m = pair α l).
    Proof.
      intros [Hnone Hng]. unfold live, ts_is_live.
      rewrite sp_is_vertex, sp_garbage.
      destruct (node_eq_dec m (pair α l)) as [->|Hneq].
      - unfold ts_is_vertex. rewrite Hnone. tauto.
      - tauto.
    Qed.

    Lemma sp_pending s α l v m :
      TMap.find α (ts_pending_pushes s) = None ->
      (ts_is_pending (ts_start_push α l v s) m <->
       ts_is_pending s m \/ m = pair α l).
    Proof.
      intros Hnone. unfold ts_is_pending. simpl.
      destruct m as [β l']. simpl.
      destruct (Pos.eq_dec β α) as [->|Hneq].
      - rewrite TMap.gss, Hnone. split.
        + intros Heq. injection Heq as ->. now right.
        + intros [Hbad|Heq]; [discriminate|]. injection Heq as ->. reflexivity.
      - rewrite TMap.gso by congruence. split.
        + now left.
        + intros [H|H]; [exact H|]. injection H as -> _. contradiction.
    Qed.

    Lemma sp_edges s α l v x y :
      ts_edges (ts_start_push α l v s) x y <->
      ts_edges s x y \/
      (x = pair α l /\ ts_is_vertex s y /\ ~ ts_is_pending s y).
    Proof. reflexivity. Qed.

    Lemma sp_edges_old s α l v x y :
      x <> pair α l ->
      (ts_edges (ts_start_push α l v s) x y <-> ts_edges s x y).
    Proof. intros Hneq. rewrite sp_edges. tauto. Qed.

    Lemma sp_no_edge_into_new s α l v x :
      graph_wf s -> ts_fresh_node s (pair α l) ->
      ~ ts_edges (ts_start_push α l v s) x (pair α l).
    Proof.
      intros [_ [_ [_ [Hedges _]]]] [Hnone _] Hedge.
      apply sp_edges in Hedge. destruct Hedge as [Hedge|[_ [Hvertex _]]].
      - apply Hedges in Hedge. destruct Hedge as [_ Hvertex]. now apply Hvertex.
      - now apply Hvertex.
    Qed.

    Lemma sp_graph_wf s α l v :
      graph_wf s ->
      TMap.find α (ts_pending_pushes s) = None ->
      ts_fresh_node s (pair α l) ->
      graph_wf (ts_start_push α l v s).
    Proof.
      intros Hwf Hnone Hfresh.
      pose proof Hwf as [[order [Hnodup [Hcompat Hall]]] [Hgarbage [Hpend [Hedges Hnoin]]]].
      pose proof Hfresh as [Hfnone Hfng].
      assert (Hnotvertex : ~ ts_is_vertex s (pair α l)).
      { unfold ts_is_vertex. now rewrite Hfnone. }
      split; [|split; [|split; [|split]]].
      - exists (pair α l :: order). split; [|split].
        + constructor; [|exact Hnodup].
          intro Hin. apply Hall in Hin. contradiction.
        + split.
          * intros m Hin. apply sp_no_edge_into_new; assumption.
          * eapply ecompat_edges_ext; [|exact Hcompat].
            intros x y Hx Hy. symmetry. apply sp_edges_old.
            intro Heq. subst x. apply Hall in Hx. contradiction.
        + intros m. rewrite sp_is_vertex. simpl. rewrite Hall.
          split; intros [H|H]; subst; auto.
      - intros m Hg. apply sp_garbage in Hg. apply sp_is_vertex. left. auto.
      - intros β l' Hl'.
        assert (Hp : ts_is_pending (ts_start_push α l v s) (pair β l')) by exact Hl'.
        apply sp_pending in Hp; [|exact Hnone].
        apply sp_is_vertex. destruct Hp as [Hp|Hp].
        + left. apply (Hpend β l'). exact Hp.
        + right. exact Hp.
      - intros x y Hedge. apply sp_edges in Hedge.
        destruct Hedge as [Hedge|[Heq [Hy _]]].
        + destruct (Hedges _ _ Hedge) as [Hx Hy].
          split; apply sp_is_vertex; left; assumption.
        + subst x. split; apply sp_is_vertex; [right; reflexivity|left; exact Hy].
      - intros x y Hedge Hp. apply sp_pending in Hp; [|exact Hnone].
        destruct Hp as [Hp|Heq]; [|subst y].
        + apply sp_edges in Hedge. destruct Hedge as [Hedge|[_ [_ Hnp]]].
          * exact (Hnoin _ _ Hedge Hp).
          * exact (Hnp Hp).
        + eapply sp_no_edge_into_new; eassumption.
    Qed.

    Lemma fp_pending s α m :
      ts_is_pending (ts_finish_push α s) m <->
      ts_is_pending s m /\ fst m <> α.
    Proof.
      unfold ts_is_pending. simpl. destruct m as [β l]. simpl.
      destruct (Pos.eq_dec β α) as [->|Hneq].
      - rewrite TMap.grs. split; [discriminate|intros [_ H]; contradiction].
      - rewrite TMap.gro by congruence. tauto.
    Qed.

    Lemma fp_graph_wf s α : graph_wf s -> graph_wf (ts_finish_push α s).
    Proof.
      intros [Hfin [Hgarbage [Hpend [Hedges Hnoin]]]].
      split; [exact Hfin|]. split; [exact Hgarbage|]. split; [|split; [exact Hedges|]].
      - intros β l Hl.
        assert (Hp : ts_is_pending (ts_finish_push α s) (pair β l)) by exact Hl.
        apply fp_pending in Hp. destruct Hp as [Hp _]. now apply (Hpend β l).
      - intros x y Hedge Hp. apply fp_pending in Hp. destruct Hp as [Hp _].
        exact (Hnoin _ _ Hedge Hp).
    Qed.

    Lemma mg_live s n m :
      live (ts_mark_garbage n s) m <-> live s m /\ m <> n.
    Proof.
      unfold live, ts_is_live, ts_is_vertex. simpl. unfold set_add.
      split.
      - intros [Hv Hng]. split; [split|].
        + exact Hv.
        + intro Hg. apply Hng. now right.
        + intro Heq. apply Hng. now left.
      - intros [[Hv Hng] Hneq]. split; [exact Hv|].
        intros [Heq|Hg]; [contradiction|now apply Hng].
    Qed.

    Lemma mg_garbage s n m :
      ts_garbage (ts_mark_garbage n s) m <-> m = n \/ ts_garbage s m.
    Proof. reflexivity. Qed.

    Lemma mg_graph_wf s n :
      graph_wf s -> ts_is_vertex s n -> graph_wf (ts_mark_garbage n s).
    Proof.
      intros [Hfin [Hgarbage [Hpend [Hedges Hnoin]]]] Hvertex.
      split; [exact Hfin|]. split; [|split; [exact Hpend|split; [exact Hedges|exact Hnoin]]].
      intros m Hg. apply mg_garbage in Hg. destruct Hg as [Heq|Hg].
      - subst m. exact Hvertex.
      - now apply Hgarbage.
    Qed.

    (** * Consequences of the invariant *)

    Lemma I_state_wf s Δ : I_state s Δ -> graph_wf s.
    Proof. intros [H _]. exact H. Qed.

    Lemma I_state_stack s Δ : I_state s Δ -> I_stack s Δ.
    Proof. intros [_ [H _]]. exact H. Qed.

    Lemma I_state_graph s Δ : I_state s Δ -> I_graph s Δ.
    Proof. intros [_ [_ [H _]]]. exact H. Qed.

    Lemma I_state_pending s Δ : I_state s Δ -> I_pending s Δ.
    Proof. intros [_ [_ [_ H]]]. exact H. Qed.

    Lemma I_state_idle s Δ ρ π :
      I_state s Δ -> Δ ρ π -> exists stk, ρ = Idle stk.
    Proof.
      intros HI Hposs.
      destruct (I_state_stack _ _ HI _ _ Hposs) as [N [_ [stk [_ ->]]]].
      eauto.
    Qed.

    Lemma wf_pending_vertex s β l :
      graph_wf s -> TMap.find β (ts_pending_pushes s) = Some l ->
      ts_is_vertex s (pair β l).
    Proof. intros [_ [_ [Hpend _]]] Hl. now apply (Hpend β l). Qed.

    Lemma wf_no_edge_into_pending s x m :
      graph_wf s -> ts_edges s x m -> ~ ts_is_pending s m.
    Proof. intros [_ [_ [_ [_ Hnoin]]]]. apply Hnoin. Qed.

    Lemma wf_live_or_garbage s n :
      graph_wf s -> ts_is_vertex s n -> live s n \/ ts_garbage s n.
    Proof.
      intros _ Hv. destruct (classic (ts_garbage s n)) as [Hg|Hng].
      - now right.
      - left. split; assumption.
    Qed.

    (** The paper's [α ↦ ◦(push) ⊕ α ↦ •(push, ok)] for a pending live
        push follows from [I_graph]. *)
    Lemma pending_live_both_tokens s Δ β l v :
      I_state s Δ ->
      TMap.find β (ts_pending_pushes s) = Some l ->
      ts_vertices s (pair β l) = Some v ->
      live s (pair β l) ->
      (exists ρ π, Δ ρ π /\ TMap.find β π = Some (push_inv_token v)) /\
      (exists ρ π, Δ ρ π /\ TMap.find β π = Some (push_ret_token v)).
    Proof.
      intros HI Hl Hv Hlive.
      pose proof (I_state_wf _ _ HI) as Hwf.
      pose proof (I_state_graph _ _ HI) as Hgraph.
      split.
      - set (P' := fun n : LPNodeId => n = pair β l).
        assert (Hpset : pending_set s P').
        { intros n Hn. unfold P' in Hn. subst n. exact Hl. }
        destruct (perm_exists s (fun n => live s n /\ ~ P' n) Hwf)
          as [N Hperm].
        { intros n [Hn _]. apply live_vertex. exact Hn. }
        destruct (values_exist s N) as [stk Hstk].
        { intros n Hn. eapply perm_vertices; [|exact Hperm|exact Hn].
          intros m [Hm _]. apply live_vertex. exact Hm. }
        destruct (Hgraph P' Hpset N Hperm stk Hstk) as [π [Hposs Htok]].
        destruct (Htok β l Hl) as (v' & Hv' & _ & Hinv).
        rewrite Hv in Hv'. injection Hv' as <-.
        exists (Idle stk), π. split; [exact Hposs|].
        apply Hinv; [reflexivity|exact Hlive].
      - set (P' := fun n : LPNodeId => False).
        assert (Hpset : pending_set s P') by (intros n Hn; contradiction).
        destruct (perm_exists s (fun n => live s n /\ ~ P' n) Hwf)
          as [N Hperm].
        { intros n [Hn _]. apply live_vertex. exact Hn. }
        destruct (values_exist s N) as [stk Hstk].
        { intros n Hn. eapply perm_vertices; [|exact Hperm|exact Hn].
          intros m [Hm _]. apply live_vertex. exact Hm. }
        destruct (Hgraph P' Hpset N Hperm stk Hstk) as [π [Hposs Htok]].
        destruct (Htok β l Hl) as (v' & Hv' & Hret & _).
        rewrite Hv in Hv'. injection Hv' as <-.
        exists (Idle stk), π. split; [exact Hposs|].
        apply Hret. intro Hbad. exact Hbad.
    Qed.

    (** A thread whose token is fixed across all possibilities, and is not
        a completed push, has no pending entry. *)
    Lemma alin_no_pending s Δ α (ls : lin_state) :
      I_state s Δ ->
      (forall ρ π, Δ ρ π -> TMap.find α π = Some ls) ->
      (forall v, ls <> push_ret_token v) ->
      TMap.find α (ts_pending_pushes s) = None.
    Proof.
      intros HI Hall Hnotret.
      destruct (TMap.find α (ts_pending_pushes s)) as [l|] eqn:Hl; [|reflexivity].
      exfalso.
      destruct (I_state_pending _ _ HI α l Hl) as (v & Hv & Hgarbage & Hlive).
      destruct (classic (ts_garbage s (pair α l))) as [Hg|Hng].
      - destruct (ac_nonempty Δ) as (ρ & π & Hposs).
        pose proof (Hgarbage Hg _ _ Hposs) as Hret.
        rewrite (Hall _ _ Hposs) in Hret. injection Hret as Heq.
        exact (Hnotret v Heq).
      - assert (Hl' : live s (pair α l)).
        { split; [|exact Hng]. eapply wf_pending_vertex; [eapply I_state_wf|]; eauto. }
        destruct (pending_live_both_tokens _ _ _ _ _ HI Hl Hv Hl')
          as ((ρ1 & π1 & Hposs1 & Hinv) & (ρ2 & π2 & Hposs2 & Hret)).
        rewrite (Hall _ _ Hposs1) in Hinv. rewrite (Hall _ _ Hposs2) in Hret.
        injection Hinv as ->. injection Hret as Heq.
        exact (Hnotret v Heq).
    Qed.

    Lemma alin_inv_no_pending s Δ α (op : Sig.op (li_sig F)) :
      I_state s Δ ->
      (forall ρ π, Δ ρ π -> TMap.find α π = Some (ls_inv op)) ->
      TMap.find α (ts_pending_pushes s) = None.
    Proof.
      intros HI Hall. eapply alin_no_pending; eauto. discriminate.
    Qed.

    Lemma alin_pop_no_pending s Δ α (r : option A) :
      I_state s Δ ->
      (forall ρ π, Δ ρ π -> TMap.find α π = Some (pop_ret_token r)) ->
      TMap.find α (ts_pending_pushes s) = None.
    Proof.
      intros HI Hall. eapply alin_no_pending; eauto. discriminate.
    Qed.

    (** * Token bookkeeping for the [push] closure *)

    Lemma lin_step_find s ρ π ρ' π' γ :
      lin_step s ρ π ρ' π' ->
      TMap.find γ π' = TMap.find γ π \/
      (exists l v, TMap.find γ (ts_pending_pushes s) = Some l /\
        ts_vertices s (pair γ l) = Some v /\ ~ ts_garbage s (pair γ l) /\
        TMap.find γ π = Some (push_inv_token v) /\
        TMap.find γ π' = Some (push_ret_token v)).
    Proof.
      intros Hstep. inversion Hstep; subst.
      destruct (Pos.eq_dec γ β) as [->|Hneq].
      - right. exists l, v. rewrite find_add_add, TMap.gss. auto.
      - left. rewrite find_add_add, TMap.gso by congruence. reflexivity.
    Qed.

    Lemma lin_closure_find s ρ π ρ' π' γ :
      lin_closure s ρ π ρ' π' ->
      TMap.find γ π' = TMap.find γ π \/
      (exists l v, TMap.find γ (ts_pending_pushes s) = Some l /\
        ts_vertices s (pair γ l) = Some v /\ ~ ts_garbage s (pair γ l) /\
        TMap.find γ π' = Some (push_ret_token v)).
    Proof.
      intros Hclos. induction Hclos as [ρ π|ρ π ρ' π' ρ'' π'' Hstep Hclos IH].
      - now left.
      - destruct (lin_step_find _ _ _ _ _ γ Hstep) as [Hsame|[l [v [Hl [Hv [Hng [Hinv0 Hret]]]]]]].
        + destruct IH as [Hsame'|Hlin].
          * left. congruence.
          * right. exact Hlin.
        + destruct IH as [Hsame'|Hlin].
          * right. exists l, v. rewrite Hsame'. auto.
          * right. exact Hlin.
    Qed.

    Lemma lin_closure_find_noninv s ρ π ρ' π' γ :
      lin_closure s ρ π ρ' π' ->
      (forall v, TMap.find γ π <> Some (push_inv_token v)) ->
      TMap.find γ π' = TMap.find γ π.
    Proof.
      intros Hclos. induction Hclos as [ρ π|ρ π ρ' π' ρ'' π'' Hstep Hclos IH];
        intros Hnot.
      - reflexivity.
      - destruct (lin_step_find _ _ _ _ _ γ Hstep) as [Hsame|[l [v [Hl0 [Hv0 [Hng0 [Hinv Hret0]]]]]]].
        + rewrite <- Hsame. apply IH. now rewrite Hsame.
        + exfalso. exact (Hnot v Hinv).
    Qed.

    Lemma lin_closure_find_nopending s ρ π ρ' π' γ :
      lin_closure s ρ π ρ' π' ->
      TMap.find γ (ts_pending_pushes s) = None ->
      TMap.find γ π' = TMap.find γ π.
    Proof.
      intros Hclos Hnone.
      destruct (lin_closure_find _ _ _ _ _ γ Hclos) as [Hsame|[l [v0 [Hl Hrest]]]].
      - exact Hsame.
      - congruence.
    Qed.

    (** * [I ∘ G_push-inv ⇒ I] *)

    Section PushInv.
      Variable s : @TryStackState A.
      Variables (α : tid) (l : Addr) (v : A).
      Variable Δ Δ' : config.
      Hypothesis HI : I_state s Δ.
      Hypothesis Hnone : TMap.find α (ts_pending_pushes s) = None.
      Hypothesis Hfresh : ts_fresh_node s (pair α l).
      Hypothesis Htoken : forall ρ π, Δ ρ π ->
        TMap.find α π = Some (push_inv_token v).
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists ρ π, Δ ρ π /\ lin_closure (ts_start_push α l v s) ρ π ρ' π'.

      Local Notation s' := (ts_start_push α l v s).

      Let Hwf : graph_wf s := I_state_wf _ _ HI.
      Let Hwf' : graph_wf (ts_start_push α l v s) :=
        sp_graph_wf s α l v Hwf Hnone Hfresh.

      Lemma pi_new_not_vertex : ~ ts_is_vertex s (pair α l).
      Proof. pose proof Hfresh as [Hn _]. unfold ts_is_vertex. now rewrite Hn. Qed.

      Lemma pi_new_pending : ts_is_pending (ts_start_push α l v s) (pair α l).
      Proof. unfold ts_is_pending. simpl. apply TMap.gss. Qed.

      Lemma pi_new_live : live (ts_start_push α l v s) (pair α l).
      Proof. apply sp_live; [exact Hfresh|]. now right. Qed.

      (** A pending vertex's thread is unique; the new vertex is the only
          pending vertex of [α]. *)
      Lemma pi_pending_other m :
        m <> pair α l ->
        (ts_is_pending (ts_start_push α l v s) m <-> ts_is_pending s m).
      Proof.
        intros Hneq. rewrite sp_pending by exact Hnone. tauto.
      Qed.

      Lemma pi_pending_old_not_alpha m :
        ts_is_pending s m -> fst m <> α.
      Proof.
        intros Hp Heq. unfold ts_is_pending in Hp. rewrite Heq, Hnone in Hp.
        discriminate.
      Qed.

      (** The old permutation stays valid: the new vertex is omitted while
          [α]'s token is [◦]. *)
      Lemma pi_justified_base ρ π N :
        TMap.find α π = Some (push_inv_token v) ->
        justified s ρ π N -> justified (ts_start_push α l v s) ρ π N.
      Proof.
        intros Hα [[Hnodup [Hcompat Hmem]] [stk [Hvals Hρ]]].
        assert (Hnotin : ~ In (pair α l) N).
        { intro Hin. apply Hmem in Hin. destruct Hin as [Hlive _].
          apply pi_new_not_vertex. apply live_vertex. exact Hlive. }
        split.
        - split; [exact Hnodup|]. split.
          + eapply ecompat_edges_ext; [|exact Hcompat].
            intros x y Hx Hy. symmetry. apply sp_edges_old.
            intro Heq. subst x. contradiction.
          + intros m. rewrite Hmem. unfold stack_domain.
            destruct (node_eq_dec m (pair α l)) as [->|Hneq].
            * split.
              -- intros [Hlive _]. exfalso. apply pi_new_not_vertex.
                 apply live_vertex. exact Hlive.
              -- intros [_ Hnot]. exfalso. apply Hnot. split.
                 ++ apply pi_new_pending.
                 ++ exists v. exact Hα.
            * rewrite sp_live by exact Hfresh.
              unfold omitted. rewrite pi_pending_other by exact Hneq.
              tauto.
        - exists stk. split; [|exact Hρ].
          eapply values_of_same_vertices; [|exact Hvals].
          intros m Hm. symmetry. apply sp_vertices.
          intro Heq. subst m. contradiction.
      Qed.

      (** Linearizing a pending live push prepends its vertex to the
          justifying permutation; no edge points into a pending vertex. *)
      Lemma lin_step_justified s0 ρ π ρ' π' N :
        graph_wf s0 ->
        justified s0 ρ π N -> lin_step s0 ρ π ρ' π' ->
        exists N', justified s0 ρ' π' N'.
      Proof.
        intros Hwf0 Hjust Hstep.
        inversion Hstep; subst.
        destruct Hjust as [[Hnodup [Hcompat Hmem]] [stk' [Hvals Hρ]]].
        injection Hρ as ->.
        assert (Hpend : ts_is_pending s0 (pair β l0)) by exact H.
        assert (Hnotin : ~ In (pair β l0) N).
        { intro Hin. apply Hmem in Hin. destruct Hin as [_ Hnot].
          apply Hnot. split; [exact Hpend|]. exists v0. exact H2. }
        exists (pair β l0 :: N). split.
        - split; [constructor; assumption|]. split.
          + split; [|exact Hcompat].
            intros m _ Hedge. exact (wf_no_edge_into_pending _ _ _ Hwf0 Hedge Hpend).
          + intros m. simpl. rewrite Hmem. unfold stack_domain, omitted.
            destruct (node_eq_dec m (pair β l0)) as [->|Hneq].
            * split.
              -- intros _. split.
                 ++ split; [unfold ts_is_vertex; congruence|exact H1].
                 ++ intros [_ [v' Hv']]. simpl in Hv'.
                    rewrite find_add_add, TMap.gss in Hv'. discriminate.
              -- intros _. now left.
            * assert (Hfst : ts_is_pending s0 m -> fst m <> β).
              { intros Hp Heq. apply Hneq.
                apply (pending_unique s0 m (pair β l0) Hp Hpend Heq). }
              split.
              -- intros [Heqm|[Hlive Hnot]]; [symmetry in Heqm; contradiction|].
                 split; [exact Hlive|]. intros [Hp [v' Hv']].
                 apply Hnot. split; [exact Hp|]. exists v'.
                 rewrite find_add_add, TMap.gso in Hv' by (apply Hfst; exact Hp).
                 exact Hv'.
              -- intros [Hlive Hnot]. right. split; [exact Hlive|].
                 intros [Hp [v' Hv']]. apply Hnot. split; [exact Hp|].
                 exists v'. rewrite find_add_add, TMap.gso by (apply Hfst; exact Hp).
                 exact Hv'.
        - exists (v0 :: stk'). split; [|reflexivity].
          constructor; assumption.
      Qed.

      Lemma lin_closure_justified s0 ρ π ρ' π' N :
        graph_wf s0 ->
        justified s0 ρ π N -> lin_closure s0 ρ π ρ' π' ->
        exists N', justified s0 ρ' π' N'.
      Proof.
        intros Hwf0 Hjust Hclos. revert N Hjust.
        induction Hclos as [ρ π|ρ π ρ' π' ρ'' π'' Hstep Hclos IH]; intros N Hjust.
        - eauto.
        - destruct (lin_step_justified s0 ρ π ρ' π' N Hwf0 Hjust Hstep) as [N' Hjust'].
          eapply IH; eauto.
      Qed.

      Lemma pi_I_stack : I_stack (ts_start_push α l v s) Δ'.
      Proof.
        intros ρ' π' Hposs'. apply HΔ' in Hposs'.
        destruct Hposs' as (ρ & π & Hposs & Hclos).
        destruct (I_state_stack _ _ HI _ _ Hposs) as [N Hjust].
        eapply lin_closure_justified; [exact Hwf'| |exact Hclos].
        apply pi_justified_base; [now apply Htoken with ρ|exact Hjust].
      Qed.

      (** Elements placed before the new vertex in a compatible order are
          pending vertices of the old graph. *)
      Lemma pi_before_new_pending N1 N2 :
        ecompat (ts_edges (ts_start_push α l v s)) (N1 ++ pair α l :: N2) ->
        (forall m, In m N1 -> ts_is_vertex s m) ->
        forall m, In m N1 -> ts_is_pending s m.
      Proof.
        intros Hcompat Hvertex m Hin.
        pose proof (ecompat_app_later _ _ _ _ Hcompat m Hin) as Hnoedge.
        destruct (classic (ts_is_pending s m)) as [Hp|Hnp]; [exact Hp|].
        exfalso. apply Hnoedge. apply sp_edges. right.
        split; [reflexivity|]. split; [now apply Hvertex|exact Hnp].
      Qed.

      Lemma pi_I_graph : I_graph (ts_start_push α l v s) Δ'.
      Proof.
        intros P' Hpset N Hperm stk Hstk.
        pose proof (I_state_graph _ _ HI) as Hgraph.
        destruct (classic (In (pair α l) N)) as [Hin|Hnotin].
        - (* the new vertex is linearized: N = N1 ++ (α,l) :: N2 *)
          destruct (in_split _ _ Hin) as [N1 [N2 ->]].
          destruct Hperm as [Hnodup [Hcompat Hmem]].
          pose proof (NoDup_remove _ _ _ Hnodup) as [Hnodup12 Hnotin12].
          assert (HN1vertex : forall m, In m N1 -> ts_is_vertex s m).
          { intros m Hm.
            assert (Hm' : In m (N1 ++ pair α l :: N2)) by (apply in_or_app; now left).
            apply Hmem in Hm'. destruct Hm' as [Hlive _].
            apply sp_live in Hlive; [|exact Hfresh]. destruct Hlive as [Hlive|Heqm]; [|subst m].
            - apply live_vertex. exact Hlive.
            - exfalso. apply Hnotin12. apply in_or_app. now left. }
          assert (HN1pending : forall m, In m N1 -> ts_is_pending s m).
          { apply (pi_before_new_pending N1 N2); assumption. }
          assert (HN1alpha : forall m, In m N1 -> fst m <> α).
          { intros m Hm. apply pi_pending_old_not_alpha. now apply HN1pending. }
          assert (HN1live : forall m, In m N1 -> live s m).
          { intros m Hm.
            assert (Hm' : In m (N1 ++ pair α l :: N2)) by (apply in_or_app; now left).
            apply Hmem in Hm'. destruct Hm' as [Hlive _].
            apply sp_live in Hlive; [|exact Hfresh]. destruct Hlive as [Hlive|Heqm]; [|subst m].
            - exact Hlive.
            - exfalso. apply Hnotin12. apply in_or_app. now left. }
          assert (HN1notP : forall m, In m N1 -> ~ P' m).
          { intros m Hm.
            assert (Hm' : In m (N1 ++ pair α l :: N2)) by (apply in_or_app; now left).
            apply Hmem in Hm'. exact (proj2 Hm'). }
          assert (HnewnotP : ~ P' (pair α l)).
          { apply Hmem in Hin. exact (proj2 Hin). }
          (* the old choice of unlinearized pushes *)
          set (P'' := fun m => (P' m /\ m <> pair α l) \/ In m N1).
          assert (Hpset'' : pending_set s P'').
          { intros m [[Hm Hneq]|Hm].
            - apply Hpset in Hm. apply pi_pending_other in Hm; assumption.
            - now apply HN1pending. }
          assert (Hperm2 : perm s (fun m => live s m /\ ~ P'' m) N2).
          { split; [|split].
            - apply NoDup_app_right in Hnodup12. exact Hnodup12.
            - eapply ecompat_edges_ext;
                [|eapply ecompat_app_inv_r with (N1 := N1 ++ pair α l :: nil);
                  rewrite <- app_assoc; exact Hcompat].
              intros x y Hx Hy. apply sp_edges_old.
              intro Heq. apply Hnotin12. rewrite <- Heq. apply in_or_app. now right.
            - intros m. split.
              + intros Hm.
                assert (Hm' : In m (N1 ++ pair α l :: N2)).
                { apply in_or_app. right. now right. }
                apply Hmem in Hm'. destruct Hm' as [Hlive HnotP].
                assert (Hneq : m <> pair α l).
                { intro Heq. subst m. apply Hnotin12. apply in_or_app. now right. }
                apply sp_live in Hlive; [|exact Hfresh].
                destruct Hlive as [Hlive|Heq]; [|contradiction].
                split; [exact Hlive|].
                intros [[HP _]|HinN1]; [contradiction|].
                exact (NoDup_app_disjoint _ _ _ Hnodup12 HinN1 Hm).
              + intros [Hlive HnotP''].
                assert (Hneq : m <> pair α l).
                { intro Heq. subst m. apply pi_new_not_vertex. apply live_vertex. exact Hlive. }
                assert (Hm' : In m (N1 ++ pair α l :: N2)).
                { apply Hmem. split.
                  - apply sp_live; [exact Hfresh|]. now left.
                  - intro HP. apply HnotP''. left. split; assumption. }
                apply in_app_or in Hm'. destruct Hm' as [Hm'|[Heq|Hm']].
                * exfalso. apply HnotP''. now right.
                * symmetry in Heq. contradiction.
                * exact Hm'. }
          (* split the stack *)
          apply Forall2_app_inv_l in Hstk.
          destruct Hstk as (vals1 & stk2' & Hvals1 & Hstk2' & ->).
          inversion Hstk2' as [|n' v' N2' stk2 Hnew Hvals2]; subst.
          rewrite sp_vertex_new in Hnew. injection Hnew as <-.
          assert (Hvals2s : values_of s N2 stk2).
          { eapply values_of_same_vertices; [|exact Hvals2].
            intros m Hm. apply sp_vertices.
            intro Heq. subst m. apply Hnotin12. apply in_or_app. now right. }
          destruct (Hgraph P'' Hpset'' N2 Hperm2 stk2 Hvals2s) as [π [Hposs Htok]].
          (* linearize the new vertex, then N1 from last to first *)
          set (π1 := TMap.add α (push_ret_token v) (TMap.add α (push_lini_token v) π)).
          assert (Hstep1 : lin_step s' (Idle stk2) π (Idle (v :: stk2)) π1).
          { apply (lin_push s' α l v stk2 π).
            - simpl. apply TMap.gss.
            - apply sp_vertex_new.
            - exact (proj2 Hfresh).
            - now apply Htoken with (Idle stk2). }
          assert (Hvals1s' : values_of s' N1 vals1) by exact Hvals1.
          assert (HN1nodup : NoDup (map fst N1)).
          { clear - HN1pending Hnodup12.
            apply NoDup_app_left in Hnodup12.
            induction N1 as [|m N1 IH]; [constructor|].
            apply NoDup_cons_iff in Hnodup12. destruct Hnodup12 as [Hnotin Hnodup'].
            simpl. constructor.
            - intro Hin. apply in_map_iff in Hin. destruct Hin as [m' [Hfst Hin]].
              apply Hnotin.
              assert (m' = m).
              { apply (pending_unique s m' m).
                - apply HN1pending. now right.
                - apply HN1pending. now left.
                - exact Hfst. }
              subst m'. exact Hin.
            - apply IH; [exact Hnodup'|]. intros m' Hm'. apply HN1pending. now right. }
          assert (Hall1 : forall m, In m N1 ->
            ts_is_pending s' m /\ ~ ts_garbage s' m /\
            exists vm, ts_vertices s' m = Some vm /\
              TMap.find (fst m) π1 = Some (push_inv_token vm)).
          { intros m Hm.
            pose proof (HN1pending m Hm) as Hp.
            pose proof (HN1alpha m Hm) as Hα.
            destruct m as [β lm]. simpl in Hα.
            destruct (Htok β lm Hp) as (vm & Hvm & _ & Hinv).
            split; [|split].
            - apply pi_pending_other; [|exact Hp].
              intro Heq. injection Heq as -> _. contradiction.
            - exact (proj2 (HN1live _ Hm)).
            - exists vm. split.
              + rewrite sp_vertices; [exact Hvm|].
                intro Heq. injection Heq as -> _. contradiction.
              + unfold π1. rewrite find_add_add, TMap.gso by congruence.
                apply Hinv; [now right|now apply HN1live]. }
          pose proof (lin_all s' N1 vals1 (v :: stk2) π1 Hvals1s' HN1nodup Hall1) as Hclos.
          exists (lin_tokens s' N1 π1). split.
          + apply HΔ'. exists (Idle stk2), π. split; [exact Hposs|].
            eapply lin_trans; [exact Hstep1|exact Hclos].
          + (* the token clauses *)
            intros β lβ Hlβ.
            destruct (Pos.eq_dec β α) as [->|Hneq].
            * simpl in Hlβ. rewrite TMap.gss in Hlβ.
              injection Hlβ as ->.
              exists v. split; [apply sp_vertex_new|]. split.
              -- intros _. rewrite lin_tokens_find_other.
                 ++ unfold π1. rewrite TMap.gss. reflexivity.
                 ++ intro Hin0. apply in_map_iff in Hin0. destruct Hin0 as [m [Hfst Hm]].
                    exact (HN1alpha m Hm Hfst).
              -- intros HP. contradiction.
            * assert (Hlβs : TMap.find β (ts_pending_pushes s) = Some lβ).
              { simpl in Hlβ. rewrite TMap.gso in Hlβ by congruence. exact Hlβ. }
              destruct (Htok β lβ Hlβs) as (vβ & Hvβ & Hret & Hinv).
              assert (Hneqn : pair β lβ <> pair α l) by (intro Heq; injection Heq as -> _; contradiction).
              exists vβ. split; [rewrite sp_vertices; assumption|].
              destruct (classic (In (pair β lβ) N1)) as [HinN1|HnotinN1].
              -- split.
                 ++ intros _.
                    change β with (fst (pair β lβ)).
                    apply lin_tokens_find_in; [exact HN1nodup|exact HinN1|].
                    rewrite sp_vertices; assumption.
                 ++ intros HP _. exfalso. exact (HN1notP _ HinN1 HP).
              -- assert (Hother : TMap.find β (lin_tokens s' N1 π1) = TMap.find β π).
                 { rewrite lin_tokens_find_other.
                   - unfold π1. rewrite find_add_add, TMap.gso by congruence. reflexivity.
                   - intro Hin0. apply in_map_iff in Hin0. destruct Hin0 as [m [Hfst Hm]].
                     apply HnotinN1.
                     assert (m = pair β lβ).
                     { apply (pending_unique s m (pair β lβ)).
                       - now apply HN1pending.
                       - exact Hlβs.
                       - exact Hfst. }
                     subst m. exact Hm. }
                 rewrite Hother. split.
                 ++ intros HnotP. apply Hret. intros [[HP _]|HinN1']; [contradiction|contradiction].
                 ++ intros HP Hlive. apply Hinv.
                    ** left. split; assumption.
                    ** apply sp_live in Hlive; [|exact Hfresh].
                       destruct Hlive as [Hlive|Heq]; [exact Hlive|contradiction].
        - (* the new vertex is not linearized: it is in P' *)
          assert (HnewP : P' (pair α l)).
          { destruct (classic (P' (pair α l))) as [HP|HnP]; [exact HP|].
            exfalso. apply Hnotin. destruct Hperm as [_ [_ Hmem]]. apply Hmem.
            split; [apply pi_new_live|exact HnP]. }
          set (P'' := fun m => P' m /\ m <> pair α l).
          assert (Hpset'' : pending_set s P'').
          { intros m [Hm Hneq]. apply Hpset in Hm. apply pi_pending_other in Hm; assumption. }
          assert (Hperm' : perm s (fun m => live s m /\ ~ P'' m) N).
          { destruct Hperm as [Hnodup [Hcompat Hmem]]. split; [exact Hnodup|]. split.
            - eapply ecompat_edges_ext; [|exact Hcompat].
              intros x y Hx Hy. apply sp_edges_old. intro Heq. subst x. contradiction.
            - intros m. rewrite Hmem. unfold P''.
              destruct (node_eq_dec m (pair α l)) as [->|Hneq].
              + split.
                * intros [_ HnP]. contradiction.
                * intros [Hlive _]. exfalso. apply pi_new_not_vertex. apply live_vertex. exact Hlive.
              + rewrite sp_live by exact Hfresh. tauto. }
          assert (Hstks : values_of s N stk).
          { eapply values_of_same_vertices; [|exact Hstk].
            intros m Hm. apply sp_vertices. intro Heq. subst m. contradiction. }
          destruct (Hgraph P'' Hpset'' N Hperm' stk Hstks) as [π [Hposs Htok]].
          exists π. split.
          + apply HΔ'. exists (Idle stk), π. split; [exact Hposs|constructor].
          + intros β lβ Hlβ.
            destruct (Pos.eq_dec β α) as [->|Hneq].
            * simpl in Hlβ. rewrite TMap.gss in Hlβ. injection Hlβ as ->.
              exists v. split; [apply sp_vertex_new|]. split.
              -- intros HnP. contradiction.
              -- intros _ _. now apply Htoken with (Idle stk).
            * assert (Hlβs : TMap.find β (ts_pending_pushes s) = Some lβ).
              { simpl in Hlβ. rewrite TMap.gso in Hlβ by congruence. exact Hlβ. }
              destruct (Htok β lβ Hlβs) as (vβ & Hvβ & Hret & Hinv).
              assert (Hneqn : pair β lβ <> pair α l) by (intro Heq; injection Heq as -> _; contradiction).
              exists vβ. split; [rewrite sp_vertices; assumption|]. split.
              -- intros HnP. apply Hret. intros [HP _]. contradiction.
              -- intros HP Hlive. apply Hinv; [split; assumption|].
                 apply sp_live in Hlive; [|exact Hfresh].
                 destruct Hlive as [Hlive|Heq]; [exact Hlive|contradiction].
      Qed.

      Lemma pi_I_pending : I_pending (ts_start_push α l v s) Δ'.
      Proof.
        intros β lβ Hlβ.
        destruct (Pos.eq_dec β α) as [->|Hneq].
        - simpl in Hlβ. rewrite TMap.gss in Hlβ. injection Hlβ as ->.
          exists v. split; [apply sp_vertex_new|]. split.
          + intros Hg. exfalso. exact (proj2 Hfresh Hg).
          + intros _ ρ' π' Hposs'. apply HΔ' in Hposs'.
            destruct Hposs' as (ρ & π & Hposs & Hclos).
            destruct (lin_closure_find _ _ _ _ _ α Hclos) as [Hsame|[l' [v' [Hl' [Hv' [Hng' Hret]]]]]].
            * left. rewrite Hsame. now apply Htoken with ρ.
            * right. simpl in Hl'. rewrite TMap.gss in Hl'.
              injection Hl' as <-. rewrite sp_vertex_new in Hv'. injection Hv' as <-.
              exact Hret.
        - assert (Hlβs : TMap.find β (ts_pending_pushes s) = Some lβ).
          { simpl in Hlβ. rewrite TMap.gso in Hlβ by congruence. exact Hlβ. }
          destruct (I_state_pending _ _ HI β lβ Hlβs) as (vβ & Hvβ & Hgarbage & Hlive).
          assert (Hneqn : pair β lβ <> pair α l) by (intro Heq; injection Heq as -> _; contradiction).
          exists vβ. split; [rewrite sp_vertices; assumption|]. split.
          + intros Hg ρ' π' Hposs'. apply HΔ' in Hposs'.
            destruct Hposs' as (ρ & π & Hposs & Hclos).
            rewrite (lin_closure_find_noninv _ _ _ _ _ β Hclos).
            * apply (Hgarbage Hg _ _ Hposs).
            * intros v' Hinv. rewrite (Hgarbage Hg _ _ Hposs) in Hinv. discriminate.
          + intros Hng ρ' π' Hposs'. apply HΔ' in Hposs'.
            destruct Hposs' as (ρ & π & Hposs & Hclos).
            destruct (lin_closure_find _ _ _ _ _ β Hclos) as [Hsame|[l' [v' [Hl' [Hv' [Hng' Hret]]]]]].
            * rewrite Hsame. apply (Hlive Hng _ _ Hposs).
            * right. simpl in Hl'. rewrite TMap.gso in Hl' by congruence.
              rewrite Hlβs in Hl'. injection Hl' as <-.
              rewrite sp_vertices in Hv' by exact Hneqn. rewrite Hvβ in Hv'. injection Hv' as <-.
              exact Hret.
      Qed.

      Lemma pi_I_state : I_state (ts_start_push α l v s) Δ'.
      Proof.
        split; [exact Hwf'|]. split; [apply pi_I_stack|]. split; [apply pi_I_graph|apply pi_I_pending].
      Qed.
    End PushInv.


    (** * [I ∘ G_push-ret ⇒ I] *)

    Section PushRet.
      Variable s : @TryStackState A.
      Variables (α : tid) (l : Addr) (v : A).
      Variable Δ Δ' : config.
      Hypothesis HI : I_state s Δ.
      Hypothesis Hl : TMap.find α (ts_pending_pushes s) = Some l.
      Hypothesis Hv : ts_vertices s (pair α l) = Some v.
      Hypothesis HΔ' : forall ρ π, Δ' ρ π <->
        Δ ρ π /\ TMap.find α π = Some (push_ret_token v).

      Local Notation s' := (ts_finish_push α s).

      Lemma pr_live m : live s' m <-> live s m.
      Proof. reflexivity. Qed.

      Lemma pr_pending_not_alpha β lβ :
        TMap.find β (ts_pending_pushes s') = Some lβ ->
        TMap.find β (ts_pending_pushes s) = Some lβ /\ β <> α.
      Proof.
        intros H. assert (Hp : ts_is_pending s' (pair β lβ)) by exact H.
        apply fp_pending in Hp. exact Hp.
      Qed.

      (** The same permutation justifies the possibility: the vertex of
          [α] is not omitted because its token is [•]. *)
      Lemma pr_justified ρ π N :
        TMap.find α π = Some (push_ret_token v) ->
        justified s ρ π N -> justified s' ρ π N.
      Proof.
        intros Hret [Hperm [stk [Hvals Hρ]]]. split; [|exists stk; split; assumption].
        eapply perm_ext; [|eapply perm_edges_ext; [reflexivity|exact Hperm]].
        intros m. unfold stack_domain, omitted. rewrite fp_pending.
        destruct (Pos.eq_dec (fst m) α) as [Heq|Hneq].
        - split.
          + intros [Hlive Hnot]. split; [exact Hlive|]. intros [[_ Hbad] _]. contradiction.
          + intros [Hlive Hnot]. split; [exact Hlive|]. intros [Hp [v' Hv']].
            rewrite Heq, Hret in Hv'. discriminate.
        - tauto.
      Qed.

      Lemma pr_I_stack : I_stack s' Δ'.
      Proof.
        intros ρ π Hposs'. apply HΔ' in Hposs'. destruct Hposs' as [Hposs Hret].
        destruct (I_state_stack _ _ HI _ _ Hposs) as [N Hjust].
        exists N. apply pr_justified; assumption.
      Qed.

      Lemma pr_I_graph : I_graph s' Δ'.
      Proof.
        intros P' Hpset N Hperm stk Hstk.
        assert (Hpset0 : pending_set s P').
        { intros m Hm. apply Hpset in Hm. apply fp_pending in Hm. exact (proj1 Hm). }
        assert (Hperm0 : perm s (fun m => live s m /\ ~ P' m) N).
        { eapply perm_edges_ext; [reflexivity|exact Hperm]. }
        destruct (I_state_graph _ _ HI P' Hpset0 N Hperm0 stk Hstk) as [π [Hposs Htok]].
        exists π. split.
        - apply HΔ'. split; [exact Hposs|].
          destruct (Htok α l Hl) as (v' & Hv' & Hret & _).
          rewrite Hv in Hv'. injection Hv' as <-.
          apply Hret. intro HP. apply Hpset in HP. apply fp_pending in HP.
          destruct HP as [_ Hbad]. now apply Hbad.
        - intros β lβ Hlβ. destruct (pr_pending_not_alpha β lβ Hlβ) as [Hlβ0 _].
          exact (Htok β lβ Hlβ0).
      Qed.

      Lemma pr_I_pending : I_pending s' Δ'.
      Proof.
        intros β lβ Hlβ. destruct (pr_pending_not_alpha β lβ Hlβ) as [Hlβ0 _].
        destruct (I_state_pending _ _ HI β lβ Hlβ0) as (vβ & Hvβ & Hgarbage & Hlive).
        exists vβ. split; [exact Hvβ|]. split.
        - intros Hg ρ π Hposs'. apply HΔ' in Hposs'. apply (Hgarbage Hg _ _ (proj1 Hposs')).
        - intros Hng ρ π Hposs'. apply HΔ' in Hposs'. apply (Hlive Hng _ _ (proj1 Hposs')).
      Qed.

      Lemma pr_I_state : I_state s' Δ'.
      Proof.
        split; [apply fp_graph_wf; eapply I_state_wf; exact HI|].
        split; [apply pr_I_stack|]. split; [apply pr_I_graph|apply pr_I_pending].
      Qed.

      Lemma pr_nonempty :
        exists ρ π, Δ ρ π /\ TMap.find α π = Some (push_ret_token v).
      Proof.
        destruct (classic (ts_garbage s (pair α l))) as [Hg|Hng].
        - destruct (I_state_pending _ _ HI α l Hl) as (v' & Hv' & Hgarbage & _).
          rewrite Hv in Hv'. injection Hv' as <-.
          destruct (ac_nonempty Δ) as (ρ & π & Hposs).
          exists ρ, π. split; [exact Hposs|]. exact (Hgarbage Hg ρ π Hposs).
        - assert (Hlive : live s (pair α l)).
          { split; [eapply wf_pending_vertex; [eapply I_state_wf|]; eauto|exact Hng]. }
          destruct (pending_live_both_tokens _ _ _ _ _ HI Hl Hv Hlive) as [_ Hret].
          exact Hret.
      Qed.
    End PushRet.

    (** * [I ∘ G_pop ⇒ I] *)

    Section Pop.
      Variable s : @TryStackState A.
      Variables (α : tid) (n : LPNodeId) (v : A).
      Variable Δ Δ' : config.
      Hypothesis HI : I_state s Δ.
      Hypothesis Htop : lp_top (fun m => ts_is_live s m) (ts_edges s) n.
      Hypothesis Hv : ts_vertices s n = Some v.
      Hypothesis Hα : forall ρ π, Δ ρ π -> TMap.find α π = Some (ls_inv st_pop).

      Local Notation s' := (ts_mark_garbage n s).

      Let Hαnone : TMap.find α (ts_pending_pushes s) = None :=
        alin_inv_no_pending s Δ α st_pop HI Hα.

      Lemma pop_pending_not_alpha m : ts_is_pending s m -> fst m <> α.
      Proof.
        intros Hp Heq. unfold ts_is_pending in Hp. rewrite Heq, Hαnone in Hp. discriminate.
      Qed.

      Lemma pop_pending_same m : ts_is_pending s' m <-> ts_is_pending s m.
      Proof. reflexivity. Qed.

      Lemma pop_find_other π β :
        β <> α ->
        TMap.find β (TMap.add α (pop_ret_token (Some v)) (TMap.add α pop_lini_token π)) =
        TMap.find β π.
      Proof. intros Hneq. rewrite find_add_add, TMap.gso by congruence. reflexivity. Qed.

      Lemma pop_omitted_same π m :
        omitted s' (TMap.add α (pop_ret_token (Some v)) (TMap.add α pop_lini_token π)) m <->
        omitted s π m.
      Proof.
        unfold omitted. rewrite pop_pending_same. split.
        - intros [Hp [v' Hv']]. split; [exact Hp|]. exists v'.
          rewrite pop_find_other in Hv' by (apply pop_pending_not_alpha; exact Hp). exact Hv'.
        - intros [Hp [v' Hv']]. split; [exact Hp|]. exists v'.
          rewrite pop_find_other by (apply pop_pending_not_alpha; exact Hp). exact Hv'.
      Qed.

      Lemma pop_live_n : live s n.
      Proof. exact (proj1 Htop). Qed.

      (** The paper's [G_pop] argument for [I_graph]: extend a post-state
          permutation by the popped top vertex and read off the possibility
          delivered by the old [I_graph]. *)
      Lemma pop_witness P' N' stk' :
        pending_set s' P' ->
        perm s' (fun m => live s' m /\ ~ P' m) N' ->
        values_of s' N' stk' ->
        exists π,
          Δ (Idle (v :: stk')) π /\
          (ts_is_pending s n -> TMap.find (fst n) π = Some (push_ret_token v)) /\
          (exists N, justified s (Idle (v :: stk')) π (n :: N)) /\
          graph_tokens s' P'
            (TMap.add α (pop_ret_token (Some v)) (TMap.add α pop_lini_token π)).
      Proof.
        intros Hpset Hperm Hstk.
        set (P'' := fun m => P' m /\ m <> n).
        assert (Hpset'' : pending_set s P'').
        { intros m [Hm _]. apply Hpset in Hm. exact Hm. }
        assert (HnotinN' : ~ In n N').
        { intro Hin. destruct Hperm as [_ [_ Hmem]]. apply Hmem in Hin.
          destruct Hin as [Hlive _]. apply mg_live in Hlive. destruct Hlive as [_ Hbad]. now apply Hbad. }
        assert (Hperm0 : perm s (fun m => live s m /\ ~ P'' m) (n :: N')).
        { destruct Hperm as [Hnodup [Hcompat Hmem]]. split; [|split].
          - constructor; assumption.
          - split; [|exact Hcompat].
            intros m Hin Hedge. apply Hmem in Hin. destruct Hin as [Hlive _].
            apply mg_live in Hlive. destruct Hlive as [Hlive _].
            exact (proj2 Htop m Hlive Hedge).
          - intros m. simpl. rewrite Hmem, mg_live. unfold P''. split.
            + intros [Heq|[[Hlive Hneq] HnP]].
              * subst m. split; [exact pop_live_n|]. intros [_ Hbad]. now apply Hbad.
              * split; [exact Hlive|]. intros [HP _]. contradiction.
            + intros [Hlive HnP''].
              destruct (node_eq_dec n m) as [Heq|Hneq]; [now left|].
              right. split; [split; [exact Hlive|congruence]|].
              intro HP. apply HnP''. split; [exact HP|congruence]. }
        assert (Hstk0 : values_of s (n :: N') (v :: stk')).
        { constructor; [exact Hv|exact Hstk]. }
        destruct (I_state_graph _ _ HI P'' Hpset'' (n :: N') Hperm0 (v :: stk') Hstk0)
          as [π [Hposs Htok]].
        exists π. split; [exact Hposs|]. split; [|split].
        - intros Hp. destruct n as [β lβ]. simpl.
          destruct (Htok β lβ Hp) as (v' & Hv' & Hret & _).
          rewrite Hv in Hv'. injection Hv' as <-.
          apply Hret. intros [_ Hbad]. now apply Hbad.
        - exists N'. split; [|exists (v :: stk'); split; [exact Hstk0|reflexivity]].
          eapply perm_ext; [|exact Hperm0].
          intros m. unfold stack_domain. split.
          + intros [Hlive HnP'']. split; [exact Hlive|]. intros [Hp [v' Hv']].
            destruct m as [β lβ].
            destruct (Htok β lβ Hp) as (v'' & Hv'' & Hret & _).
            simpl in Hv'. rewrite Hret in Hv'; [discriminate|exact HnP''].
          + intros [Hlive Hnot]. split; [exact Hlive|]. intros HP''.
            pose proof (Hpset'' m HP'') as Hp. destruct m as [β lβ].
            destruct (Htok β lβ Hp) as (v' & Hv' & _ & Hinv).
            apply Hnot. split; [exact Hp|]. exists v'. apply Hinv; assumption.
        - intros β lβ Hlβ.
          assert (Hp : ts_is_pending s (pair β lβ)) by exact Hlβ.
          pose proof (pop_pending_not_alpha _ Hp) as Hneq. simpl in Hneq.
          destruct (Htok β lβ Hlβ) as (vβ & Hvβ & Hret & Hinv).
          exists vβ. split; [exact Hvβ|]. rewrite pop_find_other by exact Hneq. split.
          + intros HnP. apply Hret. intros [HP _]. contradiction.
          + intros HP Hlive. apply mg_live in Hlive. destruct Hlive as [Hlive Hneqn].
            apply Hinv; [split; assumption|exact Hlive].
      Qed.

      Lemma pop_nonempty :
        exists stk π,
          Δ (Idle (v :: stk)) π /\
          (ts_is_pending s n -> TMap.find (fst n) π = Some (push_ret_token v)) /\
          (exists N', justified s (Idle (v :: stk)) π (n :: N')).
      Proof.
        assert (Hwf' : graph_wf s').
        { apply mg_graph_wf; [eapply I_state_wf; exact HI|apply live_vertex; exact pop_live_n]. }
        assert (Hpset : pending_set s' (fun _ : LPNodeId => False)) by (intros m Hm; contradiction).
        destruct (perm_exists s' (fun m => live s' m /\ ~ False) Hwf') as [N' Hperm].
        { intros m [Hm _]. apply live_vertex. exact Hm. }
        destruct (values_exist s' N') as [stk' Hstk].
        { intros m Hm. eapply perm_vertices; [|exact Hperm|exact Hm].
          intros m' [Hm' _]. apply live_vertex. exact Hm'. }
        destruct (pop_witness _ N' stk' Hpset Hperm Hstk) as (π & Hposs & Hpend & Hjust & _).
        exists stk', π. auto.
      Qed.
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists stk π,
          Δ (Idle (v :: stk)) π /\
          (ts_is_pending s n -> TMap.find (fst n) π = Some (push_ret_token v)) /\
          (exists N', justified s (Idle (v :: stk)) π (n :: N')) /\
          ρ' = Idle stk /\
          π' = TMap.add α (pop_ret_token (Some v)) (TMap.add α pop_lini_token π).

      Lemma pop_I_stack : I_stack s' Δ'.
      Proof.
        intros ρ' π' Hposs'. apply HΔ' in Hposs'.
        destruct Hposs' as (stk & π & Hposs & Hpend & [N' [Hperm [stk0 [Hvals Hρ]]]] & -> & ->).
        injection Hρ as <-.
        destruct Hperm as [Hnodup [Hcompat Hmem]].
        apply NoDup_cons_iff in Hnodup. destruct Hnodup as [Hnotin Hnodup].
        destruct Hcompat as [_ Hcompat].
        inversion Hvals as [|n0 v0 N0 stk1 Hn0 Hvals']; subst.
        exists N'. split.
        - split; [exact Hnodup|]. split; [exact Hcompat|].
          intros m. unfold stack_domain. rewrite mg_live, pop_omitted_same.
          specialize (Hmem m). simpl in Hmem. split.
          + intros Hin. assert (Hin' : n = m \/ In m N') by (right; exact Hin).
            apply Hmem in Hin'. destruct Hin' as [Hlive Hnot].
            split; [split; [exact Hlive|]|exact Hnot].
            intro Heq. subst m. contradiction.
          + intros [[Hlive Hneq] Hnot].
            assert (Hin' : n = m \/ In m N') by (apply Hmem; split; assumption).
            destruct Hin' as [Heq|Hin]; [symmetry in Heq; contradiction|exact Hin].
        - eexists. split; [exact Hvals'|reflexivity].
      Qed.

      Lemma pop_I_graph : I_graph s' Δ'.
      Proof.
        intros P' Hpset N' Hperm stk' Hstk.
        destruct (pop_witness P' N' stk' Hpset Hperm Hstk) as (π & Hposs & Hpend & Hjust & Htok).
        eexists. split; [|exact Htok].
        apply HΔ'. exists stk', π. repeat split; auto.
      Qed.

      Lemma pop_I_pending : I_pending s' Δ'.
      Proof.
        intros β lβ Hlβ.
        assert (Hp : ts_is_pending s (pair β lβ)) by exact Hlβ.
        pose proof (pop_pending_not_alpha _ Hp) as Hneq. simpl in Hneq.
        destruct (I_state_pending _ _ HI β lβ Hlβ) as (vβ & Hvβ & Hgarbage & Hlive).
        exists vβ. split; [exact Hvβ|]. split.
        - intros Hg ρ' π' Hposs'. apply HΔ' in Hposs'.
          destruct Hposs' as (stk & π & Hposs & Hpend & _ & -> & ->).
          rewrite pop_find_other by exact Hneq.
          apply mg_garbage in Hg. destruct Hg as [Heq|Hg].
          + subst n. simpl in Hpend. rewrite Hv in Hvβ. injection Hvβ as <-.
            now apply Hpend.
          + exact (Hgarbage Hg _ _ Hposs).
        - intros Hng ρ' π' Hposs'. apply HΔ' in Hposs'.
          destruct Hposs' as (stk & π & Hposs & Hpend & _ & -> & ->).
          rewrite pop_find_other by exact Hneq.
          apply (Hlive (fun Hg => Hng (proj2 (mg_garbage s n (pair β lβ)) (or_intror Hg))) _ _ Hposs).
      Qed.

      Lemma pop_I_state : I_state s' Δ'.
      Proof.
        split; [apply mg_graph_wf; [eapply I_state_wf; exact HI|apply live_vertex; exact pop_live_n]|].
        split; [apply pop_I_stack|]. split; [apply pop_I_graph|apply pop_I_pending].
      Qed.

    End Pop.

    (** * [I ∘ G_pop-emp ⇒ I] *)

    Section PopEmp.
      Variable s : @TryStackState A.
      Variable α : tid.
      Variable Δ Δ' : config.
      Hypothesis HI : I_state s Δ.
      Hypothesis Hall : ts_all_vertices_garbage s.
      Hypothesis Hα : forall ρ π, Δ ρ π -> TMap.find α π = Some (ls_inv st_pop).

      Let Hαnone : TMap.find α (ts_pending_pushes s) = None :=
        alin_inv_no_pending s Δ α st_pop HI Hα.

      Lemma pe_no_live m : ~ live s m.
      Proof. intros [Hv Hng]. apply Hng. apply Hall. exact Hv. Qed.

      Lemma pe_perm_nil (X : LPNodeSet) N :
        (forall m, X m -> live s m) -> perm s X N -> N = nil.
      Proof.
        intros Hsub [_ [_ Hmem]]. destruct N as [|m N]; [reflexivity|].
        exfalso. apply (pe_no_live m). apply Hsub. apply Hmem. now left.
      Qed.

      Lemma pe_find_other π β :
        β <> α ->
        TMap.find β (TMap.add α (pop_ret_token None) (TMap.add α pop_lini_token π)) =
        TMap.find β π.
      Proof. intros Hneq. rewrite find_add_add, TMap.gso by congruence. reflexivity. Qed.

      Lemma pe_nonempty : exists π, Δ (Idle nil) π.
      Proof.
        destruct (ac_nonempty Δ) as (ρ & π & Hposs).
        destruct (I_state_stack _ _ HI _ _ Hposs) as [N [Hperm [stk [Hvals ->]]]].
        assert (HN : N = nil).
        { eapply pe_perm_nil; [|exact Hperm]. intros m [Hm _]. exact Hm. }
        subst N. inversion Hvals; subst. exists π. exact Hposs.
      Qed.
      Hypothesis HΔ' : forall ρ' π', Δ' ρ' π' <->
        exists π, Δ (Idle nil) π /\
          ρ' = Idle nil /\
          π' = TMap.add α (pop_ret_token None) (TMap.add α pop_lini_token π).

      Lemma pe_I_stack : I_stack s Δ'.
      Proof.
        intros ρ' π' Hposs'. apply HΔ' in Hposs'. destruct Hposs' as (π & Hposs & -> & ->).
        exists nil. split.
        - unfold perm. split; [constructor|]. split; [simpl; trivial|].
          intros m. unfold stack_domain. simpl. split.
          + intros Hin. contradiction.
          + intros [Hlive _]. exact (pe_no_live m Hlive).
        - exists nil. split; [constructor|reflexivity].
      Qed.

      Lemma pe_I_graph : I_graph s Δ'.
      Proof.
        intros P' Hpset N Hperm stk Hstk.
        assert (HN : N = nil).
        { eapply pe_perm_nil; [|exact Hperm]. intros m [Hm _]. exact Hm. }
        subst N. inversion Hstk; subst.
        destruct (I_state_graph _ _ HI P' Hpset nil Hperm nil Hstk) as [π [Hposs Htok]].
        eexists. split.
        - apply HΔ'. exists π. auto.
        - intros β lβ Hlβ.
          assert (Hneq : β <> α) by (intro; subst; congruence).
          destruct (Htok β lβ Hlβ) as (vβ & Hvβ & Hret & Hinv).
          exists vβ. split; [exact Hvβ|]. rewrite pe_find_other by exact Hneq. auto.
      Qed.

      Lemma pe_I_pending : I_pending s Δ'.
      Proof.
        intros β lβ Hlβ.
        assert (Hneq : β <> α) by (intro; subst; congruence).
        destruct (I_state_pending _ _ HI β lβ Hlβ) as (vβ & Hvβ & Hgarbage & Hlive).
        exists vβ. split; [exact Hvβ|]. split.
        - intros Hg ρ' π' Hposs'. apply HΔ' in Hposs'. destruct Hposs' as (π & Hposs & -> & ->).
          rewrite pe_find_other by exact Hneq. exact (Hgarbage Hg _ _ Hposs).
        - intros Hng ρ' π' Hposs'. apply HΔ' in Hposs'. destruct Hposs' as (π & Hposs & -> & ->).
          rewrite pe_find_other by exact Hneq. exact (Hlive Hng _ _ Hposs).
      Qed.

      Lemma pe_I_state : I_state s Δ'.
      Proof.
        split; [eapply I_state_wf; exact HI|].
        split; [apply pe_I_stack|]. split; [apply pe_I_graph|apply pe_I_pending].
      Qed.

    End PopEmp.

    (** * Administrative steps: invocation and return of the overlay *)

    Lemma I_state_equiv s (Δ Δ' : config) :
      (forall ρ π, Δ ρ π <-> Δ' ρ π) -> I_state s Δ -> I_state s Δ'.
    Proof.
      intros Heq [Hwf [Hstack [Hgraph Hpend]]]. split; [exact Hwf|]. split; [|split].
      - intros ρ π Hposs. apply Heq in Hposs. now apply Hstack.
      - intros P' Hpset N Hperm stk Hstk.
        destruct (Hgraph P' Hpset N Hperm stk Hstk) as [π [Hposs Htok]].
        exists π. split; [apply Heq; exact Hposs|exact Htok].
      - intros β lβ Hlβ. destruct (Hpend β lβ Hlβ) as (vβ & Hvβ & Hg & Hl).
        exists vβ. split; [exact Hvβ|]. split.
        + intros Hgb ρ π Hposs. apply Heq in Hposs. exact (Hg Hgb ρ π Hposs).
        + intros Hng ρ π Hposs. apply Heq in Hposs. exact (Hl Hng ρ π Hposs).
    Qed.

    (** A thread with a pending entry has a token in every possibility. *)
    Lemma pending_has_token s (Δ : config) t l ρ π :
      I_state s Δ -> TMap.find t (ts_pending_pushes s) = Some l ->
      Δ ρ π -> exists ls, TMap.find t π = Some ls.
    Proof.
      intros HI Hl Hposs.
      destruct (I_state_pending _ _ HI t l Hl) as (v & Hv & Hg & Hlive).
      destruct (classic (ts_garbage s (pair t l))) as [Hgb|Hng].
      - exists (push_ret_token v). exact (Hg Hgb _ _ Hposs).
      - destruct (Hlive Hng _ _ Hposs) as [H|H]; eauto.
    Qed.

    Lemma omitted_add_other s π t ls m :
      TMap.find t (ts_pending_pushes s) = None ->
      (omitted s (TMap.add t ls π) m <-> omitted s π m).
    Proof.
      intros Hnone. unfold omitted. split.
      - intros [Hp [v Hv]]. split; [exact Hp|]. exists v.
        rewrite TMap.gso in Hv; [exact Hv|].
        intro Heq. unfold ts_is_pending in Hp. rewrite Heq, Hnone in Hp. discriminate.
      - intros [Hp [v Hv]]. split; [exact Hp|]. exists v.
        rewrite TMap.gso; [exact Hv|].
        intro Heq. unfold ts_is_pending in Hp. rewrite Heq, Hnone in Hp. discriminate.
    Qed.

    Lemma omitted_remove_other s π t m :
      TMap.find t (ts_pending_pushes s) = None ->
      (omitted s (TMap.remove t π) m <-> omitted s π m).
    Proof.
      intros Hnone. unfold omitted. split.
      - intros [Hp [v Hv]]. split; [exact Hp|]. exists v.
        rewrite TMap.gro in Hv; [exact Hv|].
        intro Heq. unfold ts_is_pending in Hp. rewrite Heq, Hnone in Hp. discriminate.
      - intros [Hp [v Hv]]. split; [exact Hp|]. exists v.
        rewrite TMap.gro; [exact Hv|].
        intro Heq. unfold ts_is_pending in Hp. rewrite Heq, Hnone in Hp. discriminate.
    Qed.

    Lemma justified_add_other s ρ π t ls N :
      TMap.find t (ts_pending_pushes s) = None ->
      justified s ρ π N -> justified s ρ (TMap.add t ls π) N.
    Proof.
      intros Hnone [Hperm Hstk]. split; [|exact Hstk].
      eapply perm_ext; [|exact Hperm]. intros m. unfold stack_domain.
      rewrite omitted_add_other by exact Hnone. reflexivity.
    Qed.

    Lemma justified_remove_other s ρ π t N :
      TMap.find t (ts_pending_pushes s) = None ->
      justified s ρ π N -> justified s ρ (TMap.remove t π) N.
    Proof.
      intros Hnone [Hperm Hstk]. split; [|exact Hstk].
      eapply perm_ext; [|exact Hperm]. intros m. unfold stack_domain.
      rewrite omitted_remove_other by exact Hnone. reflexivity.
    Qed.

    Lemma ginv_I_state s (Δ : config) t (f : Sig.op (li_sig F)) :
      I_state s Δ ->
      (forall ρ π, Δ ρ π -> TMap.find t π = None) ->
      I_state s (ac_inv Δ t f).
    Proof.
      intros HI Hnone.
      assert (Htnone : TMap.find t (ts_pending_pushes s) = None).
      { destruct (TMap.find t (ts_pending_pushes s)) as [l|] eqn:Hl; [|reflexivity].
        exfalso. destruct (ac_nonempty Δ) as (ρ & π & Hposs).
        destruct (pending_has_token _ _ _ _ _ _ HI Hl Hposs) as [ls Hls].
        rewrite (Hnone _ _ Hposs) in Hls. discriminate. }
      destruct HI as [Hwf [Hstack [Hgraph Hpend]]].
      split; [exact Hwf|]. split; [|split].
      - intros ρ π Hposs. inversion Hposs; subst.
        destruct (Hstack _ _ Hposs0) as [N Hjust].
        exists N. apply justified_add_other; assumption.
      - intros P' Hpset N Hperm stk Hstk.
        destruct (Hgraph P' Hpset N Hperm stk Hstk) as [π [Hposs Htok]].
        exists (TMap.add t (ls_inv f) π). split; [constructor; exact Hposs|].
        intros β lβ Hlβ. destruct (Htok β lβ Hlβ) as (vβ & Hvβ & Hret & Hinv).
        exists vβ. split; [exact Hvβ|].
        rewrite TMap.gso by (intro; subst; congruence). auto.
      - intros β lβ Hlβ. destruct (Hpend β lβ Hlβ) as (vβ & Hvβ & Hg & Hl).
        exists vβ. split; [exact Hvβ|].
        assert (Hneq : β <> t) by (intro; subst; congruence).
        split.
        + intros Hgb ρ π Hposs. inversion Hposs; subst.
          rewrite TMap.gso by exact Hneq. exact (Hg Hgb _ _ Hposs0).
        + intros Hng ρ π Hposs. inversion Hposs; subst.
          rewrite TMap.gso by exact Hneq. exact (Hl Hng _ _ Hposs0).
    Qed.

    Lemma gret_I_state s (Δ : config) t :
      I_state s Δ ->
      TMap.find t (ts_pending_pushes s) = None ->
      I_state s (ac_res Δ t).
    Proof.
      intros HI Htnone.
      destruct HI as [Hwf [Hstack [Hgraph Hpend]]].
      split; [exact Hwf|]. split; [|split].
      - intros ρ π Hposs. inversion Hposs; subst.
        destruct (Hstack _ _ Hposs0) as [N Hjust].
        exists N. apply justified_remove_other; assumption.
      - intros P' Hpset N Hperm stk Hstk.
        destruct (Hgraph P' Hpset N Hperm stk Hstk) as [π [Hposs Htok]].
        exists (TMap.remove t π). split; [constructor; exact Hposs|].
        intros β lβ Hlβ. destruct (Htok β lβ Hlβ) as (vβ & Hvβ & Hret & Hinv).
        exists vβ. split; [exact Hvβ|].
        rewrite TMap.gro by (intro; subst; congruence). auto.
      - intros β lβ Hlβ. destruct (Hpend β lβ Hlβ) as (vβ & Hvβ & Hg & Hl).
        exists vβ. split; [exact Hvβ|].
        assert (Hneq : β <> t) by (intro; subst; congruence).
        split.
        + intros Hgb ρ π Hposs. inversion Hposs; subst.
          rewrite TMap.gro by exact Hneq. exact (Hg Hgb _ _ Hposs0).
        + intros Hng ρ π Hposs. inversion Hposs; subst.
          rewrite TMap.gro by exact Hneq. exact (Hl Hng _ _ Hposs0).
    Qed.

    (** * Abstract-configuration constructors for the updates *)

    (** The image of [Δc] under the paper's [push] relation. *)
    Variant ac_lin_prop s (Δc : config) : @AbstractConfigProp _ (li_lts F) :=
    | ACLin ρ π ρ' π' (Hposs : Δc ρ π) (Hlin : lin_closure s ρ π ρ' π') :
        ac_lin_prop s Δc ρ' π'.

    Program Definition ac_lin s (Δc : config) : config :=
      {| ac_active := ac_active Δc; ac_prop := ac_lin_prop s Δc |}.
    Next Obligation.
      destruct (ac_nonempty Δc) as (ρ & π & Hposs).
      exists ρ, π. econstructor; [exact Hposs|constructor].
    Qed.
    Next Obligation.
      inversion H; subst.
      eapply domain_equiv_trans.
      - apply domain_equiv_symm. eapply poss_steps_domain.
        eapply lin_closure_poss_steps. exact Hlin.
      - eapply ac_domain. exact Hposs.
    Qed.

    Lemma ac_lin_subset_steps s Δc :
      ac_subset (ac_lin s Δc) (ac_steps Δc).
    Proof.
      intros ρ' π' Hposs'. inversion Hposs'; subst.
      econstructor; [exact Hposs|]. eapply lin_closure_poss_steps. exact Hlin.
    Qed.

    Lemma ac_lin_iff s Δc ρ' π' :
      ac_lin s Δc ρ' π' <-> exists ρ π, Δc ρ π /\ lin_closure s ρ π ρ' π'.
    Proof.
      split.
      - intros H. inversion H; subst. eauto.
      - intros (ρ & π & Hposs & Hlin). econstructor; eauto.
    Qed.

    (** Selecting possibilities and stepping each of them. *)
    Variant ac_select_prop (Δc : config)
        (sel : abstract_state -> tmap lin_state -> Prop)
        (ρf : abstract_state -> abstract_state)
        (πf : tmap lin_state -> tmap lin_state) :
        @AbstractConfigProp _ (li_lts F) :=
    | ACSelect ρ π (Hposs : Δc ρ π) (Hsel : sel ρ π) :
        ac_select_prop Δc sel ρf πf (ρf ρ) (πf π).

    Program Definition ac_select (Δc : config)
        (sel : abstract_state -> tmap lin_state -> Prop)
        (ρf : abstract_state -> abstract_state)
        (πf : tmap lin_state -> tmap lin_state)
        (Hsteps : forall ρ π, Δc ρ π -> sel ρ π ->
          poss_steps (PossOk ρ π) (PossOk (ρf ρ) (πf π)))
        (Hne : exists ρ π, Δc ρ π /\ sel ρ π) : config :=
      {| ac_active := ac_active Δc; ac_prop := ac_select_prop Δc sel ρf πf |}.
    Next Obligation.
      destruct Hne as (ρ & π & Hposs & Hsel).
      exists (ρf ρ), (πf π). constructor; assumption.
    Qed.
    Next Obligation.
      inversion H; subst.
      eapply domain_equiv_trans.
      - apply domain_equiv_symm. eapply poss_steps_domain. eapply Hsteps; eassumption.
      - eapply ac_domain. eassumption.
    Qed.

    Lemma ac_select_subset_steps Δc sel ρf πf Hsteps Hne :
      ac_subset (ac_select Δc sel ρf πf Hsteps Hne) (ac_steps Δc).
    Proof.
      intros ρ' π' Hposs'. inversion Hposs'; subst.
      econstructor; [exact Hposs|]. apply Hsteps; assumption.
    Qed.

    Lemma ac_select_iff Δc sel ρf πf Hsteps Hne ρ' π' :
      ac_select Δc sel ρf πf Hsteps Hne ρ' π' <->
      exists ρ π, Δc ρ π /\ sel ρ π /\ ρ' = ρf ρ /\ π' = πf π.
    Proof.
      split.
      - intros H. inversion H; subst. do 2 eexists.
        repeat split; first [eassumption|reflexivity].
      - intros (ρ & π & Hposs & Hsel & -> & ->). constructor; assumption.
    Qed.


    (** * Shapes of the underlay steps *)

    Ltac invert_ts_step Hstep :=
      simpl in Hstep;
      inversion Hstep; subst;
      match goal with
      | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ =>
          dependent destruction H
      end.

    Lemma ts_push_inv_shape α (v : A) (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (InvEv (ts_push v))) σ σ' ->
      exists s l,
        σ = TSReady s /\
        TMap.find α (ts_pending_pushes s) = None /\
        ts_fresh_node s (pair α l) /\
        σ' = TSReady (ts_start_push α l v s).
    Proof.
      intros Hstep. invert_ts_step Hstep.
      do 2 eexists. split; [reflexivity|]. split; [eassumption|].
      split; [eassumption|reflexivity].
    Qed.

    Lemma ts_push_res_shape α (v : A) (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (ResEv (ts_push v) tt)) σ σ' ->
      exists s l,
        σ = TSReady s /\
        TMap.find α (ts_pending_pushes s) = Some l /\
        σ' = TSReady (ts_finish_push α s).
    Proof.
      intros Hstep. invert_ts_step Hstep.
      do 2 eexists. split; [reflexivity|]. split; [eassumption|reflexivity].
    Qed.

    Lemma ts_trypop_inv_shape α (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (InvEv ts_trypop)) σ σ' ->
      exists s, σ = TSReady s /\ σ' = TSAtomicPending s α ts_trypop.
    Proof.
      intros Hstep. invert_ts_step Hstep. eexists. split; reflexivity.
    Qed.

    Lemma ts_trypop_res_shape α (ret : @TResult A) (σ σ' : concrete_state) :
      Step (li_lts E) (Build_ThreadEvent α (ResEv ts_trypop ret)) σ σ' ->
      exists s,
        σ = TSAtomicPending s α ts_trypop /\
        ((exists n v,
            ret = TSuccNode v (fst n) (snd n) /\
            lp_top (fun m => ts_is_live s m) (ts_edges s) n /\
            ts_vertices s n = Some v /\
            σ' = TSReady (ts_mark_garbage n s)) \/
         (ret = TSuccEmpty /\ ts_all_vertices_garbage s /\ σ' = TSReady s) \/
         (ret = TFail /\ σ' = TSReady s)).
    Proof.
      intros Hstep. simpl in Hstep.
      inversion Hstep; subst;
        match goal with
        | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ =>
            first [ discriminate H
                  | pose proof (f_equal te_tid H) as Hact; simpl in Hact; subst;
                    pose proof (f_equal te_ev H) as Hev; simpl in Hev;
                    apply ResEvInversion in Hev ]
        end.
      - eexists. split; [reflexivity|]. left. do 2 eexists.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|reflexivity].
      - eexists. split; [reflexivity|]. right. left.
        split; [eassumption|]. split; [eassumption|reflexivity].
      - eexists. split; [reflexivity|]. right. right.
        split; [eassumption|reflexivity].
    Qed.

    (** * What other threads' steps preserve *)

    Definition other_facts (obs : tid) (w w' : proof_state) : Prop :=
      TMap.find obs (ts_pending_pushes (graph_of w)) =
        TMap.find obs (ts_pending_pushes (graph_of w')) /\
      (forall n v, ts_vertices (graph_of w) n = Some v ->
        ts_vertices (graph_of w') n = Some v) /\
      ((exists s0 op, SetPossState.σ w = TSAtomicPending s0 obs op) ->
        SetPossState.σ w' = SetPossState.σ w) /\
      (TMap.find obs (ts_pending_pushes (graph_of w)) = None ->
        forall ρ' π', SetPossState.Δ w' ρ' π' ->
          exists ρ π, SetPossState.Δ w ρ π /\
            TMap.find obs π' = TMap.find obs π) /\
      (exists ρ' π' ρ π,
        SetPossState.Δ w' ρ' π' /\ SetPossState.Δ w ρ π /\
        (TMap.find obs π = None <-> TMap.find obs π' = None)).

    Lemma some_none_iff (x y : lin_state) :
      Some x = None <-> Some y = None.
    Proof. split; discriminate. Qed.

    Lemma G_other_facts actor w w' obs :
      obs <> actor -> G actor w w' -> other_facts obs w w'.
    Proof.
      intros Hneq HG.
      destruct HG as [HG|[HG|[HG|[HG|HG]]]].
      - destruct HG as [s l v w w' Hσ Hnone Hfresh Htok Hσ' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. cbn [payload].
        split; [|split; [|split; [|split]]].
        + change (ts_pending_pushes (ts_start_push actor l v s))
            with (TMap.add actor l (ts_pending_pushes s)).
          rewrite TMap.gso by congruence. reflexivity.
        + intros n v0 Hv0. rewrite sp_vertices; [exact Hv0|].
          intro Heq. subst n. destruct Hfresh as [Hn _]. congruence.
        + intros [s0 [op Heq]]. discriminate.
        + intros Hobs ρ' π' Hposs'. apply HΔ' in Hposs'.
          destruct Hposs' as (ρ & π & Hposs & Hclos).
          exists ρ, π. split; [exact Hposs|].
          eapply lin_closure_find_nopending; [exact Hclos|].
          change (ts_pending_pushes (ts_start_push actor l v s))
            with (TMap.add actor l (ts_pending_pushes s)).
          rewrite TMap.gso by congruence. exact Hobs.
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''.
          destruct Hposs'' as (ρ & π & Hposs & Hclos).
          exists ρ', π', ρ, π. split; [exact Hposs'|]. split; [exact Hposs|].
          destruct (lin_closure_find _ _ _ _ _ obs Hclos)
            as [Hsame|[l0 [v0 [Hl0 [Hv0 [Hng0 Hret]]]]]].
          * rewrite Hsame. reflexivity.
          * rewrite Hret.
            destruct (TMap.find obs π) as [x|] eqn:Hx.
            -- apply some_none_iff.
            -- exfalso.
               pose proof (lin_closure_find_noninv _ _ _ _ _ obs Hclos) as Hkeep.
               rewrite Hret, Hx in Hkeep. discriminate Hkeep.
               intros v1 Hbad. try rewrite Hx in Hbad. discriminate.
      - destruct HG as [s l v w w' Hσ Hl Hv Hσ' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. simpl.
        split; [|split; [|split; [|split]]].
        + rewrite TMap.gro by congruence. reflexivity.
        + intros n v0 Hv0. exact Hv0.
        + intros [s0 [op Heq]]. discriminate.
        + intros _ ρ' π' Hposs'. apply HΔ' in Hposs'. destruct Hposs' as [Hposs _].
          exists ρ', π'. split; [exact Hposs|reflexivity].
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''. destruct Hposs'' as [Hposs _].
          exists ρ', π', ρ', π'. repeat split; auto.
      - destruct HG as [s n v w w' Hσ Htop Hv Hα Hσ' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. simpl.
        split; [|split; [|split; [|split]]].
        + reflexivity.
        + intros n0 v0 Hv0. exact Hv0.
        + intros [s0 [op Heq]]. injection Heq as _ Heq _. congruence.
        + intros _ ρ' π' Hposs'. apply HΔ' in Hposs'.
          destruct Hposs' as (stk & π & Hposs & _ & _ & -> & ->).
          exists (Idle (v :: stk)), π. split; [exact Hposs|].
          rewrite find_add_add, TMap.gso by congruence. reflexivity.
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''.
          destruct Hposs'' as (stk & π & Hposs & _ & _ & -> & ->).
          exists (Idle stk), (TMap.add actor (pop_ret_token (Some v)) (TMap.add actor pop_lini_token π)),
            (Idle (v :: stk)), π.
          split; [exact Hposs'|]. split; [exact Hposs|].
          rewrite find_add_add, TMap.gso by congruence. reflexivity.
      - destruct HG as [s w w' Hσ Hall Hα Hσ' HΔ'].
        unfold other_facts, graph_of. rewrite Hσ, Hσ'. simpl.
        split; [|split; [|split; [|split]]].
        + reflexivity.
        + intros n0 v0 Hv0. exact Hv0.
        + intros [s0 [op Heq]]. injection Heq as _ Heq _. congruence.
        + intros _ ρ' π' Hposs'. apply HΔ' in Hposs'.
          destruct Hposs' as (π & Hposs & -> & ->).
          exists (Idle nil), π. split; [exact Hposs|].
          rewrite find_add_add, TMap.gso by congruence. reflexivity.
        + destruct (ac_nonempty (SetPossState.Δ w')) as (ρ' & π' & Hposs').
          pose proof Hposs' as Hposs''. apply HΔ' in Hposs''.
          destruct Hposs'' as (π & Hposs & -> & ->).
          exists (Idle nil), (TMap.add actor (pop_ret_token None) (TMap.add actor pop_lini_token π)),
            (Idle nil), π.
          split; [exact Hposs'|]. split; [exact Hposs|].
          rewrite find_add_add, TMap.gso by congruence. reflexivity.
      - destruct HG as [s w w' Hσ Hσ' HΔ'|s w w' Hσ Hσ' HΔ'].
        + unfold other_facts, graph_of. rewrite Hσ, Hσ', HΔ'. simpl.
          split; [reflexivity|]. split; [intros; assumption|]. split.
          * intros [s0 [op Heq]]. discriminate.
          * split.
            -- intros _ ρ' π' Hposs'. exists ρ', π'. split; [exact Hposs'|reflexivity].
            -- destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
               exists ρ, π, ρ, π. repeat split; auto.
        + unfold other_facts, graph_of. rewrite Hσ, Hσ', HΔ'. simpl.
          split; [reflexivity|]. split; [intros; assumption|]. split.
          * intros [s0 [op Heq]]. injection Heq as _ Heq _. congruence.
          * split.
            -- intros _ ρ' π' Hposs'. exists ρ', π'. split; [exact Hposs'|reflexivity].
            -- destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
               exists ρ, π, ρ, π. repeat split; auto.
    Qed.

    Lemma GINV_other_facts actor w w' obs :
      obs <> actor -> GINV actor w w' -> other_facts obs w w'.
    Proof.
      intros Hneq [f [Hσ [Hnone Hequiv]]].
      unfold other_facts, graph_of. rewrite Hσ.
      split; [reflexivity|]. split; [intros; assumption|]. split; [intros; reflexivity|].
      split.
      - intros _ ρ' π' Hposs'. apply Hequiv in Hposs'. inversion Hposs'; subst.
        exists ρ', π. split; [exact Hposs|]. rewrite TMap.gso by congruence. reflexivity.
      - destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
        exists ρ, (TMap.add actor (ls_inv f) π), ρ, π. split.
        + apply Hequiv. constructor. exact Hposs.
        + split; [exact Hposs|]. rewrite TMap.gso by congruence. reflexivity.
    Qed.

    Lemma GRET_other_facts actor w w' obs :
      obs <> actor -> GRET actor w w' -> other_facts obs w w'.
    Proof.
      intros Hneq [f [ret [Hσ [Hall Hequiv]]]].
      unfold other_facts, graph_of. rewrite Hσ.
      split; [reflexivity|]. split; [intros; assumption|]. split; [intros; reflexivity|].
      split.
      - intros _ ρ' π' Hposs'. apply Hequiv in Hposs'. inversion Hposs'; subst.
        exists ρ', π. split; [exact Hposs|]. rewrite TMap.gro by congruence. reflexivity.
      - destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
        exists ρ, (TMap.remove actor π), ρ, π. split.
        + apply Hequiv. constructor. exact Hposs.
        + split; [exact Hposs|]. rewrite TMap.gro by congruence. reflexivity.
    Qed.

    Lemma R_other_facts obs w w' :
      R obs w w' -> other_facts obs w w'.
    Proof.
      intros [[actor [Hneq HG]]|[[actor [Hneq Hinv]]|[[actor [Hneq Hret]]|Heq]]].
      - eapply G_other_facts; eauto.
      - eapply GINV_other_facts; eauto.
      - eapply GRET_other_facts; eauto.
      - subst w'. unfold other_facts.
        split; [reflexivity|]. split; [intros; assumption|]. split; [intros; reflexivity|].
        split.
        + intros _ ρ' π' Hposs'. exists ρ', π'. split; [exact Hposs'|reflexivity].
        + destruct (ac_nonempty (SetPossState.Δ w)) as (ρ & π & Hposs).
          exists ρ, π, ρ, π. repeat split; auto.
    Qed.

    (** * Stability *)

    Lemma I_stable t : AssertionsSet.A.Stable (R t) I I.
    Proof. apply AssertionsSet.A.Stable_invariant. Qed.

    Lemma alin_stable_core t (ls : lin_state) w w' :
      R t w w' ->
      TMap.find t (ts_pending_pushes (graph_of w)) = None ->
      (forall ρ π, SetPossState.Δ w ρ π -> TMap.find t π = Some ls) ->
      forall ρ' π', SetPossState.Δ w' ρ' π' -> TMap.find t π' = Some ls.
    Proof.
      intros HR Hnone Hall ρ' π' Hposs'.
      destruct (R_other_facts t w w' HR) as (_ & _ & _ & Htok & _).
      destruct (Htok Hnone _ _ Hposs') as (ρ & π & Hposs & Heq).
      rewrite Heq. now apply Hall with ρ.
    Qed.

    Lemma active_stable t op :
      AssertionsSet.A.Stable (R t) I (Active t op).
    Proof.
      intros w' [[w [[HI Hlin] HR]] HI']. split; [exact HI'|].
      intros ρ' π' Hposs'.
      eapply alin_stable_core; [exact HR| |exact Hlin|exact Hposs'].
      eapply alin_inv_no_pending; [exact HI|exact Hlin].
    Qed.

    Lemma completed_stable t op ret :
      AssertionsSet.A.Stable (R t) I (Completed t op ret).
    Proof.
      intros w' [[w [[HI [Hlin HnoP]] HR]] HI']. split; [exact HI'|].
      destruct (R_other_facts t w w' HR) as (Hpend & _ & _ & _ & _).
      split.
      - intros ρ' π' Hposs'.
        eapply alin_stable_core; [exact HR|exact HnoP|exact Hlin|exact Hposs'].
      - unfold NoPending. rewrite <- Hpend. exact HnoP.
    Qed.

    Lemma inside_stable t op :
      AssertionsSet.A.Stable (R t) I (Inside t op).
    Proof.
      intros w' [[w [[HA Hin] HR]] HI']. split; [|exact Hin].
      apply (active_stable t op). split; [|exact HI']. exists w. split; assumption.
    Qed.

    Lemma push_pending_stable t v :
      AssertionsSet.A.Stable (R t) I (PushPending t v).
    Proof.
      intros w' [[w [[HI [Hin [l [Hl Hv]]]] HR]] HI']. split; [exact HI'|].
      destruct (R_other_facts t w w' HR) as (Hpend & Hvert & _ & _ & _).
      split; [exact Hin|]. exists l. split.
      - rewrite <- Hpend. exact Hl.
      - apply Hvert. exact Hv.
    Qed.

    Lemma pop_atomic_stable t :
      AssertionsSet.A.Stable (R t) I (PopAtomic t).
    Proof.
      intros w' [[w [[Hinside [s Hσ]] HR]] HI']. split.
      - apply (inside_stable t st_pop). split; [|exact HI']. exists w. split; assumption.
      - destruct (R_other_facts t w w' HR) as (_ & _ & Hctl & _ & _).
        exists s. rewrite Hctl; [exact Hσ|]. exists s, ts_trypop. exact Hσ.
    Qed.

    Lemma pop_post_stable t ret :
      AssertionsSet.A.Stable (R t) I (PopPost t ret).
    Proof.
      destruct ret as [v owner loc| |]; simpl.
      - apply completed_stable.
      - apply completed_stable.
      - apply inside_stable.
    Qed.

    Lemma active_entails_I t op : ⊨ Active t op ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma completed_entails_I t op ret : ⊨ Completed t op ret ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma inside_entails_I t op : ⊨ Inside t op ==>> I.
    Proof. intros w [[HI _] _]. exact HI. Qed.

    Lemma push_pending_entails_I t v : ⊨ PushPending t v ==>> I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma pop_atomic_entails_I t : ⊨ PopAtomic t ==>> I.
    Proof. intros w [[[HI _] _] _]. exact HI. Qed.

    Lemma pop_post_entails_I t ret : ⊨ PopPost t ret ==>> I.
    Proof.
      destruct ret as [v owner loc| |]; simpl.
      - apply completed_entails_I.
      - apply completed_entails_I.
      - apply inside_entails_I.
    Qed.

    (** * Rely/guarantee validity and parallel compatibility *)

    Lemma valid_rg t :
      RGISimulationSet.RGISimulation.ValidRGI (R t) (G t) I t.
    Proof.
      constructor. intros w w' HR HI'.
      destruct (R_other_facts t w w' HR)
        as (_ & _ & _ & _ & (ρ' & π' & ρ & π & Hposs' & Hposs & Hiff)).
      split; intros Hall.
      - intros ρ0 π0 Hposs0.
        eapply ac_find_none_same; [exact Hposs'|exact Hposs0|].
        apply Hiff. now apply Hall with ρ.
      - intros ρ0 π0 Hposs0.
        eapply ac_find_none_same; [exact Hposs|exact Hposs0|].
        apply Hiff. now apply Hall with ρ'.
    Qed.

    Lemma parallel_compatible t1 t2 :
      t1 <> t2 ->
      (I ⊓ (G t1 ∪ (GINV t1 ∪ GRET t1 ∪ GId)) ⊆ R t2)%RGRelation.
    Proof.
      intros Hneq w w' [Hrel _].
      destruct Hrel as [HG | [[Hinv | Hret] | Hid]].
      - left. exists t1. split; [congruence|exact HG].
      - right. left. exists t1. split; [congruence|exact Hinv].
      - right. right. left. exists t1. split; [congruence|exact Hret].
      - right. right. right. exact Hid.
    Qed.

    (** * Overlay invocation and return *)

    Lemma set_ginv_exposes_active t op :
      ⊨ AssertionsSet.A.ComposeA I (AssertionsSet.Ginv t op) ==>> Active t op.
    Proof.
      intros w [pre [HIpre [Hσ [Hnone Hequiv]]]].
      destruct pre as [σ0 Δ0], w as [σ1 Δ1]; simpl in *. subst σ1.
      split.
      - unfold I, graph_of in *. simpl in *.
        eapply I_state_equiv; [intros ρ π; symmetry; apply Hequiv|].
        apply ginv_I_state; assumption.
      - intros ρ π Hposs. apply Hequiv in Hposs. eapply ac_inv_find_eq. exact Hposs.
    Qed.

    Lemma set_gret_closes_completed t op ret :
      ⊨ AssertionsSet.A.ComposeA (Completed t op ret)
          (AssertionsSet.Gret t op ret) ==>> I.
    Proof.
      intros w [pre [[HIpre [Hlin HnoP]] [Hσ [Hall Hequiv]]]].
      destruct pre as [σ0 Δ0], w as [σ1 Δ1]; simpl in *. subst σ1.
      unfold I, graph_of, NoPending in *. simpl in *.
      eapply I_state_equiv; [intros ρ π; symmetry; apply Hequiv|].
      apply gret_I_state; assumption.
    Qed.

    Lemma completed_has_return_token t op ret (σ : concrete_state) (Δ : config) :
      Completed t op ret (SetPossState.Build_ProofStateSet _ _ _ _ σ Δ) ->
      forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr op ret).
    Proof. intros [_ [Hlin _]]. exact Hlin. Qed.

    (** * Errors *)

    Lemma active_or_error t op :
      ⊨ Active t op ==>> Inside t op \\// AssertionsSet.APError.
    Proof.
      intros w [HI Hlin].
      destruct (ThreadDomain.contains_dec D t) as [Hin|Hout].
      - left. split; [split; assumption|exact Hin].
      - right. destruct w as [σ Δ].
        destruct (ac_nonempty Δ) as (ρ & π & Hposs).
        destruct (I_state_idle _ _ _ _ HI Hposs) as [stk ->].
        econstructor; [exact Hposs|].
        apply rt_step. eapply (@ps_error _ (li_lts F) t op (Idle stk) π).
        + eapply error_stack_actor_outside; [exact Hout|reflexivity].
        + exact (Hlin (Idle stk) π Hposs).
    Qed.

    Lemma inside_no_error t op (m : Sig.op (li_sig E)) :
      ⊨ Inside t op ==>>
        AssertionsSet.A.ANoError (Build_ThreadEvent t (InvEv m)).
    Proof.
      intros w [_ Hin] Herr. simpl in Herr.
      inversion Herr; subst.
      match goal with
      | H : Build_ThreadEvent _ _ = Build_ThreadEvent _ _ |- _ =>
          inversion H; subst
      end.
      contradiction.
    Qed.

    (** * The four event updates (Fig. 34, Fig. 35) *)

    Lemma push_inv_update α v :
      AssertionsSet.PUpdate (G α)
        (Build_ThreadEvent α (InvEv (ts_push v)))
        (Inside α (st_push v)) (PushPending α v).
    Proof.
      intros σ Δ [[HI Hlin] Hin] σ' Hstep.
      destruct (ts_push_inv_shape α v σ σ' Hstep) as (s & l & -> & Hnone & Hfresh & ->).
      unfold I, graph_of in HI. simpl in HI.
      assert (Htok : forall ρ π, Δ ρ π -> TMap.find α π = Some (push_inv_token v)).
      { intros ρ π Hposs. exact (Hlin ρ π Hposs). }
      assert (HΔ' : forall ρ' π', ac_lin (ts_start_push α l v s) Δ ρ' π' <->
        exists ρ π, Δ ρ π /\ lin_closure (ts_start_push α l v s) ρ π ρ' π').
      { intros ρ' π'. apply ac_lin_iff. }
      pose proof (pi_I_state s α l v Δ _ HI Hnone Hfresh Htok HΔ') as HI'.
      exists (ac_lin (ts_start_push α l v s) Δ). split; [apply ac_lin_subset_steps|].
      split.
      - split; [exact HI'|]. split; [exact Hin|].
        exists l. simpl. split; [apply TMap.gss|apply node_update_eq].
      - left. apply (g_push_inv α s l v); simpl; auto.
    Qed.

    Lemma push_res_update α v :
      AssertionsSet.PUpdate (G α)
        (Build_ThreadEvent α (ResEv (ts_push v) tt))
        (PushPending α v) (Completed α (st_push v) tt).
    Proof.
      intros σ Δ [HI [Hin [l [Hl Hv]]]] σ' Hstep.
      destruct (ts_push_res_shape α v σ σ' Hstep) as (s & l0 & -> & Hl0 & ->).
      unfold I, graph_of in HI, Hl, Hv. simpl in HI, Hl, Hv.
      rewrite Hl in Hl0. injection Hl0 as <-.
      pose proof (pr_nonempty s α l v Δ HI Hl Hv) as Hne.
      set (sel := fun (_ : abstract_state) π => TMap.find α π = Some (push_ret_token v)).
      assert (Hsteps : forall ρ π, Δ ρ π -> sel ρ π ->
        poss_steps (PossOk ρ π) (PossOk ((fun ρ => ρ) ρ) ((fun π => π) π))).
      { intros ρ π _ _. apply rt_refl. }
      assert (Hne' : exists ρ π, Δ ρ π /\ sel ρ π).
      { destruct Hne as (ρ & π & Hposs & Hret). exists ρ, π. split; assumption. }
      set (Δ' := ac_select Δ sel (fun ρ => ρ) (fun π => π) Hsteps Hne').
      assert (HΔ' : forall ρ π, Δ' ρ π <-> Δ ρ π /\ TMap.find α π = Some (push_ret_token v)).
      { intros ρ π. unfold Δ'. rewrite ac_select_iff. split.
        - intros (ρ0 & π0 & Hposs & Hsel & -> & ->). split; assumption.
        - intros [Hposs Hret]. exists ρ, π. repeat split; assumption. }
      pose proof (pr_I_state s α l v Δ Δ' HI Hl Hv HΔ') as HI'.
      exists Δ'. split; [apply ac_select_subset_steps|].
      split.
      - split; [exact HI'|]. split.
        + intros ρ π Hposs. apply HΔ' in Hposs. exact (proj2 Hposs).
        + unfold NoPending, graph_of. simpl. apply TMap.grs.
      - right. left. apply (g_push_ret α s l v); simpl; auto.
    Qed.

    Lemma trypop_inv_update α :
      AssertionsSet.PUpdate (G α)
        (Build_ThreadEvent α (InvEv ts_trypop))
        (Inside α st_pop) (PopAtomic α).
    Proof.
      intros σ Δ Hinside σ' Hstep.
      destruct (ts_trypop_inv_shape α σ σ' Hstep) as (s & -> & ->).
      exists Δ. split; [apply ac_steps_refl|].
      split.
      - split; [exact Hinside|]. exists s. reflexivity.
      - right. right. right. right. apply (g_control_enter α s); reflexivity.
    Qed.

    Lemma trypop_res_update α ret :
      AssertionsSet.PUpdate (G α)
        (Build_ThreadEvent α (ResEv ts_trypop ret))
        (PopAtomic α) (PopPost α ret).
    Proof.
      intros σ Δ [[[HI Hlin] Hin] [s0 Hσ]] σ' Hstep.
      destruct (ts_trypop_res_shape α ret σ σ' Hstep) as (s & Hσs & Hcases). subst σ.
      destruct Hcases as [[n [v [Hret [Htop [Hv Hσ']]]]] | [[Hret [Hall Hσ']] | [Hret Hσ']]];
        subst ret σ'.
      - (* G_pop *)
        unfold I, graph_of in HI. simpl in HI.
        assert (Hα : forall ρ π, Δ ρ π -> TMap.find α π = Some (ls_inv st_pop)).
        { intros ρ π Hposs. exact (Hlin ρ π Hposs). }
        set (sel := fun ρ π =>
          exists stk, ρ = Idle stk /\ (exists stk', stk = v :: stk') /\
            (ts_is_pending s n -> TMap.find (fst n) π = Some (push_ret_token v)) /\
            (exists N', justified s ρ π (n :: N'))).
        set (ρf := fun ρ : abstract_state =>
          match ρ with Idle (_ :: stk) => Idle stk | _ => ρ end).
        set (πf := fun π => TMap.add α (pop_ret_token (Some v)) (TMap.add α pop_lini_token π)).
        assert (Hsteps : forall ρ π, Δ ρ π -> sel ρ π ->
          poss_steps (PossOk ρ π) (PossOk (ρf ρ) (πf π))).
        { intros ρ π Hposs (stk & Hρ & [stk' Hstk'] & _ & _). subst ρ stk. unfold ρf, πf. simpl.
          eapply rt_trans.
          - apply rt_step.
            eapply (@ps_inv _ (li_lts F) α st_pop (Idle (v :: stk'))
              (Pending (v :: stk') α st_pop) π).
            + apply stack_pop_inv_step.
            + exact (Hα _ _ Hposs).
          - apply rt_step.
            eapply (@ps_ret _ (li_lts F) α st_pop (Some v) (Pending (v :: stk') α st_pop)
              (Idle stk')).
            + apply stack_pop_res_step.
            + apply TMap.gss. }
        assert (Hne : exists ρ π, Δ ρ π /\ sel ρ π).
        { destruct (pop_nonempty s α n v Δ HI Htop Hv Hα) as (stk & π & Hposs & Hpend & Hjust).
          exists (Idle (v :: stk)), π. split; [exact Hposs|].
          exists (v :: stk). split; [reflexivity|]. split; [eauto|]. split; assumption. }
        set (Δ' := ac_select Δ sel ρf πf Hsteps Hne).
        assert (HΔ' : forall ρ' π', Δ' ρ' π' <->
          exists stk π,
            Δ (Idle (v :: stk)) π /\
            (ts_is_pending s n -> TMap.find (fst n) π = Some (push_ret_token v)) /\
            (exists N', justified s (Idle (v :: stk)) π (n :: N')) /\
            ρ' = Idle stk /\
            π' = TMap.add α (pop_ret_token (Some v)) (TMap.add α pop_lini_token π)).
        { intros ρ' π'. unfold Δ'. rewrite ac_select_iff. split.
          - intros (ρ & π & Hposs & (stk & Hρ & [stk' Hstk'] & Hpend & Hjust) & -> & ->).
            subst ρ stk. exists stk', π. repeat split; assumption.
          - intros (stk & π & Hposs & Hpend & Hjust & -> & ->).
            exists (Idle (v :: stk)), π. split; [exact Hposs|]. split; [|split; reflexivity].
            exists (v :: stk). split; [reflexivity|]. split; [eauto|]. split; assumption. }
        pose proof (pop_I_state s α n v Δ Δ' HI Htop Hv Hα HΔ') as HI'.
        exists Δ'. split; [apply ac_select_subset_steps|].
        split.
        + simpl. split; [exact HI'|]. split.
          * intros ρ' π' Hposs'. apply HΔ' in Hposs'.
            destruct Hposs' as (stk & π & _ & _ & _ & -> & ->). apply TMap.gss.
          * unfold NoPending, graph_of. simpl.
            eapply alin_inv_no_pending; [exact HI|exact Hα].
        + right. right. left. apply (g_pop α s n v); simpl; auto.
      - (* G_pop-emp *)
        unfold I, graph_of in HI. simpl in HI.
        assert (Hα : forall ρ π, Δ ρ π -> TMap.find α π = Some (ls_inv st_pop)).
        { intros ρ π Hposs. exact (Hlin ρ π Hposs). }
        set (sel := fun (ρ : abstract_state) (_ : tmap lin_state) => ρ = Idle nil).
        set (πf := fun π => TMap.add α (pop_ret_token None) (TMap.add α pop_lini_token π)).
        assert (Hsteps : forall ρ π, Δ ρ π -> sel ρ π ->
          poss_steps (PossOk ρ π) (PossOk ((fun ρ => ρ) ρ) (πf π))).
        { intros ρ π Hposs ->. unfold πf. simpl.
          eapply rt_trans.
          - apply rt_step.
            eapply (@ps_inv _ (li_lts F) α st_pop (Idle nil) (Pending nil α st_pop) π).
            + apply stack_pop_inv_step.
            + exact (Hα _ _ Hposs).
          - apply rt_step.
            eapply (@ps_ret _ (li_lts F) α st_pop None (Pending nil α st_pop) (Idle nil)).
            + apply stack_pop_emp_step.
            + apply TMap.gss. }
        assert (Hne : exists ρ π, Δ ρ π /\ sel ρ π).
        { destruct (pe_nonempty s Δ HI Hall) as [π Hposs].
          exists (Idle nil), π. split; [exact Hposs|reflexivity]. }
        set (Δ' := ac_select Δ sel (fun ρ => ρ) πf Hsteps Hne).
        assert (HΔ' : forall ρ' π', Δ' ρ' π' <->
          exists π, Δ (Idle nil) π /\ ρ' = Idle nil /\
            π' = TMap.add α (pop_ret_token None) (TMap.add α pop_lini_token π)).
        { intros ρ' π'. unfold Δ'. rewrite ac_select_iff. split.
          - intros (ρ & π & Hposs & Hsel & -> & ->). unfold sel in Hsel. subst ρ.
            exists π. split; [exact Hposs|]. split; reflexivity.
          - intros (π & Hposs & -> & ->). exists (Idle nil), π.
            split; [exact Hposs|]. split; [reflexivity|]. split; reflexivity. }
        pose proof (pe_I_state s α Δ Δ' HI Hall Hα HΔ') as HI'.
        exists Δ'. split; [apply ac_select_subset_steps|].
        split.
        + simpl. split; [exact HI'|]. split.
          * intros ρ' π' Hposs'. apply HΔ' in Hposs'.
            destruct Hposs' as (π & _ & -> & ->). apply TMap.gss.
          * unfold NoPending, graph_of. simpl.
            eapply alin_inv_no_pending; [exact HI|exact Hα].
        + right. right. right. left. apply (g_pop_emp α s); simpl; auto.
      - (* Fail: identity *)
        exists Δ. split; [apply ac_steps_refl|].
        split.
        + simpl. split; [split; [exact HI|exact Hlin]|exact Hin].
        + right. right. right. right. apply (g_control_leave α s); reflexivity.
    Qed.

    (** * Method outlines *)

    Lemma push_triple t v :
      [li_lts E, li_lts F, R t, G t, I, t] ⊢
        {{ Active t (st_push v) }} push_impl D v t
        {{ fun _ => Completed t (st_push v) tt }}.
    Proof.
      eapply SetLogic.provable_perror with (P' := Inside t (st_push v)).
      - apply active_or_error.
      - unfold push_impl.
        eapply SetLogic.provable_vis_safe with
          (P' := PushPending t v)
          (Q' := fun _ => Completed t (st_push v) tt).
        + apply inside_no_error.
        + apply push_pending_entails_I.
        + intros _. apply completed_entails_I.
        + apply push_pending_stable.
        + intros _. apply completed_stable.
        + apply push_inv_update.
        + intros []. apply push_res_update.
        + intros []. eapply SetLogic.provable_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
    Qed.

    Lemma pop_triple t :
      [li_lts E, li_lts F, R t, G t, I, t] ⊢
        {{ Active t st_pop }} pop_impl D t
        {{ fun ret => Completed t st_pop ret }}.
    Proof.
      eapply SetLogic.provable_perror with (P' := Inside t st_pop).
      - apply active_or_error.
      - unfold pop_impl.
        eapply SetLogic.provable_doloop.
        + intros ret. apply completed_entails_I.
        + intros ret. apply completed_stable.
        + eapply SetLogic.provable_vis_safe with
            (P' := PopAtomic t)
            (Q' := PopPost t).
          * apply inside_no_error.
          * apply pop_atomic_entails_I.
          * intros ret. apply pop_post_entails_I.
          * apply pop_atomic_stable.
          * intros ret. apply pop_post_stable.
          * apply trypop_inv_update.
          * intros ret. apply trypop_res_update.
          * intros ret. destruct ret as [v owner loc| |]; simpl;
              eapply SetLogic.provable_ret_safe.
            -- apply ImplRefl.
            -- apply completed_entails_I.
            -- apply completed_stable.
            -- apply ImplRefl.
            -- apply completed_entails_I.
            -- apply completed_stable.
            -- apply ImplRefl.
            -- apply inside_entails_I.
            -- apply inside_stable.
    Qed.

    (** * Packaging *)

    Lemma initial_I :
      I (SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (li_init E) (ac_singleton (li_init F) (@TMap.empty lin_state))).
    Proof.
      unfold I, graph_of. simpl.
      split; [|split; [|split]].
      - split; [|split; [|split; [|split]]].
        + exists nil. split; [constructor|]. split; [simpl; trivial|].
          intros n. simpl. unfold ts_is_vertex, empty_try_stack_state, empty_node_map. simpl.
          split; [contradiction|]. intros H. apply H. reflexivity.
        + intros n Hg. contradiction.
        + intros β l Hl. rewrite TMap.gempty in Hl. discriminate.
        + intros n m Hedge. contradiction.
        + intros n m Hedge. contradiction.
      - intros ρ π Hposs. inversion Hposs; subst.
        exists nil. split.
        + unfold perm. split; [constructor|]. split; [simpl; trivial|].
          intros m. unfold stack_domain, live, ts_is_live, ts_is_vertex. simpl.
          split; [contradiction|]. intros [[H _] _]. apply H. reflexivity.
        + exists nil. split; [constructor|reflexivity].
      - intros P' Hpset N Hperm stk Hstk.
        assert (HN : N = nil).
        { destruct N as [|m N]; [reflexivity|]. exfalso.
          destruct Hperm as [_ [_ Hmem]].
          assert (Hm : In m (m :: N)) by (left; reflexivity).
          apply Hmem in Hm. destruct Hm as [[Hv _] _]. apply Hv. reflexivity. }
        subst N. inversion Hstk; subst.
        exists (@TMap.empty lin_state). split; [constructor|].
        intros β l Hl. rewrite TMap.gempty in Hl. discriminate.
      - intros β l Hl. rewrite TMap.gempty in Hl. discriminate.
    Qed.

    Program Definition MTSStack : layer_implementation_simulation E F :=
      {| li_impl := ts_stack_impl D |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := I).
      - exact valid_rg.
      - exact parallel_compatible.
      - intros t op. destruct op as [v|].
        + exists (Active t (st_push v)).
          exists (fun _ => Completed t (st_push v) tt).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active. exact Hcompose.
          * apply active_entails_I.
          * apply active_stable.
          * intros [] w Hcompose. eapply set_gret_closes_completed. exact Hcompose.
          * intros [] σ Δ Hcompleted ρ π Hposs.
            eapply completed_has_return_token; eauto.
          * apply push_triple.
        + exists (Active t st_pop).
          exists (fun ret => Completed t st_pop ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active. exact Hcompose.
          * apply active_entails_I.
          * apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed. exact Hcompose.
          * intros ret σ Δ Hcompleted ρ π Hposs.
            eapply completed_has_return_token; eauto.
          * apply pop_triple.
      - exact initial_I.
    Qed.

    Definition MTSStackLinearizable :
        layer_implementation_linearizability E F :=
      LISim2LILin MTSStack.

    Definition MListPoolTSStack :
        layer_implementation_linearizability (@ListPoolProof.E A D) F :=
      LIVComp (@TryStackProof.MListPoolTryStack A D) MTSStackLinearizable.

  End Proof.
End TSStackProof.
