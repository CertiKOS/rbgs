Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Lia.

Require Import models.EffectSignatures.
Require Import models.LinCCAL.
Require Import models.logics.Logics.
Require Import models.logics.SeparationAlgebra.
Require Import models.simlin.LTS.
Require Import models.simlin.Lang.
Require Import models.simlin.Semantics.
Require Import models.simlin.Assertion.
Require Import models.simlin.TPSimulationSet.
Require Import models.simlin.RGILogicSet.
Require Import models.simlin.SingletonPossibility.
Require Import examples.Common.AtomicLTS.
Require Import examples.Common.Heap.
Require Import examples.CAS.CASRegSpec.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.NodeMemSpec.
Require Import examples.TSStack.SPListSpec.
Require Import examples.TSStack.SPList.

(** Separation-logic verification of [SPListImpl].  The proof uses the
    singleton facade of [RGILogicSet]: every abstract configuration is a
    singleton, while all program judgments are set-logic judgments. *)
Module SPListProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSingle.
  Import TPSimulationSet.TPSimulation.
  Import AtomicLTS CASRegSpec TimestampSpec NodeMemSpec SPListSpec.
  Import ListNotations.
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
    Context {owner : tid}.

    Definition ENodeMemLayer : layer_interface :=
      {|
        li_sig := @ENodeMem A;
        li_lts := @VNodeMem A;
        li_init := Idle empty_heap
      |}.

    Definition ECASLayer : layer_interface :=
      {|
        li_sig := ECASReg (Ptr * nat);
        li_lts := @VCASReg (Ptr * nat);
        li_init := Idle (pair (@None Addr) O)
      |}.

    Definition E : layer_interface := ENodeMemLayer ⊗ₗ ECASLayer.

    Definition F : layer_interface :=
      {|
        li_sig := @ESPList A;
        li_lts := @VSPList A owner;
        li_init := Ready (@SPListImpl.empty_splist_state A)
      |}.

    Definition mem_control :=
      State (@NodeMemSpec.VNodeMem A).
    Definition cas_control :=
      State (@CASRegSpec.VCASReg (Ptr * nat)).
    Definition abstract_control :=
      State (@SPListSpec.VSPList A owner).

    Definition concrete_state := State (li_lts E).
    Definition abstract_state := State (li_lts F).
    Definition single_state :=
      @SinglePossState.ProofStateSingle _ _ (li_lts E) (li_lts F).
    Definition assertion := @Assertion single_state.
    Definition rg_relation :=
      @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F).

    Definition mem_heap (mc : mem_control) : @Heap (@Node A) :=
      AtomicLTS.state mc.

    Definition cas_value (cc : cas_control) : Ptr * nat :=
      AtomicLTS.state cc.

    Definition node_live (n : @Node A) : bool :=
      negb (snd (fst n)).

    Definition live_at (h : @Heap (@Node A)) (l : Addr) : bool :=
      match h l with
      | Some n => node_live n
      | None => false
      end.

    Fixpoint live_order (h : @Heap (@Node A)) (xs : list Addr) : list Addr :=
      match xs with
      | nil => nil
      | l :: xs' =>
          if live_at h l then l :: live_order h xs'
          else live_order h xs'
      end.

    Definition node_projection (n : @Node A) : A * TS :=
      fst (fst n).

    Definition abstract_nodes
        (h : @Heap (@Node A)) (xs : list Addr) : @Heap (A * TS) :=
      fun l =>
        if List.existsb (Nat.eqb l) xs then
          match h l with
          | Some n => Some (node_projection n)
          | None => None
          end
        else None.

    (** NodeMem heap ownership is the pointwise lift of exclusive cell
        ownership.  This is the separation algebra used to extract the one
        node touched by [get], [setTS], or [tryTake]. *)
    Definition node_Join : Join (@Node A) := @trivial_Join (@Node A).
    Definition node_SA : @SeparationAlgebra (@Node A) node_Join :=
      @trivial_SA (@Node A).
    Definition cell_Join : Join (option (@Node A)) :=
      @option_Join (@Node A) node_Join.
    Definition cell_SA : @SeparationAlgebra (option (@Node A)) cell_Join :=
      @option_SA (@Node A) node_Join node_SA.
    Definition cell_unit :
      @SeparationAlgebraUnit (option (@Node A)) cell_Join cell_SA :=
      @option_unit (@Node A) node_Join node_SA.
    Definition heap_Join : Join (@Heap (@Node A)) :=
      @fun_Join Addr (option (@Node A)) cell_Join.
    Definition heap_SA :
      @SeparationAlgebra (@Heap (@Node A)) heap_Join :=
      @fun_SA Addr (option (@Node A)) cell_Join cell_SA.
    Definition heap_unit :
      @SeparationAlgebraUnit (@Heap (@Node A)) heap_Join heap_SA :=
      @fun_unit Addr (option (@Node A)) cell_Join cell_SA cell_unit.

    (** Heap-level spatial assertions.  The atomic [Idle]/[Pending] control
        remains global; only the NodeMem payload is separated.  This avoids
        treating the racy-error control token as a frameable heap cell. *)
    Definition HAssertion := @Assertion (@Heap (@Node A)).

    Definition HExact (h : @Heap (@Node A)) : HAssertion :=
      fun owned => owned = h.

    Definition singleton_heap (l : Addr) (n : @Node A) :
        @Heap (@Node A) :=
      fun q => if Nat.eqb l q then Some n else None.

    Definition heap_without (l : Addr) (h : @Heap (@Node A)) :
        @Heap (@Node A) :=
      fun q => if Nat.eqb l q then None else h q.

    Definition HCell (l : Addr) (n : @Node A) : HAssertion :=
      HExact (singleton_heap l n).

    Definition HFrame (l : Addr) (h : @Heap (@Node A)) : HAssertion :=
      HExact (heap_without l h).

    Lemma singleton_heap_lookup l n : singleton_heap l n l = Some n.
    Proof. unfold singleton_heap. now rewrite Nat.eqb_refl. Qed.

    Lemma heap_without_lookup l h : heap_without l h l = None.
    Proof. unfold heap_without. now rewrite Nat.eqb_refl. Qed.

    Lemma heap_cell_split h l n :
      h l = Some n ->
      @join _ heap_Join (singleton_heap l n) (heap_without l h) h.
    Proof.
      intros Hlookup q. unfold singleton_heap, heap_without.
      destruct (Nat.eqb l q) eqn:Heq.
      - apply Nat.eqb_eq in Heq. subst q. rewrite Hlookup.
        constructor.
      - destruct (h q); constructor.
    Qed.

    Lemma heap_cell_recombine h l old new :
      h l = Some old ->
      @join _ heap_Join (singleton_heap l new) (heap_without l h)
        (heap_update l new h).
    Proof.
      intros _ q. unfold singleton_heap, heap_without, heap_update.
      destruct (Nat.eqb l q); [constructor|].
      destruct (h q); constructor.
    Qed.

    Lemma heap_cell_sep h l n :
      h l = Some n ->
      @sepcon _ heap_Join (HCell l n) (HFrame l h) h.
    Proof.
      intros Hlookup.
      exists (singleton_heap l n), (heap_without l h).
      repeat split; auto using heap_cell_split.
    Qed.

    (** The payload frame rule used by all in-place NodeMem operations.
        Updating the owned singleton leaves an arbitrary disjoint heap
        assertion [Fr] untouched. *)
    Lemma heap_cell_update_frame l old new (Fr : HAssertion) h :
      @sepcon _ heap_Join (HCell l old) Fr h ->
      @sepcon _ heap_Join (HCell l new) Fr (heap_update l new h).
    Proof.
      intros (owned & frame & Hjoin & Howned & Hframe).
      unfold HCell, HExact in Howned. subst owned.
      exists (singleton_heap l new), frame. repeat split; auto.
      intro q. specialize (Hjoin q).
      unfold singleton_heap, heap_update in *.
      destruct (Nat.eqb l q) eqn:Heq.
      - inversion Hjoin; subst; try contradiction. constructor.
      - exact Hjoin.
    Qed.

    Lemma heap_cell_read_frame l n (Fr : HAssertion) h :
      @sepcon _ heap_Join (HCell l n) Fr h ->
      h l = Some n.
    Proof.
      intros (owned & frame & Hjoin & Howned & Hframe).
      unfold HCell, HExact in Howned. subst owned.
      specialize (Hjoin l). rewrite singleton_heap_lookup in Hjoin.
      inversion Hjoin; subst; try contradiction; reflexivity.
    Qed.

    (** Allocation transfers one fresh singleton out of the formerly
        unchanged frame. *)
    Lemma heap_alloc_frame h l n :
      h l = None ->
      @sepcon _ heap_Join (HCell l n) (HExact h)
        (heap_update l n h).
    Proof.
      intros Hfresh. exists (singleton_heap l n), h.
      repeat split; auto.
      intro q. unfold singleton_heap, heap_update.
      destruct (Nat.eqb l q) eqn:Heq.
      - apply Nat.eqb_eq in Heq. subst q. rewrite Hfresh. constructor.
      - destruct (h q); constructor.
    Qed.

    (** [linked h p xs] owns the mathematical shape of the immutable
        successor chain beginning at [p].  Values and timestamps/taken bits
        may change, but successor pointers may not. *)
    Inductive linked (h : @Heap (@Node A)) : Ptr -> list Addr -> Prop :=
    | linked_nil : linked h None nil
    | linked_cons l v ts taken next xs :
        h l = Some (pair (pair (pair v ts) taken) next) ->
        linked h next xs ->
        ~ In l xs ->
        linked h (Some l) (l :: xs).

    Lemma linked_ptr_nil h p :
      linked h p nil -> p = None.
    Proof. inversion 1; reflexivity. Qed.

    Lemma linked_ptr_cons h p l xs :
      linked h p (l :: xs) -> p = Some l.
    Proof. inversion 1; reflexivity. Qed.

    Lemma linked_nodup h p xs :
      linked h p xs -> NoDup xs.
    Proof.
      induction 1; constructor; auto.
    Qed.

    Lemma linked_deterministic h p xs ys :
      linked h p xs -> linked h p ys -> xs = ys.
    Proof.
      intros Hx. revert ys.
      induction Hx as [|l v ts taken next xs Hlookup Htail IH Hfresh];
        intros ys Hy.
      - inversion Hy. reflexivity.
      - inversion Hy as
          [|l' v' ts' taken' next' ys' Hlookup' Htail' Hfresh']; subst.
        rewrite Hlookup in Hlookup'. inversion Hlookup'; subst.
        f_equal. eapply IH; exact Htail'.
    Qed.

    Lemma linked_lookup h p xs l :
      linked h p xs -> In l xs ->
      exists v ts taken next,
        h l = Some (pair (pair (pair v ts) taken) next).
    Proof.
      induction 1 as [|hd v ts taken next tl Hhd Htl IH Hfresh];
        simpl; intros Hin; [contradiction|].
      destruct Hin as [<-|Hin].
      - eauto.
      - eauto.
    Qed.

    Lemma linked_not_none h p xs l :
      linked h p xs -> In l xs -> h l <> None.
    Proof.
      intros Hlinked Hin Hnone.
      destruct (linked_lookup _ _ _ _ Hlinked Hin)
        as (v & ts & taken & next & Hlookup).
      congruence.
    Qed.

    Lemma linked_fresh_notin h p xs l :
      linked h p xs -> h l = None -> ~ In l xs.
    Proof.
      intros Hlinked Hnone Hin.
      eapply linked_not_none; eauto.
    Qed.

    Lemma linked_heap_ext h h' p xs :
      linked h p xs ->
      (forall l, In l xs -> h l = h' l) ->
      linked h' p xs.
    Proof.
      intros Hlinked. induction Hlinked as
        [|l v ts taken next xs Hlookup Htail IH Hfresh]; intros Heq.
      - constructor.
      - econstructor.
        + rewrite <- Heq; [exact Hlookup|now left].
        + apply IH. intros q Hq. apply Heq. now right.
        + exact Hfresh.
    Qed.

    (** A genuinely spatial presentation of the published successor chain.
        Each recursive clause owns its head cell separately from the tail;
        the terminal assertion is [True], so unreachable private storage is
        retained as a frame. *)
    Fixpoint HLinked (p : Ptr) (xs : list Addr) : HAssertion :=
      match xs with
      | nil =>
          match p with
          | None => fun _ => True
          | Some _ => fun _ => False
          end
      | x :: xs' =>
          match p with
          | None => fun _ => False
          | Some l => fun h =>
              l = x /\
              exists n,
                @sepcon _ heap_Join (HCell l n)
                  (HLinked (snd n) xs') h
          end
      end.

    Lemma HLinked_lookup h p xs l :
      HLinked p xs h -> In l xs ->
      exists n, h l = Some n.
    Proof.
      revert p h l. induction xs as [|x xs IH]; intros p h l Hsp Hin.
      - contradiction.
      - destruct p as [hd|]; simpl in Hsp; [|contradiction].
        destruct Hsp as [Ehd [n Hsep]]. subst hd.
        simpl in Hin. destruct Hin as [<-|Hin].
        + exists n. eapply heap_cell_read_frame; exact Hsep.
        + destruct Hsep as
            (owned & frame & Hjoin & Howned & Htail).
          unfold HCell, HExact in Howned. subst owned.
          destruct (IH (snd n) frame l Htail Hin) as [n' Hlookup].
          exists n'. specialize (Hjoin l).
          unfold singleton_heap in Hjoin.
          destruct (Nat.eqb x l) eqn:Heq.
          * rewrite Hlookup in Hjoin. inversion Hjoin; contradiction.
          * rewrite Hlookup in Hjoin. inversion Hjoin; reflexivity.
    Qed.

    Lemma linked_implies_HLinked h p xs :
      linked h p xs -> HLinked p xs h.
    Proof.
      revert h p. induction xs as [|x xs IH]; intros h p Hlinked.
      - apply linked_ptr_nil in Hlinked. subst p. simpl. exact I.
      - pose proof (linked_ptr_cons _ _ _ _ Hlinked) as Hp. subst p.
        inversion Hlinked as
          [|hd v ts taken next tl Hhead Htail Hfresh]; subst hd tl.
        simpl. split; [reflexivity|].
        exists (pair (pair (pair v ts) taken) next).
        exists (singleton_heap x (pair (pair (pair v ts) taken) next)),
          (heap_without x h).
        split.
        + apply heap_cell_split. exact Hhead.
        + split.
          * reflexivity.
          * apply IH.
            eapply linked_heap_ext; [exact Htail|].
            intros q Hq. unfold heap_without.
            destruct (Nat.eqb x q) eqn:Heq; [|reflexivity].
            apply Nat.eqb_eq in Heq. subst q. contradiction.
    Qed.

    Lemma HLinked_implies_linked h p xs :
      HLinked p xs h -> linked h p xs.
    Proof.
      revert h p. induction xs as [|x xs IH]; intros h p Hsp.
      - destruct p; simpl in Hsp; [contradiction|constructor].
      - destruct p as [hd|]; simpl in Hsp; [|contradiction].
        destruct Hsp as [Ehd [n Hsep]]. subst hd.
        pose proof (heap_cell_read_frame x n (HLinked (snd n) xs) h Hsep)
          as Hhead.
        destruct Hsep as
          (owned & frame & Hjoin & Howned & Htailsp).
        unfold HCell, HExact in Howned. subst owned.
        assert (Hfresh : ~ In x xs).
        { intro Hin.
          destruct (HLinked_lookup frame (snd n) xs x Htailsp Hin)
            as [n' Hframe].
          specialize (Hjoin x). rewrite singleton_heap_lookup, Hframe in Hjoin.
          inversion Hjoin; contradiction. }
        assert (Htail : linked h (snd n) xs).
        { eapply linked_heap_ext.
          - apply IH. exact Htailsp.
          - intros q Hq. specialize (Hjoin q).
            unfold singleton_heap in Hjoin.
            assert (Heq : Nat.eqb x q = false).
            { apply Nat.eqb_neq. congruence. }
            rewrite Heq in Hjoin.
            inversion Hjoin; reflexivity. }
        destruct n as [[[v ts] taken] next]. simpl in Htail, Hhead.
        econstructor; eauto.
    Qed.

    Lemma linked_spatial_equiv h p xs :
      linked h p xs <-> HLinked p xs h.
    Proof.
      split; [apply linked_implies_HLinked|apply HLinked_implies_linked].
    Qed.

    Lemma linked_update_fresh h p xs l n :
      linked h p xs -> h l = None ->
      linked (heap_update l n h) p xs.
    Proof.
      intros Hlinked Hnone.
      eapply linked_heap_ext; [exact Hlinked|].
      intros q Hq. symmetry. apply HeapUpdateOther.
      intro Heq. subst q.
      eapply linked_not_none in Hlinked; eauto.
    Qed.

    Lemma linked_prepend h p xs l v ts taken :
      linked h p xs -> h l = None ->
      linked (heap_update l (pair (pair (pair v ts) taken) p) h)
        (Some l) (l :: xs).
    Proof.
      intros Hlinked Hnone. econstructor.
      - apply HeapUpdateSelf.
      - eapply linked_update_fresh; eauto.
      - eapply linked_fresh_notin; eauto.
    Qed.

    Lemma linked_update_existing h p xs l v old_ts old_taken next
        new_ts new_taken :
      linked h p xs -> In l xs ->
      h l = Some (pair (pair (pair v old_ts) old_taken) next) ->
      linked
        (heap_update l (pair (pair (pair v new_ts) new_taken) next) h)
        p xs.
    Proof.
      intros Hlinked Hin Hlookup.
      induction Hlinked as
        [|hd hv hts htaken hnext tl Hhd Htl IH Hfresh].
      - contradiction.
      - simpl in Hin. destruct Hin as [Heq|Hin].
        + subst hd. rewrite Hlookup in Hhd. inversion Hhd; subst.
          econstructor.
          * apply HeapUpdateSelf.
          * eapply linked_heap_ext; [exact Htl|].
            intros q Hq. symmetry. apply HeapUpdateOther. congruence.
          * exact Hfresh.
        + assert (Hneq : l <> hd) by congruence.
          econstructor.
          * rewrite HeapUpdateOther; [exact Hhd|congruence].
          * apply IH; exact Hin.
          * exact Hfresh.
    Qed.

    Lemma abstract_nodes_update_existing h xs l n :
      In l xs ->
      abstract_nodes (heap_update l n h) xs =
        heap_update l (node_projection n) (abstract_nodes h xs).
    Proof.
      intro Hin. apply functional_extensionality. intro q.
      unfold abstract_nodes, heap_update.
      destruct (Nat.eqb l q) eqn:Elq.
      - apply Nat.eqb_eq in Elq. subst q.
        assert (Hex : List.existsb (Nat.eqb l) xs = true).
        { apply existsb_exists. exists l. split; auto using Nat.eqb_refl. }
        now rewrite Hex.
      - destruct (List.existsb (Nat.eqb q) xs); reflexivity.
    Qed.

    Lemma live_at_update_other h l q n :
      l <> q -> live_at (heap_update l n h) q = live_at h q.
    Proof.
      intro Hneq. unfold live_at. rewrite HeapUpdateOther by exact Hneq.
      reflexivity.
    Qed.

    Lemma live_order_ext h h' xs :
      (forall q, In q xs -> live_at h q = live_at h' q) ->
      live_order h xs = live_order h' xs.
    Proof.
      induction xs as [|q tl IH]; intro Heq; [reflexivity|].
      simpl. rewrite (Heq q) by now left.
      assert (Htail : live_order h tl = live_order h' tl).
      { apply IH. intros r Hr. apply Heq. now right. }
      destruct (live_at h' q); simpl; rewrite Htail; reflexivity.
    Qed.

    Lemma live_order_update_same_taken h xs l v old_ts taken next new_ts :
      NoDup xs -> In l xs ->
      h l = Some (pair (pair (pair v old_ts) taken) next) ->
      live_order
        (heap_update l (pair (pair (pair v new_ts) taken) next) h) xs =
      live_order h xs.
    Proof.
      intros Hnodup Hin Hlookup.
      induction xs as [|hd tl IH]; [contradiction|].
      inversion Hnodup as [|? ? Hfresh Hnodup']; subst.
      simpl in Hin. destruct Hin as [Heq|Hin].
      - subst hd. simpl. unfold live_at, node_live.
        rewrite HeapUpdateSelf, Hlookup. simpl.
        assert (Htail :
          live_order
            (heap_update l (pair (pair (pair v new_ts) taken) next) h) tl =
          live_order h tl).
        { apply live_order_ext. intros q Hq.
          apply live_at_update_other. congruence. }
        rewrite Htail. reflexivity.
      - simpl. rewrite live_at_update_other by congruence.
        specialize (IH Hnodup' Hin).
        destruct (live_at h hd); simpl; rewrite IH; reflexivity.
    Qed.

    Lemma live_order_in h xs l :
      In l (live_order h xs) -> In l xs.
    Proof.
      induction xs as [|q tl IH]; simpl; [tauto|].
      destruct (live_at h q); simpl; intuition.
    Qed.

    Lemma live_order_spec h xs l :
      NoDup xs ->
      (In l (live_order h xs) <-> In l xs /\ live_at h l = true).
    Proof.
      intro Hnodup. induction xs as [|q tl IH]; simpl.
      - tauto.
      - inversion Hnodup as [|? ? Hfresh Hnodup']; subst.
        specialize (IH Hnodup'). destruct (live_at h q) eqn:Hq; simpl.
        + split.
          * intros [Heq|Hin].
            -- subst q. split; [now left|exact Hq].
            -- apply IH in Hin as [Hin Hlive]. split; [now right|exact Hlive].
          * intros [[Heq|Hin] Hlive].
            -- now left.
            -- right. apply IH. now split.
        + split.
          * intro Hin. apply IH in Hin as [Hin Hlive]. split; [now right|exact Hlive].
          * intros [[Heq|Hin] Hlive].
            -- subst q. rewrite Hq in Hlive. discriminate.
            -- apply IH. now split.
    Qed.

    Lemma linked_live_false h p xs l v ts next :
      linked h p xs -> In l xs ->
      h l = Some (pair (pair (pair v ts) false) next) ->
      In l (live_order h xs).
    Proof.
      intros Hlinked Hin Hlookup. apply live_order_spec.
      - eapply linked_nodup; exact Hlinked.
      - split; [exact Hin|]. unfold live_at, node_live. now rewrite Hlookup.
    Qed.

    Lemma linked_live_true h p xs l v ts next :
      linked h p xs -> In l xs ->
      h l = Some (pair (pair (pair v ts) true) next) ->
      ~ In l (live_order h xs).
    Proof.
      intros Hlinked Hin Hlookup Hlive.
      apply live_order_spec in Hlive.
      - destruct Hlive as [_ Hbad]. unfold live_at, node_live in Hbad.
        rewrite Hlookup in Hbad. discriminate.
      - eapply linked_nodup; exact Hlinked.
    Qed.

    Lemma forall_live_order h xs :
      List.Forall (fun l => In l xs) (live_order h xs).
    Proof.
      induction xs as [|q tl IH]; simpl; [constructor|].
      destruct (live_at h q); simpl.
      - constructor; [now left|].
        eapply List.Forall_impl; [|exact IH]. intros l Hin. now right.
      - eapply List.Forall_impl; [|exact IH]. intros l Hin. now right.
    Qed.

    Lemma filter_live_order h xs :
      List.filter (live_at h) (live_order h xs) = live_order h xs.
    Proof.
      induction xs as [|q tl IH]; simpl; [reflexivity|].
      destruct (live_at h q) eqn:Hlive; simpl; rewrite ?Hlive, IH;
        reflexivity.
    Qed.

    Lemma filter_strengthen (p q : Addr -> bool) xs :
      (forall l, In l xs -> q l = true -> p l = true) ->
      List.filter q xs = List.filter q (List.filter p xs).
    Proof.
      induction xs as [|l tl IH]; intro Himp; simpl; [reflexivity|].
      specialize (IH (fun r Hr => Himp r (or_intror Hr))).
      destruct (q l) eqn:Hq, (p l) eqn:Hp; simpl; rewrite ?Hq, ?Hp, IH;
        try reflexivity.
      exfalso. specialize (Himp l (or_introl eq_refl) Hq). congruence.
    Qed.

    Lemma filter_order_membership h chain saved :
      NoDup chain -> List.Forall (fun l => In l chain) saved ->
      List.filter
        (fun l => List.existsb (Nat.eqb l) (live_order h chain)) saved =
      List.filter (live_at h) saved.
    Proof.
      intros Hnodup Hsaved. induction Hsaved as [|l tl Hin Hforall IH];
        simpl; [reflexivity|].
      destruct (live_at h l) eqn:Hlive.
      - assert (Hord : In l (live_order h chain)).
        { apply live_order_spec; auto. }
        assert (Hex : List.existsb (Nat.eqb l) (live_order h chain) = true).
        { apply existsb_exists. exists l. split; [exact Hord|apply Nat.eqb_refl]. }
        now rewrite Hex, IH.
      - assert (Hord : ~ In l (live_order h chain)).
        { intro Hbad. apply live_order_spec in Hbad; auto.
          destruct Hbad as [_ Hbad]. congruence. }
        assert (Hex : List.existsb (Nat.eqb l) (live_order h chain) = false).
        { apply Bool.not_true_iff_false. intro Hexists. apply Hord.
          apply existsb_exists in Hexists as [r [Hrin Heq]].
          apply Nat.eqb_eq in Heq. now subst r. }
        now rewrite Hex, IH.
    Qed.

    Lemma remove_nat_not_in l xs :
      ~ In l xs -> List.remove Nat.eq_dec l xs = xs.
    Proof.
      induction xs as [|q tl IH]; simpl; intro Hnot; [reflexivity|].
      destruct (Nat.eq_dec l q) as [Heq|Hneq].
      - subst q. exfalso. apply Hnot. now left.
      - f_equal. apply IH. intro Hin. apply Hnot. now right.
    Qed.

    Lemma live_order_take_succ h p xs l v ts next :
      linked h p xs -> In l xs ->
      h l = Some (pair (pair (pair v ts) false) next) ->
      live_order
        (heap_update l (pair (pair (pair v ts) true) next) h) xs =
      List.remove Nat.eq_dec l (live_order h xs).
    Proof.
      intros Hlinked Hin Hlookup.
      induction Hlinked as
        [|hd hv hts taken hnext tl Hhd Htl IH Hfresh].
      - contradiction.
      - simpl in Hin. destruct Hin as [Heq|Hin].
        + subst hd. rewrite Hlookup in Hhd. inversion Hhd; subst.
          simpl. unfold live_at, node_live.
          rewrite HeapUpdateSelf, Hlookup. simpl.
          destruct (Nat.eq_dec l l) as [_|Hbad]; [|contradiction].
          rewrite remove_nat_not_in.
          * apply live_order_ext. intros q Hq.
            apply live_at_update_other. intro Heq. subst q.
            apply Hfresh. exact Hq.
          * intro Hbad. apply Hfresh. eapply live_order_in; exact Hbad.
        + assert (Hneq : l <> hd) by congruence.
          simpl. rewrite live_at_update_other by exact Hneq.
          specialize (IH Hin).
          destruct (live_at h hd) eqn:Hlive; simpl.
          * destruct (Nat.eq_dec l hd); [contradiction|]. now rewrite IH.
          * exact IH.
    Qed.

    Lemma abstract_nodes_take_same h xs l v ts taken next :
      In l xs ->
      h l = Some (pair (pair (pair v ts) taken) next) ->
      abstract_nodes
        (heap_update l (pair (pair (pair v ts) true) next) h) xs =
      abstract_nodes h xs.
    Proof.
      intros Hin Hlookup.
      rewrite abstract_nodes_update_existing by exact Hin.
      apply functional_extensionality. intro q.
      destruct (Nat.eq_dec l q) as [Heq|Hneq].
      - subst q.
        rewrite HeapUpdateSelf. unfold abstract_nodes.
        assert (Hex : List.existsb (Nat.eqb l) xs = true).
        { apply existsb_exists. exists l. split; [exact Hin|apply Nat.eqb_refl]. }
        now rewrite Hex, Hlookup.
      - apply HeapUpdateOther. exact Hneq.
    Qed.

    Lemma existsb_nat_eq l xs :
      List.existsb (Nat.eqb l) xs = true <-> In l xs.
    Proof.
      rewrite existsb_exists. split.
      - intros [q [Hin Heq]]. apply Nat.eqb_eq in Heq. subst; exact Hin.
      - intros Hin. exists l. split; [exact Hin|apply Nat.eqb_refl].
    Qed.

    Lemma existsb_nat_neq l xs :
      List.existsb (Nat.eqb l) xs = false <-> ~ In l xs.
    Proof.
      rewrite <- Bool.not_true_iff_false, existsb_nat_eq. tauto.
    Qed.

    Lemma abstract_nodes_in h xs l :
      In l xs -> abstract_nodes h xs l =
        match h l with
        | Some n => Some (node_projection n)
        | None => None
        end.
    Proof.
      intro Hin. unfold abstract_nodes.
      apply existsb_nat_eq in Hin. now rewrite Hin.
    Qed.

    Lemma abstract_nodes_notin h xs l :
      ~ In l xs -> abstract_nodes h xs l = None.
    Proof.
      intro Hnot. unfold abstract_nodes.
      apply existsb_nat_neq in Hnot. now rewrite Hnot.
    Qed.

    Lemma linked_abstract_lookup h p xs l v ts taken next :
      linked h p xs -> In l xs ->
      h l = Some (pair (pair (pair v ts) taken) next) ->
      abstract_nodes h xs l = Some (pair v ts).
    Proof.
      intros _ Hin Hlookup. rewrite abstract_nodes_in by exact Hin.
      rewrite Hlookup. reflexivity.
    Qed.

    Lemma heap_update_same {V} (h : @Heap V) l v :
      h l = Some v -> heap_update l v h = h.
    Proof.
      intro Hlookup. apply functional_extensionality. intro q.
      destruct (Nat.eq_dec l q) as [->|Hneq].
      - now rewrite HeapUpdateSelf.
      - now rewrite HeapUpdateOther.
    Qed.

    (** The stable representation deliberately permits unreachable allocated
        cells.  Such a cell is the owner's private node between [nmalloc]
        and CAS publication. *)
    Definition represents
        (h : @Heap (@Node A)) (top : Ptr) (count : nat)
        (s : @SPListState A) : Prop :=
      exists chain,
        HLinked top chain h /\
        counter s = count /\
        length chain = count /\
        nodes s = abstract_nodes h chain /\
        order s = live_order h chain.

    Lemma represents_setTS h top count s chain l v old_ts taken next ts :
      HLinked top chain h ->
      counter s = count ->
      length chain = count ->
      nodes s = abstract_nodes h chain ->
      order s = live_order h chain ->
      In l chain ->
      h l = Some (pair (pair (pair v old_ts) taken) next) ->
      represents
        (heap_update l
          (pair (pair (pair v
            (match old_ts with TSTop => ts | _ => old_ts end)) taken) next) h)
        top count (SPListSpec.setTS l ts s).
    Proof.
      intros Hspatial Hcount Hlength Hnodes Horder Hin Hlookup.
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      destruct old_ts as [|lower upper].
      - assert (Habstract : nodes s l = Some (pair v TSTop)).
        { rewrite Hnodes. eapply linked_abstract_lookup; eauto. }
        unfold SPListSpec.setTS. rewrite Habstract.
        exists chain. repeat split; simpl; auto.
        + apply linked_implies_HLinked. eapply linked_update_existing; eauto.
        + rewrite Hnodes.
          symmetry. apply abstract_nodes_update_existing. exact Hin.
        + rewrite Horder.
          symmetry. eapply live_order_update_same_taken; eauto.
          eapply linked_nodup; exact Hlinked.
      - assert (Habstract :
          nodes s l = Some (pair v (TSInterval lower upper))).
        { rewrite Hnodes. eapply linked_abstract_lookup; eauto. }
        unfold SPListSpec.setTS. rewrite Habstract.
        assert (Hsame :
          heap_update l
            (pair (pair (pair v (TSInterval lower upper)) taken) next) h = h).
        { apply heap_update_same. exact Hlookup. }
        rewrite Hsame. exists chain. repeat split; auto.
    Qed.

    Lemma represents_tryTake_succ h top count s chain l v ts next :
      HLinked top chain h ->
      counter s = count ->
      length chain = count ->
      nodes s = abstract_nodes h chain ->
      order s = live_order h chain ->
      In l chain ->
      h l = Some (pair (pair (pair v ts) false) next) ->
      represents
        (heap_update l (pair (pair (pair v ts) true) next) h)
        top count (SPListSpec.remove l s).
    Proof.
      intros Hspatial Hcount Hlength Hnodes Horder Hin Hlookup.
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      exists chain. repeat split; simpl; auto.
      - apply linked_implies_HLinked. eapply linked_update_existing; eauto.
      - rewrite Hnodes. symmetry. eapply abstract_nodes_take_same; eauto.
      - rewrite Horder. symmetry. eapply live_order_take_succ; eauto.
    Qed.

    Lemma abstract_nodes_prepend_fresh h chain l v ts taken top :
      linked h top chain -> h l = None ->
      abstract_nodes
        (heap_update l (pair (pair (pair v ts) taken) top) h)
        (l :: chain) =
      heap_update l (pair v ts) (abstract_nodes h chain).
    Proof.
      intros Hlinked Hfresh. apply functional_extensionality. intro q.
      destruct (Nat.eq_dec l q) as [Heq|Hneq].
      - subst q. rewrite HeapUpdateSelf. unfold abstract_nodes. simpl.
        rewrite Nat.eqb_refl, HeapUpdateSelf. reflexivity.
      - rewrite HeapUpdateOther by exact Hneq.
        unfold abstract_nodes. simpl.
        assert (Heqb : Nat.eqb q l = false).
        { apply Nat.eqb_neq. congruence. }
        rewrite Heqb, HeapUpdateOther by exact Hneq.
        reflexivity.
    Qed.

    Lemma live_order_prepend_fresh h chain l v ts top :
      linked h top chain -> h l = None ->
      live_order
        (heap_update l (pair (pair (pair v ts) false) top) h)
        (l :: chain) = l :: live_order h chain.
    Proof.
      intros Hlinked Hfresh. simpl. unfold live_at, node_live.
      rewrite HeapUpdateSelf. simpl. f_equal.
      apply live_order_ext. intros q Hin.
      apply live_at_update_other. intro Heq. subst q.
      eapply linked_fresh_notin; eauto.
    Qed.

    Lemma represents_insert h top count s chain l v :
      HLinked top chain h ->
      counter s = count ->
      length chain = count ->
      nodes s = abstract_nodes h chain ->
      order s = live_order h chain ->
      h l = None ->
      represents
        (heap_update l (pair (pair (pair v TSTop) false) top) h)
        (Some l) (S count) (SPListSpec.insert v l s).
    Proof.
      intros Hspatial Hcount Hlength Hnodes Horder Hfresh.
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      exists (l :: chain). split.
      - apply linked_implies_HLinked. eapply linked_prepend; eauto.
      - repeat split; simpl.
        + rewrite Hcount, Nat.add_1_r. reflexivity.
        + now rewrite Hlength.
        + rewrite Hnodes. symmetry. eapply abstract_nodes_prepend_fresh; eauto.
        + rewrite Horder. symmetry. eapply live_order_prepend_fresh; eauto.
    Qed.

    Lemma represents_allocate h top count s chain l v :
      HLinked top chain h ->
      counter s = count -> length chain = count ->
      nodes s = abstract_nodes h chain ->
      order s = live_order h chain -> h l = None ->
      represents
        (heap_update l (pair (pair (pair v TSTop) false) top) h)
        top count s.
    Proof.
      intros Hspatial Hcount Hlength Hnodes Horder Hfresh.
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      exists chain. repeat split; auto.
      - apply linked_implies_HLinked. eapply linked_update_fresh; eauto.
      - rewrite Hnodes. apply functional_extensionality. intro q.
        unfold abstract_nodes.
        destruct (List.existsb (Nat.eqb q) chain) eqn:Hin; [|reflexivity].
        apply existsb_nat_eq in Hin.
        rewrite HeapUpdateOther. reflexivity.
        intro Heq. subst q. eapply linked_fresh_notin; eauto.
      - rewrite Horder. apply live_order_ext. intros q Hin.
        symmetry. apply live_at_update_other.
        intro Heq. subst q. eapply linked_fresh_notin; eauto.
    Qed.

    Lemma represents_publish h top count s chain l v :
      HLinked top chain h ->
      counter s = count -> length chain = count ->
      nodes s = abstract_nodes h chain ->
      order s = live_order h chain ->
      nodes s l = None ->
      h l = Some (pair (pair (pair v TSTop) false) top) ->
      represents h (Some l) (S count) (SPListSpec.insert v l s).
    Proof.
      intros Hspatial Hcount Hlength Hnodes Horder Hundefined Hcell.
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      assert (Hnotin : ~ In l chain).
      { intro Hin. rewrite Hnodes, abstract_nodes_in, Hcell in Hundefined
          by exact Hin. discriminate. }
      exists (l :: chain). split.
      - apply linked_implies_HLinked. econstructor; eauto.
      - repeat split; simpl.
        + rewrite Hcount, Nat.add_1_r. reflexivity.
        + now rewrite Hlength.
        + apply functional_extensionality. intro r.
          unfold abstract_nodes. simpl.
          destruct (Nat.eq_dec l r) as [Heq|Hneq].
          * subst r. rewrite Nat.eqb_refl, HeapUpdateSelf, Hcell. reflexivity.
          * assert (Herb : Nat.eqb r l = false)
              by (apply Nat.eqb_neq; congruence).
            rewrite Herb, HeapUpdateOther by exact Hneq.
            rewrite Hnodes. reflexivity.
        + unfold live_at, node_live. rewrite Hcell. simpl. now rewrite Horder.
    Qed.

    (** Spatial versions of the representation updates.  Their premises
        expose exactly one owned cell; the arbitrary heap frame is carried
        unchanged and then hidden again when [represents] is reassembled. *)
    Lemma represents_setTS_frame h top count s chain l v old_ts taken next ts
        (Fr : HAssertion) :
      HLinked top chain h ->
      counter s = count ->
      length chain = count ->
      nodes s = abstract_nodes h chain ->
      order s = live_order h chain ->
      In l chain ->
      @sepcon _ heap_Join
        (HCell l (pair (pair (pair v old_ts) taken) next)) Fr h ->
      represents
        (heap_update l
          (pair (pair (pair v
            (match old_ts with TSTop => ts | _ => old_ts end)) taken) next) h)
        top count (SPListSpec.setTS l ts s) /\
      @sepcon _ heap_Join
        (HCell l
          (pair (pair (pair v
            (match old_ts with TSTop => ts | _ => old_ts end)) taken) next))
        Fr
        (heap_update l
          (pair (pair (pair v
            (match old_ts with TSTop => ts | _ => old_ts end)) taken) next) h).
    Proof.
      intros Hlinked Hcount Hlength Hnodes Horder Hin Hspatial.
      assert (Hlookup :
        h l = Some (pair (pair (pair v old_ts) taken) next)).
      { eapply heap_cell_read_frame; exact Hspatial. }
      split.
      - eapply represents_setTS; eauto.
      - eapply heap_cell_update_frame; exact Hspatial.
    Qed.

    Lemma represents_tryTake_frame h top count s chain l v ts next
        (Fr : HAssertion) :
      HLinked top chain h ->
      counter s = count ->
      length chain = count ->
      nodes s = abstract_nodes h chain ->
      order s = live_order h chain ->
      In l chain ->
      @sepcon _ heap_Join
        (HCell l (pair (pair (pair v ts) false) next)) Fr h ->
      represents
        (heap_update l (pair (pair (pair v ts) true) next) h)
        top count (SPListSpec.remove l s) /\
      @sepcon _ heap_Join
        (HCell l (pair (pair (pair v ts) true) next)) Fr
        (heap_update l (pair (pair (pair v ts) true) next) h).
    Proof.
      intros Hlinked Hcount Hlength Hnodes Horder Hin Hspatial.
      assert (Hlookup : h l = Some (pair (pair (pair v ts) false) next)).
      { eapply heap_cell_read_frame; exact Hspatial. }
      split.
      - eapply represents_tryTake_succ; eauto.
      - eapply heap_cell_update_frame; exact Hspatial.
    Qed.

    Lemma represents_tryTake_fail_frame h top count s chain l v ts next
        (Fr : HAssertion) :
      HLinked top chain h ->
      counter s = count ->
      length chain = count ->
      nodes s = abstract_nodes h chain ->
      order s = live_order h chain ->
      @sepcon _ heap_Join
        (HCell l (pair (pair (pair v ts) true) next)) Fr h ->
      represents h top count s /\
      @sepcon _ heap_Join
        (HCell l (pair (pair (pair v ts) true) next)) Fr h.
    Proof.
      intros Hlinked Hcount Hlength Hnodes Horder Hspatial. split.
      - exists chain. repeat split; assumption.
      - exact Hspatial.
    Qed.

    Lemma represents_allocate_frame h top count s chain l v :
      HLinked top chain h ->
      counter s = count -> length chain = count ->
      nodes s = abstract_nodes h chain ->
      order s = live_order h chain -> h l = None ->
      represents
        (heap_update l (pair (pair (pair v TSTop) false) top) h)
        top count s /\
      @sepcon _ heap_Join
        (HCell l (pair (pair (pair v TSTop) false) top))
        (HExact h)
        (heap_update l (pair (pair (pair v TSTop) false) top) h).
    Proof.
      intros Hlinked Hcount Hlength Hnodes Horder Hfresh. split.
      - eapply represents_allocate; eauto.
      - apply heap_alloc_frame. exact Hfresh.
    Qed.

    Lemma represents_publish_frame h top count s chain l v :
      HLinked top chain h ->
      counter s = count -> length chain = count ->
      nodes s = abstract_nodes h chain ->
      order s = live_order h chain ->
      nodes s l = None ->
      h l = Some (pair (pair (pair v TSTop) false) top) ->
      represents h (Some l) (S count) (SPListSpec.insert v l s) /\
      @sepcon _ heap_Join
        (HCell l (pair (pair (pair v TSTop) false) top))
        (HFrame l h) h.
    Proof.
      intros Hlinked Hcount Hlength Hnodes Horder Hundefined Hcell.
      split.
      - eapply represents_publish; eauto.
      - apply heap_cell_sep. exact Hcell.
    Qed.

    Definition mem_control_ok (mc : mem_control) : Prop :=
      match mc with
      | Pending _ t (nmalloc _ _) => t = owner
      | Pending _ t (nmsetTS _ _) => t = owner
      | _ => True
      end.

    Definition cas_control_ok (cc : cas_control) : Prop :=
      match cc with
      | Pending _ t (set _) => t = owner
      | _ => True
      end.

    Definition snapshot_consistent
        (s : @SPListState A)
        (pi : tmap (@LinState (li_sig F))) : Prop :=
      forall t,
        (exists saved, TMap.find t (snapshot s) = Some saved) <->
        TMap.find t pi = Some (ls_lini (@lgetTop A)).

    Definition source_I : assertion :=
      fun w =>
        exists mc cc s,
          SinglePossState.σ w = pair mc cc /\
          SinglePossState.ρ w = Ready s /\
          mem_control_ok mc /\
          cas_control_ok cc /\
          represents (mem_heap mc) (fst (cas_value cc))
            (snd (cas_value cc)) s /\
          snapshot_consistent s (SinglePossState.π w).


    Definition timestamp_evol (actor : tid) (old new : TS) : Prop :=
      old = new \/ (actor = owner /\ old = TSTop).

    Definition node_evol (actor : tid) (old new : @Node A) : Prop :=
      fst (fst (fst old)) = fst (fst (fst new)) /\
      timestamp_evol actor (snd (fst (fst old))) (snd (fst (fst new))) /\
      (snd (fst old) = true -> snd (fst new) = true) /\
      snd old = snd new.

    Definition heap_evol (actor : tid)
        (h h' : @Heap (@Node A)) : Prop :=
      forall l,
        match h l with
        | None => h' l = None \/ actor = owner
        | Some old =>
            exists new, h' l = Some new /\ node_evol actor old new
        end.

    Lemma heap_evol_linked actor h h' p xs :
      heap_evol actor h h' -> linked h p xs -> linked h' p xs.
    Proof.
      intros Hevol Hlinked.
      induction Hlinked as
        [|l v ts taken next tl Hlookup Htail IH Hfresh].
      - constructor.
      - specialize (Hevol l). rewrite Hlookup in Hevol.
        destruct Hevol as [new [Hnew Hevol]].
        destruct new as [[[v' ts'] taken'] next'].
        unfold node_evol in Hevol. simpl in Hevol.
        destruct Hevol as [Hv [Hts [Htaken Hnext]]]. subst v' next'.
        econstructor; eauto.
    Qed.

    Lemma heap_evol_live_imp actor h h' p xs l :
      heap_evol actor h h' -> linked h p xs -> In l xs ->
      live_at h' l = true -> live_at h l = true.
    Proof.
      intros Hevol Hlinked Hin Hlive.
      destruct (linked_lookup _ _ _ _ Hlinked Hin)
        as (v & ts & taken & next & Hlookup).
      specialize (Hevol l). rewrite Hlookup in Hevol.
      destruct Hevol as [new [Hnew Hnode]].
      destruct new as [[[v' ts'] taken'] next'].
      unfold node_evol in Hnode. simpl in Hnode.
      destruct Hnode as [Hv [Hts [Htaken Hnext]]].
      unfold live_at, node_live in *. rewrite Hnew in Hlive.
      rewrite Hlookup. simpl in *.
      destruct taken.
      - specialize (Htaken eq_refl). subst taken'. discriminate.
      - reflexivity.
    Qed.

    Lemma live_order_heap_evol actor h h' p xs :
      heap_evol actor h h' -> linked h p xs ->
      live_order h' xs = List.filter (live_at h') (live_order h xs).
    Proof.
      intros Hevol Hlinked.
      induction Hlinked as
        [|l v ts taken next tl Hlookup Htail IH Hfresh]; simpl;
        [reflexivity|].
      assert (Himp : live_at h' l = true -> live_at h l = true).
      { eapply (heap_evol_live_imp actor h h' (Some l) (l :: tl) l).
        - exact Hevol.
        - econstructor; eauto.
        - now left. }
      destruct (live_at h l) eqn:Hold, (live_at h' l) eqn:Hnew; simpl;
        rewrite ?Hold, ?Hnew, IH; try reflexivity.
      exfalso. specialize (Himp eq_refl). discriminate.
    Qed.

    Lemma abstract_nodes_some_in h xs l a :
      abstract_nodes h xs l = Some a -> In l xs.
    Proof.
      unfold abstract_nodes.
      destruct (List.existsb (Nat.eqb l) xs) eqn:Hex; [|discriminate].
      intros _. apply existsb_nat_eq. exact Hex.
    Qed.

    Definition cas_evol (actor : tid)
        (h : @Heap (@Node A)) (q : Ptr * nat)
        (h' : @Heap (@Node A)) (q' : Ptr * nat) : Prop :=
      if PositiveMap.E.eq_dec actor owner then
        exists old_chain new_chain prefix,
          linked h (fst q) old_chain /\
          linked h' (fst q') new_chain /\
          new_chain = prefix ++ old_chain
      else q' = q.

    Definition abstract_payload (c : abstract_control) : @SPListState A :=
      match c with
      | Ready s => s
      | AtomicPending s _ _ => s
      end.

    Definition source_G (actor : tid) : rg_relation :=
      fun w w' =>
        source_I w /\ source_I w' /\
        heap_evol actor
          (mem_heap (fst (SinglePossState.σ w)))
          (mem_heap (fst (SinglePossState.σ w'))) /\
        (forall l, actor <> owner ->
          nodes (abstract_payload (SinglePossState.ρ w)) l = None ->
          mem_heap (fst (SinglePossState.σ w)) l =
          mem_heap (fst (SinglePossState.σ w')) l) /\
        cas_evol actor
          (mem_heap (fst (SinglePossState.σ w)))
          (cas_value (snd (SinglePossState.σ w)))
          (mem_heap (fst (SinglePossState.σ w')))
          (cas_value (snd (SinglePossState.σ w'))) /\
        (forall q, q <> actor ->
          TMap.find q
            (snapshot (abstract_payload (SinglePossState.ρ w))) =
          TMap.find q
            (snapshot (abstract_payload (SinglePossState.ρ w')))) /\
        (forall q, q <> actor ->
          TMap.find q (SinglePossState.π w) =
          TMap.find q (SinglePossState.π w')).

    Definition source_R (observer : tid) : rg_relation :=
      AssertionsSingle.GuaranteeGeneratedRely source_G observer.


    Definition token_eq (observer : tid) : rg_relation :=
      fun w w' =>
        TMap.find observer (SinglePossState.π w) =
        TMap.find observer (SinglePossState.π w').

    Definition NodeDefined (l : Addr) : assertion :=
      fun w => exists a,
        nodes (abstract_payload (SinglePossState.ρ w)) l = Some a.

    Definition NodeUndefined (l : Addr) : assertion :=
      fun w => nodes (abstract_payload (SinglePossState.ρ w)) l = None.

    Definition CASIs (q : Ptr * nat) : assertion :=
      fun w => cas_value (snd (SinglePossState.σ w)) = q.

    Lemma source_G_preserves_defined actor w w' l :
      source_G actor w w' -> NodeDefined l w -> NodeDefined l w'.
    Proof.
      intros [HI [HI' [Hheap [Hprivate [Hcas [Hsnap Htokens]]]]]] Hdefined.
      destruct HI as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hconsistent).
      destruct HI' as
        (mc' & cc' & s' & Eσ' & Eρ' & Hmc' & Hcc' & Hrep' & Hconsistent').
      destruct Hrep as
        (xs & Hspatial & Hcount & Hlength & Hnodes & Horder).
      destruct Hrep' as
        (ys & Hspatial' & Hcount' & Hlength' & Hnodes' & Horder').
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      pose proof (HLinked_implies_linked _ _ _ Hspatial') as Hlinked'.
      unfold NodeDefined in Hdefined. rewrite Eρ in Hdefined. simpl in Hdefined.
      destruct Hdefined as [a Hdefined].
      assert (Hin : In l xs).
      { apply (abstract_nodes_some_in (mem_heap mc) xs l a).
        now rewrite <- Hnodes. }
      destruct (linked_lookup _ _ _ _ Hlinked Hin)
        as (v & ts & taken & next & Hlookup).
      pose proof Hheap as Hheap_all.
      specialize (Hheap l). rewrite Eσ, Eσ' in Hheap; simpl in Hheap.
      rewrite Hlookup in Hheap.
      destruct Hheap as [new [Hnew Hnewevol]].
      assert (Hin' : In l ys).
      { rewrite Eσ, Eσ' in Hcas; simpl in Hcas.
        unfold cas_evol in Hcas.
        destruct (PositiveMap.E.eq_dec actor owner) as [Heqactor|Hneqactor].
        - destruct Hcas as
            (old_chain & new_chain & prefix & Hold & Hnewchain & Happend).
          assert (Exs : old_chain = xs).
          { eapply linked_deterministic; eauto. }
          assert (Eys : new_chain = ys).
          { eapply linked_deterministic; eauto. }
          rewrite <- Eys, Happend, Exs.
          apply in_or_app. right. exact Hin.
        - assert (Hsameq : cas_value cc' = cas_value cc) by exact Hcas.
          assert (Hpreserved :
            linked (mem_heap mc') (fst (cas_value cc)) xs).
          { eapply heap_evol_linked; [|exact Hlinked].
            rewrite Eσ, Eσ' in Hheap_all; simpl in Hheap_all.
            exact Hheap_all. }
          rewrite <- Hsameq in Hpreserved.
          assert (Exs : xs = ys).
          { eapply linked_deterministic; eauto. }
          now rewrite <- Exs. }
      unfold NodeDefined. rewrite Eρ'. simpl. exists (node_projection new).
      rewrite Hnodes', abstract_nodes_in by exact Hin'.
      now rewrite Hnew.
    Qed.

    Lemma source_G_preserves_undefined_nonowner actor w w' l :
      actor <> owner -> source_G actor w w' ->
      NodeUndefined l w -> NodeUndefined l w'.
    Proof.
      intros Hactor
        [HI [HI' [Hheap [Hprivate [Hcas [Hsnap Htokens]]]]]] Hundefined.
      destruct HI as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hconsistent).
      destruct HI' as
        (mc' & cc' & s' & Eσ' & Eρ' & Hmc' & Hcc' & Hrep' & Hconsistent').
      destruct Hrep as
        (xs & Hspatial & Hcount & Hlength & Hnodes & Horder).
      destruct Hrep' as
        (ys & Hspatial' & Hcount' & Hlength' & Hnodes' & Horder').
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      pose proof (HLinked_implies_linked _ _ _ Hspatial') as Hlinked'.
      rewrite Eσ, Eσ' in Hcas; simpl in Hcas.
      unfold cas_evol in Hcas.
      destruct (PositiveMap.E.eq_dec actor owner); [contradiction|].
      assert (Hlinked_preserved :
        linked (mem_heap mc') (fst (cas_value cc)) xs).
      { eapply heap_evol_linked; [|exact Hlinked].
        rewrite Eσ, Eσ' in Hheap; simpl in Hheap. exact Hheap. }
      rewrite <- Hcas in Hlinked_preserved.
      assert (Exs : xs = ys) by (eapply linked_deterministic; eauto).
      unfold NodeUndefined in *. rewrite Eρ in Hundefined. simpl in Hundefined.
      rewrite Eρ'. simpl. rewrite Hnodes'. apply abstract_nodes_notin.
      intro Hin. rewrite <- Exs in Hin.
      destruct (linked_lookup _ _ _ _ Hlinked Hin)
        as (v & ts & taken & next & Hlookup).
      rewrite Hnodes, abstract_nodes_in, Hlookup in Hundefined by exact Hin.
      discriminate.
    Qed.

    Lemma source_G_cas_nonowner actor w w' :
      actor <> owner -> source_G actor w w' ->
      cas_value (snd (SinglePossState.σ w)) =
      cas_value (snd (SinglePossState.σ w')).
    Proof.
      intros Hactor [_ [_ [_ [_ [Hcas _]]]]].
      unfold cas_evol in Hcas.
      destruct (PositiveMap.E.eq_dec actor owner); [contradiction|].
      symmetry. exact Hcas.
    Qed.

    Lemma source_R_owner_preserves_cas w w' :
      source_R owner w w' ->
      cas_value (snd (SinglePossState.σ w)) =
      cas_value (snd (SinglePossState.σ w')).
    Proof.
      intros [[actor [Hneq HG]]|Hadmin].
      - eapply source_G_cas_nonowner; eauto.
      - pose proof
          (AssertionsSingle.linearization_rely_observer_view owner _ _ Hadmin)
          as [Hσ [Hρ Htoken]].
        now rewrite Hσ.
    Qed.

    Lemma source_R_owner_preserves_undefined w w' l :
      source_R owner w w' -> NodeUndefined l w -> NodeUndefined l w'.
    Proof.
      intros [[actor [Hneq HG]]|Hadmin] Hundefined.
      - eapply source_G_preserves_undefined_nonowner; eauto.
      - pose proof
          (AssertionsSingle.linearization_rely_observer_view owner _ _ Hadmin)
          as [Hσ [Hρ Htoken]].
        unfold NodeUndefined in *. now rewrite <- Hρ.
    Qed.

    Lemma source_R_owner_preserves_private w w' l :
      source_R owner w w' -> NodeUndefined l w ->
      mem_heap (fst (SinglePossState.σ w)) l =
      mem_heap (fst (SinglePossState.σ w')) l.
    Proof.
      intros [[actor [Hneq HG]]|Hadmin] Hundefined.
      - destruct HG as
          [HI [HI' [Hheap [Hprivate [Hcas [Hsnap Htokens]]]]]].
        apply Hprivate; [exact Hneq|exact Hundefined].
      - pose proof
          (AssertionsSingle.linearization_rely_observer_view owner _ _ Hadmin)
          as [Hσ [Hρ Htoken]].
        now rewrite Hσ.
    Qed.

    Lemma source_I_defined_lookup w l :
      source_I w -> NodeDefined l w ->
      exists v ts taken next,
        mem_heap (fst (SinglePossState.σ w)) l =
          Some (pair (pair (pair v ts) taken) next).
    Proof.
      intros HI Hdefined.
      destruct HI as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hconsistent).
      destruct Hrep as
        (xs & Hspatial & Hcount & Hlength & Hnodes & Horder).
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      unfold NodeDefined in Hdefined. rewrite Eρ in Hdefined. simpl in Hdefined.
      destruct Hdefined as [a Hdefined].
      assert (Hin : In l xs).
      { apply (abstract_nodes_some_in (mem_heap mc) xs l a).
        now rewrite <- Hnodes. }
      destruct (linked_lookup _ _ _ _ Hlinked Hin)
        as (v & ts & taken & next & Hlookup).
      exists v, ts, taken, next. now rewrite Eσ.
    Qed.

    Lemma heap_evol_setTS h l v old_ts taken next ts :
      h l = Some (pair (pair (pair v old_ts) taken) next) ->
      heap_evol owner h
        (heap_update l
          (pair (pair (pair v
            (match old_ts with TSTop => ts | _ => old_ts end)) taken) next) h).
    Proof.
      intros Hlookup q. destruct (Nat.eq_dec l q) as [->|Hneq].
      - rewrite Hlookup, HeapUpdateSelf. eexists. split; [reflexivity|].
        unfold node_evol, timestamp_evol. simpl. repeat split; auto.
        destruct old_ts; auto.
      - rewrite HeapUpdateOther by exact Hneq.
        destruct (h q) as [n|] eqn:Hq.
        + exists n. split; [reflexivity|].
          unfold node_evol, timestamp_evol. repeat split; auto.
        + now left.
    Qed.

    Lemma heap_evol_tryTake actor h l v ts next :
      h l = Some (pair (pair (pair v ts) false) next) ->
      heap_evol actor h
        (heap_update l (pair (pair (pair v ts) true) next) h).
    Proof.
      intros Hlookup q. destruct (Nat.eq_dec l q) as [Heq|Hneq].
      - subst q. rewrite Hlookup, HeapUpdateSelf. eexists. split; [reflexivity|].
        unfold node_evol, timestamp_evol. simpl. repeat split; auto.
      - rewrite HeapUpdateOther by exact Hneq.
        destruct (h q) as [n|] eqn:Hq.
        + exists n. split; [reflexivity|].
          unfold node_evol, timestamp_evol. repeat split; auto.
        + now left.
    Qed.

    Lemma heap_evol_allocate h l v top :
      h l = None ->
      heap_evol owner h
        (heap_update l (pair (pair (pair v TSTop) false) top) h).
    Proof.
      intros Hfresh q. destruct (Nat.eq_dec l q) as [Heq|Hneq].
      - subst q. rewrite Hfresh. right. reflexivity.
      - rewrite HeapUpdateOther by exact Hneq.
        destruct (h q) as [n|] eqn:Hq.
        + exists n. split; [reflexivity|].
          unfold node_evol, timestamp_evol. repeat split; auto.
        + now left.
    Qed.

    Lemma source_G_token_other actor observer :
      actor <> observer ->
      (source_G actor ⊆ token_eq observer)%RGRelation.
    Proof.
      intros Hneq w w' [_ [_ [_ [_ [_ [_ Htokens]]]]]].
      apply Htokens. congruence.
    Qed.

    Lemma observer_view_token observer :
      (AssertionsSingle.ObserverViewEq observer ⊆
        token_eq observer)%RGRelation.
    Proof. intros w w' [_ [_ Htoken]]. exact Htoken. Qed.

    Lemma source_R_token observer :
      (source_R observer ⊆ token_eq observer)%RGRelation.
    Proof.
      eapply AssertionsSingle.guarantee_generated_rely_facts.
      - intros actor Hneq. apply source_G_token_other; exact Hneq.
      - apply observer_view_token.
    Qed.

    Definition defined_facts (l : Addr) : rg_relation :=
      fun w w' => NodeDefined l w -> NodeDefined l w'.

    Lemma observer_view_defined l observer :
      (AssertionsSingle.ObserverViewEq observer ⊆
        defined_facts l)%RGRelation.
    Proof.
      intros w w' [Hsigma [Hrho Htoken]] Hdefined.
      unfold NodeDefined in *. rewrite <- Hrho. exact Hdefined.
    Qed.

    Lemma source_R_preserves_defined observer l :
      (source_R observer ⊆ defined_facts l)%RGRelation.
    Proof.
      intros w w' HR Hdefined.
      destruct HR as [[actor [Hneq HG]]|Hadmin].
      - eapply source_G_preserves_defined; eauto.
      - eapply observer_view_defined; [|exact Hdefined].
        eapply AssertionsSingle.linearization_rely_observer_view.
        exact Hadmin.
    Qed.

    Lemma source_valid_rg observer w w' :
      source_R observer w w' -> source_I w' ->
      TMap.find observer (SinglePossState.π w) = None <->
      TMap.find observer (SinglePossState.π w') = None.
    Proof.
      intros HR _. pose proof (source_R_token observer _ _ HR) as Heq.
      rewrite Heq. tauto.
    Qed.

    Lemma source_parallel_compatible actor observer :
      actor <> observer -> forall w w',
      (source_G actor w w' \/
       (AssertionsSingle.GINV actor w w' \/
        AssertionsSingle.GRET actor w w') \/
       AssertionsSingle.A.GId w w') ->
      source_R observer w w'.
    Proof.
      intros Hneq. eapply AssertionsSingle.guarantee_generated_parallel_compatible.
      exact Hneq.
    Qed.

    Lemma heap_evol_refl actor h : heap_evol actor h h.
    Proof.
      intros l. destruct (h l) as [n|] eqn:Hlookup.
      - exists n. split; [reflexivity|].
        unfold node_evol, timestamp_evol. repeat split; auto.
      - now left.
    Qed.

    Lemma source_G_refl actor w :
      source_I w -> source_G actor w w.
    Proof.
      intro HI. repeat split; auto using heap_evol_refl.
      - unfold cas_evol.
        destruct (PositiveMap.E.eq_dec actor owner) as [Heq|Hneq].
        + destruct HI as
            (mc & cc & s & Hsigma & Habstract & Hmc & Hcc & Hrep & Hsnap).
          destruct Hrep as
            (chain & Hspatial & Hcount & Hlength & Hnodes & Horder).
          pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
          rewrite Hsigma. simpl.
          exists chain, chain, nil. repeat split; auto.
        + reflexivity.
    Qed.

    Lemma source_G_same_payload actor w w' :
      source_I w -> source_I w' ->
      mem_heap (fst (SinglePossState.σ w)) =
        mem_heap (fst (SinglePossState.σ w')) ->
      cas_value (snd (SinglePossState.σ w)) =
        cas_value (snd (SinglePossState.σ w')) ->
      snapshot (abstract_payload (SinglePossState.ρ w)) =
        snapshot (abstract_payload (SinglePossState.ρ w')) ->
      (forall q, q <> actor ->
        TMap.find q (SinglePossState.π w) =
        TMap.find q (SinglePossState.π w')) ->
      source_G actor w w'.
    Proof.
      intros HI HI' Hheap Hcas Hsnapshot Htokens.
      repeat split; auto.
      - rewrite <- Hheap. apply heap_evol_refl.
      - intros l Hactor Hundefined. now rewrite Hheap.
      - unfold cas_evol.
        destruct (PositiveMap.E.eq_dec actor owner) as [Heq|Hneq].
        + destruct HI as
            (mc & cc & s & Hsigma & Habstract & Hmc & Hcc & Hrep & Hsnap).
          destruct Hrep as
            (chain & Hspatial & Hcount & Hlength & Hnodes & Horder).
          pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
          rewrite Hsigma in Hheap, Hcas |- *; simpl in Hheap, Hcas |- *.
          exists chain, chain, nil. repeat split; auto.
          rewrite <- Hheap, <- Hcas. exact Hlinked.
        + symmetry. exact Hcas.
      - intros q Hq. rewrite <- Hsnapshot. reflexivity.
    Qed.

    Lemma source_I_change_controls w mc' cc' :
      source_I w ->
      mem_heap mc' = mem_heap (fst (SinglePossState.σ w)) ->
      cas_value cc' = cas_value (snd (SinglePossState.σ w)) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair mc' cc') (SinglePossState.ρ w) (SinglePossState.π w)).
    Proof.
      intros HI Hheap Hcas Hmc' Hcc'.
      destruct HI as
        (mc & cc & s & Hsigma & Hrho & Hmc & Hcc & Hrep & Hsnap).
      exists mc', cc', s. simpl. split; [reflexivity|].
      split; [exact Hrho|].
      split; [exact Hmc'|].
      split; [exact Hcc'|].
      split.
      - rewrite Hheap, Hcas, Hsigma. exact Hrep.
      - exact Hsnap.
    Qed.

    Lemma source_I_mem_control w :
      source_I w -> mem_control_ok (fst (SinglePossState.σ w)).
    Proof.
      intros (mc & cc & s & Hsigma & Hrho & Hmc & Hcc & Hrep & Hsnap).
      rewrite Hsigma. exact Hmc.
    Qed.

    Lemma source_I_cas_control w :
      source_I w -> cas_control_ok (snd (SinglePossState.σ w)).
    Proof.
      intros (mc & cc & s & Hsigma & Hrho & Hmc & Hcc & Hrep & Hsnap).
      rewrite Hsigma. exact Hcc.
    Qed.

    (** ** Slot-local replay of abstract steps

        Possibilities in a set differ only in per-thread "slots": a thread's
        snapshot entry and its linearization-map entry.  Abstract steps of
        a thread never inspect another thread's slot, so a sequence of
        steps can be replayed on a possibility that differs only in some
        other thread's slot. *)

    Definition payload_agree (q : tid) (s s' : @SPListState A) : Prop :=
      counter s = counter s' /\ nodes s = nodes s' /\ order s = order s' /\
      (forall r, r <> q ->
        TMap.find r (snapshot s) = TMap.find r (snapshot s')).

    Definition control_agree (q : tid) (c c' : abstract_control) : Prop :=
      match c, c' with
      | Ready s, Ready s' => payload_agree q s s'
      | AtomicPending s t op, AtomicPending s' t' op' =>
          t = t' /\ op = op' /\ payload_agree q s s'
      | _, _ => False
      end.

    Lemma payload_agree_refl q s : payload_agree q s s.
    Proof. repeat split; auto. Qed.

    Lemma payload_agree_sym q s s' :
      payload_agree q s s' -> payload_agree q s' s.
    Proof.
      intros (Hc & Hn & Ho & Hs). repeat split; auto.
      intros r Hr. symmetry. auto.
    Qed.

    Lemma actual_snapshot_agree q t s s' :
      t <> q -> payload_agree q s s' ->
      actual_snapshot t s = actual_snapshot t s'.
    Proof.
      intros Hneq (Hc & Hn & Ho & Hs).
      unfold actual_snapshot. rewrite (Hs t Hneq), Ho. reflexivity.
    Qed.

    Lemma payload_agree_start q t s s' :
      t <> q -> payload_agree q s s' ->
      payload_agree q (start_snapshot t s) (start_snapshot t s').
    Proof.
      intros Hneq (Hc & Hn & Ho & Hs).
      repeat split; simpl; auto.
      intros r Hr. destruct (PositiveMap.E.eq_dec r t) as [->|Hrt].
      - rewrite !TMap.gss, Ho, Hc. reflexivity.
      - rewrite !TMap.gso by exact Hrt. auto.
    Qed.

    Lemma payload_agree_clear q t s s' :
      payload_agree q s s' ->
      payload_agree q (clear_snapshot t s) (clear_snapshot t s').
    Proof.
      intros (Hc & Hn & Ho & Hs).
      repeat split; simpl; auto.
      intros r Hr. destruct (PositiveMap.E.eq_dec r t) as [->|Hrt].
      - rewrite !TMap.grs. reflexivity.
      - rewrite !TMap.gro by exact Hrt. auto.
    Qed.

    Lemma payload_agree_insert q v l s s' :
      payload_agree q s s' ->
      payload_agree q (insert v l s) (insert v l s').
    Proof.
      intros (Hc & Hn & Ho & Hs).
      repeat split; simpl; auto; congruence.
    Qed.

    Lemma payload_agree_setTS q l ts s s' :
      payload_agree q s s' ->
      payload_agree q (setTS l ts s) (setTS l ts s').
    Proof.
      intros Hagree. pose proof Hagree as (Hc & Hn & Ho & Hs).
      unfold setTS. rewrite <- Hn.
      destruct (nodes s l) as [[v [|lo hi]]|]; auto.
      repeat split; simpl; auto; congruence.
    Qed.

    Lemma payload_agree_remove q l s s' :
      payload_agree q s s' ->
      payload_agree q (remove l s) (remove l s').
    Proof.
      intros (Hc & Hn & Ho & Hs).
      repeat split; simpl; auto; congruence.
    Qed.

    Definition control_snapshot (q : tid) (c : abstract_control) :=
      TMap.find q (snapshot (abstract_payload c)).

    Lemma step_replay q ev c1 c2 c1' :
      te_tid ev <> q ->
      @StepSPList A owner ev c1 c2 ->
      control_agree q c1 c1' ->
      exists c2',
        @StepSPList A owner ev c1' c2' /\ control_agree q c2 c2' /\
        control_snapshot q c2' = control_snapshot q c1'.
    Proof.
      intros Hneq Hstep Hagree.
      inversion Hstep; subst; simpl in Hneq;
        destruct c1' as [s' | s' t' op']; simpl in Hagree; try contradiction;
        try (destruct Hagree as (<- & <- & Hagree));
        pose proof Hagree as (Hc & Hn & Ho & Hs).
      - (* getTop inv *)
        eexists. split; [|split].
        + constructor. rewrite <- (Hs _ Hneq). assumption.
        + apply payload_agree_start; auto.
        + unfold control_snapshot. simpl.
          rewrite TMap.gso by congruence. reflexivity.
      - (* getTop nonEmpty *)
        eexists. split; [|split].
        + eapply step_getTop_nonEmpty.
          * rewrite <- (actual_snapshot_agree q _ s s' Hneq Hagree).
            eassumption.
          * rewrite <- Hn. eassumption.
        + apply payload_agree_clear; auto.
        + unfold control_snapshot. simpl.
          rewrite TMap.gro by congruence. reflexivity.
      - (* getTop empty *)
        eexists. split; [|split].
        + eapply step_getTop_empty.
          rewrite <- (actual_snapshot_agree q _ s s' Hneq Hagree).
          eassumption.
        + apply payload_agree_clear; auto.
        + unfold control_snapshot. simpl.
          rewrite TMap.gro by congruence. reflexivity.
      - (* linsert inv *)
        eexists. split; [|split].
        + constructor; auto.
        + simpl. repeat split; auto.
        + reflexivity.
      - (* linsert res *)
        eexists. split; [|split].
        + constructor. rewrite <- Hn. assumption.
        + apply payload_agree_insert; auto.
        + reflexivity.
      - (* setTS inv *)
        eexists. split; [|split].
        + constructor; auto.
        + simpl. repeat split; auto.
        + reflexivity.
      - (* setTS res *)
        eexists. split; [|split].
        + constructor.
        + apply payload_agree_setTS; auto.
        + unfold control_snapshot. simpl. unfold setTS.
          destruct (nodes s' l) as [[? [|? ?]]|]; reflexivity.
      - (* getCounter inv *)
        eexists. split; [|split].
        + constructor.
        + simpl. repeat split; auto.
        + reflexivity.
      - (* getCounter res *)
        exists (Ready s'). split; [|split].
        + rewrite Hc. constructor.
        + assumption.
        + reflexivity.
      - (* tryRemove inv *)
        eexists. split; [|split].
        + constructor. rewrite <- Hn. assumption.
        + simpl. repeat split; auto.
        + reflexivity.
      - (* tryRemove succ *)
        eexists. split; [|split].
        + constructor; [rewrite <- Hn | rewrite <- Ho]; assumption.
        + apply payload_agree_remove; auto.
        + reflexivity.
      - (* tryRemove fail *)
        exists (Ready s'). split; [|split].
        + constructor; [rewrite <- Hn | rewrite <- Ho]; assumption.
        + assumption.
        + reflexivity.
    Qed.

    (** Linearization-map entries only ever advance, so a thread whose entry
        is unchanged across a step sequence took no step in it. *)
    Definition ls_rank (ls : option (@LinState (li_sig F))) : nat :=
      match ls with
      | None => O
      | Some (ls_inv _) => S O
      | Some (ls_lini _) => S (S O)
      | Some (ls_linr _ _) => S (S (S O))
      end.

    Lemma poss_step_rank q (ρ1 ρ2 : abstract_state) π1 π2 :
      @poss_step _ (li_lts F) (PossOk ρ1 π1) (PossOk ρ2 π2) ->
      Peano.le (ls_rank (TMap.find q π1)) (ls_rank (TMap.find q π2)) /\
      (TMap.find q π1 = TMap.find q π2 \/
       Peano.lt (ls_rank (TMap.find q π1)) (ls_rank (TMap.find q π2))).
    Proof.
      intros Hstep. inversion Hstep; subst;
        match goal with
        | Hlin : TMap.find ?tt π1 = Some _ |- _ =>
          destruct (PositiveMap.E.eq_dec q tt) as [->|Hqt];
          [ rewrite Hlin, TMap.gss; unfold ls_rank; simpl;
            split; [repeat constructor|right; repeat constructor]
          | rewrite TMap.gso by exact Hqt; split; [apply Nat.le_refl|left; reflexivity] ]
        end.
    Qed.

    Lemma poss_steps_from_error p :
      @poss_steps _ (li_lts F) PossError p -> p = PossError.
    Proof.
      intros H. apply clos_rt_rt1n in H.
      remember PossError as e. induction H; subst; [reflexivity|].
      inversion H.
    Qed.

    Lemma poss_steps_rank q (ρ1 ρ2 : abstract_state) π1 π2 :
      @poss_steps _ (li_lts F) (PossOk ρ1 π1) (PossOk ρ2 π2) ->
      Peano.le (ls_rank (TMap.find q π1)) (ls_rank (TMap.find q π2)).
    Proof.
      intros Hsteps.
      remember (PossOk ρ1 π1) as p1. remember (PossOk ρ2 π2) as p2.
      revert ρ1 π1 ρ2 π2 Heqp1 Heqp2.
      induction Hsteps as [p1 p2 Hstep | p | p1 p2 p3 H12 IH12 H23 IH23];
        intros ρ1 π1 ρ2 π2 E1 E2; subst.
      - apply (poss_step_rank q) in Hstep. tauto.
      - inversion E2; subst. apply Nat.le_refl.
      - destruct p2 as [ρm πm|].
        + etransitivity; [eapply IH12 | eapply IH23]; eauto.
        + apply poss_steps_from_error in H23. discriminate.
    Qed.

    Lemma poss_step_replay q ρx πx ρx' πx' ρy πy :
      @poss_step _ (li_lts F) (PossOk ρx πx) (PossOk ρx' πx') ->
      TMap.find q πx' = TMap.find q πx ->
      control_agree q ρx ρy ->
      (forall r, r <> q -> TMap.find r πx = TMap.find r πy) ->
      exists ρy' πy',
        @poss_step _ (li_lts F) (PossOk ρy πy) (PossOk ρy' πy') /\
        control_agree q ρx' ρy' /\
        control_snapshot q ρy' = control_snapshot q ρy /\
        (forall r, r <> q -> TMap.find r πx' = TMap.find r πy') /\
        TMap.find q πy' = TMap.find q πy.
    Proof.
      intros Hstep Hq Hagree Htok.
      inversion Hstep; subst.
      - (* inv step *)
        match goal with
        | Hlin : TMap.find ?tt πx = Some (ls_inv ?ff),
          Hs : Step (li_lts F) ?ev ρx ρx' |- _ =>
          assert (Htq : tt <> q)
            by (intros Heq; subst; rewrite TMap.gss, Hlin in Hq; discriminate);
          destruct (step_replay q ev _ _ ρy Htq Hs Hagree)
            as (ρy' & Hstep' & Hagree' & Hsnap');
          exists ρy', (TMap.add tt (ls_lini ff) πy);
          split; [|split; [exact Hagree'|split; [exact Hsnap'|split]]];
          [ eapply ps_inv; [exact Hstep' | rewrite <- Htok by exact Htq; exact Hlin]
          | intros r Hr; destruct (PositiveMap.E.eq_dec r tt) as [->|Hrt];
            [rewrite !TMap.gss; reflexivity
            |rewrite !TMap.gso by exact Hrt; auto]
          | rewrite TMap.gso by congruence; reflexivity ]
        end.
      - (* res step *)
        match goal with
        | Hlin : TMap.find ?tt πx = Some (ls_lini ?ff),
          Hs : Step (li_lts F) ?ev ρx ρx' |- _ =>
          assert (Htq : tt <> q)
            by (intros Heq; subst; rewrite TMap.gss, Hlin in Hq; discriminate);
          destruct (step_replay q ev _ _ ρy Htq Hs Hagree)
            as (ρy' & Hstep' & Hagree' & Hsnap');
          eexists ρy', (TMap.add tt (ls_linr ff _) πy);
          split; [|split; [exact Hagree'|split; [exact Hsnap'|split]]];
          [ eapply ps_ret; [exact Hstep' | rewrite <- Htok by exact Htq; exact Hlin]
          | intros r Hr; destruct (PositiveMap.E.eq_dec r tt) as [->|Hrt];
            [rewrite !TMap.gss; reflexivity
            |rewrite !TMap.gso by exact Hrt; auto]
          | rewrite TMap.gso by congruence; reflexivity ]
        end.
    Qed.

    Lemma poss_steps_replay q ρx πx ρx' πx' ρy πy :
      @poss_steps _ (li_lts F) (PossOk ρx πx) (PossOk ρx' πx') ->
      TMap.find q πx' = TMap.find q πx ->
      control_agree q ρx ρy ->
      (forall r, r <> q -> TMap.find r πx = TMap.find r πy) ->
      exists ρy' πy',
        @poss_steps _ (li_lts F) (PossOk ρy πy) (PossOk ρy' πy') /\
        control_agree q ρx' ρy' /\
        control_snapshot q ρy' = control_snapshot q ρy /\
        (forall r, r <> q -> TMap.find r πx' = TMap.find r πy') /\
        TMap.find q πy' = TMap.find q πy.
    Proof.
      intros Hsteps. apply clos_rt_rt1n in Hsteps.
      remember (PossOk ρx πx) as p1. remember (PossOk ρx' πx') as p2.
      revert ρx πx ρx' πx' ρy πy Heqp1 Heqp2.
      induction Hsteps as [p | p1 p2 p3 H12 H23 IH];
        intros ρx πx ρx' πx' ρy πy E1 E2 Hq Hagree Htok; subst.
      - inversion E2; subst. exists ρy, πy.
        repeat split; auto. apply rt_refl.
      - destruct p2 as [ρm πm|].
        2:{ exfalso. apply clos_rt1n_rt, poss_steps_from_error in H23.
            discriminate. }
        assert (Hqm : TMap.find q πm = TMap.find q πx).
        { pose proof (poss_step_rank q _ _ _ _ H12)
            as [Hle [Heq|Hlt]]; [symmetry; exact Heq|].
          exfalso.
          pose proof (poss_steps_rank q _ _ _ _
            (clos_rt1n_rt _ _ _ _ H23)) as Hle'.
          rewrite Hq in Hle'.
          exact (Nat.lt_irrefl _ (Nat.lt_le_trans _ _ _ Hlt Hle')). }
        destruct (poss_step_replay q _ _ _ _ _ _ H12 Hqm Hagree Htok)
          as (ρy1 & πy1 & Hstep1 & Hagree1 & Hsnap1 & Htok1 & Hq1).
        destruct (IH _ _ _ _ ρy1 πy1 eq_refl eq_refl) as
          (ρy' & πy' & Hsteps' & Hagree' & Hsnap' & Htok' & Hq');
          [congruence | exact Hagree1 | exact Htok1 |].
        exists ρy', πy'. repeat split; auto.
        + eapply rt_trans; [apply rt_step; exact Hstep1 | exact Hsteps'].
        + congruence.
        + congruence.
    Qed.

    (** ** The payload of a possibility is determined by the concrete state *)

    Definition payload_of (w : single_state) : @SPListState A :=
      abstract_payload (SinglePossState.ρ w).

    Lemma source_I_ready w :
      source_I w -> SinglePossState.ρ w = Ready (payload_of w).
    Proof.
      intros (mc & cc & s & Eσ & Eρ & _). unfold payload_of.
      rewrite Eρ. reflexivity.
    Qed.

    Lemma represents_determined h top count s s' :
      represents h top count s -> represents h top count s' ->
      counter s = counter s' /\ nodes s = nodes s' /\ order s = order s'.
    Proof.
      intros (chain & Hsp & Hc & Hl & Hn & Ho)
        (chain' & Hsp' & Hc' & Hl' & Hn' & Ho').
      assert (chain' = chain).
      { eapply linked_deterministic; eapply HLinked_implies_linked; eauto. }
      subst chain'. repeat split; congruence.
    Qed.

    Lemma source_I_payload_determined w w' :
      source_I w -> source_I w' ->
      SinglePossState.σ w = SinglePossState.σ w' ->
      counter (payload_of w) = counter (payload_of w') /\
      nodes (payload_of w) = nodes (payload_of w') /\
      order (payload_of w) = order (payload_of w').
    Proof.
      intros HI HI' Eσ.
      destruct HI as (mc & cc & s & Eσ1 & Eρ1 & _ & _ & Hrep & _).
      destruct HI' as (mc' & cc' & s' & Eσ2 & Eρ2 & _ & _ & Hrep' & _).
      unfold payload_of. rewrite Eρ1, Eρ2. simpl.
      rewrite Eσ, Eσ2 in Eσ1. inversion Eσ1; subst mc' cc'.
      eapply represents_determined; eauto.
    Qed.

    (** ** Pointwise possibility facade

        [SPListImpl.getTop_impl] reads a node's timestamp before its taken
        flag.  When the flag is read as [false], [getTop] linearizes at the
        earlier timestamp read, which cannot be known at that time.  The
        proof therefore keeps, between the two reads, both the possibility
        in which [getTop] has already returned and the one in which it is
        still scanning, and drops one of them at the flag read.

        Every assertion below holds pointwise on all possibilities of a
        set.  The rely/guarantee relations relate each new possibility back
        to an old one, and in addition preserve the "twin" structure that
        keeps both branches available for an observer [q]: for every
        possibility there is one that differs only in [q]'s slot (its
        snapshot entry and its linearization-map entry) and carries the
        other linearization kind. *)

    Definition set_state :=
      @SetPossState.ProofStateSet _ _ (li_lts E) (li_lts F).
    Definition set_assertion := @Assertion set_state.
    Definition set_relation :=
      @AssertionsSet.A.RGRelation _ _ (li_lts E) (li_lts F).

    Definition mk (σ : concrete_state) (ρ : abstract_state)
        (π : tmap (@LinState (li_sig F))) : single_state :=
      @SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        σ ρ π.

    Definition mks (σ : concrete_state)
        (Δ : @AbstractConfig (li_sig F) (li_lts F)) : set_state :=
      @SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F) σ Δ.

    Definition slot_snapshot (q : tid) (w : single_state) :=
      TMap.find q (snapshot (payload_of w)).
    Definition slot_token (q : tid) (w : single_state) :=
      TMap.find q (SinglePossState.π w).

    (** Agreement everywhere except in [q]'s slot. *)
    Definition offslot_agree (q : tid) (x y : single_state) : Prop :=
      SinglePossState.σ x = SinglePossState.σ y /\
      (forall r, r <> q -> slot_snapshot r x = slot_snapshot r y) /\
      (forall r, r <> q -> slot_token r x = slot_token r y).

    (** Agreement on the concrete state and on [q]'s slot. *)
    Definition slot_agree (q : tid) (x y : single_state) : Prop :=
      SinglePossState.σ x = SinglePossState.σ y /\
      slot_snapshot q x = slot_snapshot q y /\
      slot_token q x = slot_token q y.

    (** An assertion of thread [q] that only looks at the concrete state,
        the (concrete-state-determined) payload, and [q]'s own slot. *)
    Definition slot_local (q : tid) (P : assertion) : Prop :=
      forall x y, P x -> source_I y -> slot_agree q x y -> P y.

    Definition kind_lini (q : tid) (x : single_state) : Prop :=
      exists f, slot_token q x = Some (ls_lini f).
    Definition kind_linr (q : tid) (x : single_state) : Prop :=
      exists f ret, slot_token q x = Some (ls_linr f ret).

    Definition HasKind (K : tid -> single_state -> Prop) (q : tid)
        (s : set_state) : Prop :=
      forall ρ π, SetPossState.Δ s ρ π ->
        exists ρ' π', SetPossState.Δ s ρ' π' /\
          offslot_agree q (mk (SetPossState.σ s) ρ π)
            (mk (SetPossState.σ s) ρ' π') /\
          K q (mk (SetPossState.σ s) ρ' π').

    Definition twins_preserved (q : tid) (s s' : set_state) : Prop :=
      (HasKind kind_lini q s -> HasKind kind_lini q s') /\
      (HasKind kind_linr q s -> HasKind kind_linr q s').

    Definition lift_assert (P : assertion) : set_assertion :=
      fun s => forall ρ π, SetPossState.Δ s ρ π ->
        P (mk (SetPossState.σ s) ρ π).

    Definition lift_backward (Rs : rg_relation) (s s' : set_state) : Prop :=
      forall ρ' π', SetPossState.Δ s' ρ' π' ->
        exists ρ π, SetPossState.Δ s ρ π /\
          Rs (mk (SetPossState.σ s) ρ π) (mk (SetPossState.σ s') ρ' π').

    Definition lift_relation (actor : tid) (Rs : rg_relation) :
        set_relation :=
      fun s s' => lift_backward Rs s s' /\
        forall q, q <> actor -> twins_preserved q s s'.

    Definition SI : set_assertion := lift_assert source_I.
    Definition G (t : tid) : set_relation := lift_relation t (source_G t).
    Definition R (t : tid) : set_relation :=
      fun s s' => lift_backward (source_R t) s s' /\ twins_preserved t s s'.

    Lemma lift_impl (P Q : assertion) :
      (forall x, P x -> Q x) ->
      forall s, lift_assert P s -> lift_assert Q s.
    Proof. intros HPQ s HP ρ π Hposs. apply HPQ, HP, Hposs. Qed.

    Lemma lift_no_error ev (P : assertion) :
      (forall x, P x -> AssertionsSingle.A.ANoError ev x) ->
      forall s, lift_assert P s -> AssertionsSet.A.ANoError ev s.
    Proof.
      intros Hsafe s HP.
      destruct (ac_nonempty (SetPossState.Δ s)) as (ρ & π & Hposs).
      exact (Hsafe _ (HP _ _ Hposs)).
    Qed.

    Lemma lift_stable t (P : assertion) :
      AssertionsSingle.A.Stable (source_R t) source_I P ->
      AssertionsSet.A.Stable (R t) SI (lift_assert P).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSet.A.Stable,
        AssertionsSingle.A.ComposeA, AssertionsSet.A.ComposeA.
      intros Hstable s' [[s [HP [Hback _]]] HI] ρ' π' Hposs'.
      destruct (Hback _ _ Hposs') as (ρ & π & Hposs & HR).
      apply Hstable. split.
      - exists (mk (SetPossState.σ s) ρ π). split; [apply HP, Hposs | exact HR].
      - apply HI, Hposs'.
    Qed.

    Lemma lift_post_lin (P : assertion) t ls :
      (forall x, P x -> TMap.find t (SinglePossState.π x) = Some ls) ->
      forall s, lift_assert P s ->
      forall ρ π, SetPossState.Δ s ρ π -> TMap.find t π = Some ls.
    Proof. intros Hlin s HP ρ π Hposs. exact (Hlin _ (HP _ _ Hposs)). Qed.

    Lemma lift_initial (P : assertion) σ ρ π :
      P (mk σ ρ π) -> lift_assert P (mks σ (ac_singleton ρ π)).
    Proof.
      intros HP ρ' π' Hposs. inversion Hposs; subst. exact HP.
    Qed.

    Lemma kind_lini_token q x y :
      slot_token q x = slot_token q y -> kind_lini q x -> kind_lini q y.
    Proof. intros Heq [f Hf]. exists f. rewrite <- Heq. exact Hf. Qed.

    Lemma kind_linr_token q x y :
      slot_token q x = slot_token q y -> kind_linr q x -> kind_linr q y.
    Proof. intros Heq [f [ret Hf]]. exists f, ret. rewrite <- Heq. exact Hf. Qed.

    Lemma offslot_agree_change_σ q σ1 σ2 ρ π ρ' π' :
      offslot_agree q (mk σ1 ρ π) (mk σ1 ρ' π') ->
      offslot_agree q (mk σ2 ρ π) (mk σ2 ρ' π').
    Proof. intros [_ [Hs Ht]]. split; [reflexivity|split; assumption]. Qed.

    Lemma twins_preserved_refl q σ σ' Δ :
      twins_preserved q (mks σ Δ) (mks σ' Δ).
    Proof.
      assert (Hgen : forall K : tid -> single_state -> Prop,
        (forall σ1 σ2 ρ π, K q (mk σ1 ρ π) -> K q (mk σ2 ρ π)) ->
        HasKind K q (mks σ Δ) -> HasKind K q (mks σ' Δ)).
      { intros K Kσ HK ρ π Hposs.
        destruct (HK ρ π Hposs) as (ρ' & π' & Hposs' & Hoff & Hkind).
        exists ρ', π'. split; [exact Hposs'|]. split.
        - eapply offslot_agree_change_σ. exact Hoff.
        - eapply Kσ. exact Hkind. }
      split; apply Hgen; intros σ1 σ2 ρ π H; exact H.
    Qed.

    Lemma lift_valid_rgi t :
      RGISimulationSet.RGISimulation.ValidRGI (R t) (G t) SI t.
    Proof.
      constructor. intros s s' [Hback _] _. split.
      - intros Hnone ρ' π' Hposs'.
        destruct (Hback _ _ Hposs') as (ρ & π & Hposs & HR).
        pose proof (source_R_token t _ _ HR) as Htok.
        unfold token_eq in Htok. simpl in Htok.
        exact (eq_trans (eq_sym Htok) (Hnone _ _ Hposs)).
      - intros Hnone' ρ π Hposs.
        destruct (ac_nonempty (SetPossState.Δ s')) as (ρ' & π' & Hposs').
        destruct (Hback _ _ Hposs') as (ρ0 & π0 & Hposs0 & HR).
        pose proof (source_R_token t _ _ HR) as Htok.
        unfold token_eq in Htok. simpl in Htok.
        pose proof (eq_trans Htok (Hnone' _ _ Hposs')) as Hn0.
        eapply ac_find_none_same; eauto.
    Qed.

    Lemma lift_ginv_twins t1 t2 f σ Δ :
      t1 <> t2 ->
      twins_preserved t2 (mks σ Δ) (mks σ (ac_inv Δ t1 f)).
    Proof.
      intros Hneq. split; intros HK ρ' π' Hposs'; inversion Hposs'; subst;
        destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & [Hσ [Hs Ht]] & Hkind);
        exists ρy, (TMap.add t1 (ls_inv f) πy);
        (split; [constructor; exact Hpossy|]);
        (split; [split; [reflexivity|split; [exact Hs|]]|]).
      - intros r Hr. unfold slot_token. simpl.
        destruct (PositiveMap.E.eq_dec r t1) as [->|Hrt].
        + rewrite !TMap.gss. reflexivity.
        + rewrite !TMap.gso by exact Hrt. apply Ht, Hr.
      - eapply kind_lini_token; [|exact Hkind].
        unfold slot_token. simpl. rewrite TMap.gso by congruence. reflexivity.
      - intros r Hr. unfold slot_token. simpl.
        destruct (PositiveMap.E.eq_dec r t1) as [->|Hrt].
        + rewrite !TMap.gss. reflexivity.
        + rewrite !TMap.gso by exact Hrt. apply Ht, Hr.
      - eapply kind_linr_token; [|exact Hkind].
        unfold slot_token. simpl. rewrite TMap.gso by congruence. reflexivity.
    Qed.

    Lemma lift_gret_twins t1 t2 σ Δ :
      t1 <> t2 ->
      twins_preserved t2 (mks σ Δ) (mks σ (ac_res Δ t1)).
    Proof.
      intros Hneq. split; intros HK ρ' π' Hposs'; inversion Hposs'; subst;
        destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & [Hσ [Hs Ht]] & Hkind);
        exists ρy, (TMap.remove t1 πy);
        (split; [constructor; exact Hpossy|]);
        (split; [split; [reflexivity|split; [exact Hs|]]|]).
      - intros r Hr. unfold slot_token. simpl.
        destruct (PositiveMap.E.eq_dec r t1) as [->|Hrt].
        + rewrite !TMap.grs. reflexivity.
        + rewrite !TMap.gro by exact Hrt. apply Ht, Hr.
      - eapply kind_lini_token; [|exact Hkind].
        unfold slot_token. simpl. rewrite TMap.gro by congruence. reflexivity.
      - intros r Hr. unfold slot_token. simpl.
        destruct (PositiveMap.E.eq_dec r t1) as [->|Hrt].
        + rewrite !TMap.grs. reflexivity.
        + rewrite !TMap.gro by exact Hrt. apply Ht, Hr.
      - eapply kind_linr_token; [|exact Hkind].
        unfold slot_token. simpl. rewrite TMap.gro by congruence. reflexivity.
    Qed.

    Lemma twins_preserved_equiv q s s' s'' :
      SetPossState.σ s' = SetPossState.σ s'' ->
      ac_equiv (SetPossState.Δ s') (SetPossState.Δ s'') ->
      twins_preserved q s s' -> twins_preserved q s s''.
    Proof.
      intros Hσ Heq [H1 H2].
      assert (Hconv : forall K, HasKind K q s' -> HasKind K q s'').
      { intros K HK ρ π Hposs. apply Heq in Hposs.
        destruct (HK _ _ Hposs) as (ρ' & π' & Hposs' & Hoff & Hkind).
        exists ρ', π'. split; [apply Heq, Hposs'|].
        rewrite <- Hσ. split; assumption. }
      split; intros HK; apply Hconv; auto.
    Qed.

    Lemma lift_parallel_compat t1 t2 :
      t1 <> t2 -> forall s s',
        (G t1 s s' \/
         (AssertionsSet.GINV t1 s s' \/ AssertionsSet.GRET t1 s s') \/
         AssertionsSet.A.GId s s') /\ SI s ->
        R t2 s s'.
    Proof.
      intros Hneq s s' [Hrel HI].
      destruct Hrel as [[Hback Htwins] | [[[f Hinv] | [f [ret Hret]]] | Hid]].
      - split.
        + intros ρ' π' Hposs'.
          destruct (Hback _ _ Hposs') as (ρ & π & Hposs & HG).
          exists ρ, π. split; [exact Hposs|].
          apply (source_parallel_compatible t1 t2 Hneq). left. exact HG.
        + apply Htwins. congruence.
      - destruct Hinv as [Hσ [Hnone HΔ]]. split.
        + intros ρ' π' Hposs'. apply HΔ in Hposs'. inversion Hposs'; subst.
          eexists ρ', _. split; [exact Hposs|].
          apply (source_parallel_compatible t1 t2 Hneq).
          right. left. left. exists f.
          unfold AssertionsSingle.Ginv, AssertionsSingle.LiftRelation_π. simpl.
          split; [exact Hσ|]. split; [reflexivity|].
          split; [exact (Hnone _ _ Hposs)|reflexivity].
        + destruct s as [σ Δ], s' as [σ' Δ']. simpl in *. subst σ'.
          eapply twins_preserved_equiv with (s' := mks σ (ac_inv Δ t1 f)).
          * reflexivity.
          * intros ρ π. simpl. symmetry. apply HΔ.
          * apply lift_ginv_twins. exact Hneq.
      - destruct Hret as [Hσ [Hlin HΔ]]. split.
        + intros ρ' π' Hposs'. apply HΔ in Hposs'. inversion Hposs'; subst.
          eexists ρ', _. split; [exact Hposs|].
          apply (source_parallel_compatible t1 t2 Hneq).
          right. left. right. exists f, ret.
          unfold AssertionsSingle.Gret, AssertionsSingle.LiftRelation_π. simpl.
          split; [exact Hσ|]. split; [reflexivity|].
          split; [exact (Hlin _ _ Hposs)|reflexivity].
        + destruct s as [σ Δ], s' as [σ' Δ']. simpl in *. subst σ'.
          eapply twins_preserved_equiv with (s' := mks σ (ac_res Δ t1)).
          * reflexivity.
          * intros ρ π. simpl. symmetry. apply HΔ.
          * apply lift_gret_twins. exact Hneq.
      - unfold AssertionsSet.A.GId in Hid. subst s'. split.
        + intros ρ π Hposs. exists ρ, π. split; [exact Hposs|].
          apply (source_parallel_compatible t1 t2 Hneq).
          right. right. reflexivity.
        + destruct s as [σ Δ]. apply twins_preserved_refl.
    Qed.

    Lemma lift_ginv_compose t f (I P : assertion) :
      (forall x, AssertionsSingle.A.ComposeA I (AssertionsSingle.Ginv t f) x ->
        P x) ->
      forall s, AssertionsSet.A.ComposeA (lift_assert I)
        (AssertionsSet.Ginv t f) s -> lift_assert P s.
    Proof.
      intros Himpl s [s0 [HI [Hσ [Hnone HΔ]]]] ρ' π' Hposs'.
      apply HΔ in Hposs'. inversion Hposs'; subst.
      apply Himpl. eexists (mk (SetPossState.σ s0) ρ' _). split.
      - eapply HI. exact Hposs.
      - unfold AssertionsSingle.Ginv, AssertionsSingle.LiftRelation_π. simpl.
        split; [exact Hσ|]. split; [reflexivity|].
        split; [exact (Hnone _ _ Hposs)|reflexivity].
    Qed.

    Lemma lift_gret_compose t f ret (Q I : assertion) :
      (forall x, AssertionsSingle.A.ComposeA Q (AssertionsSingle.Gret t f ret) x ->
        I x) ->
      forall s, AssertionsSet.A.ComposeA (lift_assert Q)
        (AssertionsSet.Gret t f ret) s -> lift_assert I s.
    Proof.
      intros Himpl s [s0 [HQ [Hσ [Hlin HΔ]]]] ρ' π' Hposs'.
      apply HΔ in Hposs'. inversion Hposs'; subst.
      apply Himpl. eexists (mk (SetPossState.σ s0) ρ' _). split.
      - eapply HQ. exact Hposs.
      - unfold AssertionsSingle.Gret, AssertionsSingle.LiftRelation_π. simpl.
        split; [exact Hσ|]. split; [reflexivity|].
        split; [exact (Hlin _ _ Hposs)|reflexivity].
    Qed.

    (** *** Transfer of facts between twins *)

    Lemma offslot_control_agree q x y :
      source_I x -> source_I y -> offslot_agree q x y ->
      control_agree q (SinglePossState.ρ x) (SinglePossState.ρ y).
    Proof.
      intros HIx HIy [Hσ [Hs Ht]].
      pose proof (source_I_payload_determined _ _ HIx HIy Hσ) as (Hc & Hn & Ho).
      rewrite (source_I_ready _ HIx), (source_I_ready _ HIy). simpl.
      repeat split; auto.
    Qed.

    Lemma control_agree_ready q c s' :
      control_agree q c (Ready s') ->
      exists s, c = Ready s /\ payload_agree q s s'.
    Proof.
      destruct c as [s | s t op]; simpl; [eauto | contradiction].
    Qed.

    Lemma control_agree_ready' q s c' :
      control_agree q (Ready s) c' ->
      exists s', c' = Ready s' /\ payload_agree q s s'.
    Proof.
      destruct c' as [s' | s' t op]; simpl; [eauto | contradiction].
    Qed.

    Lemma control_agree_snapshot q c c' :
      control_agree q c c' ->
      forall r, r <> q ->
        TMap.find r (snapshot (abstract_payload c)) =
        TMap.find r (snapshot (abstract_payload c')).
    Proof.
      destruct c as [s | s t op], c' as [s' | s' t' op']; simpl;
        try contradiction.
      - intros (_ & _ & _ & Hs). exact Hs.
      - intros (_ & _ & (_ & _ & _ & Hs)). exact Hs.
    Qed.

    Lemma represents_payload_agree q h top count s s' :
      payload_agree q s s' -> represents h top count s ->
      represents h top count s'.
    Proof.
      intros (Hc & Hn & Ho & _) (chain & Hsp & Hcount & Hlen & Hnodes & Horder).
      exists chain. split; [exact Hsp|]. repeat split; congruence.
    Qed.

    (** A replayed twin satisfies the invariant: its payload agrees with
        the original image off [q], and its [q] slot is the twin's. *)
    Lemma source_I_transfer q x' y y' :
      source_I x' -> source_I y ->
      SinglePossState.σ y' = SinglePossState.σ x' ->
      control_agree q (SinglePossState.ρ x') (SinglePossState.ρ y') ->
      (forall r, r <> q -> slot_token r x' = slot_token r y') ->
      control_snapshot q (SinglePossState.ρ y') = slot_snapshot q y ->
      slot_token q y' = slot_token q y ->
      source_I y'.
    Proof.
      intros HIx' HIy Hσ Hagree Htok Hsnap Hq.
      destruct HIx' as (mc & cc & sx & Eσ & Eρ & Hmc & Hcc & Hrep & Hcons).
      destruct HIy as (mcy & ccy & sy & Eσy & Eρy & _ & _ & _ & Hconsy).
      rewrite Eρ in Hagree.
      destruct (control_agree_ready' _ _ _ Hagree) as (sy' & Eρ' & Hpay).
      exists mc, cc, sy'. split; [exact (eq_trans Hσ Eσ)|]. split; [exact Eρ'|].
      split; [exact Hmc|]. split; [exact Hcc|]. split.
      - eapply represents_payload_agree; eauto.
      - intros r. destruct (PositiveMap.E.eq_dec r q) as [->|Hrq].
        + unfold control_snapshot, slot_snapshot, payload_of in Hsnap.
          rewrite Eρ', Eρy in Hsnap. simpl in Hsnap.
          unfold slot_token in Hq.
          rewrite Hsnap, Hq. apply Hconsy.
        + destruct Hpay as (_ & _ & _ & Hs).
          rewrite <- (Hs r Hrq). unfold slot_token in Htok.
          rewrite <- (Htok r Hrq). apply Hcons.
    Qed.

    Lemma source_G_transfer t q x x' y y' :
      q <> t ->
      source_G t x x' ->
      source_I y -> source_I y' ->
      offslot_agree q x y ->
      SinglePossState.σ y' = SinglePossState.σ x' ->
      control_agree q (SinglePossState.ρ x') (SinglePossState.ρ y') ->
      (forall r, r <> q -> slot_token r x' = slot_token r y') ->
      control_snapshot q (SinglePossState.ρ y') = slot_snapshot q y ->
      slot_token q y' = slot_token q y ->
      source_G t y y'.
    Proof.
      intros Hqt HG HIy HIy' [Hσxy [Hsxy Htxy]] Hσ Hagree Htok Hsnap Hq.
      destruct HG as (HIx & HIx' & Hheap & Hpriv & Hcas & Hsnaps & Htoks).
      pose proof (source_I_payload_determined _ _ HIx HIy Hσxy)
        as (_ & Hnodes & _).
      pose proof (control_agree_snapshot _ _ _ Hagree) as Hs'.
      split; [exact HIy|]. split; [exact HIy'|].
      rewrite <- Hσxy, Hσ. split; [exact Hheap|].
      split.
      { intros l Hactor Hundef. apply Hpriv; [exact Hactor|].
        unfold payload_of in Hnodes. rewrite Hnodes. exact Hundef. }
      split; [exact Hcas|].
      split.
      - intros r Hr. destruct (PositiveMap.E.eq_dec r q) as [->|Hrq].
        + unfold control_snapshot, slot_snapshot, payload_of in Hsnap.
          symmetry. exact Hsnap.
        + unfold slot_snapshot, payload_of in Hsxy.
          rewrite <- (Hsxy r Hrq), <- (Hs' r Hrq). apply Hsnaps. exact Hr.
      - intros r Hr. destruct (PositiveMap.E.eq_dec r q) as [->|Hrq].
        + unfold slot_token in Hq. symmetry. exact Hq.
        + unfold slot_token in Htxy, Htok.
          rewrite <- (Htxy r Hrq), <- (Htok r Hrq). apply Htoks. exact Hr.
    Qed.

    Lemma map_domain_equiv_of_tokens q (π1 π2 π1' π2' : tmap (@LinState (li_sig F))) :
      domain_equiv (map_domain π1) (map_domain π2) ->
      (forall r, r <> q -> TMap.find r π1' = TMap.find r π2') ->
      TMap.find q π1' = TMap.find q π1 ->
      TMap.find q π2' = TMap.find q π2 ->
      domain_equiv (map_domain π1') (map_domain π2').
    Proof.
      intros Hdom Hoff H1 H2 r. unfold map_domain.
      destruct (PositiveMap.E.eq_dec r q) as [->|Hrq].
      - rewrite H1, H2. apply Hdom.
      - rewrite (Hoff r Hrq). reflexivity.
    Qed.

    (** *** Lifting a pointwise update

        The image of a possibility set under a thread's update.  Only
        images with the domain [D] are kept, which is what makes the result
        a well-formed configuration.  [D] is chosen as the domain of one
        witness image; every image has that domain anyway because the
        postcondition fixes the acting thread's slot. *)
    Definition image_prop (Δ : @AbstractConfig (li_sig F) (li_lts F))
        (σ σ' : concrete_state) (Q : assertion) (Gs : rg_relation)
        (D : ThreadDomain) : @AbstractConfigProp (li_sig F) (li_lts F) :=
      fun ρ' π' => exists ρ π, Δ ρ π /\
        @poss_steps _ (li_lts F) (PossOk ρ π) (PossOk ρ' π') /\
        Q (mk σ' ρ' π') /\ Gs (mk σ ρ π) (mk σ' ρ' π') /\
        domain_equiv (map_domain π') D.

    Definition image_config Δ σ σ' Q Gs D
        (Hne : exists ρ' π', image_prop Δ σ σ' Q Gs D ρ' π') :
        @AbstractConfig (li_sig F) (li_lts F) :=
      {| ac_active := D;
         ac_prop := image_prop Δ σ σ' Q Gs D;
         ac_nonempty := Hne;
         ac_domain := fun ρ' π' H =>
           match H with
           | ex_intro _ ρ (ex_intro _ π (conj _ (conj _ (conj _ (conj _ Hdom))))) =>
               Hdom
           end |}.

    Lemma lift_pupdate t ev (P Q : assertion) :
      (forall x, P x -> source_I x) ->
      (forall x, Q x -> source_I x) ->
      slot_local t Q ->
      AssertionsSingle.PUpdate (source_G t) ev P Q ->
      AssertionsSet.PUpdate (G t) ev (lift_assert P) (lift_assert Q).
    Proof.
      intros HPI HQI Hloc Hupd σ Δ HP σ' Hstep.
      destruct (ac_nonempty Δ) as (ρ0 & π0 & Hposs0).
      destruct (Hupd σ ρ0 π0 (HP _ _ Hposs0) σ' Hstep)
        as (ρ0' & π0' & Hsteps0 & HQ0 & HG0).
      assert (Hne : exists ρ' π',
        image_prop Δ σ σ' Q (source_G t) (map_domain π0') ρ' π').
      { exists ρ0', π0', ρ0, π0.
        split; [exact Hposs0|]. split; [exact Hsteps0|].
        split; [exact HQ0|]. split; [exact HG0|]. apply domain_equiv_refl. }
      exists (image_config Δ σ σ' Q (source_G t) (map_domain π0') Hne).
      split; [|split].
      - intros ρ' π' (ρ & π & Hposs & Hsteps & _). econstructor; eauto.
      - intros ρ' π' (ρ & π & _ & _ & HQ & _). exact HQ.
      - split.
        + intros ρ' π' (ρ & π & Hposs & _ & _ & HG & _).
          exists ρ, π. split; assumption.
        + intros q Hq.
          assert (Hgen : forall K : tid -> single_state -> Prop,
            (forall x y, slot_token q x = slot_token q y -> K q x -> K q y) ->
            HasKind K q (mks σ Δ) ->
            HasKind K q (mks σ'
              (image_config Δ σ σ' Q (source_G t) (map_domain π0') Hne))).
          { intros K Ktok HK ρ' π' (ρ & π & Hposs & Hsteps & HQ' & HG & Hdom).
            destruct (HK ρ π Hposs) as (ρy & πy & Hpossy & Hoff & Hkind).
            pose proof (HPI _ (HP _ _ Hposs)) as HIx.
            pose proof (HPI _ (HP _ _ Hpossy)) as HIy.
            pose proof HG as (_ & _ & _ & _ & _ & _ & Htoks).
            simpl in Htoks.
            pose proof (offslot_control_agree q _ _ HIx HIy Hoff) as Hagree.
            simpl in Hagree.
            pose proof Hoff as [_ [Hsxy Htxy]].
            destruct (poss_steps_replay q ρ π ρ' π' ρy πy Hsteps
              (eq_sym (Htoks q Hq)) Hagree Htxy)
              as (ρy' & πy' & Hstepsy & Hagree' & Hsnap' & Htok' & Hqy).
            assert (HIy' : source_I (mk σ' ρy' πy')).
            { apply (source_I_transfer q (mk σ' ρ' π') (mk σ ρy πy)
                (mk σ' ρy' πy')).
              - exact (HQI _ HQ').
              - exact HIy.
              - reflexivity.
              - exact Hagree'.
              - intros r Hr. exact (Htok' r Hr).
              - exact Hsnap'.
              - exact Hqy. }
            assert (Htq : t <> q) by (intros Heq; apply Hq; symmetry; exact Heq).
            assert (HQy' : Q (mk σ' ρy' πy')).
            { eapply Hloc; [exact HQ' | exact HIy' |].
              split; [reflexivity|]. split.
              - unfold slot_snapshot, payload_of. simpl.
                apply (control_agree_snapshot _ _ _ Hagree' t Htq).
              - exact (Htok' t Htq). }
            assert (HGy : source_G t (mk σ ρy πy) (mk σ' ρy' πy')).
            { apply (source_G_transfer t q (mk σ ρ π) (mk σ' ρ' π')
                (mk σ ρy πy) (mk σ' ρy' πy')).
              - exact Hq.
              - exact HG.
              - exact HIy.
              - exact HIy'.
              - exact Hoff.
              - reflexivity.
              - exact Hagree'.
              - intros r Hr. exact (Htok' r Hr).
              - exact Hsnap'.
              - exact Hqy. }
            exists ρy', πy'. split; [|split].
            - exists ρy, πy. split; [exact Hpossy|]. split; [exact Hstepsy|].
              split; [exact HQy'|]. split; [exact HGy|].
              eapply domain_equiv_trans; [|exact Hdom].
              apply (map_domain_equiv_of_tokens q πy π πy' π').
              + eapply domain_equiv_trans; [eapply ac_domain; exact Hpossy|].
                apply domain_equiv_symm. eapply ac_domain; exact Hposs.
              + intros r Hr. symmetry. apply Htok', Hr.
              + exact Hqy.
              + symmetry. exact (Htoks q Hq).
            - split; [reflexivity|]. split.
              + intros r Hr. unfold slot_snapshot, payload_of. simpl.
                apply (control_agree_snapshot _ _ _ Hagree' r Hr).
              + intros r Hr. exact (Htok' r Hr).
            - eapply Ktok; [|exact Hkind]. exact (eq_sym Hqy). }
          split.
          * intros HK. exact (Hgen kind_lini (kind_lini_token q) HK).
          * intros HK. exact (Hgen kind_linr (kind_linr_token q) HK).
    Qed.

    (** A concrete step that changes no possibility. *)
    Lemma lift_pupdate_pure t ev (P Q : assertion) :
      (forall x, P x -> forall σ',
        Step (li_lts E) ev (SinglePossState.σ x) σ' ->
        Q (mk σ' (SinglePossState.ρ x) (SinglePossState.π x)) /\
        source_G t x (mk σ' (SinglePossState.ρ x) (SinglePossState.π x))) ->
      AssertionsSet.PUpdate (G t) ev (lift_assert P) (lift_assert Q).
    Proof.
      intros Hupd σ Δ HP σ' Hstep. exists Δ. split; [apply ac_steps_refl|].
      split.
      - intros ρ π Hposs. exact (proj1 (Hupd _ (HP _ _ Hposs) _ Hstep)).
      - split.
        + intros ρ π Hposs. exists ρ, π. split; [exact Hposs|].
          exact (proj2 (Hupd _ (HP _ _ Hposs) _ Hstep)).
        + intros q _. apply twins_preserved_refl.
    Qed.

    (** *** Program rules with pointwise leaf obligations *)

    Lemma singleton_provable_vis_safe {X} t
        (P : assertion) (Q : X -> assertion)
        (m : Sig.op (li_sig E)) (k : Sig.ar m -> Prog (li_sig E) X)
        (P' : assertion) (Q' : Sig.ar m -> assertion) :
      (⊨ P ==>> AssertionsSingle.A.ANoError (Build_ThreadEvent t (InvEv m))) ->
      (⊨ P' ==>> source_I) ->
      (forall a, ⊨ Q' a ==>> source_I) ->
      AssertionsSingle.A.Stable (source_R t) source_I P' ->
      (forall a, AssertionsSingle.A.Stable (source_R t) source_I (Q' a)) ->
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (InvEv m)) P P' ->
      (forall ret, AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (ResEv m ret)) P' (Q' ret)) ->
      (forall ret,
        [li_lts E, li_lts F, R t, G t, SI, t] ⊢
          {{ lift_assert (Q' ret) }} k ret {{ fun a => lift_assert (Q a) }}) ->
      (⊨ P ==>> source_I) ->
      slot_local t P' ->
      (forall a, slot_local t (Q' a)) ->
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ lift_assert P }} Vis m k {{ fun a => lift_assert (Q a) }}.
    Proof.
      intros Herror HinvP HinvQ HstableP HstableQ Hpinv Hpret Hnext HPI
        HlocP HlocQ.
      eapply SetLogic.provable_vis_safe with
        (P' := lift_assert P') (Q' := fun a => lift_assert (Q' a)).
      - intros s HP. eapply lift_no_error; [exact Herror|exact HP].
      - intros s HP. eapply lift_impl; [exact HinvP|exact HP].
      - intros a s HQ. eapply lift_impl; [exact (HinvQ a)|exact HQ].
      - apply lift_stable; exact HstableP.
      - intros a. apply lift_stable; exact (HstableQ a).
      - apply lift_pupdate.
        + exact HPI.
        + exact HinvP.
        + exact HlocP.
        + exact Hpinv.
      - intros ret. apply lift_pupdate.
        + exact HinvP.
        + exact (HinvQ ret).
        + exact (HlocQ ret).
        + exact (Hpret ret).
      - exact Hnext.
    Qed.

    Lemma singleton_provable_ret_safe {X} t (a : X)
        (P : assertion) (Q : X -> assertion) :
      (⊨ P ==>> Q a) ->
      (⊨ Q a ==>> source_I) ->
      AssertionsSingle.A.Stable (source_R t) source_I (Q a) ->
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ lift_assert P }} Ret a {{ fun r => lift_assert (Q r) }}.
    Proof.
      intros HP Hinv Hstable.
      eapply SetLogic.provable_ret_safe.
      - intros s Hpre. eapply lift_impl; [exact HP|exact Hpre].
      - intros s Hpost. eapply lift_impl; [exact Hinv|exact Hpost].
      - apply lift_stable; exact Hstable.
    Qed.

    Ltac singleton_ret_safe := eapply singleton_provable_ret_safe.

    Lemma valid_rg observer :
      RGISimulationSet.RGISimulation.ValidRGI
        (R observer) (G observer) SI observer.
    Proof. apply lift_valid_rgi. Qed.

    Lemma parallel_compatible actor observer :
      actor <> observer -> forall w w',
      (G actor w w' \/
       (AssertionsSet.GINV actor w w' \/ AssertionsSet.GRET actor w w') \/
       AssertionsSet.A.GId w w') /\ SI w ->
      R observer w w'.
    Proof. apply lift_parallel_compat. Qed.

    Definition Active (t : tid) (m : Sig.op (li_sig F)) : assertion :=
      source_I //\\ ALin t (ls_inv m).

    Definition Completed (t : tid) (m : Sig.op (li_sig F))
        (ret : Sig.ar m) : assertion :=
      source_I //\\ ALin t (ls_linr m ret).

    Definition SActive t m := lift_assert (Active t m).
    Definition SCompleted t m ret := lift_assert (Completed t m ret).

    Definition ActiveOwned (t : tid) (m : Sig.op (li_sig F)) : assertion :=
      fun w => Active t m w /\ t = owner.

    Definition SActiveOwned t m := lift_assert (ActiveOwned t m).

    Definition InsertRead (t : tid) (v : A) (q : Ptr * nat) : assertion :=
      ActiveOwned t (linsert v) //\\ CASIs q.

    Definition InsertAllocated (t : tid) (v : A) (q : Ptr * nat)
        (l : Addr) : assertion :=
      fun w => InsertRead t v q w /\ NodeUndefined l w /\
        mem_heap (fst (SinglePossState.σ w)) l =
          Some (pair (pair (pair v TSTop) false) (fst q)).

    Definition GetTopScan (t : tid) (count : nat) (p : Ptr) : assertion :=
      fun w =>
        source_I w /\ ALin t (ls_lini (@lgetTop A)) w /\
        exists saved chain suffix prefix,
          linked (mem_heap (fst (SinglePossState.σ w)))
            (fst (cas_value (snd (SinglePossState.σ w)))) chain /\
          TMap.find t
            (snapshot (abstract_payload (SinglePossState.ρ w))) =
            Some (pair saved count) /\
          linked (mem_heap (fst (SinglePossState.σ w))) p suffix /\
          chain = prefix ++ suffix /\
          List.Forall (fun l => In l chain) saved /\
          List.filter
            (live_at (mem_heap (fst (SinglePossState.σ w)))) saved =
          live_order (mem_heap (fst (SinglePossState.σ w))) suffix.

    Definition SGetTopScan t count p := lift_assert (GetTopScan t count p).

    Definition GetTopLoop (t : tid) (count : nat) (p : Ptr) : assertion :=
      match p with
      | None => Completed t (@lgetTop A) (@inr (@LNode A) nat count)
      | Some _ => GetTopScan t count p
      end.

    Definition SGetTopLoop t count p := lift_assert (GetTopLoop t count p).

    Definition GetTopReadPost (t : tid) (count : nat) (l : Addr)
        (node : @Node A) : assertion :=
      let 'pair (pair (pair v ts) taken) next := node in
      if taken then GetTopLoop t count next
      else Completed t (@lgetTop A)
        (@inl (@LNode A) nat (pair (pair v ts) l)).

    Definition GetTopBodyPost (t : tid) (count : nat)
        (r : Ptr + (@LNode A + nat)) : assertion :=
      match r with
      | inl p => GetTopLoop t count p
      | inr ret => Completed t (@lgetTop A) ret
      end.

    Lemma active_entails_I t m :
      ⊨ Active t m ==>> source_I.
    Proof. apply ConjLeftImpl. apply ImplRefl. Qed.

    Lemma completed_entails_I t m ret :
      ⊨ Completed t m ret ==>> source_I.
    Proof. apply ConjLeftImpl. apply ImplRefl. Qed.

    Lemma active_stable t m :
      AssertionsSingle.A.Stable (source_R t) source_I (Active t m).
    Proof.
      unfold AssertionsSingle.A.Stable, Active.
      intros out [[pre [[HIpre Hlin] HR]] HIout].
      split; [exact HIout|].
      unfold ALin in *. rewrite <- (source_R_token t _ _ HR).
      exact Hlin.
    Qed.

    Lemma completed_stable t m ret :
      AssertionsSingle.A.Stable (source_R t) source_I
        (Completed t m ret).
    Proof.
      unfold AssertionsSingle.A.Stable, Completed.
      intros out [[pre [[HIpre Hlin] HR]] HIout].
      split; [exact HIout|].
      unfold ALin in *. rewrite <- (source_R_token t _ _ HR).
      exact Hlin.
    Qed.

    Lemma active_owned_entails_I t m :
      ⊨ ActiveOwned t m ==>> source_I.
    Proof. intros w [Hactive Howner]. now apply active_entails_I in Hactive. Qed.

    Lemma active_owned_stable t m :
      AssertionsSingle.A.Stable (source_R t) source_I (ActiveOwned t m).
    Proof.
      unfold AssertionsSingle.A.Stable, ActiveOwned.
      intros out [[pre [[Hactive Howner] HR]] HIout].
      split; [|exact Howner].
      eapply active_stable. split; [exists pre; eauto|exact HIout].
    Qed.

    Lemma insert_read_entails_I t v q :
      ⊨ InsertRead t v q ==>> source_I.
    Proof. intros w [Howned Hcas]. eapply active_owned_entails_I; eauto. Qed.

    Lemma insert_read_stable t v q :
      AssertionsSingle.A.Stable (source_R t) source_I (InsertRead t v q).
    Proof.
      unfold AssertionsSingle.A.Stable, InsertRead.
      intros out [[pre [[Howned Hcas] HR]] HIout].
      assert (Howner : t = owner) by exact (proj2 Howned).
      split.
      - eapply active_owned_stable. split; [exists pre; eauto|exact HIout].
      - unfold CASIs in *. subst t.
        rewrite <- (source_R_owner_preserves_cas _ _ HR). exact Hcas.
    Qed.

    Lemma insert_allocated_entails_I t v q l :
      ⊨ InsertAllocated t v q l ==>> source_I.
    Proof.
      intros w [Hread [Hundefined Hcell]].
      apply insert_read_entails_I in Hread. exact Hread.
    Qed.

    Lemma insert_allocated_stable t v q l :
      AssertionsSingle.A.Stable (source_R t) source_I
        (InsertAllocated t v q l).
    Proof.
      unfold AssertionsSingle.A.Stable, InsertAllocated.
      intros out [[pre [[Hread [Hundefined Hcell]] HR]] HIout].
      assert (Howner : t = owner) by exact (proj2 (proj1 Hread)).
      split.
      - eapply insert_read_stable. split; [exists pre; eauto|exact HIout].
      - split.
        + subst t. eapply source_R_owner_preserves_undefined; eauto.
        + subst t. unfold NodeUndefined in Hundefined.
        rewrite <- (source_R_owner_preserves_private _ _ l HR Hundefined).
        exact Hcell.
    Qed.

    Lemma getTop_scan_entails_I t count p :
      ⊨ GetTopScan t count p ==>> source_I.
    Proof. intros w [HI Hrest]. exact HI. Qed.

    Lemma getTop_scan_stable t count p :
      AssertionsSingle.A.Stable (source_R t) source_I
        (GetTopScan t count p).
    Proof.
      unfold AssertionsSingle.A.Stable.
      intros out [[pre [Hscan HR]] HIout].
      destruct Hscan as [HIpre [Hlin Hdata]].
      destruct Hdata as
        (saved & chain & suffix & prefix & Hfull & Hsaved & Hsuffix &
         Hchain & Hforall & Hfilter).
      split; [exact HIout|]. split.
      - pose proof (source_R_token t _ _ HR) as Htoken.
        unfold ALin in Hlin |- *.
        etransitivity; [symmetry; exact Htoken|exact Hlin].
      - destruct HR as [[actor [Hactor HG]]|Hadmin].
        + destruct HG as
            [HGI [HGI' [Hheap [Hprivate [Hcas [Hsnap Htokens]]]]]].
          pose proof HIpre as HIpre0. pose proof HIout as HIout0.
          destruct HIpre as
            (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hconsistent).
          destruct HIout as
            (mc' & cc' & s' & Eσ' & Eρ' & Hmc' & Hcc' & Hrep' &
             Hconsistent').
          destruct Hrep as
            (repchain & Hrepspatial & Hcount & Hlength & Hnodes & Horder).
          destruct Hrep' as
            (newchain & Hnewspatial & Hcount' & Hlength' & Hnodes' & Horder').
          pose proof (HLinked_implies_linked _ _ _ Hrepspatial)
            as Hreplinked.
          pose proof (HLinked_implies_linked _ _ _ Hnewspatial)
            as Hnewlinked.
          rewrite Eσ in Hfull, Hsuffix, Hfilter.
          rewrite Eρ in Hsaved.
          simpl in Hfull, Hsaved, Hsuffix, Hforall, Hfilter.
          rewrite Eσ, Eσ' in Hheap, Hcas; simpl in Hheap, Hcas.
          assert (Erepchain : repchain = chain).
          { eapply linked_deterministic; eauto. }
          subst repchain.
          assert (Hsuffix' : linked (mem_heap mc') p suffix).
          { eapply heap_evol_linked; eauto. }
          assert (Hextension : exists extra, newchain = extra ++ chain).
          { unfold cas_evol in Hcas.
            destruct (PositiveMap.E.eq_dec actor owner) as [Heq|Hneq].
            - destruct Hcas as
                (oldc & newc & extra & Hold & Hnew & Happend).
              assert (Eold : oldc = chain) by
                (eapply linked_deterministic; eauto).
              assert (Enew : newc = newchain) by
                (eapply linked_deterministic; eauto).
              subst oldc newc. eauto.
            - assert (Hpreserved : linked (mem_heap mc')
                (fst (cas_value cc)) chain).
              { eapply heap_evol_linked; eauto. }
              rewrite <- Hcas in Hpreserved.
              assert (Enew : newchain = chain) by
                (eapply linked_deterministic; eauto).
              exists nil. simpl. exact Enew. }
          destruct Hextension as [extra Hextension].
          assert (Hsnap_t : TMap.find t (snapshot s) =
              TMap.find t (snapshot s')).
          { pose proof (Hsnap t ltac:(congruence)) as Hsnap_t.
            rewrite Eρ, Eρ' in Hsnap_t. simpl in Hsnap_t. exact Hsnap_t. }
          exists saved, newchain, suffix, (extra ++ prefix).
          repeat split.
          * rewrite Eσ'. simpl. exact Hnewlinked.
          * rewrite Eρ'. simpl.
            rewrite <- Hsnap_t. exact Hsaved.
          * rewrite Eσ'. simpl. exact Hsuffix'.
          * rewrite Hextension, Hchain, app_assoc. reflexivity.
          * eapply List.Forall_impl; [|exact Hforall].
            intros l Hin. rewrite Hextension. apply in_or_app. right. exact Hin.
          * rewrite Eσ'. simpl.
            assert (Hstrength :
              List.filter (live_at (mem_heap mc')) saved =
              List.filter (live_at (mem_heap mc'))
                (List.filter (live_at (mem_heap mc)) saved)).
            { apply filter_strengthen. intros l Hin Hnewlive.
              apply List.Forall_forall with (x := l) in Hforall; [|exact Hin].
              eapply (heap_evol_live_imp actor (mem_heap mc) (mem_heap mc')
                (fst (cas_value cc)) chain l); eauto. }
            rewrite Hstrength, Hfilter.
            symmetry. eapply live_order_heap_evol; eauto.
        + pose proof
            (AssertionsSingle.linearization_rely_observer_view t _ _ Hadmin)
            as [Hσ [Hρ Htoken]].
          exists saved, chain, suffix, prefix. repeat split.
          * rewrite <- Hσ. exact Hfull.
          * rewrite <- Hρ. exact Hsaved.
          * rewrite <- Hσ. exact Hsuffix.
          * exact Hchain.
          * exact Hforall.
          * rewrite <- Hσ. exact Hfilter.
    Qed.

    Lemma getTop_loop_entails_I t count p :
      ⊨ GetTopLoop t count p ==>> source_I.
    Proof.
      destruct p; simpl.
      - apply getTop_scan_entails_I.
      - apply completed_entails_I.
    Qed.

    Lemma getTop_loop_stable t count p :
      AssertionsSingle.A.Stable (source_R t) source_I
        (GetTopLoop t count p).
    Proof.
      destruct p; simpl.
      - apply getTop_scan_stable.
      - apply completed_stable.
    Qed.

    Lemma actual_snapshot_from_scan_data t (s : @SPListState A)
        (h : @Heap (@Node A)) top (chain saved : list Addr) count
        (suffix : list Addr) :
      linked h top chain ->
      order s = live_order h chain ->
      TMap.find t (snapshot s) = Some (pair saved count) ->
      List.Forall (fun l => In l chain) saved ->
      List.filter (live_at h) saved = live_order h suffix ->
      actual_snapshot t s = Some (pair (live_order h suffix) count).
    Proof.
      intros Hlinked Horder Hsaved Hforall Hfilter.
      assert (Hmembers :
        List.filter
          (fun l => List.existsb (Nat.eqb l) (live_order h chain)) saved =
        List.filter (live_at h) saved).
      { apply filter_order_membership.
        - eapply linked_nodup; exact Hlinked.
        - exact Hforall. }
      unfold actual_snapshot. rewrite Hsaved, Horder, Hmembers, Hfilter.
      reflexivity.
    Qed.

    Definition ActiveDefined (t : tid) (m : Sig.op (li_sig F))
        (l : Addr) : assertion := Active t m //\\ NodeDefined l.

    Definition SActiveDefined t m l := lift_assert (ActiveDefined t m l).

    Lemma active_defined_entails_I t m l :
      ⊨ ActiveDefined t m l ==>> source_I.
    Proof. apply ConjLeftImpl, active_entails_I. Qed.

    Lemma active_defined_stable t m l :
      AssertionsSingle.A.Stable (source_R t) source_I
        (ActiveDefined t m l).
    Proof.
      unfold AssertionsSingle.A.Stable, ActiveDefined.
      intros out [[pre [[[HIpre Hlin] Hdefined] HR]] HIout].
      split.
      - split; [exact HIout|].
        unfold ALin in *. rewrite <- (source_R_token t _ _ HR). exact Hlin.
      - eapply source_R_preserves_defined; eauto.
    Qed.

    Definition ActiveOwnedDefined (t : tid) (m : Sig.op (li_sig F))
        (l : Addr) : assertion :=
      fun w => ActiveDefined t m l w /\ t = owner.

    Definition SActiveOwnedDefined t m l :=
      lift_assert (ActiveOwnedDefined t m l).

    Lemma active_owned_defined_entails_I t m l :
      ⊨ ActiveOwnedDefined t m l ==>> source_I.
    Proof. intros w [H _]. apply active_defined_entails_I in H. exact H. Qed.

    Lemma active_owned_defined_stable t m l :
      AssertionsSingle.A.Stable (source_R t) source_I
        (ActiveOwnedDefined t m l).
    Proof.
      unfold AssertionsSingle.A.Stable, ActiveOwnedDefined.
      intros out [[pre [[Hactive Howner] HR]] HIout].
      destruct Hactive as [[HIpre Hlin] Hdefined].
      split; [|exact Howner]. split.
      - split; [exact HIout|].
        unfold ALin in *. rewrite <- (source_R_token t _ _ HR). exact Hlin.
      - eapply source_R_preserves_defined; eauto.
    Qed.


    (** *** Slot locality of the method assertions *)

    Lemma slot_local_conj q (P Q : assertion) :
      slot_local q P -> slot_local q Q -> slot_local q (P //\\ Q).
    Proof.
      intros HP HQ x y [Hx1 Hx2] HI Hag. split; [eapply HP|eapply HQ]; eauto.
    Qed.

    Lemma slot_local_source_I q : slot_local q source_I.
    Proof. intros x y _ HI _. exact HI. Qed.

    Lemma slot_local_ALin q ls : slot_local q (ALin q ls).
    Proof.
      intros x y Hx HI [_ [_ Ht]]. unfold ALin in *. unfold slot_token in Ht.
      rewrite <- Ht. exact Hx.
    Qed.

    Lemma slot_local_active t m : slot_local t (Active t m).
    Proof.
      unfold Active. apply slot_local_conj;
        [apply slot_local_source_I | apply slot_local_ALin].
    Qed.

    Lemma slot_local_completed t m ret : slot_local t (Completed t m ret).
    Proof.
      unfold Completed. apply slot_local_conj;
        [apply slot_local_source_I | apply slot_local_ALin].
    Qed.

    Lemma slot_local_active_owned t m : slot_local t (ActiveOwned t m).
    Proof.
      intros x y [Hx Ho] HI Hag. split; [|exact Ho].
      eapply slot_local_active; eauto.
    Qed.

    Lemma slot_agree_nodes q x y :
      source_I x -> source_I y -> slot_agree q x y ->
      nodes (payload_of x) = nodes (payload_of y).
    Proof.
      intros HIx HIy [Hσ _].
      exact (proj1 (proj2 (source_I_payload_determined _ _ HIx HIy Hσ))).
    Qed.

    Lemma slot_local_active_defined t m l :
      slot_local t (ActiveDefined t m l).
    Proof.
      intros x y [Hact [a Hnode]] HI Hag.
      pose proof (proj1 Hact) as HIx.
      split; [eapply slot_local_active; eauto|].
      exists a. pose proof (slot_agree_nodes t x y HIx HI Hag) as Hn.
      unfold payload_of in Hn. rewrite <- Hn. exact Hnode.
    Qed.

    Lemma slot_local_active_owned_defined t m l :
      slot_local t (ActiveOwnedDefined t m l).
    Proof.
      intros x y [Hact Ho] HI Hag. split; [|exact Ho].
      eapply slot_local_active_defined; eauto.
    Qed.

    Lemma slot_local_cas_is q p : slot_local q (CASIs p).
    Proof.
      intros x y Hx _ [Hσ _]. unfold CASIs in *. rewrite <- Hσ. exact Hx.
    Qed.

    Lemma slot_local_insert_read t v p : slot_local t (InsertRead t v p).
    Proof.
      unfold InsertRead. apply slot_local_conj;
        [apply slot_local_active_owned | apply slot_local_cas_is].
    Qed.

    Lemma slot_local_insert_allocated t v p l :
      slot_local t (InsertAllocated t v p l).
    Proof.
      intros x y [Hread [Hundef Hcell]] HI Hag.
      pose proof (proj1 (proj1 (proj1 Hread))) as HIx.
      pose proof Hag as [Hσ _].
      split; [eapply slot_local_insert_read; eauto|].
      split.
      - unfold NodeUndefined in *.
        pose proof (slot_agree_nodes t x y HIx HI Hag) as Hn.
        unfold payload_of in Hn. rewrite <- Hn. exact Hundef.
      - rewrite <- Hσ. exact Hcell.
    Qed.

    Lemma slot_local_getTop_scan t count p :
      slot_local t (GetTopScan t count p).
    Proof.
      intros x y [HI [Hlin Hdata]] HIy Hag.
      pose proof Hag as [Hσ [Hs Ht]].
      destruct Hdata as
        (saved & chain & suffix & prefix & H1 & H2 & H3 & H4 & H5 & H6).
      split; [exact HIy|]. split; [eapply slot_local_ALin; eauto|].
      exists saved, chain, suffix, prefix.
      unfold slot_snapshot, payload_of in Hs.
      rewrite <- Hσ, <- Hs.
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      split; [exact H4|]. split; [exact H5|]. exact H6.
    Qed.

    Lemma slot_local_getTop_loop t count p :
      slot_local t (GetTopLoop t count p).
    Proof.
      destruct p; simpl;
        [apply slot_local_getTop_scan | apply slot_local_completed].
    Qed.

    Lemma snapshot_consistent_add_inv s pi t m :
      snapshot_consistent s pi -> TMap.find t pi = None ->
      snapshot_consistent s (TMap.add t (ls_inv m) pi).
    Proof.
      intros Hconsistent Hnone q.
      destruct (PositiveMap.E.eq_dec q t) as [->|Hneq].
      - rewrite TMap.gss. split.
        + intros [saved Hsaved].
          pose proof
            (proj1 (Hconsistent t) (ex_intro _ saved Hsaved)) as Hbad.
          rewrite Hnone in Hbad. discriminate.
        + discriminate.
      - rewrite TMap.gso by exact Hneq. apply Hconsistent.
    Qed.

    Lemma snapshot_consistent_remove_linr s pi t m ret :
      snapshot_consistent s pi ->
      TMap.find t pi = Some (ls_linr m ret) ->
      snapshot_consistent s (TMap.remove t pi).
    Proof.
      intros Hconsistent Hlin q.
      destruct (PositiveMap.E.eq_dec q t) as [->|Hneq].
      - rewrite TMap.grs. split.
        + intros [saved Hsaved].
          pose proof (proj1 (Hconsistent t) (ex_intro _ saved Hsaved)) as Hbad.
          rewrite Hlin in Hbad. discriminate.
        + discriminate.
      - rewrite TMap.gro by exact Hneq. apply Hconsistent.
    Qed.

    Lemma snapshot_consistent_atomic s pi t m ret :
      snapshot_consistent s pi ->
      TMap.find t pi = Some (ls_inv m) ->
      snapshot_consistent s
        (TMap.add t (ls_linr m ret) (TMap.add t (ls_lini m) pi)).
    Proof.
      intros Hconsistent Hlin q.
      destruct (PositiveMap.E.eq_dec q t) as [->|Hneq].
      - repeat rewrite TMap.gss. split.
        + intros [saved Hsaved].
          pose proof
            (proj1 (Hconsistent t) (ex_intro _ saved Hsaved)) as Hbad.
          rewrite Hlin in Hbad. discriminate.
        + discriminate.
      - repeat rewrite TMap.gso by exact Hneq. apply Hconsistent.
    Qed.

    Lemma snapshot_consistent_getTop_inv s pi t :
      snapshot_consistent s pi ->
      TMap.find t pi = Some (ls_inv (@lgetTop A)) ->
      snapshot_consistent (start_snapshot t s)
        (TMap.add t (ls_lini (@lgetTop A)) pi).
    Proof.
      intros Hconsistent Hlin q.
      destruct (PositiveMap.E.eq_dec q t) as [->|Hneq].
      - simpl. rewrite TMap.gss, TMap.gss. split; [intros _; reflexivity|].
        intros _. eexists. reflexivity.
      - simpl. repeat rewrite TMap.gso by exact Hneq. apply Hconsistent.
    Qed.

    Lemma snapshot_consistent_getTop_res s pi t ret :
      snapshot_consistent s pi ->
      TMap.find t pi = Some (ls_lini (@lgetTop A)) ->
      snapshot_consistent (clear_snapshot t s)
        (TMap.add t (ls_linr (@lgetTop A) ret) pi).
    Proof.
      intros Hconsistent Hlin q.
      destruct (PositiveMap.E.eq_dec q t) as [->|Hneq].
      - simpl. rewrite TMap.grs, TMap.gss. split; [intros [? H]; discriminate|].
        discriminate.
      - simpl. rewrite TMap.gro, TMap.gso by exact Hneq. apply Hconsistent.
    Qed.

    Lemma source_I_change_pi w pi' :
      source_I w ->
      snapshot_consistent
        (abstract_payload (SinglePossState.ρ w)) pi' ->
      source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (SinglePossState.σ w) (SinglePossState.ρ w) pi').
    Proof.
      intros HI Hsnap'.
      destruct HI as
        (mc & cc & s & Hsigma & Hrho & Hmc & Hcc & Hrep & Hsnap).
      exists mc, cc, s. simpl.
      split; [exact Hsigma|].
      split; [exact Hrho|].
      split; [exact Hmc|].
      split; [exact Hcc|].
      split; [exact Hrep|].
      rewrite Hrho in Hsnap'. simpl in Hsnap'. exact Hsnap'.
    Qed.

    Lemma ginv_exposes_active t m :
      forall out,
        AssertionsSingle.A.ComposeA source_I
          (AssertionsSingle.Ginv t m) out ->
        Active t m out.
    Proof.
      intros out [pre [HI Hginv]].
      unfold AssertionsSingle.Ginv, AssertionsSingle.LiftRelation_π in Hginv.
      destruct Hginv as [Hsigma [Hrho [Hnone Hpi]]].
      destruct HI as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      split.
      - exists mc, cc, s.
        split; [rewrite <- Hsigma; exact Eσ|].
        split; [rewrite <- Hrho; exact Eρ|].
        split; [exact Hmc|].
        split; [exact Hcc|].
        split; [exact Hrep|].
        rewrite Hpi. eapply snapshot_consistent_add_inv; eauto.
      - unfold ALin. rewrite Hpi, TMap.gss. reflexivity.
    Qed.

    Lemma gret_closes_completed t m ret :
      forall out,
        AssertionsSingle.A.ComposeA (Completed t m ret)
          (AssertionsSingle.Gret t m ret) out ->
        source_I out.
    Proof.
      intros out [pre [[HI Hlin] Hgret]].
      unfold AssertionsSingle.Gret, AssertionsSingle.LiftRelation_π in Hgret.
      destruct Hgret as [Hsigma [Hrho [Hfind Hpi]]].
      destruct HI as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      exists mc, cc, s.
      split; [rewrite <- Hsigma; exact Eσ|].
      split; [rewrite <- Hrho; exact Eρ|].
      split; [exact Hmc|].
      split; [exact Hcc|].
      split; [exact Hrep|].
      rewrite Hpi. eapply snapshot_consistent_remove_linr; eauto.
    Qed.

    Lemma set_ginv_exposes_active t m :
      forall w,
        AssertionsSet.A.ComposeA SI (AssertionsSet.Ginv t m) w ->
        SActive t m w.
    Proof.
      eapply lift_ginv_compose. apply ginv_exposes_active.
    Qed.

    Lemma set_gret_closes_completed t m ret :
      forall w,
        AssertionsSet.A.ComposeA (SCompleted t m ret)
          (AssertionsSet.Gret t m ret) w -> SI w.
    Proof.
      eapply lift_gret_compose. apply gret_closes_completed.
    Qed.

    Lemma completed_has_return_token t m ret :
      forall w, SCompleted t m ret w ->
      forall rho pi, SetPossState.Δ w rho pi ->
        TMap.find t pi = Some (ls_linr m ret).
    Proof.
      eapply lift_post_lin.
      intros x [_ Hlin]. exact Hlin.
    Qed.

    Definition in_mem := @SPListImpl.in_mem A.
    Definition in_cas := @SPListImpl.in_cas A.

    Lemma getCounter_get_inv_update t :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@InvEv (li_sig E) (in_cas get)))
        (Active t lgetCounter) (Active t lgetCounter).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [HIpre Hlin].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair s1 (Pending s4 t get)) ρ1 π1)).
      { eapply source_I_change_controls with
          (w := @SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (pair s1 (Idle s4)) ρ1 π1).
        - exact HIpre.
        - reflexivity.
        - reflexivity.
        - pose proof (source_I_mem_control _ HIpre) as Hok.
          simpl in Hok. exact Hok.
        - reflexivity. }
      pupdate_finish. split.
      - split; [exact HIpost|exact Hlin].
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getCounter_get_res_update t q :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_cas get) q))
        (Active t lgetCounter)
        (Completed t lgetCounter (snd q)).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [HIpre Hlin].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc.
      subst ρ1.
      destruct Hrep as
        (chain & Hlinked & Hcount & Hlength & Hnodes & Horder).
      simpl in Hcount.
      pupdate_start.
      pupdate_forward t (InvEv (@lgetCounter A)).
      pupdate_forward t (ResEv (@lgetCounter A) (snd q)).
      rewrite <- Hcount. constructor.
      pupdate_finish.
      split.
      - split.
        + exists s1, (Idle q), s. simpl.
          split; [reflexivity|].
          split; [reflexivity|].
          split; [exact Hmc|].
          split; [reflexivity|].
          split.
          * exists chain. repeat split; auto.
          * eapply snapshot_consistent_atomic; eauto.
        + unfold ALin. simpl. rewrite TMap.gss. reflexivity.
      - eapply source_G_same_payload; simpl.
        + exact HIpre0.
        + exists s1, (Idle q), s. simpl.
          split; [reflexivity|].
          split; [reflexivity|].
          split; [exact Hmc|].
          split; [reflexivity|].
          split.
          * exists chain. repeat split; auto.
          * eapply snapshot_consistent_atomic; eauto.
        + reflexivity.
        + reflexivity.
        + reflexivity.
        + intros r Hneq. simpl.
          repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.

    Lemma getCounter_triple t :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t lgetCounter }}
          (@SPListImpl.getCounter_impl A t)
        {{ fun ret => SCompleted t lgetCounter ret }}.
    Proof.
      unfold SPListImpl.getCounter_impl.
      eapply singleton_provable_vis_safe with
        (P' := Active t lgetCounter)
        (Q' := fun q => Completed t lgetCounter (snd q)).
      - intros w _ Herror.
        destruct (SinglePossState.σ w) as [mc cc]. simpl in Herror.
        dependent destruction Herror.
      - apply active_entails_I.
      - intros q. apply completed_entails_I.
      - apply active_stable.
      - intros q. apply completed_stable.
      - apply getCounter_get_inv_update.
      - intros q. apply getCounter_get_res_update.
      - intros q. singleton_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
      - apply active_entails_I.
      - apply slot_local_active.
      - intros q. apply slot_local_completed.
    Qed.

    Lemma setTS_inv_update t l ts :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@InvEv (li_sig E) (in_mem (nmsetTS l ts))))
        (ActiveOwnedDefined t (lsetTS l ts) l)
        (ActiveOwnedDefined t (lsetTS l ts) l).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[[HIpre Hlin] Hdefined] Howner].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Pending s3 t0 (nmsetTS l0 ts0)) s2) ρ1 π1)).
      { eapply source_I_change_controls with
          (w := @SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (pair (Idle s3) s2) ρ1 π1).
        - exact HIpre.
        - reflexivity.
        - reflexivity.
        - simpl. exact Howner.
        - pose proof (source_I_cas_control _ HIpre) as Hok.
          simpl in Hok. exact Hok. }
      pupdate_finish. split.
      - repeat split; auto.
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma setTS_res_update t l ts :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_mem (nmsetTS l ts)) tt))
        (ActiveOwnedDefined t (lsetTS l ts) l)
        (Completed t (lsetTS l ts) tt).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[[HIpre Hlin] Hdefined] Howner].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      destruct Hrep as
        (chain & Hspatial & Hcount & Hlength & Hnodes & Horder).
      simpl in Hspatial, Hcount, Hlength, Hnodes, Horder.
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      assert (Hin : In l0 chain).
      { unfold NodeDefined in Hdefined. simpl in Hdefined.
        destruct Hdefined as [a Hdefined].
        apply (abstract_nodes_some_in s0 chain l0 a).
        rewrite <- Hnodes. exact Hdefined. }
      assert (Hrep' : represents
        (heap_update l0
          (pair (pair (pair v
            (match old_ts with TSTop => ts0 | _ => old_ts end)) taken) next) s0)
        (fst (cas_value s2)) (snd (cas_value s2))
        (SPListSpec.setTS l0 ts0 s)).
      { assert (Hcellframe :
          @sepcon _ heap_Join
            (HCell l0 (pair (pair (pair v old_ts) taken) next))
            (HFrame l0 s0) s0).
        { apply heap_cell_sep. exact H0. }
        destruct (@represents_setTS_frame
          s0 (fst (cas_value s2)) (snd (cas_value s2)) s chain
          l0 v old_ts taken next ts0 (HFrame l0 s0)
          Hspatial Hcount Hlength Hnodes Horder Hin Hcellframe)
          as [Hrepresented _].
        exact Hrepresented. }
      pupdate_start.
      pupdate_forward t0 (InvEv (@lsetTS A l0 ts0)).
      constructor. exact Howner.
      pupdate_forward t0 (ResEv (@lsetTS A l0 ts0) tt).
      pupdate_finish.
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair
            (Idle
              (heap_update l0
                (pair (pair (pair v
                  (match old_ts with TSTop => ts0 | _ => old_ts end)) taken)
                  next) s0))
            s2)
          (Ready (SPListSpec.setTS l0 ts0 s))
          (TMap.add t0 (ls_linr (lsetTS l0 ts0) tt)
            (TMap.add t0 (ls_lini (lsetTS l0 ts0)) π1)))).
      { exists
          (Idle
            (heap_update l0
              (pair (pair (pair v
                (match old_ts with TSTop => ts0 | _ => old_ts end)) taken)
                next) s0)),
          s2, (SPListSpec.setTS l0 ts0 s).
        simpl. split; [reflexivity|].
        split; [reflexivity|].
        split; [reflexivity|].
        split; [exact Hcc|].
        split; [exact Hrep'|].
        eapply snapshot_consistent_atomic; [|exact Hlin].
        unfold SPListSpec.setTS.
        destruct (nodes s l0) as [[v' old']|]; [destruct old'|];
          exact Hsnap. }
      split.
      - split; [exact HIpost|].
        unfold ALin. simpl. rewrite TMap.gss. reflexivity.
      - unfold source_G. repeat split; auto.
        + simpl. rewrite Howner. eapply heap_evol_setTS; eauto.
        + intros q Hnotowner Hundefined. contradiction Hnotowner.
        + unfold cas_evol. simpl.
          destruct (PositiveMap.E.eq_dec t0 owner) as [Heq|Hneq];
            [|contradiction].
          exists chain, chain, nil. repeat split; auto.
          eapply linked_update_existing; eauto.
        + intros q Hneq. simpl.
          unfold SPListSpec.setTS.
          destruct (nodes s l0) as [[v' old']|]; [destruct old'|];
            reflexivity.
        + intros q Hneq. simpl.
          repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.

    Lemma setTS_valid_triple t l ts :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActiveOwnedDefined t (lsetTS l ts) l }}
          (@SPListImpl.setTS_impl A l ts t)
        {{ fun ret => SCompleted t (lsetTS l ts) ret }}.
    Proof.
      unfold SPListImpl.setTS_impl.
      eapply singleton_provable_vis_safe with
        (P' := ActiveOwnedDefined t (lsetTS l ts) l)
        (Q' := fun _ => Completed t (lsetTS l ts) tt).
      - intros w [[[HI Hlin] Hdefined] Howner] Herror.
        destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
        simpl in Herror. revert Howner. dependent destruction Herror.
        + intros Howner. destruct (source_I_defined_lookup _ _ HI Hdefined)
            as (v & old & taken & next & Hlookup).
          rewrite Eσ in Hlookup. simpl in Hlookup. congruence.
        + intros Howner. pose proof (source_I_mem_control _ HI) as Hok.
          rewrite Eσ in Hok. simpl in Hok. congruence.
      - apply active_owned_defined_entails_I.
      - intros []; apply completed_entails_I.
      - apply active_owned_defined_stable.
      - intros []; apply completed_stable.
      - apply setTS_inv_update.
      - intros []; apply setTS_res_update.
      - intros []. singleton_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
      - apply active_owned_defined_entails_I.
      - apply slot_local_active_owned_defined.
      - intros []. apply slot_local_completed.
    Qed.

    Lemma setTS_active_valid_or_error t l ts :
      ⊨ SActive t (lsetTS l ts) ==>>
        SActiveOwnedDefined t (lsetTS l ts) l \\// AssertionsSet.APError.
    Proof.
      intros w Hall.
      destruct (ac_nonempty (SetPossState.Δ w)) as (ρ0 & π0 & Hposs0).
      pose proof (Hall _ _ Hposs0) as [HI0 Hlin0].
      destruct (PositiveMap.E.eq_dec t owner) as [Howner|Howner].
      - destruct (nodes (payload_of (mk (SetPossState.σ w) ρ0 π0)) l)
          as [a|] eqn:Hnode.
        + left. intros ρ π Hposs. pose proof (Hall _ _ Hposs) as [HI Hlin].
          split; [|exact Howner]. split; [split; assumption|].
          exists a.
          pose proof (proj1 (proj2 (source_I_payload_determined _ _ HI HI0
            eq_refl))) as Hn.
          unfold payload_of in Hn, Hnode. simpl in Hn, Hnode. simpl.
          rewrite Hn. exact Hnode.
        + right. destruct HI0 as
            (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
          econstructor; [exact Hposs0|].
          apply rt_step. eapply ps_error.
          * simpl in Eρ. rewrite Eρ.
            eapply (@error_setTS_undefined A owner t s l ts _).
            -- unfold payload_of in Hnode. simpl in Hnode.
               rewrite Eρ in Hnode. simpl in Hnode. exact Hnode.
            -- reflexivity.
          * exact Hlin0.
      - right. destruct HI0 as
          (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
        econstructor; [exact Hposs0|].
        apply rt_step. eapply ps_error.
        + simpl in Eρ. rewrite Eρ.
          eapply (@error_setTS_not_owner A owner t s l ts _); eauto.
        + exact Hlin0.
    Qed.

    Lemma setTS_triple t l ts :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t (lsetTS l ts) }}
          (@SPListImpl.setTS_impl A l ts t)
        {{ fun ret => SCompleted t (lsetTS l ts) ret }}.
    Proof.
      eapply SetLogic.provable_perror.
      - apply setTS_active_valid_or_error.
      - apply setTS_valid_triple.
    Qed.

    Lemma tryRemove_inv_update t l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@InvEv (li_sig E) (in_mem (nmtryTake l))))
        (ActiveDefined t (ltryRemove l) l)
        (ActiveDefined t (ltryRemove l) l).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[HIpre Hlin] Hdefined].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Pending s3 t0 (nmtryTake l0)) s2) ρ1 π1)).
      { eapply source_I_change_controls with
          (w := @SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (pair (Idle s3) s2) ρ1 π1).
        - exact HIpre.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - pose proof (source_I_cas_control _ HIpre) as Hok.
          simpl in Hok. exact Hok. }
      pupdate_finish. split.
      - split; [split; [exact HIpost|exact Hlin]|exact Hdefined].
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma tryRemove_succ_update t l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_mem (nmtryTake l)) true))
        (ActiveDefined t (ltryRemove l) l)
        (Completed t (ltryRemove l) true).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[HIpre Hlin] Hdefined].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      destruct Hrep as
        (chain & Hspatial & Hcount & Hlength & Hnodes & Horder).
      simpl in Hspatial, Hcount, Hlength, Hnodes, Horder.
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      rename H0 into Hconcrete.
      assert (Hin : In l0 chain).
      { unfold NodeDefined in Hdefined. simpl in Hdefined.
        destruct Hdefined as [a Hdefined].
        apply (abstract_nodes_some_in s0 chain l0 a).
        rewrite <- Hnodes. exact Hdefined. }
      assert (Hnode_defined : nodes s l0 <> None).
      { rewrite Hnodes. eapply linked_abstract_lookup in Hconcrete; eauto.
        congruence. }
      assert (Hlive : In l0 (order s)).
      { rewrite Horder. eapply linked_live_false; eauto. }
      assert (Hrep' : represents
        (heap_update l0 (pair (pair (pair v ts) true) next) s0)
        (fst (cas_value s2)) (snd (cas_value s2))
        (SPListSpec.remove l0 s)).
      { assert (Hcellframe :
          @sepcon _ heap_Join
            (HCell l0 (pair (pair (pair v ts) false) next))
            (HFrame l0 s0) s0).
        { apply heap_cell_sep. exact Hconcrete. }
        destruct (@represents_tryTake_frame
          s0 (fst (cas_value s2)) (snd (cas_value s2)) s chain
          l0 v ts next (HFrame l0 s0)
          Hspatial Hcount Hlength Hnodes Horder Hin Hcellframe)
          as [Hrepresented _].
        exact Hrepresented. }
      pupdate_start.
      pupdate_forward t0 (InvEv (@ltryRemove A l0)).
      constructor. exact Hnode_defined.
      pupdate_forward t0 (ResEv (@ltryRemove A l0) true).
      constructor; assumption.
      pupdate_finish.
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair
            (Idle (heap_update l0 (pair (pair (pair v ts) true) next) s0))
            s2)
          (Ready (SPListSpec.remove l0 s))
          (TMap.add t0 (ls_linr (ltryRemove l0) true)
            (TMap.add t0 (ls_lini (ltryRemove l0)) π1)))).
      { exists
          (Idle (heap_update l0 (pair (pair (pair v ts) true) next) s0)),
          s2, (SPListSpec.remove l0 s).
        simpl. split; [reflexivity|].
        split; [reflexivity|].
        split; [reflexivity|].
        split; [exact Hcc|].
        split; [exact Hrep'|].
        eapply snapshot_consistent_atomic; [exact Hsnap|exact Hlin]. }
      split.
      - split; [exact HIpost|].
        unfold ALin. simpl. rewrite TMap.gss. reflexivity.
      - unfold source_G. repeat split; auto.
        + simpl. eapply heap_evol_tryTake; exact Hconcrete.
        + intros q Hnotowner Hundefined. simpl.
          destruct (Nat.eq_dec l0 q) as [Heq|Hneq].
          * subst q. exfalso. apply Hnode_defined. exact Hundefined.
          * symmetry. apply HeapUpdateOther. exact Hneq.
        + unfold cas_evol. simpl.
          destruct (PositiveMap.E.eq_dec t0 owner) as [Heq|Hneq].
          * exists chain, chain, nil. repeat split; auto.
            eapply linked_update_existing; eauto.
          * reflexivity.
        + intros q Hneq. simpl.
          repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.

    Lemma tryRemove_fail_update t l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_mem (nmtryTake l)) false))
        (ActiveDefined t (ltryRemove l) l)
        (Completed t (ltryRemove l) false).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[HIpre Hlin] Hdefined].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      destruct Hrep as
        (chain & Hspatial & Hcount & Hlength & Hnodes & Horder).
      simpl in Hspatial, Hcount, Hlength, Hnodes, Horder.
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      rename H0 into Hconcrete.
      assert (Hcellframe :
        @sepcon _ heap_Join
          (HCell l0 (pair (pair (pair v ts) true) next))
          (HFrame l0 s3) s3).
      { apply heap_cell_sep. exact Hconcrete. }
      assert (Hrep_same : represents s3 (fst (cas_value s2))
          (snd (cas_value s2)) s).
      { destruct (@represents_tryTake_fail_frame
          s3 (fst (cas_value s2)) (snd (cas_value s2)) s chain
          l0 v ts next (HFrame l0 s3)
          Hspatial Hcount Hlength Hnodes Horder Hcellframe)
          as [Hrepresented _].
        exact Hrepresented. }
      assert (Hin : In l0 chain).
      { unfold NodeDefined in Hdefined. simpl in Hdefined.
        destruct Hdefined as [a Hdefined].
        apply (abstract_nodes_some_in s3 chain l0 a).
        rewrite <- Hnodes. exact Hdefined. }
      assert (Hnode_defined : nodes s l0 <> None).
      { rewrite Hnodes. eapply linked_abstract_lookup in Hconcrete; eauto.
        congruence. }
      assert (Hnotlive : ~ In l0 (order s)).
      { rewrite Horder. eapply linked_live_true; eauto. }
      pupdate_start.
      pupdate_forward t0 (InvEv (@ltryRemove A l0)).
      constructor. exact Hnode_defined.
      pupdate_forward t0 (ResEv (@ltryRemove A l0) false).
      constructor; assumption.
      pupdate_finish.
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Idle s3) s2) (Ready s)
          (TMap.add t0 (ls_linr (ltryRemove l0) false)
            (TMap.add t0 (ls_lini (ltryRemove l0)) π1)))).
      { exists (Idle s3), s2, s. simpl.
        split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [exact Hcc|].
        split.
        - exact Hrep_same.
        - eapply snapshot_consistent_atomic; [exact Hsnap|exact Hlin]. }
      split.
      - split; [exact HIpost|].
        unfold ALin. simpl. rewrite TMap.gss. reflexivity.
      - eapply source_G_same_payload; simpl; eauto.
        intros q Hneq. repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.

    Lemma tryRemove_valid_triple t l :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActiveDefined t (ltryRemove l) l }}
          (@SPListImpl.tryRemove_impl A l t)
        {{ fun ret => SCompleted t (ltryRemove l) ret }}.
    Proof.
      unfold SPListImpl.tryRemove_impl.
      eapply singleton_provable_vis_safe with
        (P' := ActiveDefined t (ltryRemove l) l)
        (Q' := fun ret => Completed t (ltryRemove l) ret).
      - intros w [[HI Hlin] Hdefined] Herror.
        destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
        simpl in Herror. dependent destruction Herror.
        destruct (source_I_defined_lookup _ _ HI Hdefined)
          as (v & ts & taken & next & Hlookup).
        rewrite Eσ in Hlookup. simpl in Hlookup. congruence.
      - apply active_defined_entails_I.
      - intros ret. apply completed_entails_I.
      - apply active_defined_stable.
      - intros ret. apply completed_stable.
      - apply tryRemove_inv_update.
      - intros ret. destruct ret.
        + apply tryRemove_succ_update.
        + apply tryRemove_fail_update.
      - intros ret. singleton_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
      - apply active_defined_entails_I.
      - apply slot_local_active_defined.
      - intros ret. apply slot_local_completed.
    Qed.

    Lemma tryRemove_active_valid_or_error t l :
      ⊨ SActive t (ltryRemove l) ==>>
        SActiveDefined t (ltryRemove l) l \\// AssertionsSet.APError.
    Proof.
      intros w Hall.
      destruct (ac_nonempty (SetPossState.Δ w)) as (ρ0 & π0 & Hposs0).
      pose proof (Hall _ _ Hposs0) as [HI0 Hlin0].
      destruct (nodes (payload_of (mk (SetPossState.σ w) ρ0 π0)) l)
        as [a|] eqn:Hnode.
      - left. intros ρ π Hposs. pose proof (Hall _ _ Hposs) as [HI Hlin].
        split; [split; assumption|].
        exists a.
        pose proof (proj1 (proj2 (source_I_payload_determined _ _ HI HI0
          eq_refl))) as Hn.
        unfold payload_of in Hn, Hnode. simpl in Hn, Hnode. simpl.
        rewrite Hn. exact Hnode.
      - right. destruct HI0 as
          (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
        econstructor; [exact Hposs0|].
        apply rt_step. eapply ps_error.
        + simpl in Eρ. rewrite Eρ.
          eapply (@error_tryRemove_undefined A owner t s l _).
          * unfold payload_of in Hnode. simpl in Hnode.
            rewrite Eρ in Hnode. simpl in Hnode. exact Hnode.
          * reflexivity.
        + exact Hlin0.
    Qed.

    Lemma tryRemove_triple t l :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t (ltryRemove l) }}
          (@SPListImpl.tryRemove_impl A l t)
        {{ fun ret => SCompleted t (ltryRemove l) ret }}.
    Proof.
      eapply SetLogic.provable_perror.
      - apply tryRemove_active_valid_or_error.
      - apply tryRemove_valid_triple.
    Qed.

    Lemma insert_get_inv_update t v :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_cas get)))
        (ActiveOwned t (linsert v)) (ActiveOwned t (linsert v)).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[HIpre Hlin] Howner].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair s1 (Pending s4 t get)) ρ1 π1)).
      { eapply source_I_change_controls with
          (w := @SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (pair s1 (Idle s4)) ρ1 π1);
          simpl; eauto.
        pose proof (source_I_mem_control _ HIpre) as Hok. simpl in Hok. exact Hok. }
      pupdate_finish. split.
      - split; [split; assumption|exact Howner].
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma insert_get_res_update t v q :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_cas get) q))
        (ActiveOwned t (linsert v)) (InsertRead t v q).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[HIpre Hlin] Howner].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair s1 (Idle q)) ρ1 π1)).
      { eapply source_I_change_controls with
          (w := @SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (pair s1 (Pending q t get)) ρ1 π1);
          simpl; eauto.
        pose proof (source_I_mem_control _ HIpre) as Hok. simpl in Hok. exact Hok. }
      pupdate_finish. split.
      - split.
        + split; [split; assumption|exact Howner].
        + reflexivity.
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma insert_malloc_inv_update t v q :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@InvEv (li_sig E) (in_mem (nmalloc v (fst q)))))
        (InsertRead t v q) (InsertRead t v q).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[[HIpre Hlin] Howner] Hcas].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Pending s3 t0 (nmalloc v0 (fst q))) s2) ρ1 π1)).
      { eapply source_I_change_controls with
          (w := @SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (pair (Idle s3) s2) ρ1 π1);
          simpl; eauto.
        - pose proof (source_I_cas_control _ HIpre) as Hok. simpl in Hok.
          exact Hok. }
      pupdate_finish. split.
      - split; [split; [split; assumption|exact Howner]|exact Hcas].
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma insert_malloc_res_update t v q l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_mem (nmalloc v (fst q))) l))
        (InsertRead t v q) (InsertAllocated t v q l).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[[HIpre Hlin] Howner] Hcas].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      rename H0 into Hfresh.
      destruct Hrep as
        (chain & Hspatial & Hcount & Hlength & Hnodes & Horder).
      simpl in Hspatial, Hcount, Hlength, Hnodes, Horder, Hcas.
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      assert (Hundefined : nodes s l = None).
      { rewrite Hnodes. apply abstract_nodes_notin.
        eapply linked_fresh_notin; eauto. }
      assert (Hrep' : represents
        (heap_update l
          (pair (pair (pair v0 TSTop) false) (fst q)) s0)
        (fst (cas_value s2)) (snd (cas_value s2)) s).
      { rewrite Hcas in Hspatial, Hcount, Hlength |- *.
        destruct (@represents_allocate_frame
          s0 (fst q) (snd q) s chain l v0
          Hspatial Hcount Hlength Hnodes Horder Hfresh)
          as [Hrepresented _].
        exact Hrepresented. }
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair
            (Idle (heap_update l
              (pair (pair (pair v0 TSTop) false) (fst q)) s0)) s2)
          (Ready s) π1)).
      { exists
          (Idle (heap_update l
            (pair (pair (pair v0 TSTop) false) (fst q)) s0)), s2, s.
        simpl. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [exact Hcc|].
        split; [exact Hrep'|exact Hsnap]. }
      pupdate_finish. split.
      - split.
        + split.
          * split; [split; [exact HIpost|exact Hlin]|exact Howner].
          * exact Hcas.
        + split.
          * unfold NodeUndefined. simpl. exact Hundefined.
          * simpl. apply HeapUpdateSelf.
      - unfold source_G. repeat split; auto.
        + simpl. rewrite Howner. eapply heap_evol_allocate; exact Hfresh.
        + intros q0 Hnotowner Hundef. contradiction Hnotowner.
        + unfold cas_evol. simpl.
          destruct (PositiveMap.E.eq_dec t0 owner) as [Heq|Hneq];
            [|contradiction].
          exists chain, chain, nil. repeat split; auto.
          eapply linked_update_fresh; eauto.
    Qed.

    Lemma insert_set_inv_update t v q l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@InvEv (li_sig E)
            (in_cas (set (pair (Some l) (S (snd q)))))))
        (InsertAllocated t v q l) (InsertAllocated t v q l).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as
        [[[[HIpre Hlin] Howner] Hcas] [Hundefined Hcell]].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair s1
            (Pending s4 t (set (pair (Some l) (S (snd q)))))) ρ1 π1)).
      { eapply source_I_change_controls with
          (w := @SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (pair s1 (Idle s4)) ρ1 π1);
          simpl; eauto.
        pose proof (source_I_mem_control _ HIpre) as Hok. simpl in Hok.
        exact Hok. }
      pupdate_finish. split.
      - split.
        + split; [split; [split; [exact HIpost|exact Hlin]|exact Howner]
          |exact Hcas].
        + split; [exact Hundefined|exact Hcell].
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma insert_set_res_update t v q l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E)
            (in_cas (set (pair (Some l) (S (snd q))))) tt))
        (InsertAllocated t v q l)
        (Completed t (linsert v) l).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as
        [[[[HIpre Hlin] Howner] Hcas] [Hundefined Hcell]].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      destruct Hrep as
        (chain & Hspatial & Hcount & Hlength & Hnodes & Horder).
      simpl in Hspatial, Hcount, Hlength, Hnodes, Horder, Hcas, Hcell,
        Hundefined.
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      unfold CASIs in Hcas. simpl in Hcas.
      unfold NodeUndefined in Hundefined. simpl in Hundefined.
      assert (Hrep' : represents (mem_heap s1) (Some l) (S (snd q))
        (SPListSpec.insert v l s)).
      { rewrite Hcas in Hspatial, Hcount, Hlength.
        destruct (@represents_publish_frame
          (mem_heap s1) (fst q) (snd q) s chain l v
          Hspatial Hcount Hlength Hnodes Horder Hundefined Hcell)
          as [Hrepresented _].
        exact Hrepresented. }
      pupdate_start.
      pupdate_forward t (InvEv (@linsert A v)).
      constructor. exact Howner.
      pupdate_forward t (ResEv (@linsert A v) l).
      constructor. exact Hundefined.
      pupdate_finish.
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair s1 (Idle (pair (Some l) (S (snd q)))))
          (Ready (SPListSpec.insert v l s))
          (TMap.add t (ls_linr (linsert v) l)
            (TMap.add t (ls_lini (linsert v)) π1)))).
      { exists s1, (Idle (pair (Some l) (S (snd q)))),
          (SPListSpec.insert v l s).
        simpl. split; [reflexivity|]. split; [reflexivity|].
        split; [exact Hmc|]. split; [reflexivity|].
        split; [exact Hrep'|].
        eapply snapshot_consistent_atomic; [exact Hsnap|exact Hlin]. }
      split.
      - split; [exact HIpost|].
        unfold ALin. simpl. rewrite TMap.gss. reflexivity.
      - unfold source_G. repeat split; auto.
        + simpl. rewrite Howner. apply heap_evol_refl.
        + unfold cas_evol. simpl.
          destruct (PositiveMap.E.eq_dec t owner) as [Heq|Hneq];
            [|contradiction].
          exists chain, (l :: chain), (l :: nil). split.
          * exact Hlinked.
          * split.
            -- econstructor.
               ++ exact Hcell.
               ++ rewrite Hcas in Hlinked. exact Hlinked.
               ++ intro Hin.
                  rewrite Hnodes, abstract_nodes_in, Hcell in Hundefined
                    by exact Hin. discriminate.
            -- reflexivity.
        + intros r Hneq. simpl.
          repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.

    Lemma insert_valid_triple t v :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ lift_assert (ActiveOwned t (linsert v)) }}
          (@SPListImpl.insert_impl A v t)
        {{ fun l => SCompleted t (linsert v) l }}.
    Proof.
      unfold SPListImpl.insert_impl.
      eapply singleton_provable_vis_safe with
        (P' := ActiveOwned t (linsert v))
        (Q' := fun q => InsertRead t v q).
      - intros w Hpre Herror.
        destruct (SinglePossState.σ w) as [mc cc]. simpl in Herror.
        dependent destruction Herror.
      - apply active_owned_entails_I.
      - intros q. apply insert_read_entails_I.
      - apply active_owned_stable.
      - intros q. apply insert_read_stable.
      - apply insert_get_inv_update.
      - intros q. apply insert_get_res_update.
      - intros q. destruct q as [top count]. simpl.
        eapply singleton_provable_vis_safe with
          (P' := InsertRead t v (pair top count))
          (Q' := fun l => InsertAllocated t v (pair top count) l).
        + intros w Hpre Herror.
          destruct (SinglePossState.σ w) as [mc cc]. simpl in Herror.
          dependent destruction Herror.
        + apply insert_read_entails_I.
        + intros l. apply insert_allocated_entails_I.
        + apply insert_read_stable.
        + intros l. apply insert_allocated_stable.
        + apply insert_malloc_inv_update.
        + intros l. apply insert_malloc_res_update.
        + intros l.
          eapply singleton_provable_vis_safe with
            (P' := InsertAllocated t v (pair top count) l)
            (Q' := fun _ => Completed t (linsert v) l).
          * intros w Hpre Herror.
            destruct Hpre as
              [[[[HI Hlin] Howner] Hcas] [Hundefined Hcell]].
            destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
            simpl in Herror. dependent destruction Herror.
            pose proof (source_I_cas_control _ HI) as Hok.
            rewrite Eσ in Hok. simpl in Hok. congruence.
          * apply insert_allocated_entails_I.
          * intros []; apply completed_entails_I.
          * apply insert_allocated_stable.
          * intros []; apply completed_stable.
          * apply insert_set_inv_update.
          * intros []; apply insert_set_res_update.
          * intros []. singleton_ret_safe.
            -- apply ImplRefl.
            -- apply completed_entails_I.
            -- apply completed_stable.
          * apply insert_allocated_entails_I.
          * apply slot_local_insert_allocated.
          * intros []. apply slot_local_completed.
        + apply insert_read_entails_I.
        + apply slot_local_insert_read.
        + intros l. apply slot_local_insert_allocated.
      - apply active_owned_entails_I.
      - apply slot_local_active_owned.
      - intros q. apply slot_local_insert_read.
    Qed.

    Lemma insert_active_valid_or_error t v :
      ⊨ SActive t (linsert v) ==>>
        lift_assert (ActiveOwned t (linsert v)) \\// AssertionsSet.APError.
    Proof.
      intros w Hall.
      destruct (ac_nonempty (SetPossState.Δ w)) as (ρ0 & π0 & Hposs0).
      pose proof (Hall _ _ Hposs0) as [HI0 Hlin0].
      destruct (PositiveMap.E.eq_dec t owner) as [Howner|Howner].
      - left. intros ρ π Hposs. split; [apply Hall, Hposs|exact Howner].
      - right. destruct HI0 as
          (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
        econstructor; [exact Hposs0|].
        apply rt_step. eapply ps_error.
        + simpl in Eρ. rewrite Eρ.
          eapply (@error_linsert_not_owner A owner t s v _); eauto.
        + exact Hlin0.
    Qed.

    Lemma insert_triple t v :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t (linsert v) }}
          (@SPListImpl.insert_impl A v t)
        {{ fun l => SCompleted t (linsert v) l }}.
    Proof.
      eapply SetLogic.provable_perror.
      - apply insert_active_valid_or_error.
      - apply insert_valid_triple.
    Qed.

    Lemma getTop_get_inv_update t :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_cas get)))
        (Active t (@lgetTop A)) (Active t (@lgetTop A)).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [HIpre Hlin].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair s1 (Pending s4 t get)) ρ1 π1)).
      { eapply source_I_change_controls with
          (w := @SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (pair s1 (Idle s4)) ρ1 π1).
        - exact HIpre.
        - reflexivity.
        - reflexivity.
        - pose proof (source_I_mem_control _ HIpre) as Hok. simpl in Hok.
          exact Hok.
        - reflexivity. }
      pupdate_finish. split.
      - split; assumption.
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getTop_get_res_update t q :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_cas get) q))
        (Active t (@lgetTop A))
        (GetTopLoop t (snd q) (fst q)).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [HIpre Hlin]. pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      destruct Hrep as
        (chain & Hspatial & Hcount & Hlength & Hnodes & Horder).
      simpl in Hspatial, Hcount, Hlength, Hnodes, Horder.
      pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
      assert (Hsnapshot_none : TMap.find t (snapshot s) = None).
      { destruct (TMap.find t (snapshot s)) as [saved|] eqn:Hfind;
          [|reflexivity].
        pose proof (proj1 (Hsnap t) (ex_intro _ saved Hfind)) as Hbad.
        unfold ALin in Hlin. rewrite Hlin in Hbad. discriminate. }
      destruct q as [top count]. simpl in *.
      destruct top as [l|].
      - pupdate_start.
        pupdate_forward t (InvEv (@lgetTop A)).
        constructor. exact Hsnapshot_none.
        pupdate_finish.
        assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair s1 (Idle (pair (Some l) count)))
            (Ready (start_snapshot t s))
            (TMap.add t (ls_lini (@lgetTop A)) π1))).
        { exists s1, (Idle (pair (Some l) count)), (start_snapshot t s).
          simpl. split; [reflexivity|]. split; [reflexivity|].
          split; [exact Hmc|]. split; [reflexivity|].
          split.
          * exists chain. repeat split; auto.
          * eapply snapshot_consistent_getTop_inv; eauto. }
        split.
        + split; [exact HIpost|]. split.
          * unfold ALin. simpl. rewrite TMap.gss. reflexivity.
          * exists (order s), chain, chain, nil. simpl.
            repeat split; auto.
            -- rewrite TMap.gss, Horder, Hcount. reflexivity.
            -- rewrite Horder. apply forall_live_order.
            -- rewrite Horder. apply filter_live_order.
        + unfold source_G. repeat split; auto.
          * simpl. apply heap_evol_refl.
          * unfold cas_evol. simpl.
            destruct (PositiveMap.E.eq_dec t owner).
            -- exists chain, chain, nil. repeat split; auto.
            -- reflexivity.
          * intros r Hneq. simpl. rewrite TMap.gso by exact Hneq. reflexivity.
          * intros r Hneq. simpl. rewrite TMap.gso by exact Hneq. reflexivity.
      - pupdate_start.
        pupdate_forward t (InvEv (@lgetTop A)).
        constructor. exact Hsnapshot_none.
        assert (Echain : chain = nil).
        { eapply linked_deterministic; [exact Hlinked|constructor]. }
        subst chain. simpl in Horder, Hcount, Hlength, Hnodes.
        pupdate_forward t
          (ResEv (@lgetTop A) (@inr (@LNode A) nat count)).
        constructor. unfold actual_snapshot. simpl.
        rewrite TMap.gss. simpl. rewrite Horder, Hcount. reflexivity.
        pupdate_finish.
        assert (Echain_post : chain = nil).
        { eapply linked_deterministic; [exact Hlinked|constructor]. }
        subst chain. simpl in Horder, Hcount, Hlength, Hnodes.
        assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair s1 (Idle (pair None count)))
            (Ready (clear_snapshot t (start_snapshot t s)))
            (TMap.add t
              (ls_linr (@lgetTop A) (@inr (@LNode A) nat count))
              (TMap.add t (ls_lini (@lgetTop A)) π1)))).
        { exists s1, (Idle (pair None count)),
            (clear_snapshot t (start_snapshot t s)).
          simpl. split; [reflexivity|]. split; [reflexivity|].
          split; [exact Hmc|]. split; [reflexivity|].
          split.
          * exists nil. simpl. split; [exact Hspatial|].
            split; [exact Hcount|]. split; [exact Hlength|].
            split; [exact Hnodes|exact Horder].
          * eapply snapshot_consistent_getTop_res.
            -- eapply snapshot_consistent_getTop_inv; eauto.
            -- rewrite TMap.gss. reflexivity. }
        split.
        + simpl. split; [exact HIpost|].
          unfold ALin. simpl. rewrite TMap.gss. reflexivity.
        + unfold source_G. repeat split; auto.
          * simpl. apply heap_evol_refl.
          * unfold cas_evol. simpl.
            destruct (PositiveMap.E.eq_dec t owner).
            -- exists nil, nil, nil. repeat split; auto; constructor.
            -- reflexivity.
          * intros r Hneq. simpl.
            rewrite TMap.gro, TMap.gso by exact Hneq. reflexivity.
          * intros r Hneq. simpl.
            repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.

    (** ** [getTop]: per-field reads and the two-possibility window

        [getTop_impl] reads a node's value, next pointer and timestamp, and
        then its taken flag.  The value and next pointer never change; the
        timestamp is set once (from [TSTop]) and the flag flipped once.  A
        node observed untaken after its timestamp was read was untaken,
        with that timestamp, at the time of the timestamp read, which is
        therefore the linearization point.  Between the two reads the proof
        keeps both the "still scanning" and the "already returned"
        possibilities. *)

    Definition NodeCell (l : Addr) (v : A) (nx : Ptr)
        (σ : concrete_state) : Prop :=
      exists ts taken,
        mem_heap (fst σ) l = Some (pair (pair (pair v ts) taken) nx).

    Definition GetTopScanVal (t : tid) (count : nat) (l : Addr) (v : A) :
        assertion :=
      fun w => GetTopScan t count (Some l) w /\
        exists nx, NodeCell l v nx (SinglePossState.σ w).

    Definition GetTopScanAt (t : tid) (count : nat) (l : Addr) (v : A)
        (nx : Ptr) : assertion :=
      fun w => GetTopScan t count (Some l) w /\
        NodeCell l v nx (SinglePossState.σ w).

    Definition GetTopKind (t : tid) (count : nat) (l : Addr) (v : A)
        (nx : Ptr) (ts : TS) : assertion :=
      fun w => GetTopScanAt t count l v nx w \/
        Completed t (@lgetTop A) (@inl (@LNode A) nat (pair (pair v ts) l)) w.

    Definition GetTopWindow (t : tid) (count : nat) (l : Addr) (v : A)
        (nx : Ptr) (ts : TS) : set_assertion :=
      fun s =>
        lift_assert (GetTopKind t count l v nx ts) s /\
        NodeCell l v nx (SetPossState.σ s) /\
        HasKind kind_lini t s /\
        (live_at (mem_heap (fst (SetPossState.σ s))) l = true ->
          HasKind kind_linr t s).

    Definition GetTopTakenPost (t : tid) (count : nat) (l : Addr) (v : A)
        (nx : Ptr) (ts : TS) (b : bool) : assertion :=
      if b then GetTopLoop t count nx
      else Completed t (@lgetTop A) (@inl (@LNode A) nat (pair (pair v ts) l)).

    (** *** Stability *)

    Lemma source_R_node_cell t l v nx x x' :
      source_R t x x' ->
      NodeCell l v nx (SinglePossState.σ x) ->
      NodeCell l v nx (SinglePossState.σ x').
    Proof.
      intros HR (ts & taken & Hcell).
      destruct HR as [[actor [Hneq HG]] | Hadmin].
      - destruct HG as (_ & _ & Hheap & _). specialize (Hheap l).
        rewrite Hcell in Hheap. destruct Hheap as [new [Hnew Hevol]].
        destruct new as [[[v' ts'] taken'] nx'].
        destruct Hevol as (Hv & _ & _ & Hn). simpl in Hv, Hn. subst v' nx'.
        exists ts', taken'. exact Hnew.
      - apply AssertionsSingle.linearization_rely_observer_view in Hadmin.
        destruct Hadmin as [Hσ _]. rewrite <- Hσ. exists ts, taken. exact Hcell.
    Qed.

    Lemma source_R_live_imp t l v nx x x' :
      source_R t x x' ->
      NodeCell l v nx (SinglePossState.σ x) ->
      live_at (mem_heap (fst (SinglePossState.σ x'))) l = true ->
      live_at (mem_heap (fst (SinglePossState.σ x))) l = true.
    Proof.
      intros HR (ts & taken & Hcell) Hlive.
      destruct HR as [[actor [Hneq HG]] | Hadmin].
      - destruct HG as (_ & _ & Hheap & _). specialize (Hheap l).
        rewrite Hcell in Hheap. destruct Hheap as [new [Hnew Hevol]].
        destruct new as [[[v' ts'] taken'] nx'].
        destruct Hevol as (_ & _ & Htaken & _). simpl in Htaken.
        unfold live_at, node_live in *. rewrite Hnew in Hlive. rewrite Hcell.
        simpl in *. destruct taken; [|reflexivity].
        specialize (Htaken eq_refl). subst taken'. discriminate.
      - apply AssertionsSingle.linearization_rely_observer_view in Hadmin.
        destruct Hadmin as [Hσ _]. rewrite Hσ. exact Hlive.
    Qed.

    Lemma getTop_scan_val_entails_I t count l v :
      ⊨ GetTopScanVal t count l v ==>> source_I.
    Proof. intros w [[HI _] _]. exact HI. Qed.

    Lemma getTop_scan_at_entails_I t count l v nx :
      ⊨ GetTopScanAt t count l v nx ==>> source_I.
    Proof. intros w [[HI _] _]. exact HI. Qed.

    Lemma getTop_scan_val_stable t count l v :
      AssertionsSingle.A.Stable (source_R t) source_I
        (GetTopScanVal t count l v).
    Proof.
      unfold AssertionsSingle.A.Stable.
      intros out [[pre [[Hscan [nx Hcell]] HR]] HIout]. split.
      - eapply getTop_scan_stable.
        split; [exists pre; split; [exact Hscan|exact HR] | exact HIout].
      - exists nx. eapply source_R_node_cell; eauto.
    Qed.

    Lemma getTop_scan_at_stable t count l v nx :
      AssertionsSingle.A.Stable (source_R t) source_I
        (GetTopScanAt t count l v nx).
    Proof.
      unfold AssertionsSingle.A.Stable.
      intros out [[pre [[Hscan Hcell] HR]] HIout]. split.
      - eapply getTop_scan_stable.
        split; [exists pre; split; [exact Hscan|exact HR] | exact HIout].
      - eapply source_R_node_cell; eauto.
    Qed.

    Lemma slot_local_node_cell q l v nx :
      slot_local q (fun w => NodeCell l v nx (SinglePossState.σ w)).
    Proof. intros x y Hx _ [Hσ _]. rewrite <- Hσ. exact Hx. Qed.

    Lemma slot_local_getTop_scan_val t count l v :
      slot_local t (GetTopScanVal t count l v).
    Proof.
      intros x y [Hscan [nx Hcell]] HI Hag. split.
      - eapply slot_local_getTop_scan; eauto.
      - exists nx. eapply slot_local_node_cell; eauto.
    Qed.

    Lemma slot_local_getTop_scan_at t count l v nx :
      slot_local t (GetTopScanAt t count l v nx).
    Proof.
      intros x y [Hscan Hcell] HI Hag. split.
      - eapply slot_local_getTop_scan; eauto.
      - eapply slot_local_node_cell; eauto.
    Qed.

    Lemma getTop_kind_entails_I t count l v nx ts :
      ⊨ GetTopKind t count l v nx ts ==>> source_I.
    Proof.
      intros w [HA | HB]; [exact (proj1 (proj1 HA)) | exact (proj1 HB) ].
    Qed.

    Lemma getTop_window_entails_I t count l v nx ts :
      ⊨ GetTopWindow t count l v nx ts ==>> SI.
    Proof.
      intros s [Hkinds _] ρ π Hposs.
      eapply getTop_kind_entails_I. apply Hkinds, Hposs.
    Qed.

    Lemma getTop_window_stable t count l v nx ts :
      AssertionsSet.A.Stable (R t) SI (GetTopWindow t count l v nx ts).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA.
      intros s' [[s [[Hkinds [Hcell [Hlini Hlinr]]] [Hback Htwins]]] HI].
      destruct (ac_nonempty (SetPossState.Δ s')) as (ρ0 & π0 & Hposs0).
      destruct (Hback _ _ Hposs0) as (ρ1 & π1 & Hposs1 & HR0).
      split; [|split; [|split]].
      - intros ρ' π' Hposs'.
        destruct (Hback _ _ Hposs') as (ρ & π & Hposs & HR).
        pose proof (Hkinds _ _ Hposs) as Hk. pose proof (HI _ _ Hposs') as HI'.
        destruct Hk as [HA | HB].
        + left. eapply getTop_scan_at_stable.
          split; [exists (mk (SetPossState.σ s) ρ π); split;
            [exact HA|exact HR] | exact HI'].
        + right. eapply completed_stable.
          split; [exists (mk (SetPossState.σ s) ρ π); split;
            [exact HB|exact HR] | exact HI'].
      - exact (source_R_node_cell t l v nx (mk (SetPossState.σ s) ρ1 π1)
          (mk (SetPossState.σ s') ρ0 π0) HR0 Hcell).
      - apply (proj1 Htwins). exact Hlini.
      - intros Hlive. apply (proj2 Htwins). apply Hlinr.
        exact (source_R_live_imp t l v nx (mk (SetPossState.σ s) ρ1 π1)
          (mk (SetPossState.σ s') ρ0 π0) HR0 Hcell Hlive).
    Qed.

    Lemma getTop_taken_post_entails_I t count l v nx ts b :
      ⊨ GetTopTakenPost t count l v nx ts b ==>> source_I.
    Proof.
      destruct b; simpl;
        [apply getTop_loop_entails_I | apply completed_entails_I].
    Qed.

    Lemma getTop_taken_post_stable t count l v nx ts b :
      AssertionsSingle.A.Stable (source_R t) source_I
        (GetTopTakenPost t count l v nx ts b).
    Proof.
      destruct b; simpl; [apply getTop_loop_stable | apply completed_stable].
    Qed.

    (** *** Transfer across the mem control (same heap and CAS value) *)

    Lemma getTop_scan_change_controls t count p w mc' cc' :
      GetTopScan t count p w ->
      mem_heap mc' = mem_heap (fst (SinglePossState.σ w)) ->
      cas_value cc' = cas_value (snd (SinglePossState.σ w)) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      GetTopScan t count p
        (mk (pair mc' cc') (SinglePossState.ρ w) (SinglePossState.π w)).
    Proof.
      intros [HI [Hlin Hdata]] Hheap Hcas Hmc Hcc.
      split; [exact (source_I_change_controls _ _ _ HI Hheap Hcas Hmc Hcc)|].
      split; [exact Hlin|].
      destruct Hdata as
        (saved & chain & suffix & prefix & H1 & H2 & H3 & H4 & H5 & H6).
      exists saved, chain, suffix, prefix. simpl. rewrite Hheap, Hcas.
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      split; [exact H4|]. split; [exact H5|]. exact H6.
    Qed.

    Lemma completed_change_controls t m ret w mc' cc' :
      Completed t m ret w ->
      mem_heap mc' = mem_heap (fst (SinglePossState.σ w)) ->
      cas_value cc' = cas_value (snd (SinglePossState.σ w)) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      Completed t m ret
        (mk (pair mc' cc') (SinglePossState.ρ w) (SinglePossState.π w)).
    Proof.
      intros [HI Hlin] Hheap Hcas Hmc Hcc.
      split; [exact (source_I_change_controls _ _ _ HI Hheap Hcas Hmc Hcc)|].
      exact Hlin.
    Qed.

    Lemma getTop_kind_change_controls t count l v nx ts w mc' cc' :
      GetTopKind t count l v nx ts w ->
      mem_heap mc' = mem_heap (fst (SinglePossState.σ w)) ->
      cas_value cc' = cas_value (snd (SinglePossState.σ w)) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      GetTopKind t count l v nx ts
        (mk (pair mc' cc') (SinglePossState.ρ w) (SinglePossState.π w)).
    Proof.
      intros [[Hscan Hcell] | Hcomp] Hheap Hcas Hmc Hcc.
      - left. split.
        + exact (getTop_scan_change_controls _ _ _ _ _ _ Hscan Hheap Hcas Hmc Hcc).
        + destruct Hcell as (ts' & taken & Hcell). exists ts', taken.
          simpl. rewrite Hheap. exact Hcell.
      - right. exact (completed_change_controls _ _ _ _ _ _ Hcomp Hheap Hcas Hmc Hcc).
    Qed.

    Lemma offslot_agree_refl q x : offslot_agree q x x.
    Proof. split; [reflexivity|]. split; intros; reflexivity. Qed.

    Lemma offslot_agree_sym q x y :
      offslot_agree q x y -> offslot_agree q y x.
    Proof.
      intros [Hσ [Hs Ht]]. split; [symmetry; exact Hσ|].
      split; intros r Hr; symmetry; auto.
    Qed.

    Lemma HasKind_change_σ (K : tid -> single_state -> Prop) q σ1 σ2 Δ :
      (forall σ1 σ2 ρ π, K q (mk σ1 ρ π) -> K q (mk σ2 ρ π)) ->
      HasKind K q (mks σ1 Δ) -> HasKind K q (mks σ2 Δ).
    Proof.
      intros Kσ HK ρ π Hposs.
      destruct (HK ρ π Hposs) as (ρ' & π' & Hposs' & Hoff & Hkind).
      exists ρ', π'. split; [exact Hposs'|]. split.
      - eapply offslot_agree_change_σ. exact Hoff.
      - eapply Kσ. exact Hkind.
    Qed.

    Lemma kind_lini_σ q σ1 σ2 ρ π :
      kind_lini q (mk σ1 ρ π) -> kind_lini q (mk σ2 ρ π).
    Proof. intros H. exact H. Qed.

    Lemma kind_linr_σ q σ1 σ2 ρ π :
      kind_linr q (mk σ1 ρ π) -> kind_linr q (mk σ2 ρ π).
    Proof. intros H. exact H. Qed.

    (** *** The completing step of a scanning possibility *)

    Lemma getTop_scan_facts t count l v ts taken nx σ s π :
      GetTopScan t count (Some l) (mk σ (Ready s) π) ->
      mem_heap (fst σ) l = Some (pair (pair (pair v ts) taken) nx) ->
      exists tl,
        linked (mem_heap (fst σ)) nx tl /\
        actual_snapshot t s =
          Some (pair (live_order (mem_heap (fst σ)) (l :: tl)) count) /\
        nodes s l = Some (pair v ts) /\
        TMap.find t π = Some (ls_lini (@lgetTop A)) /\
        exists chain prefix saved,
          linked (mem_heap (fst σ)) (fst (cas_value (snd σ))) chain /\
          chain = prefix ++ (l :: tl) /\
          TMap.find t (snapshot s) = Some (pair saved count) /\
          List.Forall (fun l => In l chain) saved /\
          List.filter (live_at (mem_heap (fst σ))) saved =
            live_order (mem_heap (fst σ)) (l :: tl).
    Proof.
      intros [HI [Hlin Hdata]] Hcell.
      destruct Hdata as
        (saved & chain & suffix & prefix & Hfull & Hsaved & Hsuffix &
         Hchain & Hforall & Hfilter).
      simpl in Hfull, Hsaved, Hsuffix, Hfilter.
      destruct HI as (mc & cc & s0 & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eρ. inversion Eρ; subst s0.
      destruct Hrep as
        (repchain & Hrepspatial & Hcount & Hlength & Hnodes & Horder).
      pose proof (HLinked_implies_linked _ _ _ Hrepspatial) as Hreplinked.
      simpl in Eσ. subst σ. simpl in *.
      assert (Erep : repchain = chain) by
        (eapply linked_deterministic; eauto).
      subst repchain.
      inversion Hsuffix as
        [|hd hv hts htaken hnext tl Hhead Htail Hfresh]; subst hd.
      subst suffix.
      rewrite Hcell in Hhead. inversion Hhead; subst hv hts htaken hnext.
      exists tl. split; [exact Htail|]. split.
      { eapply actual_snapshot_from_scan_data with
          (h := mem_heap mc) (top := fst (cas_value cc))
          (chain := chain) (saved := saved) (suffix := l :: tl); eauto. }
      split.
      { rewrite Hnodes. eapply linked_abstract_lookup; eauto.
        rewrite Hchain. apply in_or_app. right. now left. }
      split; [exact Hlin|].
      exists chain, prefix, saved. repeat split; auto.
    Qed.

    Lemma live_order_cons_live h l tl :
      live_at h l = true -> live_order h (l :: tl) = l :: live_order h tl.
    Proof. intros H. simpl. rewrite H. reflexivity. Qed.

    Lemma live_order_cons_dead h l tl :
      live_at h l = false -> live_order h (l :: tl) = live_order h tl.
    Proof. intros H. simpl. rewrite H. reflexivity. Qed.

    Lemma getTop_complete_step t count l v ts nx σ s π :
      GetTopScan t count (Some l) (mk σ (Ready s) π) ->
      mem_heap (fst σ) l = Some (pair (pair (pair v ts) false) nx) ->
      Step (li_lts F)
        (Build_ThreadEvent t
          (ResEv (@lgetTop A) (@inl (@LNode A) nat (pair (pair v ts) l))))
        (Ready s) (Ready (clear_snapshot t s)).
    Proof.
      intros Hscan Hcell.
      destruct (getTop_scan_facts _ _ _ _ _ _ _ _ _ _ Hscan Hcell)
        as (tl & Htail & Hactual & Habstract & _).
      eapply step_getTop_nonEmpty; [|exact Habstract].
      assert (Hlive : live_at (mem_heap (fst σ)) l = true).
      { unfold live_at, node_live. rewrite Hcell. reflexivity. }
      rewrite (live_order_cons_live _ _ _ Hlive) in Hactual. exact Hactual.
    Qed.

    Lemma getTop_empty_step t count l v ts σ s π :
      GetTopScan t count (Some l) (mk σ (Ready s) π) ->
      mem_heap (fst σ) l = Some (pair (pair (pair v ts) true) None) ->
      Step (li_lts F)
        (Build_ThreadEvent t
          (ResEv (@lgetTop A) (@inr (@LNode A) nat count)))
        (Ready s) (Ready (clear_snapshot t s)).
    Proof.
      intros Hscan Hcell.
      destruct (getTop_scan_facts _ _ _ _ _ _ _ _ _ _ Hscan Hcell)
        as (tl & Htail & Hactual & _).
      assert (Etl : tl = nil) by
        (eapply linked_deterministic; [exact Htail|constructor]).
      subst tl.
      eapply step_getTop_empty.
      assert (Hdead : live_at (mem_heap (fst σ)) l = false).
      { unfold live_at, node_live. rewrite Hcell. reflexivity. }
      rewrite (live_order_cons_dead _ _ _ Hdead) in Hactual. exact Hactual.
    Qed.

    Lemma getTop_shift_scan t count l v ts l' σ s π :
      GetTopScan t count (Some l) (mk σ (Ready s) π) ->
      mem_heap (fst σ) l = Some (pair (pair (pair v ts) true) (Some l')) ->
      GetTopScan t count (Some l') (mk σ (Ready s) π).
    Proof.
      intros Hscan Hcell. pose proof Hscan as [HI [Hlin _]].
      destruct (getTop_scan_facts _ _ _ _ _ _ _ _ _ _ Hscan Hcell)
        as (tl & Htail & Hactual & Habstract & _ &
            chain & prefix & saved & Hfull & Hchain & Hsaved & Hforall &
            Hfilter).
      split; [exact HI|]. split; [exact Hlin|].
      exists saved, chain, tl, (prefix ++ (l :: nil)). simpl.
      split; [exact Hfull|]. split; [exact Hsaved|].
      split; [exact Htail|].
      split; [rewrite Hchain, <- app_assoc; reflexivity|].
      split; [exact Hforall|].
      assert (Hdead : live_at (mem_heap (fst σ)) l = false).
      { unfold live_at, node_live. rewrite Hcell. reflexivity. }
      rewrite (live_order_cons_dead _ _ _ Hdead) in Hfilter. exact Hfilter.
    Qed.

    Lemma getTop_ret_completed t ret σ s π :
      source_I (mk σ (Ready s) π) ->
      TMap.find t π = Some (ls_lini (@lgetTop A)) ->
      Completed t (@lgetTop A) ret
        (mk σ (Ready (clear_snapshot t s))
          (TMap.add t (ls_linr (@lgetTop A) ret) π)).
    Proof.
      intros HI Hlin.
      destruct HI as (mc & cc & s0 & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eρ. inversion Eρ; subst s0.
      split.
      - exists mc, cc, (clear_snapshot t s). simpl.
        split; [exact Eσ|]. split; [reflexivity|].
        split; [exact Hmc|]. split; [exact Hcc|]. split.
        + destruct Hrep as (chain & H1 & H2 & H3 & H4 & H5).
          exists chain. simpl.
          split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
          split; [exact H4|]. exact H5.
        + eapply snapshot_consistent_getTop_res; eauto.
      - unfold ALin. simpl. rewrite TMap.gss. reflexivity.
    Qed.

    Lemma getTop_ret_G t ret mc cc mc' cc' s π :
      mem_heap mc' = mem_heap mc ->
      cas_value cc' = cas_value cc ->
      source_I (mk (pair mc cc) (Ready s) π) ->
      source_I (mk (pair mc' cc') (Ready (clear_snapshot t s))
        (TMap.add t (ls_linr (@lgetTop A) ret) π)) ->
      source_G t (mk (pair mc cc) (Ready s) π)
        (mk (pair mc' cc') (Ready (clear_snapshot t s))
          (TMap.add t (ls_linr (@lgetTop A) ret) π)).
    Proof.
      intros Hheap Hcas HI HI'.
      split; [exact HI|]. split; [exact HI'|].
      cbn [mk SinglePossState.σ SinglePossState.ρ SinglePossState.π fst snd].
      rewrite Hheap, Hcas.
      split; [apply heap_evol_refl|].
      split; [intros; reflexivity|].
      split.
      { unfold cas_evol.
        destruct (PositiveMap.E.eq_dec t owner) as [Heq|Hneq].
        - destruct HI as (mc0 & cc0 & s0 & Eσ & Eρ & _ & _ & Hrep & _).
          destruct Hrep as (chain & Hspatial & _).
          pose proof (HLinked_implies_linked _ _ _ Hspatial) as Hlinked.
          simpl in Eσ. inversion Eσ; subst mc0 cc0.
          exists chain, chain, nil. repeat split; auto.
        - reflexivity. }
      split.
      - intros q Hq. simpl. rewrite TMap.gro by exact Hq. reflexivity.
      - intros q Hq. simpl. rewrite TMap.gso by exact Hq. reflexivity.
    Qed.

    (** *** Configurations built by the window steps *)

    Definition ret_image_prop (Δ : @AbstractConfig (li_sig F) (li_lts F))
        (t : tid) (ret : Sig.ar (@lgetTop A))
        (Sel : tmap (@LinState (li_sig F)) -> Prop) :
        @AbstractConfigProp (li_sig F) (li_lts F) :=
      fun ρ' π' => exists s π, Δ (Ready s) π /\ Sel π /\
        ρ' = Ready (clear_snapshot t s) /\
        π' = TMap.add t (ls_linr (@lgetTop A) ret) π.

    Lemma ret_image_domain (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret (Sel : tmap (@LinState (li_sig F)) -> Prop) :
      (forall ρ π, Δ ρ π -> Sel π ->
        TMap.find t π = Some (ls_lini (@lgetTop A))) ->
      forall ρ' π', ret_image_prop Δ t ret Sel ρ' π' ->
        domain_equiv (map_domain π') (ac_active Δ).
    Proof.
      intros Hlini ρ' π' (s & π & Hposs & Hsel & _ & ->).
      eapply domain_equiv_trans; [|eapply ac_domain; exact Hposs].
      intros r. unfold map_domain.
      destruct (PositiveMap.E.eq_dec r t) as [->|Hrt].
      - rewrite TMap.gss, (Hlini _ _ Hposs Hsel).
        split; intros _; eexists; reflexivity.
      - rewrite TMap.gso by exact Hrt. reflexivity.
    Qed.

    Definition fork_prop (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret : @AbstractConfigProp (li_sig F) (li_lts F) :=
      fun ρ' π' => Δ ρ' π' \/ ret_image_prop Δ t ret (fun _ => True) ρ' π'.

    Lemma fork_nonempty (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret : exists ρ π, fork_prop Δ t ret ρ π.
    Proof.
      destruct (ac_nonempty Δ) as (ρ & π & H). exists ρ, π. left. exact H.
    Qed.

    Lemma fork_domain (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret
        (Hlini : forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_lini (@lgetTop A))) :
      forall ρ π, fork_prop Δ t ret ρ π ->
        domain_equiv (map_domain π) (ac_active Δ).
    Proof.
      intros ρ π [H | H]; [eapply ac_domain; exact H |].
      eapply ret_image_domain; [|exact H].
      intros ρ0 π0 Hposs _. exact (Hlini _ _ Hposs).
    Qed.

    Definition fork_config (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret Hlini : @AbstractConfig (li_sig F) (li_lts F) :=
      {| ac_active := ac_active Δ; ac_prop := fork_prop Δ t ret;
         ac_nonempty := fork_nonempty Δ t ret;
         ac_domain := fork_domain Δ t ret Hlini |}.

    Definition filter_prop (Δ : @AbstractConfig (li_sig F) (li_lts F)) (Sel : tmap (@LinState (li_sig F)) -> Prop) :
        @AbstractConfigProp (li_sig F) (li_lts F) :=
      fun ρ π => Δ ρ π /\ Sel π.

    Lemma filter_domain (Δ : @AbstractConfig (li_sig F) (li_lts F)) (Sel : tmap (@LinState (li_sig F)) -> Prop) :
      forall ρ π, filter_prop Δ Sel ρ π ->
        domain_equiv (map_domain π) (ac_active Δ).
    Proof. intros ρ π [H _]. eapply ac_domain; exact H. Qed.

    Definition filter_config (Δ : @AbstractConfig (li_sig F) (li_lts F)) (Sel : tmap (@LinState (li_sig F)) -> Prop)
        (Hne : exists ρ π, filter_prop Δ Sel ρ π) :
        @AbstractConfig (li_sig F) (li_lts F) :=
      {| ac_active := ac_active Δ; ac_prop := filter_prop Δ Sel;
         ac_nonempty := Hne; ac_domain := filter_domain Δ Sel |}.

    Definition ret_image_config (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret (Sel : tmap (@LinState (li_sig F)) -> Prop) Hlini
        (Hne : exists ρ' π', ret_image_prop Δ t ret Sel ρ' π') :
        @AbstractConfig (li_sig F) (li_lts F) :=
      {| ac_active := ac_active Δ; ac_prop := ret_image_prop Δ t ret Sel;
         ac_nonempty := Hne; ac_domain := ret_image_domain Δ t ret Sel Hlini |}.

    Lemma ret_image_offslot q t ret σ s π sy πy :
      q <> t ->
      offslot_agree q (mk σ (Ready s) π) (mk σ (Ready sy) πy) ->
      offslot_agree q
        (mk σ (Ready (clear_snapshot t s))
          (TMap.add t (ls_linr (@lgetTop A) ret) π))
        (mk σ (Ready (clear_snapshot t sy))
          (TMap.add t (ls_linr (@lgetTop A) ret) πy)).
    Proof.
      intros Hqt [_ [Hs Ht]]. split; [reflexivity|]. split.
      - intros r Hr. unfold slot_snapshot, payload_of. simpl.
        destruct (PositiveMap.E.eq_dec r t) as [->|Hrt].
        + rewrite !TMap.grs. reflexivity.
        + rewrite !TMap.gro by exact Hrt. exact (Hs r Hr).
      - intros r Hr. unfold slot_token. simpl.
        destruct (PositiveMap.E.eq_dec r t) as [->|Hrt].
        + rewrite !TMap.gss. reflexivity.
        + rewrite !TMap.gso by exact Hrt. exact (Ht r Hr).
    Qed.

    Lemma ret_image_offslot_orig t ret σ s π :
      offslot_agree t
        (mk σ (Ready (clear_snapshot t s))
          (TMap.add t (ls_linr (@lgetTop A) ret) π))
        (mk σ (Ready s) π).
    Proof.
      split; [reflexivity|]. split.
      - intros r Hr. unfold slot_snapshot, payload_of. simpl.
        rewrite TMap.gro by exact Hr. reflexivity.
      - intros r Hr. unfold slot_token. simpl.
        rewrite TMap.gso by exact Hr. reflexivity.
    Qed.

    Lemma ret_image_kind_linr t ret σ s π :
      kind_linr t
        (mk σ (Ready (clear_snapshot t s))
          (TMap.add t (ls_linr (@lgetTop A) ret) π)).
    Proof.
      exists (@lgetTop A), ret. unfold slot_token. simpl.
      rewrite TMap.gss. reflexivity.
    Qed.

    Lemma ret_image_token_other q t ret σ s π :
      q <> t ->
      slot_token q (mk σ (Ready (clear_snapshot t s))
        (TMap.add t (ls_linr (@lgetTop A) ret) π)) =
      slot_token q (mk σ (Ready s) π).
    Proof.
      intros Hq. unfold slot_token. simpl. rewrite TMap.gso by exact Hq.
      reflexivity.
    Qed.

    (** *** Errors *)

    Lemma getTop_value_no_error t count l :
      ⊨ GetTopScan t count (Some l) ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetValue l)))).
    Proof.
      intros w [HI [Hlin Hdata]] Herror.
      destruct Hdata as
        (saved & chain & suffix & prefix & Hfull & Hsaved & Hsuffix &
         Hchain & Hforall & Hfilter).
      destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
      simpl in Hsuffix. simpl in Herror. dependent destruction Herror.
      inversion Hsuffix; subst. simpl in *. congruence.
    Qed.

    Lemma getTop_next_no_error t count l v :
      ⊨ GetTopScanVal t count l v ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetNext l)))).
    Proof.
      intros w [_ [nx (ts & taken & Hcell) ]] Herror.
      destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
      simpl in Hcell. simpl in Herror. dependent destruction Herror.
      simpl in *. congruence.
    Qed.

    Lemma getTop_ts_no_error t count l v nx :
      ⊨ GetTopScanAt t count l v nx ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetTS l)))).
    Proof.
      intros w [_ (ts & taken & Hcell) ] Herror.
      destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
      simpl in Hcell. simpl in Herror. dependent destruction Herror.
      simpl in *. congruence.
    Qed.

    Lemma getTop_taken_no_error t count l v nx ts :
      ⊨ GetTopWindow t count l v nx ts ==>>
        AssertionsSet.A.ANoError
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetTaken l)))).
    Proof.
      intros s [_ [ (ts' & taken & Hcell) _] ] Herror.
      destruct (SetPossState.σ s) as [mc cc] eqn:Eσ.
      simpl in Hcell. simpl in Herror. dependent destruction Herror.
      simpl in *. congruence.
    Qed.

    (** *** Twins across the window steps *)

    Lemma filter_twins q t σ1 σ2 (Δ : @AbstractConfig (li_sig F) (li_lts F)) (Sel : tmap (@LinState (li_sig F)) -> Prop) Hne :
      q <> t ->
      (forall π π', TMap.find t π = TMap.find t π' -> Sel π -> Sel π') ->
      twins_preserved q (mks σ1 Δ) (mks σ2 (filter_config Δ Sel Hne)).
    Proof.
      intros Hq Hsel.
      assert (Hgen : forall K : tid -> single_state -> Prop,
        (forall x y, slot_token q x = slot_token q y -> K q x -> K q y) ->
        HasKind K q (mks σ1 Δ) ->
        HasKind K q (mks σ2 (filter_config Δ Sel Hne))).
      { intros K Ktok HK ρ π [Hposs Hlin].
        destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & Hoff & Hkind).
        exists ρy, πy. split.
        - split; [exact Hpossy|]. destruct Hoff as [_ [_ Ht]].
          apply (Hsel π πy); [|exact Hlin].
          exact (Ht t (fun Heq => Hq (eq_sym Heq))).
        - split; [eapply offslot_agree_change_σ; exact Hoff|].
          eapply Ktok; [|exact Hkind]. reflexivity. }
      split.
      - intros HK. exact (Hgen kind_lini (kind_lini_token q) HK).
      - intros HK. exact (Hgen kind_linr (kind_linr_token q) HK).
    Qed.

    Lemma ret_image_twins q t ret σ1 σ2 (Δ : @AbstractConfig (li_sig F) (li_lts F)) (Sel : tmap (@LinState (li_sig F)) -> Prop) Hlini Hne :
      q <> t ->
      (forall ρ π, Δ ρ π -> exists s, ρ = Ready s) ->
      (forall π π', TMap.find t π = TMap.find t π' -> Sel π -> Sel π') ->
      twins_preserved q (mks σ1 Δ)
        (mks σ2 (ret_image_config Δ t ret Sel Hlini Hne)).
    Proof.
      intros Hq Hready Hsel.
      assert (Hgen : forall K : tid -> single_state -> Prop,
        (forall x y, slot_token q x = slot_token q y -> K q x -> K q y) ->
        HasKind K q (mks σ1 Δ) ->
        HasKind K q (mks σ2 (ret_image_config Δ t ret Sel Hlini Hne))).
      { intros K Ktok HK ρ' π' (s & π & Hposs & Hlin & -> & ->).
        destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & Hoff & Hkind).
        destruct (Hready _ _ Hpossy) as [sy ->].
        exists (Ready (clear_snapshot t sy)),
          (TMap.add t (ls_linr (@lgetTop A) ret) πy).
        split.
        - exists sy, πy. split; [exact Hpossy|]. split.
          + destruct Hoff as [_ [_ Ht]]. apply (Hsel π πy); [|exact Hlin].
            exact (Ht t (fun Heq => Hq (eq_sym Heq))).
          + split; reflexivity.
        - split.
          + apply ret_image_offslot; [exact Hq|].
            eapply offslot_agree_change_σ; exact Hoff.
          + eapply Ktok; [|exact Hkind]. unfold slot_token. simpl.
            rewrite TMap.gso by exact Hq. reflexivity. }
      split.
      - intros HK. exact (Hgen kind_lini (kind_lini_token q) HK).
      - intros HK. exact (Hgen kind_linr (kind_linr_token q) HK).
    Qed.

    Lemma fork_twins q t ret σ1 σ2 (Δ : @AbstractConfig (li_sig F) (li_lts F)) Hlini :
      q <> t ->
      (forall ρ π, Δ ρ π -> exists s, ρ = Ready s) ->
      twins_preserved q (mks σ1 Δ) (mks σ2 (fork_config Δ t ret Hlini)).
    Proof.
      intros Hq Hready.
      assert (Hgen : forall K : tid -> single_state -> Prop,
        (forall x y, slot_token q x = slot_token q y -> K q x -> K q y) ->
        HasKind K q (mks σ1 Δ) ->
        HasKind K q (mks σ2 (fork_config Δ t ret Hlini))).
      { intros K Ktok HK ρ' π' [Hposs | (s & π & Hposs & _ & -> & ->) ].
        - destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & Hoff & Hkind).
          exists ρy, πy. split; [left; exact Hpossy|].
          split; [eapply offslot_agree_change_σ; exact Hoff|].
          eapply Ktok; [|exact Hkind]. reflexivity.
        - destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & Hoff & Hkind).
          destruct (Hready _ _ Hpossy) as [sy ->].
          exists (Ready (clear_snapshot t sy)),
            (TMap.add t (ls_linr (@lgetTop A) ret) πy).
          split.
          + right. exists sy, πy. split; [exact Hpossy|].
            split; [exact I|]. split; reflexivity.
          + split.
            * apply ret_image_offslot; [exact Hq|].
              eapply offslot_agree_change_σ; exact Hoff.
            * eapply Ktok; [|exact Hkind]. unfold slot_token. simpl.
              rewrite TMap.gso by exact Hq. reflexivity. }
      split.
      - intros HK. exact (Hgen kind_lini (kind_lini_token q) HK).
      - intros HK. exact (Hgen kind_linr (kind_linr_token q) HK).
    Qed.

    Lemma source_I_ready_ex w :
      source_I w -> exists s, SinglePossState.ρ w = Ready s.
    Proof. intros HI. eexists. exact (source_I_ready _ HI). Qed.

    (** *** Updates of the per-field reads *)

    Lemma getTop_value_inv_update t count l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetValue l))))
        (GetTopScan t count (Some l)) (GetTopScan t count (Some l)).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      pose proof (proj1 Hpre) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      pose proof (getTop_scan_change_controls _ _ _ _
        (Pending s3 t0 (nmgetValue l0)) s2 Hpre eq_refl eq_refl I Hcc) as Hpost.
      pose proof (proj1 Hpost) as HIpost.
      split; [exact Hpost|].
      eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getTop_value_res_update t count l v :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmgetValue l)) v))
        (GetTopScan t count (Some l)) (GetTopScanVal t count l v).
    Proof.
      pupdate_intros_atomic.
      match goal with H : s3 l0 = Some _ |- _ => rename H into Hconcrete end.
      pupdate_finish.
      pose proof (proj1 Hpre) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      pose proof (getTop_scan_change_controls _ _ _ _
        (Idle s3) s2 Hpre eq_refl eq_refl I Hcc) as Hpost.
      pose proof (proj1 Hpost) as HIpost.
      split.
      - split; [exact Hpost|]. do 3 eexists. exact Hconcrete.
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getTop_next_inv_update t count l v :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetNext l))))
        (GetTopScanVal t count l v) (GetTopScanVal t count l v).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      destruct Hpre as [Hscan [nx Hcell]].
      pose proof (proj1 Hscan) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      pose proof (getTop_scan_change_controls _ _ _ _
        (Pending s3 t0 (nmgetNext l0)) s2 Hscan eq_refl eq_refl I Hcc) as Hpost.
      pose proof (proj1 Hpost) as HIpost.
      split.
      - split; [exact Hpost|]. exists nx. exact Hcell.
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getTop_next_res_update t count l v nx :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmgetNext l)) nx))
        (GetTopScanVal t count l v) (GetTopScanAt t count l v nx).
    Proof.
      pupdate_intros_atomic.
      match goal with H : s3 l0 = Some _ |- _ => rename H into Hconcrete end.
      pupdate_finish.
      destruct Hpre as [Hscan [nx0 (ts0 & tk0 & Hcell0) ]]. simpl in Hcell0.
      rewrite Hcell0 in Hconcrete. injection Hconcrete as Hv Hts Htk Hnx.
      rewrite Hnx in Hcell0.
      pose proof (proj1 Hscan) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      pose proof (getTop_scan_change_controls _ _ _ _
        (Idle s3) s2 Hscan eq_refl eq_refl I Hcc) as Hpost.
      pose proof (proj1 Hpost) as HIpost.
      split.
      - split; [exact Hpost|]. do 2 eexists. exact Hcell0.
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getTop_ts_inv_update t count l v nx :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetTS l))))
        (GetTopScanAt t count l v nx) (GetTopScanAt t count l v nx).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      destruct Hpre as [Hscan Hcell].
      pose proof (proj1 Hscan) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      pose proof (getTop_scan_change_controls _ _ _ _
        (Pending s3 t0 (nmgetTS l0)) s2 Hscan eq_refl eq_refl I Hcc) as Hpost.
      pose proof (proj1 Hpost) as HIpost.
      split.
      - split; [exact Hpost|]. exact Hcell.
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    (** The timestamp read: every scanning possibility whose node is still
        untaken forks a possibility in which [getTop] has returned it. *)
    Lemma getTop_ts_res_update t count l v nx ts :
      AssertionsSet.PUpdate (G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmgetTS l)) ts))
        (lift_assert (GetTopScanAt t count l v nx))
        (GetTopWindow t count l v nx ts).
    Proof.
      AssertionsSet.pupdate_intros_atomic.
      match goal with H : s3 l0 = Some _ |- _ => rename H into Hconcrete end.
      match goal with
      | |- context [GetTopWindow _ _ _ _ _ ?tss] => pose (TS := tss)
      end.
      pose (RET := @inl (@LNode A) nat (pair (pair v TS) l0)).
      destruct (ac_nonempty Δ1) as (ρ0 & π0 & Hposs0).
      destruct (Hpre _ _ Hposs0) as [_ (ts' & tk & Hc) ]. simpl in Hc.
      rewrite Hc in Hconcrete. injection Hconcrete as Hv Hts Htk Hnx.
      rewrite Hts in Hc. clear Hv Hts Htk Hnx ts'.
      assert (Hlini : forall ρ π, Δ1 ρ π ->
        TMap.find t0 π = Some (ls_lini (@lgetTop A))).
      { intros ρ π Hposs. destruct (Hpre _ _ Hposs) as [[_ [Hlin _]] _].
        exact Hlin. }
      assert (HIpre : forall ρ π, Δ1 ρ π ->
        source_I (mk (pair (Pending s3 t0 (nmgetTS l0)) s2) ρ π)).
      { intros ρ π Hposs. exact (proj1 (proj1 (Hpre _ _ Hposs))). }
      assert (Hready : forall ρ π, Δ1 ρ π -> exists s, ρ = Ready s).
      { intros ρ π Hposs. exact (source_I_ready_ex _ (HIpre _ _ Hposs)). }
      assert (Hcc : cas_control_ok s2).
      { exact (source_I_cas_control _ (HIpre _ _ Hposs0)). }
      assert (HpostA : forall ρ π, Δ1 ρ π ->
        GetTopScanAt t0 count l0 v nx (mk (pair (Idle s3) s2) ρ π)).
      { intros ρ π Hposs. destruct (Hpre _ _ Hposs) as [Hscan Hcell]. split.
        - exact (getTop_scan_change_controls _ _ _ _ (Idle s3) s2 Hscan
            eq_refl eq_refl I Hcc).
        - destruct Hcell as (a & b & Hcell). exists a, b. exact Hcell. }
      assert (HIpost : forall ρ π, Δ1 ρ π -> source_I (mk (pair (Idle s3) s2) ρ π)).
      { intros ρ π Hposs. exact (proj1 (proj1 (HpostA _ _ Hposs))). }
      assert (Gsame : forall ρ π, Δ1 ρ π ->
        source_G t0 (mk (pair (Pending s3 t0 (nmgetTS l0)) s2) ρ π)
          (mk (pair (Idle s3) s2) ρ π)).
      { intros ρ π Hposs. apply source_G_same_payload; simpl; auto. }
      destruct tk.
      - (* already taken: no fork *)
        exists Δ1. split; [apply ac_steps_refl|]. split.
        + split; [|split; [|split]].
          * intros ρ π Hposs. left. exact (HpostA _ _ Hposs).
          * exists TS, true. exact Hc.
          * intros ρ π Hposs. exists ρ, π. split; [exact Hposs|].
            split; [apply offslot_agree_refl|].
            exists (@lgetTop A). exact (Hlini _ _ Hposs).
          * intros Hlive. exfalso. unfold live_at, node_live in Hlive.
            simpl in Hlive. rewrite Hc in Hlive. discriminate.
        + split.
          * intros ρ π Hposs. exists ρ, π. split; [exact Hposs|].
            exact (Gsame _ _ Hposs).
          * intros q _. apply twins_preserved_refl.
      - (* untaken: fork *)
        assert (Hcomplete : forall s π, Δ1 (Ready s) π ->
          Step (li_lts F)
            (Build_ThreadEvent t0 (ResEv (@lgetTop A) RET))
            (Ready s) (Ready (clear_snapshot t0 s))).
        { intros s π Hposs. destruct (Hpre _ _ Hposs) as [Hscan _].
          eapply getTop_complete_step; [exact Hscan | exact Hc]. }
        assert (HpostB : forall s π, Δ1 (Ready s) π ->
          Completed t0 (@lgetTop A) RET
            (mk (pair (Idle s3) s2) (Ready (clear_snapshot t0 s))
              (TMap.add t0 (ls_linr (@lgetTop A) RET) π))).
        { intros s π Hposs.
          apply getTop_ret_completed; [exact (HIpost _ _ Hposs) | exact (Hlini _ _ Hposs) ]. }
        exists (fork_config Δ1 t0 RET Hlini).
        split; [|split].
        + intros ρ' π' [Hposs | (s & π & Hposs & _ & -> & ->) ].
          * apply ac_steps_refl. exact Hposs.
          * econstructor; [exact Hposs|]. apply rt_step.
            eapply ps_ret; [exact (Hcomplete _ _ Hposs) | exact (Hlini _ _ Hposs) ].
        + split; [|split; [|split]].
          * intros ρ' π' [Hposs | (s & π & Hposs & _ & -> & ->) ].
            -- left. exact (HpostA _ _ Hposs).
            -- right. exact (HpostB _ _ Hposs).
          * exists TS, false. exact Hc.
          * intros ρ' π' [Hposs | (s & π & Hposs & _ & -> & ->) ].
            -- exists ρ', π'. split; [left; exact Hposs|].
               split; [apply offslot_agree_refl|].
               exists (@lgetTop A). exact (Hlini _ _ Hposs).
            -- exists (Ready s), π. split; [left; exact Hposs|].
               split; [apply ret_image_offslot_orig|].
               exists (@lgetTop A). exact (Hlini _ _ Hposs).
          * intros _ ρ' π' [Hposs | (s & π & Hposs & _ & -> & ->) ].
            -- destruct (Hready _ _ Hposs) as [s ->].
               exists (Ready (clear_snapshot t0 s)),
                 (TMap.add t0 (ls_linr (@lgetTop A) RET) π').
               split.
               ++ right. exists s, π'. split; [exact Hposs|].
                  split; [exact I|]. split; reflexivity.
               ++ split; [apply offslot_agree_sym, ret_image_offslot_orig |
                          apply ret_image_kind_linr].
            -- exists (Ready (clear_snapshot t0 s)),
                 (TMap.add t0 (ls_linr (@lgetTop A) RET) π).
               split.
               ++ right. exists s, π. split; [exact Hposs|].
                  split; [exact I|]. split; reflexivity.
               ++ split; [apply offslot_agree_refl | apply ret_image_kind_linr].
        + split.
          * intros ρ' π' [Hposs | (s & π & Hposs & _ & -> & ->) ].
            -- exists ρ', π'. split; [exact Hposs|]. exact (Gsame _ _ Hposs).
            -- exists (Ready s), π. split; [exact Hposs|].
               apply getTop_ret_G; [reflexivity | reflexivity |
                 exact (HIpre _ _ Hposs) | exact (proj1 (HpostB _ _ Hposs)) ].
          * intros q Hq. apply fork_twins; [exact Hq | exact Hready].
    Qed.

    Lemma getTop_taken_inv_update t count l v nx ts :
      AssertionsSet.PUpdate (G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetTaken l))))
        (GetTopWindow t count l v nx ts) (GetTopWindow t count l v nx ts).
    Proof.
      AssertionsSet.pupdate_intros_atomic.
      destruct Hpre as [Hkinds [Hcell [Hlini Hlinr]]].
      destruct (ac_nonempty Δ1) as (ρ0 & π0 & Hposs0).
      assert (Hcc : cas_control_ok s2).
      { exact (source_I_cas_control _
          (getTop_kind_entails_I _ _ _ _ _ _ _ (Hkinds _ _ Hposs0))). }
      assert (Hkinds' : forall ρ π, Δ1 ρ π ->
        GetTopKind t0 count l0 v nx ts (mk (pair (Pending s3 t0 (nmgetTaken l0)) s2) ρ π)).
      { intros ρ π Hposs.
        exact (getTop_kind_change_controls _ _ _ _ _ _ _
          (Pending s3 t0 (nmgetTaken l0)) s2 (Hkinds _ _ Hposs)
          eq_refl eq_refl I Hcc). }
      exists Δ1. split; [apply ac_steps_refl|]. split.
      - split; [|split; [|split]].
        + intros ρ π Hposs. exact (Hkinds' _ _ Hposs).
        + exact Hcell.
        + exact (HasKind_change_σ kind_lini t0 (pair (Idle s3) s2)
            (pair (Pending s3 t0 (nmgetTaken l0)) s2) Δ1 (kind_lini_σ t0) Hlini).
        + intros Hlive.
          apply (HasKind_change_σ kind_linr t0 (pair (Idle s3) s2)
            (pair (Pending s3 t0 (nmgetTaken l0)) s2) Δ1 (kind_linr_σ t0)).
          apply Hlinr. exact Hlive.
      - split.
        + intros ρ π Hposs. exists ρ, π. split; [exact Hposs|].
          apply source_G_same_payload; simpl; auto.
          * exact (getTop_kind_entails_I _ _ _ _ _ _ _ (Hkinds _ _ Hposs)).
          * exact (getTop_kind_entails_I _ _ _ _ _ _ _ (Hkinds' _ _ Hposs)).
        + intros q _. apply twins_preserved_refl.
    Qed.

    (** The taken read: a [false] flag keeps the returned possibilities,
        a [true] flag keeps the scanning ones (and completes them with
        the empty result when the node was the last one). *)
    Lemma getTop_taken_res_update t count l v nx ts b :
      AssertionsSet.PUpdate (G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmgetTaken l)) b))
        (GetTopWindow t count l v nx ts)
        (lift_assert (GetTopTakenPost t count l v nx ts b)).
    Proof.
      AssertionsSet.pupdate_intros_atomic.
      match goal with H : s3 l0 = Some _ |- _ => rename H into Hconcrete end.
      destruct Hpre as [Hkinds [Hcell [Hlini Hlinr]]].
      simpl in Hcell. destruct Hcell as (ts' & tk & Hc). simpl in Hc.
      rewrite Hc in Hconcrete. injection Hconcrete as Hv Hts Htk Hnx.
      subst tk. clear Hv Hts Hnx.
      pose (RET := @inl (@LNode A) nat (pair (pair v ts) l0)).
      destruct (ac_nonempty Δ1) as (ρ0 & π0 & Hposs0).
      assert (HIpre : forall ρ π, Δ1 ρ π ->
        source_I (mk (pair (Pending s3 t0 (nmgetTaken l0)) s2) ρ π)).
      { intros ρ π Hposs.
        exact (getTop_kind_entails_I _ _ _ _ _ _ _ (Hkinds _ _ Hposs)). }
      assert (Hcc : cas_control_ok s2).
      { exact (source_I_cas_control _ (HIpre _ _ Hposs0)). }
      assert (HIpost : forall ρ π, Δ1 ρ π -> source_I (mk (pair (Idle s3) s2) ρ π)).
      { intros ρ π Hposs.
        exact (source_I_change_controls _ (Idle s3) s2 (HIpre _ _ Hposs)
          eq_refl eq_refl I Hcc). }
      assert (Hready : forall ρ π, Δ1 ρ π -> exists s, ρ = Ready s).
      { intros ρ π Hposs. exact (source_I_ready_ex _ (HIpre _ _ Hposs)). }
      assert (Gsame : forall ρ π, Δ1 ρ π ->
        source_G t0 (mk (pair (Pending s3 t0 (nmgetTaken l0)) s2) ρ π)
          (mk (pair (Idle s3) s2) ρ π)).
      { intros ρ π Hposs. apply source_G_same_payload; simpl; auto. }
      assert (HkindA : forall ρ π, Δ1 ρ π ->
        TMap.find t0 π = Some (ls_lini (@lgetTop A)) ->
        GetTopScanAt t0 count l0 v nx (mk (pair (Pending s3 t0 (nmgetTaken l0)) s2) ρ π)).
      { intros ρ π Hposs Hlin.
        destruct (Hkinds _ _ Hposs) as [HA | [_ HB]]; [exact HA|].
        unfold ALin in HB. simpl in HB.
        pose proof (eq_trans (eq_sym Hlin) HB) as Habs. discriminate Habs. }
      assert (HkindB : forall ρ π, Δ1 ρ π ->
        (exists f r, TMap.find t0 π = Some (ls_linr f r)) ->
        Completed t0 (@lgetTop A) RET
          (mk (pair (Pending s3 t0 (nmgetTaken l0)) s2) ρ π)).
      { intros ρ π Hposs (f & r & Hlin).
        destruct (Hkinds _ _ Hposs) as [[[_ [HA _]] _] | HB]; [|exact HB].
        unfold ALin in HA. simpl in HA.
        pose proof (eq_trans (eq_sym Hlin) HA) as Habs. discriminate Habs. }
      match goal with
      | |- context [GetTopTakenPost _ _ _ _ _ _ ?bb] => destruct bb
      end.
      - (* taken: keep the scanning possibilities *)
        assert (Hne : exists ρ π,
          filter_prop Δ1 (fun π => TMap.find t0 π = Some (ls_lini (@lgetTop A))) ρ π).
        { destruct (Hlini _ _ Hposs0) as (ρ1 & π1 & Hposs1 & _ & [f Hf]).
          unfold slot_token in Hf. simpl in Hf.
          destruct (Hkinds _ _ Hposs1) as [[[_ [HA _]] _] | [_ HB]].
          - exists ρ1, π1. split; [exact Hposs1|]. exact HA.
          - unfold ALin in HB. simpl in HB.
            pose proof (eq_trans (eq_sym Hf) HB) as Habs. discriminate Habs. }
        match goal with
        | |- context [GetTopTakenPost _ _ _ _ ?nn _ _] => destruct nn as [l'|]
        end.
        + (* there is a next node: shift the scan *)
          exists (filter_config Δ1 _ Hne). split; [|split].
          * intros ρ π [Hposs _]. apply ac_steps_refl. exact Hposs.
          * intros ρ π [Hposs Hlin]. simpl.
            destruct (Hready _ _ Hposs) as [s ->].
            destruct (HkindA _ _ Hposs Hlin) as [Hscan _].
            pose proof (getTop_shift_scan _ _ _ _ _ _ _ _ _ Hscan Hc) as Hshift.
            exact (getTop_scan_change_controls _ _ _ _ (Idle s3) s2 Hshift
              eq_refl eq_refl I Hcc).
          * split.
            -- intros ρ π [Hposs _]. exists ρ, π. split; [exact Hposs|].
               exact (Gsame _ _ Hposs).
            -- intros q Hq. apply (filter_twins q t0); [exact Hq|].
               intros π π' Heq Hsel. exact (eq_trans (eq_sym Heq) Hsel).
        + (* the node was the last one: the list is empty *)
          assert (Hlini' : forall ρ π, Δ1 ρ π ->
            TMap.find t0 π = Some (ls_lini (@lgetTop A)) ->
            TMap.find t0 π = Some (ls_lini (@lgetTop A))).
          { intros ρ π _ H. exact H. }
          assert (Hne' : exists ρ' π',
            ret_image_prop Δ1 t0 (@inr (@LNode A) nat count)
              (fun π => TMap.find t0 π = Some (ls_lini (@lgetTop A))) ρ' π').
          { destruct Hne as (ρ1 & π1 & Hposs1 & Hlin1).
            destruct (Hready _ _ Hposs1) as [s1 ->].
            exists (Ready (clear_snapshot t0 s1)),
              (TMap.add t0 (ls_linr (@lgetTop A) (@inr (@LNode A) nat count)) π1).
            exists s1, π1. split; [exact Hposs1|]. split; [exact Hlin1|].
            split; reflexivity. }
          exists (ret_image_config Δ1 t0 (@inr (@LNode A) nat count) _ Hlini' Hne').
          split; [|split].
          * intros ρ' π' (s & π & Hposs & Hlin & -> & ->).
            econstructor; [exact Hposs|]. apply rt_step.
            eapply ps_ret; [|exact Hlin].
            destruct (HkindA _ _ Hposs Hlin) as [Hscan _].
            eapply getTop_empty_step; [exact Hscan | exact Hc].
          * intros ρ' π' (s & π & Hposs & Hlin & -> & ->). simpl.
            exact (getTop_ret_completed t0 (@inr (@LNode A) nat count)
              (pair (Idle s3) s2) s π (HIpost _ _ Hposs) Hlin).
          * split.
            -- intros ρ' π' (s & π & Hposs & Hlin & -> & ->).
               exists (Ready s), π. split; [exact Hposs|].
               apply getTop_ret_G; [reflexivity | reflexivity |
                 exact (HIpre _ _ Hposs) |].
               exact (proj1 (getTop_ret_completed t0 (@inr (@LNode A) nat count)
                 (pair (Idle s3) s2) s π (HIpost _ _ Hposs) Hlin)).
            -- intros q Hq. apply ret_image_twins; [exact Hq | exact Hready |].
               intros π π' Heq Hsel. exact (eq_trans (eq_sym Heq) Hsel).
      - (* untaken: keep the returned possibilities *)
        assert (Hlive : live_at (mem_heap (fst
            (SetPossState.σ (mks (pair (Pending s3 t0 (nmgetTaken l0)) s2) Δ1)))) l0 = true).
        { unfold live_at, node_live. simpl. rewrite Hc. reflexivity. }
        assert (Hne : exists ρ π,
          filter_prop Δ1 (fun π => exists f r, TMap.find t0 π = Some (ls_linr f r)) ρ π).
        { destruct (Hlinr Hlive _ _ Hposs0) as (ρ1 & π1 & Hposs1 & _ & Hk).
          exists ρ1, π1. split; [exact Hposs1|]. exact Hk. }
        exists (filter_config Δ1 _ Hne). split; [|split].
        + intros ρ π [Hposs _]. apply ac_steps_refl. exact Hposs.
        + intros ρ π [Hposs Hlin]. simpl.
          exact (completed_change_controls _ _ _ _ (Idle s3) s2
            (HkindB _ _ Hposs Hlin) eq_refl eq_refl I Hcc).
        + split.
          * intros ρ π [Hposs _]. exists ρ, π. split; [exact Hposs|].
            exact (Gsame _ _ Hposs).
          * intros q Hq. apply (filter_twins q t0); [exact Hq|].
            intros π π' Heq (f & r & Hsel). exists f, r.
            exact (eq_trans (eq_sym Heq) Hsel).
    Qed.

    (** *** The [getTop] triple *)

    Lemma getTop_triple t :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t (@lgetTop A) }}
          (@SPListImpl.getTop_impl A t)
        {{ fun ret => SCompleted t (@lgetTop A) ret }}.
    Proof.
      unfold SPListImpl.getTop_impl.
      eapply singleton_provable_vis_safe with
        (P' := Active t (@lgetTop A))
        (Q' := fun q => GetTopLoop t (snd q) (fst q)).
      - intros w Hpre Herror.
        destruct (SinglePossState.σ w) as [mc cc]. simpl in Herror.
        dependent destruction Herror.
      - apply active_entails_I.
      - intros q. apply getTop_loop_entails_I.
      - apply active_stable.
      - intros q. apply getTop_loop_stable.
      - apply getTop_get_inv_update.
      - intros q. apply getTop_get_res_update.
      - intros [top count]. simpl.
        eapply SetLogic.provable_doloop_data with
          (Iloop := fun p => SGetTopLoop t count p)
          (Q := fun ret => SCompleted t (@lgetTop A) ret).
        + intros ret w Hcompleted.
          eapply lift_impl; [apply completed_entails_I|exact Hcompleted].
        + intros ret. apply lift_stable. apply completed_stable.
        + intros p. destruct p as [l|]; simpl.
          * unfold SGetTopLoop, GetTopLoop. simpl.
            eapply SetLogic.provable_conseq_weak_post with
              (Q' := fun r => lift_assert (GetTopBodyPost t count r)).
            -- intros [p|ret]; unfold GetTopBodyPost; simpl.
               ++ intros w Hpost. eapply lift_impl;
                    [apply getTop_loop_entails_I|exact Hpost].
               ++ intros w Hpost. eapply lift_impl;
                    [apply completed_entails_I|exact Hpost].
            -- intros [p|ret]; simpl.
               ++ apply lift_stable. apply getTop_loop_stable.
               ++ apply lift_stable. apply completed_stable.
            -- intros [p|ret]; unfold GetTopBodyPost; simpl.
               ++ unfold SGetTopLoop. intros w Hpost. exact Hpost.
               ++ unfold SCompleted. intros w Hpost. exact Hpost.
            -- (* value read *)
               eapply singleton_provable_vis_safe with
                 (P' := GetTopScan t count (Some l))
                 (Q' := fun v => GetTopScanVal t count l v).
               ++ apply getTop_value_no_error.
               ++ apply getTop_scan_entails_I.
               ++ intros v. apply getTop_scan_val_entails_I.
               ++ apply getTop_scan_stable.
               ++ intros v. apply getTop_scan_val_stable.
               ++ apply getTop_value_inv_update.
               ++ intros v. apply getTop_value_res_update.
               ++ intros v. (* next read *)
                  eapply singleton_provable_vis_safe with
                    (P' := GetTopScanVal t count l v)
                    (Q' := fun nx => GetTopScanAt t count l v nx).
                  ** apply getTop_next_no_error.
                  ** apply getTop_scan_val_entails_I.
                  ** intros nx. apply getTop_scan_at_entails_I.
                  ** apply getTop_scan_val_stable.
                  ** intros nx. apply getTop_scan_at_stable.
                  ** apply getTop_next_inv_update.
                  ** intros nx. apply getTop_next_res_update.
                  ** intros nx. (* timestamp read: fork *)
                     eapply SetLogic.provable_vis_safe with
                       (P' := lift_assert (GetTopScanAt t count l v nx))
                       (Q' := fun ts => GetTopWindow t count l v nx ts).
                     --- intros s HP. eapply lift_no_error;
                           [apply getTop_ts_no_error | exact HP].
                     --- intros s HP. eapply lift_impl;
                           [apply getTop_scan_at_entails_I | exact HP].
                     --- intros ts. apply getTop_window_entails_I.
                     --- apply lift_stable. apply getTop_scan_at_stable.
                     --- intros ts. apply getTop_window_stable.
                     --- apply lift_pupdate.
                         +++ apply getTop_scan_at_entails_I.
                         +++ apply getTop_scan_at_entails_I.
                         +++ apply slot_local_getTop_scan_at.
                         +++ apply getTop_ts_inv_update.
                     --- intros ts. apply getTop_ts_res_update.
                     --- intros ts. (* taken read: drop *)
                         eapply SetLogic.provable_vis_safe with
                           (P' := GetTopWindow t count l v nx ts)
                           (Q' := fun b =>
                             lift_assert (GetTopTakenPost t count l v nx ts b)).
                         +++ apply getTop_taken_no_error.
                         +++ apply getTop_window_entails_I.
                         +++ intros b s HQ. eapply lift_impl;
                               [apply getTop_taken_post_entails_I | exact HQ].
                         +++ apply getTop_window_stable.
                         +++ intros b. apply lift_stable.
                             apply getTop_taken_post_stable.
                         +++ apply getTop_taken_inv_update.
                         +++ intros b. apply getTop_taken_res_update.
                         +++ intros b. destruct b.
                             *** unfold GetTopTakenPost. singleton_ret_safe.
                                 ---- intros w H. exact H.
                                 ---- apply getTop_loop_entails_I.
                                 ---- apply getTop_loop_stable.
                             *** unfold GetTopTakenPost. singleton_ret_safe.
                                 ---- intros w H. exact H.
                                 ---- apply completed_entails_I.
                                 ---- apply completed_stable.
                  ** apply getTop_scan_val_entails_I.
                  ** apply slot_local_getTop_scan_val.
                  ** intros nx. apply slot_local_getTop_scan_at.
               ++ apply getTop_scan_entails_I.
               ++ apply slot_local_getTop_scan.
               ++ intros v. apply slot_local_getTop_scan_val.
          * unfold SGetTopLoop, GetTopLoop. simpl.
            eapply SetLogic.provable_conseq_weak_post with
              (Q' := fun r => lift_assert (GetTopBodyPost t count r)).
            -- intros [p|ret]; unfold GetTopBodyPost; simpl.
               ++ intros w Hpost. eapply lift_impl;
                    [apply getTop_loop_entails_I|exact Hpost].
               ++ intros w Hpost. eapply lift_impl;
                    [apply completed_entails_I|exact Hpost].
            -- intros [p|ret]; simpl.
               ++ apply lift_stable. apply getTop_loop_stable.
               ++ apply lift_stable. apply completed_stable.
            -- intros [p|ret]; unfold GetTopBodyPost; simpl.
               ++ unfold SGetTopLoop. intros w Hpost. exact Hpost.
               ++ unfold SCompleted. intros w Hpost. exact Hpost.
            -- unfold GetTopBodyPost. simpl. singleton_ret_safe.
               ++ apply ImplRefl.
               ++ apply completed_entails_I.
               ++ apply completed_stable.
      - apply active_entails_I.
      - apply slot_local_active.
      - intros q. apply slot_local_getTop_loop.
    Qed.

    Lemma initial_represents :
      represents (@empty_heap (@Node A)) None 0
        (@SPListImpl.empty_splist_state A).
    Proof.
      exists nil. split; [constructor|].
      split; [reflexivity|].
      split; [reflexivity|].
      split.
      - apply functional_extensionality. intro l.
        unfold empty_heap, abstract_nodes. simpl. reflexivity.
      - reflexivity.
    Qed.

    Lemma initial_snapshot_consistent :
      snapshot_consistent (@SPListImpl.empty_splist_state A)
        (@TMap.empty (@LinState (li_sig F))).
    Proof.
      intros t. simpl. rewrite TMap.gempty, TMap.gempty.
      split; [intros [? H]; discriminate|discriminate].
    Qed.

    Lemma initial_source_I :
      source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (li_init E) (li_init F)
          (@TMap.empty (@LinState (li_sig F)))).
    Proof.
      unfold source_I.
      exists (Idle (@empty_heap (@Node A))).
      exists (Idle (pair (@None Addr) O)).
      exists (@SPListImpl.empty_splist_state A).
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [exact initial_represents|exact initial_snapshot_consistent].
    Qed.

    Lemma initial_SI :
      SI
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (li_init E)
          (ac_singleton (li_init F)
            (@TMap.empty (@LinState (li_sig F))))).
    Proof.
      apply lift_initial. exact initial_source_I.
    Qed.

    Lemma active_closes_invariant t m :
      ⊨ SActive t m ==>> SI.
    Proof.
      intros w Hactive. eapply lift_impl; [apply active_entails_I|exact Hactive].
    Qed.

    Program Definition MSPList : layer_implementation_simulation E F :=
      {| li_impl := @SPListImpl.splist_impl A owner |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := SI).
      - exact valid_rg.
      - exact parallel_compatible.
      - intros t f. destruct f as [v|l ts| | |l].
        + exists (SActive t (linsert v)).
          exists (fun ret => SCompleted t (linsert v) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply insert_triple.
        + exists (SActive t (lsetTS l ts)).
          exists (fun ret => SCompleted t (lsetTS l ts) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply setTS_triple.
        + exists (SActive t (@lgetTop A)).
          exists (fun ret => SCompleted t (@lgetTop A) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply getTop_triple.
        + exists (SActive t (@lgetCounter A)).
          exists (fun ret => SCompleted t (@lgetCounter A) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply getCounter_triple.
        + exists (SActive t (ltryRemove l)).
          exists (fun ret => SCompleted t (ltryRemove l) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply tryRemove_triple.
      - exact initial_SI.
    Qed.

  End Proof.

  Print Assumptions MSPList.
End SPListProof.
