Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Program.
Require Import Classical.
Require Import Coq.PArith.PArith.

Require Import coqrel.LogicalRelations.
Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import models.EffectSignatures.
Require Import LinCCAL.


Module Import LC := LinCCAL.

Module Sets.
  Section SetOps.
    Context {A : Type}.

    Definition set (A : Type) := A -> Prop.

    Definition Empty : set A := fun _ => False.
    Definition Full : set A := fun _ => True.

    Definition Singleton (a : A) : set A := fun x => x = a.

    Definition Union (s1 s2 : set A) : set A :=
      fun x => s1 x \/ s2 x.

    Definition Inter (s1 s2 : set A) : set A :=
      fun x => s1 x /\ s2 x.

    Definition Diff (s1 s2 : set A) : set A :=
      fun x => s1 x /\ ~ s2 x.

    Definition Complement (s : set A) : set A :=
      fun x => ~ s x.

    Definition Subset (s1 s2 : set A) : Prop :=
      forall x, s1 x -> s2 x.

    Definition Equal (s1 s2 : set A) : Prop :=
      forall x, s1 x <-> s2 x.

    Definition Disjoint (s1 s2 : set A) : Prop :=
      Equal (Inter s1 s2) Empty.
  End SetOps.

  Delimit Scope set_scope with set.
  Bind Scope set_scope with set.

  Notation "s1 ∪ s2" := (Union s1 s2) (at level 50) : set_scope.
  Notation "s1 ∩ s2" := (Inter s1 s2) (at level 40) : set_scope.
  Notation "s1 \ s2" := (Diff s1 s2) (at level 40) : set_scope.
  Notation "¬ s" := (Complement s) (at level 35) : set_scope.
  Notation "s1 ⊆ s2" := (Subset s1 s2) (at level 70) : set_scope.
  Notation "s1 ≡ s2" := (Equal s1 s2) (at level 70) : set_scope.
  Notation "s1 ⟂ s2" := (Disjoint s1 s2) (at level 70) : set_scope.
End Sets.

Module Rel.
  Section RelOps.
    Context {A : Type}.
    
    Definition Subset (r1 r2 : relation A) : Prop :=
      forall x y, r1 x y -> r2 x y.
    
    Definition Union (r1 r2 : relation A) : relation A :=
      fun x y => r1 x y \/ r2 x y.
    
    Definition Inter (r1 r2 : relation A) : relation A :=
      fun x y => r1 x y /\ r2 x y.
  End RelOps.

  Delimit Scope relation_scope with relation.
  Bind Scope relation_scope with relation.
  
  Notation "R ⊆ S" := (Subset R S) (at level 70) : relation_scope.
  Notation "R ∪ S" := (Union R S) (at level 50) : relation_scope.
  Notation "R ∩ S" := (Inter R S) (at level 40) : relation_scope.
End Rel.

Import Sets.
Import Rel.
Open Scope set_scope.
Open Scope relation_scope.

Definition rg_relation {E F} := relation (state E F).


Module ThreadSetBasedSimulation.
  Variant tl_estep {E F} (M : Reg.Op.m E F) (T : tid -> Prop) : relation (state E F) :=
  | einvoke t q Δ s s' Σ :
      T t ->
      TMap.find t s = None ->
      TMap.add t (mkts q (M q) None) s = s' ->
      tl_estep M T (mkst Δ s Σ) (mkst Δ s' Σ)
  | eaction t q m n k R Δ s Σ s' Σ' :
      T t ->
      TMap.find t s = Some (mkts q (Sig.cons m k) R) ->
      Σ t m = spec_ret n Σ' ->
      TMap.add t (mkts q (k n) R) s = s' ->
      tl_estep M T (mkst Δ s Σ) (mkst Δ s' Σ')
  | ereturn t q r Δ s s' Σ :
      T t ->
      TMap.find t s = Some (mkts q (Sig.var r) (Some r)) ->
      TMap.remove t s = s' ->
      tl_estep M T (mkst Δ s Σ) (mkst Δ s' Σ).

  Lemma tl_estep_parallel_decomposition {E F} (M : Reg.Op.m E F) (T1 T2 : tid -> Prop) x y:
    tl_estep M (T1 ∪ T2)%set x y ->
    tl_estep M T1 x y \/ tl_estep M T2 x y.
  Proof.
    destruct 1; (destruct H; [left|right]).
    - eapply einvoke; eauto.
    - eapply einvoke; eauto.
    - eapply eaction; eauto.
    - eapply eaction; eauto.
    - eapply ereturn; eauto.
    - eapply ereturn; eauto.
  Qed.

  CoInductive tl_correct {E F} (M : Reg.Op.m E F) (T : tid -> Prop) (R G : rg_relation) (s : state E F) : Prop :=
    {
      tl_correct_valid :
        specified s ->
        forall i, threadstate_valid (TMap.find i s);
      tl_correct_safe :
        specified s ->
        forall i q m k R,
          TMap.find i s = Some (mkts q (Sig.cons m k) R) ->
          st_base s i m <> spec_bot;
      tl_correct_stable :
        specified s ->
        forall s', R s s' -> tl_correct M T R G s';
      tl_correct_next :
        specified s ->
        forall s', tl_estep M T s s' -> reachable lstep (fun x => tl_correct M T R G x /\ G s x) s';
    }.

  Lemma tl_correct_parallel_composition {E F} (M : Reg.Op.m E F) (T1 T2 : tid -> Prop) (R1 G1 R2 G2 : rg_relation) :
    T1 ⟂ T2 ->
    G1 ⊆ R2 ->
    G2 ⊆ R1 ->
    forall s,
      tl_correct M T1 R1 G1 s ->
      tl_correct M T2 R2 G2 s ->
      tl_correct M (T1 ∪ T2)%set (R1 ∩ R2) (G1 ∪ G2) s.
  Proof.
    intros Hdisjoint HRG12 HRG21.
    cofix IH.
    intros s H1 H2. constructor.
    - destruct H1; auto.
    - destruct H1; auto.
    - destruct H1 as [_ _ H1_stable _].
      destruct H2 as [_ _ H2_stable _].
      intros ? ? [? ?]. auto.
    - intros.
      apply tl_estep_parallel_decomposition in H0 as [? | ?].
      + destruct H1 as [_ _ _ H1_correct].
        destruct H2 as [_ _ H2_stable _].
        specialize (H1_correct H _ H0).
        destruct H1_correct as [s'' [? [? ?]]].
        specialize (H2_stable H _ (HRG12 _ _ H3)).
        exists s''.
        split; auto.
        split; auto.
        left; auto.
      + destruct H2 as [_ _ _ H2_correct].
        destruct H1 as [_ _ H1_stable _].
        specialize (H2_correct H _ H0).
        destruct H2_correct as [s'' [? [? ?]]].
        specialize (H1_stable H _ (HRG21 _ _ H3)).
        exists s''.
        split; auto.
        split; auto.
        right; auto.
  Qed.
End ThreadSetBasedSimulation.


Module SingleThreadBasedSimulation.
  Variant tl_ustep {E F} (t : tid) : relation (state E F) :=
  | ustep q m n k R Δ s Σ s' Σ' :
      TMap.find t s = Some (mkts q (Sig.cons m k) R) ->
      Spec.next Σ t m = Spec.ret n Σ' ->
      TMap.add t (mkts q (k n) R) s = s' ->
      tl_ustep t (mkst Δ s Σ) (mkst Δ s' Σ').
  
  Variant tl_invstep {E F} (M : Reg.Op.m E F) (t : tid) (f : Sig.op F) : relation (state E F) :=
  | invstep Δ s s' Σ:
      TMap.find t s = None ->
      TMap.add t (mkts f (M f) None) s = s' ->
      tl_invstep M t f (mkst Δ s Σ) (mkst Δ s' Σ).
  
  Variant tl_retstep {E F} (t : tid) : relation (state E F) :=
  | retstep f r Δ s s' Σ:
      TMap.find t s = Some (mkts f (Sig.var r) (Some r)) ->
      TMap.remove t s = s' ->
      tl_retstep t (mkst Δ s Σ) (mkst Δ s' Σ).

  Variant tl_estep {E F} (M : Reg.Op.m E F) (t : tid) : relation (state E F) :=
  | einvoke f Δ s s' Σ :
      tl_invstep M t f (mkst Δ s Σ) (mkst Δ s' Σ) ->
      tl_estep M t (mkst Δ s Σ) (mkst Δ s' Σ)
  | eaction Δ s Σ s' Σ' :
      tl_ustep t (mkst Δ s Σ) (mkst Δ s' Σ') ->
      tl_estep M t (mkst Δ s Σ) (mkst Δ s' Σ')
  | ereturn Δ s s' Σ :
      tl_retstep t (mkst Δ s Σ) (mkst Δ s' Σ) ->
      tl_estep M t (mkst Δ s Σ) (mkst Δ s' Σ).
  
  Lemma estep_parallel_decomposition {E F} (M : Reg.Op.m E F) s1 s2:
    estep M s1 s2 -> exists t, tl_estep M t s1 s2.
  Proof.
    destruct 1; exists t0.
    - eapply einvoke, invstep; eauto.
    - eapply eaction, ustep; eauto.
    - eapply ereturn, retstep; eauto.
  Qed.
  
  Definition threadstate_safe {E F} i (s : state E F) :=
    forall q m k R,
    TMap.find i s = Some (mkts q (Sig.cons m k) R) ->
      Spec.next (st_base s) i m <> Spec.bot.
    
  CoInductive tl_correct {E F} (M : Reg.Op.m E F) (t : tid) (R G : rg_relation) (s : state E F) : Prop :=
    {
      tl_correct_valid :
        specified s ->
        forall i, threadstate_valid (TMap.find i s);
      tl_correct_safe :
        specified s ->
        forall i, threadstate_safe i s;
      tl_correct_stable :
        specified s ->
        forall s', R s s' -> tl_correct M t R G s';
      tl_correct_next :
        specified s ->
        forall s', tl_estep M t s s' -> reachable lstep (fun x => tl_correct M t R G x /\ G s x) s';
    }.
    

  Lemma tl_correct_parallel_composition {E F} (M : Reg.Op.m E F) (R G : tid -> rg_relation) :
    (forall t1 t2, t1 <> t2 -> G t1 ⊆ R t2) ->
    forall s,
      (forall t, tl_correct M t (R t) (G t) s) ->
      correct M s.
  Proof.
    intros HRG.
    cofix IH.
    intros s H. constructor.
    - intros ? t. destruct (H t); auto.
    - intros ? t; intros; destruct (H t); unfold threadstate_safe in *; eauto.
    - intros.
      apply estep_parallel_decomposition in H1 as [t ?].
      destruct (H t) as [_ _ _ H_correct].
      specialize (H_correct H0 _ H1) as [s'' [? [? ?]]].
      exists s''; split; auto.
      apply IH; intros.
      destruct (Pos.eq_dec t t0); subst; auto.
      specialize (H t0) as [_ _ H_stable _].
      apply H_stable; auto.
      eapply HRG; eauto.
  Qed.


  Record tl_correctness_invariant {E F} (M : Reg.Op.m E F) (t : tid) (R G : rg_relation) (P : state E F -> Prop) : Prop :=
    {
      tlci_valid s :
        P s -> specified s ->
        forall i, threadstate_valid (TMap.find i s);
      tlci_safe s :
        P s -> specified s ->
        forall i, threadstate_safe i s;
      tlci_stable s:
        P s -> specified s ->
        forall s', R s s' -> P s';
      tlci_next s :
        P s -> specified s ->
        forall s', tl_estep M t s s' -> reachable lstep (fun s'' => P s'' /\ G s s'') s';
    }.

  Lemma tl_correct_ci {E F} (M : Reg.Op.m E F) (t : tid) (R G : rg_relation):
    tl_correctness_invariant M t R G (tl_correct M t R G).
  Proof.
  constructor.
    - apply tl_correct_valid.
    - apply tl_correct_safe.
    - apply tl_correct_stable.
    - intros u Hu Hspec u' Hu'.
      eapply tl_correct_next in Hu'; eauto.
  Qed.

  Lemma tl_correctness_invariant_sound {E F} (M : Reg.Op.m E F) (t : tid) (R G : rg_relation) I :
    tl_correctness_invariant M t R G I ->
    forall s, I s -> tl_correct M t R G s.
  Proof.
    intros HI.
    cofix H.
    intros s Hs. constructor.
    - eapply tlci_valid; eauto.
    - eapply tlci_safe; eauto.
    - intros. apply H. eapply tlci_stable; eauto.
    - intros Hspec s' Hs'.
      unfold reachable.
      edestruct @tlci_next as (s'' & ? & ? & ?); eauto.
  Qed.
End SingleThreadBasedSimulation.


Module Assertion.
  Definition assertion {E F} : Type := state E F -> Prop.

  Section AssertionOps. 
    Context {E F : Sig.t}.
    
    Definition Conj (P Q : assertion) : assertion := fun (s : state E F) => P s /\ Q s.
    Definition Disj (P Q : assertion) : assertion := fun (s : state E F) => P s \/ Q s.
    Definition Imply (P Q : assertion) : assertion := fun (s : state E F) => P s -> Q s.
    Definition ComposeA (P : assertion) (R : relation (state E F)) : assertion :=
      fun (s : state E F) => exists s', P s' /\ R s' s.
      Definition ComposeR (R S : relation (state E F)) : relation (state E F) :=
      fun (s s' : state E F) => exists s'', R s s'' /\ S s'' s'.
  End AssertionOps.
  
  Delimit Scope assertion_scope with assertion.
  Bind Scope assertion_scope with assertion.
  
  Notation "P //\\ Q" := (Conj P Q) (at level 40) : assertion_scope.
  Notation "P \\// Q" := (Disj P Q) (at level 50) : assertion_scope.
  Notation "P ==>> Q" := (Imply P Q) (at level 70) : assertion_scope.
  Notation "R ⊚ P" := (ComposeA P R) (at level 30) : assertion_scope.
  Notation "R ○ S" := (ComposeR S R) (at level 30) : assertion_scope.
End Assertion.


Module ProgramLogic.
  Import SingleThreadBasedSimulation.
  Import Assertion.
  Open Scope assertion_scope.

  (* CoInductive valid_triple {E F} (t : tid) (f : Sig.op F) (R G : @rg_relation E F) : assertion -> Sig.term E (Sig.ar f) -> @assertion E F -> Prop :=
  (* | valid_return: forall r,
    valid_triple t f R G P (Sig.var r) Q. *)
  | valid_cons : forall,
    (* stable P *)
    Commit 
    valid_triple t f R G P (Sig.cons m k) Q. *)
  
  CoInductive wp {E F} (t : tid) (f : Sig.op F) (R G : @rg_relation E F) (I : @assertion E F) : Sig.term E (Sig.ar f) -> ((Sig.ar f) -> @assertion E F) -> @assertion E F :=
  | wp_var : forall r r' (Q : (Sig.ar f) -> @assertion E F) s,
      (* the state needs to satisfy the invariant *)
      I s ->
      (* stable: after one rely step, the weakest-pre still holds *)
      (forall s', R s s' -> wp t f R G I (Sig.var r) Q s') ->
      (* ensure the command in the weakest-pre matches the continuation for thread t *)
      TMap.find t (st_impl s) = Some (mkts f (Sig.var r) r') ->
      (* can perform return step *)
      (exists s', tl_retstep t s s') ->
      (* after return step, the postcondition is satisfied and the transition is in guarantee *)
      (forall s', tl_retstep t s s' -> (Q r) s' /\ G s s') ->
      wp t f R G I (Sig.var r) Q s
  | wp_cons : forall (Q : (Sig.ar f) -> @assertion E F) s r m k,
      (* the state needs to satisfy the invariant *)
      I s ->
      (* stable: after one rely step, the weakest-pre still holds *)
      (forall s', R s s' -> wp t f R G I (Sig.cons m k) Q s') ->
      (* ensure the command in the weakest-pre matches the continuation for thread t *)
      TMap.find t (st_impl s) = Some (mkts f (Sig.cons m k) r) ->
      (* preservation *)
      (forall s' c' r',
        (* after one thread local underlay step *)
        tl_ustep t s s' ->
        TMap.find t (st_impl s') = Some (mkts f c' r') ->
        (* can establish the weakest-pre again by lstep and the whole transition is in the guarantee *)
        reachable lstep (fun s'' => wp t f R G I c' Q s'' /\ G s s'') s') ->
      wp t f R G I (Sig.cons m k) Q s.
  
  Definition htriple_valid {E F} (t : tid) (f : Sig.op F) (R G : @rg_relation E F) (I P : @assertion E F) (c : Sig.term E (Sig.ar f)) (Q : (Sig.ar f) -> @assertion E F) :=
    forall s, P s -> wp t f R G I c Q s.

  Notation "[ R , G , I , t , f ] ⊨ {{ P }} c {{ Q }}" := (htriple_valid t f R G I P c Q).

  Lemma lstep_same_continuation {E F}:
    forall (s1 s2 : state E F), lstep s1 s2 ->
    forall t f c r1,
      TMap.find t s1 = Some (mkts f c r1) ->
      exists r2, TMap.find t s2 = Some (mkts f c r2).
  Proof.
    intros.
    destruct H; subst; simpl in *.
    destruct (Pos.eq_dec t0 t1); subst.
    - rewrite H in H0.
      inversion H0.
      subst.
      apply inj_pair2 in H4. subst.
      exists (Some r).
      rewrite LinCCAL.TMap.gss. auto.
    - exists r1.
      rewrite LinCCAL.TMap.gso; auto.
  Qed.

  Lemma multi_lstep_same_continuation {E F}:
    forall (s1 s2 : state E F), star lstep s1 s2 ->
    forall t f c r1,
      TMap.find t s1 = Some (mkts f c r1) ->
      exists r2, TMap.find t s2 = Some (mkts f c r2).
  Proof.
    intros ? ? ?.
    apply clos_rt_rtn1 in H.
    induction H; intros; eauto.
    apply IHclos_refl_trans_n1 in H1 as [? ?].
    eapply lstep_same_continuation in H; eauto.
  Qed.

  Lemma soundness {E F} (M : Reg.Op.m E F) (t : tid) (R G : @rg_relation E F) (I : @assertion E F) :
    (* hoare triples *)
    (forall (f : Sig.op F), 
        (tl_invstep M t f) ⊆ G /\
        (forall s, ((tl_invstep M t f) ⊚ I ==>> I) s) /\
        [R,G,I,t,f] ⊨ {{ (tl_invstep M t f) ⊚ I }} (M f) {{ fun _ => I }}) ->
    (* invariant implies valid state *)
    (forall s, I s -> specified s -> forall i : tid, threadstate_valid (TMap.find i s)) ->
    (* invariant implies safety *)
    (forall s, I s -> specified s -> forall i : tid, threadstate_safe i s) ->
    (* invariant is stable *)
    (forall s, I s -> specified s -> forall s', R s s' -> I s') ->
    (* rely does not change local continuation *)
    (forall s s' f c, R s s' ->
      (exists r, TMap.find t s = Some {| ts_op := f; ts_prog := c; ts_res := r |})
      <-> (exists r, TMap.find t s' = Some {| ts_op := f; ts_prog := c; ts_res := r |})) ->
    exists P, tl_correctness_invariant M t R G P.
  Proof.
    intros Htriple Hvalid Hsafe Hstable Hrely_local.

    exists (fun s => I s /\ 
    forall f c r,
      TMap.find t (st_impl s) = Some (mkts f c r) ->
        wp t f R G I c (fun _ => I) s).

    constructor; intros ? [Hs Hwp]; intros; eauto.
    (* stable *)
    {
      split; eauto.
      intros.
      eapply ex_intro with (x:=r) in H1.
      eapply Hrely_local in H1 as [r' ?]; eauto.
      apply Hwp in H1.
      destruct H1; eauto.
    }
    
    clear Hvalid Hsafe Hstable Hrely_local.
    
    destruct H0.
    (* invoke step *)
    {
      clear Hwp.

      inversion H0; subst.
      specialize (Htriple f) as (Hguar & Hinv & Htriple).
      (* specialize (Htriple f) as (P & HP & Hguar & Htriple). *)

      exists {|
        st_spec := Δ;
        st_impl := TMap.add t {| ts_op := f; ts_prog := M f; ts_res := None |} s;
        st_base := Σ
      |}.
      repeat split; auto.
      - apply rt_refl.
      - apply Hinv. eexists; eauto.
      - intros. 
        simpl in H1.
        rewrite LinCCAL.TMap.gss in H1.
        inversion H1; subst; clear H1.
        eapply inj_pair2 in H5, H6; subst.
        apply Htriple.
        eexists; eauto.
    }
    (* underlay step *)
    {
      inversion H0; subst.
      (* simpl in Hwp. *)
      apply Hwp in H5.
      inversion H5; subst; clear H5.
      eapply inj_pair2 in H2; subst.
      eapply H10 in H0.
      2:{ simpl. rewrite LinCCAL.TMap.gss. auto. }
      destruct H0 as (s'' & ? & ? & ?).
      exists s''.
      repeat split; eauto.
      - destruct H1; auto.
      - intros.
        remember {|
          st_spec := Δ;
          st_impl := TMap.add t {| ts_op := q; ts_prog := k n; ts_res := R0 |} s;
          st_base := Σ'
        |} as s1.
        eapply multi_lstep_same_continuation with (t:=t) in H0 as [? ?].
        2:{
          subst. simpl.
          rewrite LinCCAL.TMap.gss. auto.
        }
        rewrite H5 in H0.
        inversion H0; subst.
        apply inj_pair2 in H11; subst.
        auto.
    }
    (* return step *)
    {
      inversion H0; subst.
      exists {| st_spec := Δ; st_impl := TMap.remove t s; st_base := Σ |}.
      repeat split; eauto.
      - apply rt_refl.
      - apply Hwp in H3.
        inversion H3; subst; auto.
        apply H7 in H0 as [? ?].
        auto.
      - intros.
        simpl in H1.
        rewrite LinCCAL.TMap.grs in H1.
        inversion H1.
      - apply Hwp in H3.
        inversion H3; subst; auto.
        apply H7 in H0 as [? ?].
        auto.
    }
  Qed.

  
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Locate "*".
  (* Check LinCCAL.Tens.omap. *)
  
  Program Definition Mcounter : LinCCAL.m (LinCCAL.LinCCALExample.Llock * LinCCAL.LinCCALExample.Lreg 0%nat)%obj LinCCAL.LinCCALExample.Lcounter :=
  {| LinCCAL.li_impl 'fai := LinCCAL.LinCCALExample.fai_impl |}.
  Next Obligation.
    eapply LinCCAL.correctness_invariant_sound.
  Abort.

  (* Another program logic: LHL-style *)
  
  Definition stable {E F} (R : @rg_relation E F) (P : @assertion E F) :=
    forall s s', R s s' -> P s -> P s'.

  Definition commit {E F} (t : tid) (f : Sig.op F) (G : @rg_relation E F) (P : @assertion E F) m k (Q : (Sig.ar m) -> @assertion E F) :=
    forall s s' r n,
      P s ->
      tl_ustep t s s' ->
      TMap.find t (st_impl s) = Some (mkts f (Sig.cons m k) r) ->
      TMap.find t (st_impl s') = Some (mkts f (k n) r) ->
      reachable lstep (fun s'' => Q n s'' /\ G s s'') s'.
    
  CoInductive safe {E F} (t : tid) (f : Sig.op F) (R G : @rg_relation E F) :
    (@assertion E F) -> Sig.term E (Sig.ar f) -> ((Sig.ar f) -> @assertion E F) -> Prop :=
  | safe_var : forall (P : @assertion E F) Q r,
    (* precondition stable *)
    stable R P ->
    (* check abstract returned in the precondition *)
    (forall s, P s -> TMap.find t (st_impl s) = Some (mkts f (Sig.var r) (Some r))) ->
    (* perform concrete return and satisfy postcondition and guarantee *)
    (forall s s', P s -> tl_retstep t s s' -> (Q r) s' /\ G s s') ->
    safe t f R G P (Sig.var r) Q
  | safe_cons : forall m k P P' Q,
    (* precondition stable *)
    stable R P ->
    (* perform concrete exeuction and lstep *)
    commit t f G P m k P' ->
    (* the rest of the program is safe *)
    forall n, safe t f R G (P' n) (k n) Q ->
    safe t f R G P (Sig.cons m k) Q
  .

End ProgramLogic.
