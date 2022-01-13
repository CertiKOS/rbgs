From Coq Require Import
     Relations
     RelationClasses
     List
     FunctionalExtensionality.
From models Require Import
     IntSpec.
From lattices Require Import
     Upset Downset FCD.
From structures Require Import
     Effects Lattice.
From examples Require Import CAL.
Import ListNotations ISpec.

Unset Asymmetric Patterns.

Obligation Tactic := idtac.

Ltac fcd_step :=
  (setoid_rewrite FCD.ext_ana ||
   setoid_rewrite Inf.mor ||
   setoid_rewrite Sup.mor ||
   setoid_rewrite Sup.mor_join ||
   setoid_rewrite Sup.mor_bot ||
   setoid_rewrite Inf.mor_meet); cbn.

Ltac fcd := repeat fcd_step.

(** * Adjunctions in Interaction Specification *)

(** ** Adjunctions as generalized relations *)

(** An adjunction A ⇆ B is a pair or morphisms which can "cancel" each other *)
(* TODO: a more general formalization of adjunctions? *)
(* A is the high level specification; B is the low level implementation *)
Class poset_adjunction (A B: esig) :=
  {
    left_arrow : A ~> B;
    right_arrow : B ~> A;
    epsilon : left_arrow @ right_arrow [= identity;
    eta : identity [= right_arrow @ left_arrow;
  }.
Arguments left_arrow {_ _}.
Arguments right_arrow {_ _}.
Arguments epsilon {_ _}.
Arguments eta {_ _}.

Infix "<=>" := poset_adjunction (at level 50).

(** *** Composition and identity of adjunctions *)

Program Definition adjunction_compose {A B C} (phi: A <=> B) (psi: B <=> C) :=
  {|
    (* A ~> C := B ~> C @ A ~> B *)
    left_arrow := left_arrow psi @ left_arrow phi;
    (* C ~> A := B ~> A @ C ~> B *)
    right_arrow := right_arrow phi @ right_arrow psi;
  |}.
Next Obligation.
  intros *. etransitivity.
  instantiate (1 := left_arrow psi @ (left_arrow phi @ right_arrow phi) @ right_arrow psi).
  rewrite !ISpec.compose_assoc. reflexivity.
  rewrite epsilon. rewrite compose_unit_l. apply epsilon.
Qed.
Next Obligation.
  intros *. etransitivity.
  instantiate (1 := right_arrow phi @ (right_arrow psi @ left_arrow psi) @ left_arrow phi).
  rewrite <- eta. rewrite compose_unit_l. apply eta.
  rewrite !ISpec.compose_assoc. reflexivity.
Qed.

Lemma apply_inf {E F A I} (f : forall ar, E ar -> I -> ispec F ar) (t: ispec E A):
  apply (fun _ m => inf i, f _ m i) t [= inf i, apply (fun _ m => f _ m i) t.
Proof.
  apply inf_iff. intros i.
  unfold apply. apply ext_proper_ref'; try typeclasses eauto.
  intros p. induction p; cbn.
  - reflexivity.
  - rewrite Inf.mor. apply (inf_at i). reflexivity.
  - rewrite Inf.mor. apply (inf_at i).
    apply ext_proper_ref'; try typeclasses eauto.
    intros px. induction px; cbn.
    + apply sup_iff. intros <-.
      apply (sup_at eq_refl). rstep.
    + reflexivity.
    + apply join_lub.
      * apply join_l. reflexivity.
      * apply join_r. rewrite IHpx. reflexivity.
Qed.

Lemma fmap_cons_bind {E A X} m (n: X) (t: t E A):
  FCD.emb (pmove m) || FCD.map (pcons m n) t = n' <- FCD.emb (pcons m n (pret n)); sup _ : n' = n, t.
Proof.
  unfold bind. setoid_rewrite FCD.ext_ana. cbn. f_equal.
  unfold FCD.map. f_equal.
  apply antisymmetry.
  - apply (sup_at eq_refl). reflexivity.
  - apply sup_iff. intros. reflexivity.
Qed.

Lemma fmap_cons_bind_ref {E A X} m (n: X) (t: t E A):
  FCD.map (pcons m n) t [= n' <- FCD.emb (pcons m n (pret n)); sup _ : n' = n, t.
Proof.
  setoid_rewrite <- fmap_cons_bind. apply join_r. reflexivity.
Qed.

Lemma apply_fmap_cons {E F A X} (f: E ~> F) m (n: X) (t: t F A):
  apply f (FCD.map (pcons m n) t) [= n' <- f _ m; sup _ : n' = n, apply f t.
Proof.
  rewrite fmap_cons_bind_ref. intm.
  setoid_rewrite FCD.ext_ana. cbn.
  unfold bind. setoid_rewrite Sup.mor. rstep.
  edestruct (FCD.join_meet_dense (f X m)) as (I & J & c & Hc).
  rewrite Hc. clear Hc.
  setoid_rewrite Sup.mor. apply sup_iff. intros i. apply (sup_at i).
  setoid_rewrite Inf.mor. apply inf_iff. intros j. apply (inf_at j).
  rewrite FCD.ext_ana.
  induction (c i j); cbn.
  - apply sup_iff. intros <-. reflexivity.
  - reflexivity.
  - apply join_lub.
    + rstep. constructor.
    + rewrite IHp. rewrite FCD.ext_ana. reflexivity.
Qed.

(* X is the abstraction; Y is the implementation. So angelic choice over x and
   demonic choice over y *)
(** ** Relations as adjunctions *)
Section LIFT.

  Context {E:esig} {X Y} (R: X -> Y -> Prop).

  Definition rel_left: E # X ~> E # Y :=
    fun _ '(st m y) => sup { x | R x y },
    nx' <- int (st m x);
    let '(n, x') := nx' in
    inf { y' | R x' y' }, ret (n, y').
  Definition rel_right: E # Y ~> E # X :=
    fun _ '(st m x) => inf { y | R x y },
    ny' <- int (st m y);
    let '(n, y') := ny' in
    sup { x' | R x' y' }, ret (n, x').

  Program Definition rel_adj: E # X <=> E # Y :=
    {|
      left_arrow := rel_left;
      right_arrow := rel_right;
    |}.
  Next Obligation.
    unfold rel_left, rel_right, compose, identity. cbn.
    intros ? mk. destruct mk as [? m y0].
    fcd_step. apply sup_iff. intros [x0 H]. cbn.
    intm. fcd_step. apply (inf_at (exist _ y0 H)). cbn.
    fcd. apply sup_iff. intros [[n0 y1]|].
    - fcd. apply join_lub.
      + apply (sup_at None). reflexivity.
      + apply sup_iff. intros [x1 H1]. cbn.
        apply join_lub.
        * apply (sup_at None). reflexivity.
        * apply (inf_at (exist _ y1 H1)). cbn.
          apply (sup_at (Some (n0, y1))). reflexivity.
    - fcd. apply (sup_at None). reflexivity.
  Qed.
  Next Obligation.
    unfold rel_left, rel_right, compose, identity. cbn.
    intros ? mk. destruct mk as [? m x0].
    fcd_step. apply inf_iff. intros [y0 H]. cbn.
    intm. fcd_step. apply (sup_at (exist _ x0 H)). cbn.
    fcd. apply sup_iff. intros [[n0 x1]|].
    - apply (sup_at (Some (n0, x1))). fcd.
      apply join_r. apply inf_iff. intros [y1 H1].
      apply join_r. apply (sup_at (exist _ x1 H1)). reflexivity.
    - apply (sup_at None). fcd. reflexivity.
  Qed.

  Definition rel_right_inline {ar} (x: X) (t: ispec E ar) : ispec (E # Y) (ar * X) :=
    inf { y | R x y },
    ny' <- srun y t;
    let '(n, y') := ny' in
    sup { x' | R x' y' },
    ret (n, x').
  Definition rel_left_inline {ar} (y: Y) (t: ispec E ar) : ispec (E # X) (ar * Y) :=
    sup { x | R x y },
    nx' <- srun x t;
    let '(n, x') := nx' in
    inf { y' | R x' y' },
    ret (n, y').

  (* TODO: there's something more fundamental behind this lemma *)
  Lemma apply_rel_right {ar} (t: ispec E ar) (x: X):
    apply rel_right (srun x t) [= rel_right_inline x t.
  Proof.
    unfold rel_right_inline. unfold srun.
    apply inf_iff. intros [y Hr]. cbn.
    edestruct (FCD.join_meet_dense t) as (I & J & c & Hc). subst t.
    fcd.
    apply sup_iff. intros i. apply (sup_at i).
    apply inf_iff. intros j. apply (inf_at j).
    revert x y Hr. induction (c i j); intros x y Hr; cbn.
    + fcd. eapply (fsup_at x); easy.
    + fcd. eapply (inf_at (exist _ y Hr)). cbn.
      apply sup_iff. intros [[n y']|].
      * fcd. apply join_lub; try easy.
        apply sup_iff. intros [x' H'].
        apply join_lub; try easy. apply bot_lb.
      * fcd. reflexivity.
    + fcd. apply sup_iff. intros [xr|].
      * rewrite apply_fmap_cons. cbn.
        fcd_step. apply (inf_at (exist _ y Hr)). cbn.
        fcd. apply sup_iff. intros [[n' y']|].
        -- apply (sup_at (Some y')). fcd.
           apply join_lub.
           {
             destruct p; cbn; fcd.
             - apply join_l. reflexivity.
             - apply join_l. reflexivity.
             - unfold FCD.map. fcd.
               apply (sup_at None). fcd.
               apply join_l. reflexivity.
           }
           apply sup_iff. intros [x' H']. cbn.
           apply join_lub.
           {
             destruct p; cbn; fcd.
             - apply join_l. reflexivity.
             - apply join_l. reflexivity.
             - unfold FCD.map. fcd.
               apply (sup_at None). fcd.
               apply join_l. reflexivity.
           }
           apply sup_iff. intros Hn. inversion Hn. subst. clear Hn.
           specialize (IHp _ _ H'). rewrite IHp. clear IHp.
           unfold bind, FCD.map, t. rewrite !FCD.ext_ext.
           {
             apply ext_proper_ref'.
             - split. intros p1 p2 Hp.
               apply ext_proper_ref; try typeclasses eauto.
               + intros px. reflexivity.
               + rewrite Hp. reflexivity.
             - split. intros p1 p2 Hp.
               apply ext_proper_ref; try typeclasses eauto.
               + intros px. reflexivity.
               + rstep. now constructor.
             - intros pc. fcd.
               apply join_r. reflexivity.
           }
        -- apply (sup_at None). unfold bind. fcd. reflexivity.
      * apply (sup_at None). unfold bind. fcd.
        apply (inf_at (exist _ y Hr)). cbn.
        apply sup_iff. intros [[n' y']|].
        -- fcd. apply join_lub; try easy.
           apply sup_iff. intros [x' H']. cbn.
           apply join_lub; try easy.
           apply bot_lb.
        -- fcd. reflexivity.
  Qed.

  Lemma sup_join {L: cdlattice} {I} (f g: I -> L):
    sup i: I, f i || g i = (sup i, f i) || (sup i, g i).
  Proof with reflexivity.
    apply antisymmetry.
    - apply sup_iff. intros i. apply join_lub.
      + apply join_l. apply (sup_at i)...
      + apply join_r. apply (sup_at i)...
    - apply join_lub.
      + apply sup_iff. intros i. apply (sup_at i). apply join_l...
      + apply sup_iff. intros i. apply (sup_at i). apply join_r...
  Qed.

  Lemma apply_rel_left {ar} (t: ispec E ar) (y: Y):
    rel_left_inline y t [= apply rel_left (srun y t).
  Proof.
  Admitted.
(*
    unfold rel_left_inline. unfold srun.
    apply sup_iff. intros [x Hr]. cbn.
    edestruct (FCD.join_meet_dense t) as (I & J & c & Hc). subst t.
    fcd.
    apply sup_iff. intros i. apply (sup_at i).
    apply inf_iff. intros j. apply (inf_at j).
    revert x y Hr. induction (c i j); intros x y Hr; cbn.
    - fcd. eapply (finf_at y); easy.
    - fcd. eapply (sup_at (exist _ x Hr)). cbn.
      apply (sup_at None). fcd. reflexivity.
    - rewrite !sup_option.
      etransitivity.
      instantiate (1 := ny' <- rel_left _ (st m y); let '(n', y') := ny' in sup _: n = n', apply rel_left (stateful_play y' p)).
      + cbn.
        setoid_rewrite Sup.mor. apply (sup_at (exist _ x Hr)).
        setoid_rewrite Sup.mor. setoid_rewrite Sup.mor. cbn.
        setoid_rewrite Sup.mor_join. apply join_lub.
        * setoid_rewrite FCD.ext_ana. cbn.
          apply (sup_at None). fcd. reflexivity.
        * setoid_rewrite Sup.mor. apply sup_iff. intros xr.
          apply (sup_at (Some (n, xr))).
          setoid_rewrite FCD.ext_ana. cbn.
          setoid_rewrite Sup.mor_join. apply join_r. unfold FCD.map. cbn.
          setoid_rewrite Inf.mor. setoid_rewrite Inf.mor.
          apply inf_iff. intros [y' Hr']. cbn.
          setoid_rewrite FCD.ext_ana. setoid_rewrite FCD.ext_ana. cbn.
          apply join_r. setoid_rewrite Sup.mor.
          apply (sup_at eq_refl).
          specialize (IHp _ _ Hr'). rewrite <- IHp.
          unfold bind. rewrite !@FCD.ext_ext; try typeclasses eauto.
          apply ext_proper_ref'. admit. admit. intros px.
          rewrite FCD.ext_ana. cbn. apply join_lub.
          2: { reflexivity. }
          destruct px.
          -- cbn. destruct v. setoid_rewrite Inf.mor.
             apply inf_iff. intros [y'' Hr'']. cbn.
             fcd. rstep. constructor.
          -- cbn. fcd. rstep. constructor.
          -- cbn. fcd. apply join_l. rstep. constructor.
      + clear. etransitivity.
        instantiate (1 := (FCD.emb (pmove (st m y)) || (sup x : Y, FCD.emb (pmove (st m y)) || FCD.map (pcons (st m y) (n, x)) (stateful_play x p))) / rel_left).
        2: {
          setoid_rewrite Sup.mor_join. apply join_lub.
          - apply join_l. reflexivity.
          - setoid_rewrite Sup.mor. apply sup_iff. intros y'.
            rewrite Sup.mor_join. apply join_lub.
            + apply join_l. reflexivity.
            + apply join_r. apply (sup_at y'). reflexivity.
        }
        * setoid_rewrite fmap_cons_bind.
          rewrite Sup.mor_join. apply join_r.
          rewrite Sup.mor. cbn.
          setoid_rewrite Sup.mor. apply sup_iff. intros [x Hr]. cbn.
          setoid_rewrite Sup.mor. setoid_rewrite Sup.mor.
          apply sup_iff. intros [[n' x']|].
          -- setoid_rewrite apply_bind.
             setoid_rewrite FCD.ext_ana. cbn. unfold bind.
             setoid_rewrite Sup.mor. setoid_rewrite Sup.mor.
             rewrite sup_sup. apply (sup_at (exist _ x Hr)). cbn.
             setoid_rewrite Sup.mor. setoid_rewrite Sup.mor.
             setoid_rewrite Sup.mor. rewrite sup_sup. apply (sup_at (Some (n', x'))).
             setoid_rewrite FCD.ext_ana. cbn.
             rewrite Sup.mor_join. apply join_lub.
             ++ apply (sup_at y). rewrite !Sup.mor_join. apply join_l. cbn.
                fcd. reflexivity.
             ++ setoid_rewrite Sup.mor_join. setoid_rewrite Sup.mor_join.
                rewrite sup_join. apply join_r.
                repeat setoid_rewrite Inf.mor. rewrite sup_inf.
                apply inf_iff. intros fy. destruct (fy y) as [y' Hr'] eqn: Hfy.
                apply (sup_at y'). apply (inf_at (exist _ y' Hr')). cbn.
                fcd.
  Admitted.
 *)

End LIFT.

Section PROPS.

  Context {E F} (f: E ~> F).
  Context {X Y} (R: X -> Y -> Prop).

  (** Left adjoint commutes with functor (-#S):

    f : E → F, R ⊆ X × Y ⊢ (R@F)* ∘ f@X ⊑ f@Y ∘ (R@E)*

   *)
  Lemma rel_left_commute: rel_left R @ slift f [= slift f @ rel_left R.
  Proof.
    unfold compose. intros ? mk.
    destruct mk as [ar m y]. cbn.
    rewrite <- apply_rel_left. unfold rel_left_inline.
    fcd_step. apply sup_iff. intros [x Hr].
    apply (fsup_at x); eauto. intm. unfold bind.
    apply bind_proper_ref; try easy.
    intros [n x']. fcd. apply inf_iff. intros i. apply (inf_at i). reflexivity.
  Qed.

  (** Right adjoint commutes with functor (-#S):

    f : E → F, R ⊆ X × Y ⊢ f@X ∘ (R@F)ₒ ⊑ (R@E)ₒ ∘ f@Y

   *)
  Lemma rel_right_commute: slift f @ rel_right R [= rel_right R @ slift f.
  Proof.
    unfold compose. intros ? mk.
    destruct mk as [ar m x]. cbn.
    rewrite apply_rel_right. unfold rel_right_inline.
    fcd_step. apply inf_iff. intros [y Hr].
    apply (finf_at y); eauto. intm. unfold bind.
    apply bind_proper_ref; try easy.
    intros [n y']. fcd. apply sup_iff. intros i. apply (sup_at i). reflexivity.
  Qed.

  Context {Z} (T: Y -> Z -> Prop).
  (** Left adjoint preserves composition:

    E: Type, R ⊆ X × Y, T ⊆ Y × Z ⊢ (T@E)* ∘ (R@E)* = ((R ∘ T)@E)*

   *)
  Lemma rel_left_compose:
    rel_left (E:=E) T @ rel_left R = rel_left (rel_compose R T).
  Proof.
    unfold compose. apply antisymmetry; intros ? mk.
    - destruct mk as [? m z]. cbn.
      fcd_step. apply sup_iff. intros [y Ht]. intm.
      fcd_step. apply sup_iff. intros [x Hr]. cbn.
      eapply (fsup_at x). exists y; split; eauto.
      fcd. apply sup_iff. intros [[n x']|].
      + apply (sup_at (Some (n, x'))). intm. fcd_step.
        apply join_lub.
        * apply join_l. reflexivity.
        * apply join_r. fcd. apply inf_iff.
          intros [z' [y' [Hr' Ht']]]. cbn.
          apply (inf_at (exist _ y' Hr')). cbn.
          apply (inf_at (exist _ z' Ht')). cbn. reflexivity.
      + apply (sup_at None). fcd. reflexivity.
    - destruct mk as [? m z]. cbn.
      apply sup_iff. intros [x [y [Hr Ht]]]. cbn.
      fcd_step. apply (sup_at (exist _ y Ht)). intm.
      apply sup_iff. intros [[n x']|].
      + fcd. apply (sup_at (exist _ x Hr)). apply (sup_at (Some (n, x'))). cbn.
        fcd. apply join_lub.
        * apply join_l. reflexivity.
        * apply join_r. apply inf_iff. intros [y' Hr']. cbn.
          apply join_r. apply inf_iff. intros [z' Ht']. cbn.
          assert (H': rel_compose R T x' z'). eexists; split; eauto.
          apply (inf_at (exist _ z' H')). cbn. reflexivity.
      + fcd. apply (sup_at (exist _ x Hr)). apply (sup_at None).
        fcd. reflexivity.
  Qed.

  (** Right adjoint preserves composition:

    E: Type, R ⊆ X × Y, T ⊆ Y × Z ⊢ (R@E)ₒ ∘ (T@E)ₒ = ((R ∘ T)@E)ₒ

   *)
  Lemma rel_right_compose:
    rel_right (E:=E) R @ rel_right T = rel_right (rel_compose R T).
  Proof.
    unfold compose. apply antisymmetry; intros ? mk.
    - destruct mk as [? m x]. cbn.
      apply inf_iff. intros [z [y [Hr Ht]]]. cbn.
      fcd_step. apply (inf_at (exist _ y Hr)). intm.
      fcd_step. apply (inf_at (exist _ z Ht)). cbn.
      fcd. apply sup_iff. intros i. apply (sup_at i).
      destruct i as [[n z']|].
      + fcd. apply join_lub.
        * apply join_l. reflexivity.
        * apply sup_iff. intros [y' Ht']. cbn.
          apply join_lub.
          -- apply join_l. reflexivity.
          -- apply join_r. apply sup_iff. intros [x' Hr'].
             assert (Hrt: rel_compose R T x' z').
             eexists; split; eauto.
             apply (sup_at (exist _ x' Hrt)). reflexivity.
      + fcd. reflexivity.
    - destruct mk as [? m x]. cbn.
      fcd_step. apply inf_iff. intros [y Hr]. cbn. intm.
      fcd_step. apply inf_iff. intros [z Ht]. cbn.
      assert (Hrt: rel_compose R T x z).
      eexists; split; eauto.
      apply (inf_at (exist _ z Hrt)). cbn.
      fcd. apply sup_iff. intros i. apply (sup_at i).
      destruct i as [[n z']|].
      + fcd. apply join_lub.
        * apply join_l. reflexivity.
        * apply join_r. apply sup_iff.
          intros [x' [y' [Hr' Ht']]]. cbn.
          apply (sup_at (exist _ y' Ht')). cbn. apply join_r.
          apply (sup_at (exist _ x' Hr')). reflexivity.
      + fcd. reflexivity.
  Qed.

  Context {G} (g: F ~> G).
  (** The lifting (-#S) preserves composition:

    S: Type, f: E ~> F, g: F ~> G ⊢ (g ∘ f) @ S = g@S ∘ f@S

   *)
  Lemma lift_subst_compose:
    slift (S:=X) (g @ f) = slift g @ slift f.
  Proof.
    unfold compose. apply antisymmetry;
      intros ? [? ? ?]; cbn; rewrite srun_slift; reflexivity.
  Qed.

End PROPS.

(** ** Extending adjunctions with relations *)

(** Given an adjunction ϕ: E ⇆ F and a relation R ⊆ S × Q, we can lift the
    adjunction to ϕ@R : E@S ⇆ F@Q. In particular for the language interface C
    simple and an effect signature E, we define an adjunction ϕ: E ⇆ C. With an
    abstraction relation R ⊆ S × mem, we further derive ϕ@R: E@S ⇆ C@mem. As a
    result, the Clight programs can compose with high level specifications.

    In particular, we extend with layer calculus to

      (L1, γ) ⊢R M : (L2, δ)

    where L1: 1 → E@S1 and L2: 1 → F@S2 with γ: E ⇆ C and δ: F ⇆ C. R is the
    abstraction relation between S2 and (mem, S1)

    We interpret the layer calculus as

      L2 ⊑ (δ@R)^ ∘ Clight(M)@S1 ∘ (u ∘ γ^ )@S1 ∘ L1 *)

Section LIFT.

  Context {E F} (phi: E <=> F).
  Context {X Y} (R: X -> Y -> Prop).

  (** E#X ~> F#Y := F#X ~> F#Y ∘ E#X ~> F#X *)
  Definition left_arr: E # X ~> F # Y := (left_arrow (rel_adj R)) @ (slift (left_arrow phi)).
  Definition right_arr: F # Y ~> E # X := (slift (right_arrow phi)) @ (right_arrow (rel_adj R)).

  Lemma lift_epsilon: left_arr @ right_arr [= identity.
  Proof.
    unfold left_arr, right_arr. etransitivity.
    - instantiate (1 := (left_arrow (rel_adj R) @ (slift (left_arrow phi)) @ slift (right_arrow phi)) @ right_arrow (rel_adj R)).
      rewrite !compose_assoc. reflexivity.
    - rewrite <- lift_subst_compose. rewrite epsilon.
      rewrite slift_identity. rewrite compose_unit_r.
      apply epsilon.
  Qed.

  Lemma lift_eta: identity [= right_arr @ left_arr.
  Proof.
    unfold left_arr, right_arr. etransitivity.
    - instantiate (1 := (slift (right_arrow phi) @ (right_arrow (rel_adj R)) @ left_arrow (rel_adj R)) @ slift (left_arrow phi)).
      rewrite <- eta. rewrite compose_unit_r.
      rewrite <- lift_subst_compose. rewrite <- eta.
      rewrite slift_identity. reflexivity.
    - rewrite !compose_assoc. reflexivity.
  Qed.

  Program Definition lift_adjunction : E # X <=> F # Y :=
    {|
      left_arrow := left_arr;
      right_arrow := right_arr;
      epsilon := lift_epsilon;
      eta := lift_eta;
    |}.

End LIFT.

Section FUNCTOR.

  Context {E F G} (phi: E <=> F) (psi: F <=> G).
  Context {X Y Z} (R: X -> Y -> Prop) (S: Y -> Z -> Prop).
  Let comp_lift := lift_adjunction (adjunction_compose phi psi) (rel_compose R S).
  Let lift_comp := adjunction_compose (lift_adjunction phi R) (lift_adjunction psi S).

  Lemma left_arrow_commute: left_arrow comp_lift = left_arrow lift_comp.
  Proof.
    unfold comp_lift, lift_comp.
    cbn. unfold left_arr. unfold adjunction_compose. cbn.
  Abort.

End FUNCTOR.
