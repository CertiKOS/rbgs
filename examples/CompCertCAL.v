From Coq Require Import
     Relations
     RelationClasses
     List
     FunctionalExtensionality.
From models Require Import
     IntSpec.
From examples Require Import
     CAL CompCertIntSpec.
From lattices Require Import
     Upset Downset FCD.
From structures Require Import
     Effects Lattice.
From compcert Require Import
     Memory AST Values
     Clight Ctypes
     LanguageInterface
     Events Globalenvs
     Smallstep.
From compcertox Require
     CModule.
Import ListNotations ISpec.

Obligation Tactic := idtac.
(** ** Preliminaries *)

(** *** Adjunctions as generalized relations *)

(** An adjunction A ⇆ B is a pair or morphisms which can "cancel" each other *)
(* TODO: a more general formalization of adjunctions? *)
(* A is the high level specification; B is the low level implementation *)
Class poset_adjunction (A B: esig) :=
  {
    up_arrow : A ~> B;
    down_arrow : B ~> A;
    epsilon : up_arrow @ down_arrow [= identity;
    eta : identity [= down_arrow @ up_arrow;
  }.
Arguments up_arrow {_ _}.
Arguments down_arrow {_ _}.
Arguments epsilon {_ _}.
Arguments eta {_ _}.

Infix "<=>" := poset_adjunction (at level 50).

(** In particular, the calling conventions in CompCertO forms an adjunction *)
Program Definition cc_adjunction {liA liB} (cc: callconv liA liB):
  poset_adjunction liA liB :=
  {|
    up_arrow := cc_up cc;
    down_arrow := cc_down cc;
    epsilon := cc_epsilon cc;
    eta := cc_eta cc;
  |}.

Global Instance pbind_proper_ref {E A B}:
  Proper ((pointwise_relation _ ref) ++> ref ++> ref) (@pbind E A B).
Proof.
  intros f g H x y Hx. induction Hx; cbn.
  - apply H.
  - reflexivity.
  - apply join_l. reflexivity.
  - apply join_lub.
    + apply join_l. reflexivity.
    + apply join_r. now rstep.
Qed.

Instance compose_proper_ref {A B C}:
  Proper (ref ++> ref ++> ref) (@compose A B C).
Proof.
  intros f1 f2 Hf g1 g2 Hg. unfold compose.
  intros ar m. unfold apply.
  apply ext_proper_ref; try typeclasses eauto.
  - intros c. induction c; cbn.
    + reflexivity.
    + unfold bind. rstep. apply Hg.
    + unfold bind.
      apply ext_proper_ref; try typeclasses eauto.
      * intros p. apply pbind_proper_ref. intros x.
        apply sup_iff. intros xn. now apply (sup_at xn).
        reflexivity.
      * apply Hg.
  - apply Hf.
Qed.

Lemma compose_unit_l {E F} (f: E ~> F):
  identity @ f = f.
Proof.
  unfold ISpec.compose, identity.
  apply functional_extensionality_dep. intros ar.
  apply functional_extensionality_dep. intros m.
  intm. reflexivity.
Qed.

Lemma compose_unit_r {E F} (f: E ~> F):
  f @ identity = f.
Proof.
  unfold ISpec.compose, identity.
  apply functional_extensionality_dep. intros ar.
  apply functional_extensionality_dep. intros m.
  intm. reflexivity.
Qed.

(** *** Composition and identity of adjunctions *)

Program Definition adjunction_compose {A B C} (phi: A <=> B) (psi: B <=> C) :=
  {|
    (* A ~> C := B ~> C @ A ~> B *)
    up_arrow := up_arrow psi @ up_arrow phi;
    (* C ~> A := B ~> A @ C ~> B *)
    down_arrow := down_arrow phi @ down_arrow psi;
  |}.
Next Obligation.
  intros *. etransitivity.
  instantiate (1 := up_arrow psi @ (up_arrow phi @ down_arrow phi) @ down_arrow psi).
  rewrite !ISpec.compose_assoc. reflexivity.
  rewrite epsilon. rewrite compose_unit_l. apply epsilon.
Qed.
Next Obligation.
  intros *. etransitivity.
  instantiate (1 := down_arrow phi @ (down_arrow psi @ up_arrow psi) @ up_arrow phi).
  rewrite <- eta. rewrite compose_unit_l. apply eta.
  rewrite !ISpec.compose_assoc. reflexivity.
Qed.

Unset Asymmetric Patterns.

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

  Definition rel_up: E # X ~> E # Y :=
    fun _ '(st m y) => sup { x | R x y },
    nx' <- int (st m x);
    let '(n, x') := nx' in
    inf { y' | R x' y' }, ret (n, y').
  Definition rel_down: E # Y ~> E # X :=
    fun _ '(st m x) => inf { y | R x y },
    ny' <- int (st m y);
    let '(n, y') := ny' in
    sup { x' | R x' y' }, ret (n, x').

  Program Definition rel_adj: E # X <=> E # Y :=
    {|
      up_arrow := rel_up;
      down_arrow := rel_down;
    |}.
  Next Obligation.
    unfold rel_up, rel_down, compose, identity. cbn.
    intros ? mk. destruct mk as [? m y0].
    setoid_rewrite Sup.mor. apply sup_iff. intros [x0 H]. cbn.
    rewrite apply_bind. rewrite apply_int_r.
    setoid_rewrite Inf.mor. apply (inf_at (exist _ y0 H)). cbn.
    repeat setoid_rewrite Sup.mor. apply sup_iff. intros [[n0 y1]|].
    - setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite Sup.mor_join. apply join_lub.
      + setoid_rewrite FCD.ext_ana. cbn.
        apply (sup_at None). reflexivity.
      + repeat setoid_rewrite Sup.mor.
        apply sup_iff. intros [x1 H1]. cbn.
        repeat setoid_rewrite FCD.ext_ana. cbn.
        apply join_lub.
        * apply (sup_at None). reflexivity.
        * repeat setoid_rewrite Inf.mor.
          apply (inf_at (exist _ y1 H1)). cbn.
          setoid_rewrite FCD.ext_ana. cbn.
          setoid_rewrite FCD.ext_ana.
          apply (sup_at (Some (n0, y1))). reflexivity.
    - setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      apply (sup_at None). reflexivity.
  Qed.
  Next Obligation.
  Admitted.

  Definition rel_down_inline {ar} (x: X) (t: ispec E ar) : ispec (E # Y) (ar * X) :=
    inf { y | R x y },
    ny' <- srun y t;
    let '(n, y') := ny' in
    sup { x' | R x' y' },
    ret (n, x').

  (* I think there's something more fundamental behind this lemma *)
  Lemma rel_apply {ar} (t: ispec E ar) (x: X):
    apply rel_down (srun x t) [= rel_down_inline x t.
  Proof.
    unfold rel_down_inline. unfold srun.
    apply inf_iff. intros [y Hr]. cbn.
    edestruct (FCD.join_meet_dense t) as (I & J & c & Hc). subst t.
    repeat setoid_rewrite Sup.mor.
    repeat setoid_rewrite Inf.mor.
    apply sup_iff. intros i. apply (sup_at i).
    apply inf_iff. intros j. apply (inf_at j).
    setoid_rewrite FCD.ext_ana.

    revert x y Hr. induction (c i j); intros x y Hr; cbn.
    + setoid_rewrite FCD.ext_ana. cbn.
      eapply (fsup_at x). assumption. reflexivity.
    + setoid_rewrite FCD.ext_ana. cbn.
      unfold bind.
      setoid_rewrite Inf.mor. eapply (inf_at (exist _ y Hr)). cbn.
      repeat setoid_rewrite Sup.mor. apply sup_iff.
      intros [[n y']|].
      * rewrite FCD.ext_ana. cbn.
        rewrite Sup.mor_join. apply join_lub.
        -- rewrite FCD.ext_ana. reflexivity.
        -- repeat setoid_rewrite Sup.mor.
           apply sup_iff. intros [x' H']. cbn.
           repeat setoid_rewrite FCD.ext_ana. cbn.
           apply join_lub.
           ++ reflexivity.
           ++ rewrite Sup.mor_bot. apply bot_lb.
      * rewrite FCD.ext_ana. cbn.
        rewrite FCD.ext_ana. cbn. reflexivity.
    + setoid_rewrite Sup.mor. apply sup_iff. intros [xr|].
      * rewrite apply_fmap_cons. cbn.
        setoid_rewrite Inf.mor. apply (inf_at (exist _ y Hr)). cbn.
        repeat setoid_rewrite Sup.mor. apply sup_iff.
        intros [[n' y']|].
        -- apply (sup_at (Some y')).
           setoid_rewrite FCD.ext_ana. cbn.
           rewrite Sup.mor_join. apply join_lub.
           ++ setoid_rewrite FCD.ext_ana. cbn.
              unfold bind.
              {
                destruct p.
                - cbn. unfold FCD.map.
                  repeat setoid_rewrite FCD.ext_ana. cbn.
                  apply join_l. reflexivity.
                - cbn. repeat setoid_rewrite FCD.ext_ana. cbn.
                  apply join_l. reflexivity.
                - cbn. unfold FCD.map.
                  repeat setoid_rewrite Sup.mor.
                  apply (sup_at None).
                  repeat setoid_rewrite FCD.ext_ana. cbn.
                  apply join_l. reflexivity.
              }
           ++ repeat setoid_rewrite Sup.mor.
              apply sup_iff. intros [x' H']. cbn.
              setoid_rewrite FCD.ext_ana.
              setoid_rewrite FCD.ext_ana. cbn.
              apply join_lub.
              ** unfold bind.
                 {
                   destruct p.
                   - cbn. unfold FCD.map.
                     repeat setoid_rewrite FCD.ext_ana. cbn.
                     apply join_l. reflexivity.
                   - cbn. repeat setoid_rewrite FCD.ext_ana. cbn.
                     apply join_l. reflexivity.
                   - cbn. unfold FCD.map.
                     repeat setoid_rewrite Sup.mor.
                     apply (sup_at None).
                     repeat setoid_rewrite FCD.ext_ana. cbn.
                     apply join_l. reflexivity.
                 }
              ** rewrite Sup.mor. apply sup_iff.
                 intros Hn. inversion Hn. subst. clear Hn.
                 specialize (IHp _ _ H'). rewrite IHp. clear IHp.
                 unfold bind. unfold FCD.map.
                 rewrite !@FCD.ext_ext; try typeclasses eauto.
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
                   - intros pc.
                     setoid_rewrite FCD.ext_ana. cbn.
                     apply join_r. reflexivity.
                 }
        -- apply (sup_at None). unfold bind.
           setoid_rewrite FCD.ext_ana. cbn.
           setoid_rewrite FCD.ext_ana. cbn. reflexivity.
      * apply (sup_at None). unfold bind.
        setoid_rewrite FCD.ext_ana. cbn.
        setoid_rewrite Inf.mor. apply (inf_at (exist _ y Hr)). cbn.
        repeat setoid_rewrite Sup.mor.
        apply sup_iff. intros [[n' y']|].
        -- setoid_rewrite FCD.ext_ana. cbn.
           rewrite Sup.mor_join. apply join_lub.
           ++ setoid_rewrite FCD.ext_ana. cbn. reflexivity.
           ++ repeat setoid_rewrite Sup.mor.
              apply sup_iff. intros [x' H']. cbn.
              setoid_rewrite FCD.ext_ana. cbn.
              setoid_rewrite FCD.ext_ana. cbn.
              apply join_lub.
              ** reflexivity.
              ** rewrite Sup.mor_bot. apply bot_lb.
        -- setoid_rewrite FCD.ext_ana. cbn.
           setoid_rewrite FCD.ext_ana. cbn. reflexivity.
  Qed.

End LIFT.

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

    L2 ⊑ (δ@R)^ ∘ Clight(M)@S1 ∘ (u ∘ γ^ )@S1 ∘ L1

    Some type annotations:

    L1 : 1 → E@S1

    (u ∘ γ^ )@S1 : E@S1 → C@mem@S1 where u: C → C@mem

    Clight(M)@S1 : C@mem@S1 → C@mem@S1

    (δ@R)^ : F@S2 → C@mem@S1

 *)
Definition lift_subst_up {E F} {X Y} (f: E ~> F) (R: X -> Y -> Prop): E # X ~> F # Y :=
  fun _ '(st m y) => sup { x | R x y },
    nx' <- (srun x (f _ m));
    let '(n, x') := nx' in
    inf { y' | R x' y' }, ret (n, y').

(* This is equivalent to [apply rel_down (srun y (apply f ...))] *)
Definition lift_subst_down {E F} {X Y} (f: F ~> E) (R: Y -> X -> Prop): F # Y ~> E # X :=
  fun _ '(st m x) => inf { y | R y x },
    ny' <- (srun y (f _ m));
    let '(n, y') := ny' in
    sup { x' | R y' x' }, ret (n, x').

Section LIFT.

  Context {E F} (phi: E <=> F).
  Context {X Y} (R: X -> Y -> Prop).

  (* Definition up_arr: E # X ~> F # Y := lift_subst_up (up_arrow phi) R. *)
  (* Definition down_arr: F # Y ~> E # X := lift_subst_down (down_arrow phi) (flip R). *)
  Definition up_arr: E # X ~> F # Y := (up_arrow (rel_adj R)) @ (slift (up_arrow phi)).
  Definition down_arr: F # Y ~> E # X := (slift (down_arrow phi)) @ (down_arrow (rel_adj R)).

  (* Definition darr {ar} (f: ispec E ar) (x: X): ispec (F # Y) (ar * X) := *)
  (*   inf { y | R x y }, *)
  (*   ny' <- srun y (apply (down_arrow phi) f); *)
  (*   let '(n, y') := ny' in *)
  (*   sup { x' | R x' y'}, ret (n, x'). *)

  (* Definition darr' {ar} (f: ispec E ar) (x: X): ispec (F # Y) (ar * X) := *)
  (*   apply (down_arrow (rel_adj R)) (srun x (apply (down_arrow phi) f)). *)

  (* (* FIXME: generalize this lemma *) *)
  (* Lemma down_arr_foo {ar} (x: X) (t: ispec E ar): *)
  (*   apply down_arr (srun x t) [= darr t x. *)
  (* Proof. *)
  (* Admitted. *)
(*    unfold darr.
    (* unfold apply. unfold srun. unfold bind. *)
    apply antisymmetry.
    - apply inf_iff. intros [y Hr]. cbn.
      unfold apply. unfold srun. unfold bind at 1.
      destruct (FCD.join_meet_dense t) as (I & J & c & Hc).
      rewrite Hc.
      repeat rewrite Sup.mor.
      apply sup_iff. intros i. apply (sup_at i).
      repeat rewrite Inf.mor.
      apply inf_iff. intros j. apply (inf_at j).
      rewrite !FCD.ext_ana.
      induction (c i j); cbn.
      + rewrite !FCD.ext_ana. cbn.
        rewrite FCD.ext_ana. cbn.
        apply (sup_at (exist _ x Hr)). reflexivity.
      + rewrite FCD.ext_ana. cbn.
        unfold bind. unfold srun.
        setoid_rewrite Inf.mor.
        apply (inf_at (exist _ y Hr)). cbn.
        rewrite !@FCD.ext_ext; try typeclasses eauto.
        apply ext_proper_ref'.
        3: {
          intros p. induction p.
          - cbn. rewrite Sup.mor_bot.
            rewrite @FCD.ext_ana by admit. cbn.
            setoid_rewrite Sup.mor. apply sup_iff.
            intros [x' Hx']. cbn. unfold ret.
            rewrite FCD.ext_ana. cbn. reflexivity.
          - cbn. rewrite !@FCD.ext_ana by admit. cbn.
            rewrite !@FCD.ext_ana by admit. cbn. reflexivity.
          - cbn. setoid_rewrite Sup.mor. apply sup_iff.
            rewrite Sup.mor_join. intros [k'|].
            + apply join_r.
              admit.
            + admit.
        }
        admit. admit. admit. admit.
      + rewrite Sup.mor. apply sup_iff. intros [x'|].
        * setoid_rewrite srun_bind.
          setoid_rewrite bind_bind.
          admit.
        * admit.
    - Admitted.
*)
  Lemma lift_epsilon: up_arr @ down_arr [= identity.
  Proof.
    unfold up_arr, compose.
    intm. intros ar k.
    destruct k as [ar m y]. unfold identity.
    unfold rel_up.
    repeat setoid_rewrite Sup.mor. apply sup_iff. intros [x Rx]. cbn.
    apply sup_iff. intros [[n xr]|].
    - intm. unfold bind.
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite apply_bind. unfold down_arr at 3.
      rewrite <- apply_assoc.
      rewrite srun_slift.
      setoid_rewrite -> rel_apply.
      repeat setoid_rewrite Inf.mor.
      apply (inf_at (exist _ y Rx)). cbn.
      (* code below can be simplified *)
      pose proof (epsilon phi). unfold compose in H.
      specialize (H ar m). cbn in H.
      unfold identity in H.
      assert (Hx: srun y (apply (down_arrow phi) (up_arrow phi ar m)) [= srun y (int m)).
      { unfold srun. rauto. } clear H.
      (* until here *)
      rewrite Hx. rewrite srun_int.
      repeat setoid_rewrite Sup.mor.
      apply sup_iff. intros [[n' y']|].
      + setoid_rewrite FCD.ext_ana. cbn.
        repeat rewrite Sup.mor_join.
        apply join_lub.
        * setoid_rewrite FCD.ext_ana. cbn.
          setoid_rewrite FCD.ext_ana. cbn.
          apply (sup_at None). reflexivity.
        * repeat setoid_rewrite Sup.mor.
          apply sup_iff. intros [x' H']. cbn.
          repeat (setoid_rewrite FCD.ext_ana; cbn).
          rewrite Sup.mor_join. apply join_lub.
          -- rewrite FCD.ext_ana. cbn.
             apply (sup_at None). reflexivity.
          -- rewrite !Sup.mor. apply sup_iff. intros Hn.
             inversion Hn. subst. clear Hn.
             repeat setoid_rewrite FCD.ext_ana. cbn. apply join_lub.
             ++ apply (sup_at None). reflexivity.
             ++ repeat setoid_rewrite Inf.mor.
                apply (inf_at (exist _ y' H')).
                repeat (setoid_rewrite FCD.ext_ana; cbn).
                unfold int. apply (sup_at (Some (n, y'))).
                reflexivity.
      + repeat (setoid_rewrite FCD.ext_ana; cbn).
        apply (sup_at None). reflexivity.
    - setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite apply_bind. unfold down_arr.
      rewrite <- !apply_assoc. rewrite srun_slift.
      setoid_rewrite rel_apply.
      setoid_rewrite Inf.mor. apply (inf_at (exist _ y Rx)). cbn.
      pose proof (epsilon phi). unfold compose in H.
      specialize (H ar m). cbn in H.
      unfold identity in H.
      assert (Hx: srun y (apply (down_arrow phi) (up_arrow phi ar m)) [= srun y (int m)).
      { unfold srun. rauto. } clear H.
      rewrite Hx. rewrite srun_int.
      repeat setoid_rewrite Sup.mor.
      apply sup_iff. intros [[n' y']|].
      + setoid_rewrite FCD.ext_ana. cbn.
        repeat rewrite Sup.mor_join.
        apply join_lub.
        * setoid_rewrite FCD.ext_ana. cbn.
          apply (sup_at None). reflexivity.
        * repeat setoid_rewrite Sup.mor.
          apply sup_iff. intros [x' H'].
          setoid_rewrite FCD.ext_ana. cbn.
          setoid_rewrite FCD.ext_ana. cbn.
          apply join_lub.
          -- apply (sup_at None). reflexivity.
          -- repeat rewrite Sup.mor_bot. apply bot_lb.
      + setoid_rewrite FCD.ext_ana. cbn.
        setoid_rewrite FCD.ext_ana. cbn.
        apply (sup_at None). reflexivity.
  Qed.

(*
    unfold up_arr, compose.
    unfold lift_subst_up.
    intm. intros ar k.
    destruct k as [ar m y]. unfold identity.
    setoid_rewrite Sup.mor. apply sup_iff. intros [x Rx]. cbn.
    pose proof (epsilon phi). unfold compose in H.
    specialize (H ar m). cbn in H.
    unfold identity in H.
    rewrite apply_bind. unfold bind.
    assert (Hx: srun y (apply (down_arrow phi) (up_arrow phi ar m)) [= srun y (int m)).
    { unfold srun. rauto. } clear H.
    (* rewrite <- srun_slift in Hx. rewrite srun_int in Hx. *)
    unfold down_arr at 2.
    rewrite down_arr_foo.
    setoid_rewrite Inf.mor. apply (inf_at (exist _ y Rx)). cbn.
    unfold darr.
    unfold bind. rewrite Hx.
    rewrite srun_int.
    repeat setoid_rewrite Sup.mor. apply sup_iff.
    intros [[n y']|]; cbn.
    - rewrite FCD.ext_ana. cbn.
      rewrite Sup.mor_join. apply join_lub.
      + rewrite FCD.ext_ana. cbn.
        apply (sup_at None). reflexivity.
      + repeat setoid_rewrite Sup.mor.
        apply sup_iff. intros [x' Hx']. cbn.
        repeat setoid_rewrite FCD.ext_ana. cbn.
        apply join_lub.
        * apply (sup_at None). reflexivity.
        * apply (sup_at (Some (n, y'))).
          repeat setoid_rewrite Inf.mor.
          apply (inf_at (exist _ y' Hx')). cbn.
          unfold ret. setoid_rewrite FCD.ext_ana. cbn.
          setoid_rewrite FCD.ext_ana. reflexivity.
    - rewrite FCD.ext_ana. cbn.
      rewrite FCD.ext_ana. cbn.
      apply (sup_at None). reflexivity.
  Qed.
*)

  Lemma lift_eta: identity [= down_arr @ up_arr.
  Proof.
  Admitted.

  Program Definition lift_adjunction : E # X <=> F # Y :=
    {|
      up_arrow := up_arr;
      down_arrow := down_arr;
      epsilon := lift_epsilon;
      eta := lift_eta;
    |}.

End LIFT.

(** The language interface "C simple" which does not include the memory *)
Record c_query :=
  cq {
      cq_vf: val;
      cq_sg: signature;
      cq_args: list val;
    }.

Record c_reply :=
  cr { cr_retval: val; }.

Canonical Structure li_c :=
  {|
    query := c_query;
    reply := c_reply;
    entry := cq_vf;
  |}.

(** * Example: ring buffer and bounded queue *)

(** With CompCertO semantics embedded in the interaction specification, we
    substitute Clight programs for the layer implementation. *)

(** ** Language interfaces vs. effect signatures *)

(** We define "marshalling" transformations between coarse-grained language
    interfaces and fine-grained effect signatures as adjunctions, similar to the
    embedding of calling conventions. We lift the language interfaces with
    abstract states to smooth the convertion. To further connect the abstract
    states with values in memory blocks we use the calling conventions induced
    by the abstraction relations from CompCertOX. *)

Require Import Coqlib.

Definition set_id: positive := 101.
Definition get_id: positive := 102.
Definition inc1_id: positive := 103.
Definition inc2_id: positive := 104.
Definition enq_id: positive := 105.
Definition deq_id: positive := 106.

Section MARSHALL.

  (* TODO: there seems to be a problem with the definition of subst: the arity
     [ar] has to be the same for both E and F. *)
  Parameter spec_val_rel: CAL.val -> val -> Prop.
  Context (se: Genv.symtbl).

  Inductive val_rel : forall ar, ar -> val -> Prop :=
  | unit_val i: val_rel _ tt (Vint i)
  | nat_val n i:
    Integers.Int.intval i = Z.of_nat n -> val_rel _ n (Vint i)
  | spec_val sv v:
    spec_val_rel sv v -> val_rel _ sv v.

  Inductive rb_rel : forall ar, rb_sig ar -> val -> list val -> Prop :=
  | set_rel i v b ofs arg1 arg2:
    val_rel _ i arg1 -> val_rel _ v arg2 ->
    Genv.find_symbol se set_id = Some b ->
    rb_rel _ (set i v) (Vptr b ofs) [arg1;arg2]
  | get_rel i b ofs arg:
    val_rel _ i arg ->
    Genv.find_symbol se get_id = Some b ->
    rb_rel _ (CAL.get i) (Vptr b ofs) [arg]
  | inc1_rel b ofs:
    Genv.find_symbol se inc1_id = Some b ->
    rb_rel _ inc1 (Vptr b ofs) []
  | inc2_rel b ofs:
    Genv.find_symbol se inc2_id = Some b ->
    rb_rel _ inc2 (Vptr b ofs) [].

  Inductive bq_rel : forall ar, bq_sig ar -> val -> list val -> Prop :=
  | enq_rel v b ofs arg:
    val_rel _ v arg ->
    Genv.find_symbol se enq_id = Some b ->
    bq_rel _ (enq v) (Vptr b ofs) [arg]
  | deq_rel b ofs:
    Genv.find_symbol se get_id = Some b ->
    bq_rel _ deq (Vptr b ofs) [].

  Inductive args_type_check (vs: list val) (sg: signature) : Prop :=
  | args_tyck ts:
    Cop.val_casted_list vs ts ->
    typlist_of_typelist ts = sig_args sg ->
    args_type_check vs sg.
  Inductive retval_type_check (v: val) (sg: signature) : Prop :=
  | ret_tyck t:
    Cop.val_casted v t ->
    opttyp_of_type t = sig_res sg ->
    retval_type_check v sg.

  (** Morphisms that compose the adjunctions Erb ⇆ C and Ebq ⇆ C *)

  Definition rb_up: rb_sig ~> li_c :=
    fun _ '(li_sig q) =>
      match q with
      | cq vf sg args =>
          _ <- assert (args_type_check args sg);
          sup ar, sup { m | rb_rel ar m vf args },
          n <- int m;
          inf { r | val_rel ar n r /\ retval_type_check r sg },
          ret (cr r)
      end.
  Definition rb_down: li_c ~> rb_sig :=
    fun _ m =>
      inf vf, inf sg, inf { args | rb_rel _ m vf args /\ args_type_check args sg},
      r <- query_int (cq vf sg args);
      match r with
      | cr retval =>
        sup { n | val_rel _ n retval }, ret n
      end.

  Definition bq_up: bq_sig ~> li_c :=
    fun _ '(li_sig q) =>
      match q with
      | cq vf sg args =>
          _ <- assert (args_type_check args sg);
          sup ar, sup { m | bq_rel ar m vf args },
          n <- int m;
          inf { r | val_rel ar n r /\ retval_type_check r sg },
          ret (cr r)
      end.
  Definition bq_down: li_c ~> bq_sig :=
    fun _ m =>
      inf vf, inf sg, inf { args | bq_rel _ m vf args /\ args_type_check args sg},
      r <- query_int (cq vf sg args);
      match r with
      | cr retval =>
        sup { n | val_rel _ n retval }, ret n
      end.

End MARSHALL.

(** ** Definition of Clight program *)
Definition arr_id: positive := 1.
Definition cnt1_id: positive := 2.
Definition cnt2_id: positive := 3.
Definition get_arg_id: positive := 1.
Definition set_arg1_id: positive := 1.
Definition set_arg2_id: positive := 2.
Definition enq_arg_id: positive := 1.

Require Import Maps.

Section CLIGHT.
  Notation tint := (Tint I32 Unsigned noattr).
  Notation tarray := (fun ty size => Tarray ty size noattr).
  Notation tptr := (fun ty => Tpointer ty noattr).
  Notation tvoid := (Tvoid).

  Definition Nz: Z := Z.of_nat CAL.N.

  (**
<<
    int get(int i) {
      return arr[i];
    }
>>
   *)
  Definition rb_get_body : statement :=
    Sreturn
      (Some
         (Ederef
            (Ebinop Cop.Oadd
                    (Evar arr_id (tarray tint Nz))
                    (Evar get_arg_id tint)
                    (tptr tint))
            tint)).
  Definition rb_get : function :=
    {|
      fn_return := tint;
      fn_callconv := cc_default;
      fn_params := [(get_arg_id, tint)];
      fn_vars := [];
      fn_temps := [];
      fn_body := rb_get_body;
    |}.

  (**
<<
    void set(int i, int v) {
      arr[i] = v;
    }
>>
   *)
  Definition rb_set_body : statement :=
    Sassign
      (Ederef
         (Ebinop Cop.Oadd
                 (Evar arr_id (tarray tint Nz))
                 (Evar set_arg1_id tint)
                 (tptr tint))
         tint)
      (Evar set_arg2_id tint).
  Definition rb_set : function :=
    {|
      fn_return := tvoid;
      fn_callconv := cc_default;
      fn_params := [(set_arg1_id, tint); (set_arg2_id, tint)];
      fn_vars := [];
      fn_temps := [];
      fn_body := rb_set_body;
    |}.
  (**
<<
    int inc1() {
      cnt1 += 1;
      return cnt1;
    }
>>
  *)
  Definition rb_inc1_body : statement :=
    Sassign
      (Ederef (Evar cnt1_id tint) tint)
      (Ebinop Cop.Oadd
              (Evar cnt1_id tint)
              (Econst_int (Integers.Int.repr 1) tint)
              tint).
  Definition rb_inc1 : function :=
    {|
      fn_return := tvoid;
      fn_callconv := cc_default;
      fn_params := [];
      fn_vars := [];
      fn_temps := [];
      fn_body := rb_inc1_body;
    |}.

  (**
<<
    int inc2() {
      cnt2 += 1;
      return cnt2;
    }
>>
  *)
  Definition rb_inc2_body : statement :=
    Sassign
      (Ederef (Evar cnt2_id tint) tint)
      (Ebinop Cop.Oadd
              (Evar cnt2_id tint)
              (Econst_int (Integers.Int.repr 1) tint)
              tint).
  Definition rb_inc2 : function :=
    {|
      fn_return := tvoid;
      fn_callconv := cc_default;
      fn_params := [];
      fn_vars := [];
      fn_temps := [];
      fn_body := rb_inc2_body;
    |}.
  (* FIXME: *)
  Definition arr_gvar : globvar type :=
    {|
      gvar_info := tarray tint Nz;
      gvar_init := [Init_space (Nz * 4)];
      gvar_readonly := false;
      gvar_volatile := false;
    |}.
  Program Definition rb_program: Clight.program :=
    {|
      prog_defs := [(get_id, Gfun (Internal rb_get));
        (set_id, Gfun (Internal rb_set));
        (inc1_id, Gfun (Internal rb_inc1));
        (inc2_id, Gfun (Internal rb_inc2));
        (arr_id, Gvar arr_gvar)];
      prog_public := [get_id; set_id; inc1_id; inc2_id];
      prog_main := 999%positive;
      prog_types := [];
      prog_comp_env := (PTree.empty _);
    |}.
  Next Obligation. reflexivity. Qed.

  (**
<<
    void enq(int v) {
      int i = inc2();
      set(i, v);
    }
>>
   *)

  Definition bq_enq_tmp : positive := 2.
  Definition bq_enq_body : statement :=
    Ssequence
      (Scall (Some bq_enq_tmp) (Evar inc2_id (Tfunction Tnil tvoid cc_default)) nil)
      (Scall None (Evar set_id (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
             ([Evar bq_enq_tmp tint; Evar enq_arg_id tint])).
  Definition bq_enq : function :=
    {|
      fn_return := tvoid;
      fn_callconv := cc_default;
      fn_params := [(enq_arg_id, tint)];
      fn_vars := [];
      fn_temps := [(bq_enq_tmp, tint)];
      fn_body := bq_enq_body;
    |}.

  (**
<<
    int deq() {
      int i = inc1();
      return get(i);
    }
>>
   *)
  Definition bq_deq_tmp1 : positive := 1.
  Definition bq_deq_tmp2 : positive := 2.
  Definition bq_deq_body : statement :=
    Ssequence
      (Scall (Some bq_deq_tmp1) (Evar inc1_id (Tfunction Tnil tvoid cc_default)) nil)
      (Ssequence
         (Scall (Some bq_deq_tmp2) (Evar get_id (Tfunction (Tcons tint Tnil) tint cc_default))
                ([Evar bq_deq_tmp1 tint]))
         (Sreturn (Some (Evar bq_deq_tmp2 tint)))).
  Definition bq_deq : function :=
    {|
      fn_return := tint;
      fn_callconv := cc_default;
      fn_params := [];
      fn_vars := [];
      fn_temps := [(bq_deq_tmp1, tint); (bq_deq_tmp2, tint)];
      fn_body := bq_enq_body;
    |}.

  Program Definition bq_program : Clight.program :=
    {|
      prog_defs := [(enq_id, Gfun (Internal bq_enq)); (deq_id, Gfun (Internal bq_deq))];
      prog_public := [enq_id; deq_id];
      prog_main := 999%positive;
      prog_types := [];
      prog_comp_env := (PTree.empty _);
    |}.
  Next Obligation. reflexivity. Qed.

End CLIGHT.

(** ** Correctness  *)
Section CORRECT.
(*
  Context (se:Genv.symtbl).

  (** L_rb ⊑ R_rb ∘ ⟦M_rb⟧ ∘ ⊥ *)
  Lemma rb_correct:
    L_rb [= rb_down @ ang_lts_spec (Clight.semantics1 rb_program se) @ bot.
  Admitted.

  (** L_bq ⊑ R_bq ∘ ⟦M_bq⟧ ∘ R_rb ∘ L_rb *)
  Lemma bq_correct:
    L_bq [= bq_down @ ang_lts_spec (Clight.semantics1 bq_program se) @ rb_up @ L_rb.
  Admitted.

  Context (sk: AST.program unit unit).
  (** Vertical composition
      L_bq ⊑ R_bq ∘ ⟦M_bq⟧ ∘ R_rb ∘ R_rb ∘ ⟦M_rb⟧ ∘ ⊥
           ⊑ R_bq ∘ ⟦M_bq⟧ ∘ ⟦M_rb⟧ ∘ ⊥
           ⊑ R_bq ∘ ⟦M_bq ∘ M_rb⟧ ∘ ⊥
           ⊑ R_bq ∘ ⟦M_bq + M_rb⟧ ∘ ⊥ *)
  Lemma rb_bq_correct:
    L_bq [= bq_down @ ang_lts_spec (CModule.semantics [rb_program; bq_program] sk se) @ bot.
  Admitted.
*)
End CORRECT.
