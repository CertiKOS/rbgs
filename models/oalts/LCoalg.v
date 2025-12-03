Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.Pullbacks.

Require Import ProofIrrelevance.

Module LCoalg (L C : Category) (F : BifunctorDefinition L C C) <: Category.
  Import C.

  Record coalg :=
    mk_coalg {
      labels : L.t;
      states : C.t;
      step :> C.m states (F.omap labels states);
    }.

  Record coalg_mor (α β : coalg) :=
    mk_coalg_mor {
      morL : L.m (labels α) (labels β);
      morS : C.m (states α) (states β);
      coalg_sim_cond :
        β @ morS = (F.fmap morL morS) @ α;
    }.
  Arguments morL {_ _}.
  Arguments morS {_ _}.
  Arguments coalg_sim_cond {_ _}.

  Definition t : Type := coalg.

  Definition m (α β : t) : Type := coalg_mor α β.

  Lemma meq {α β : coalg} (f : m α β) (g : m α β) :
    (morL f) = (morL g) -> (morS f) = (morS g) -> f = g.
  Proof.
    destruct f as [fl fs Hf]; destruct g as [gl gs Hg].
    cbn. intros Hl Hs. subst. f_equal. apply proof_irrelevance.
  Qed.

  Program Definition id (α : t) : m α α :=
  {|
    morL := L.id (labels α);
    morS := C.id (states α);
  |}.
  Next Obligation.
    rewrite C.compose_id_right.
    rewrite F.fmap_id. rewrite C.compose_id_left. reflexivity.
  Defined.

  Program Definition compose {α β γ} (g : m β γ) (f : m α β) : m α γ :=
  {|
    morL := L.compose (morL g) (morL f);
    morS := (morS g) @ (morS f);
  |}.
  Next Obligation.
    rewrite <- compose_assoc. rewrite coalg_sim_cond. rewrite compose_assoc.
    rewrite coalg_sim_cond. rewrite <- compose_assoc.
    rewrite <- F.fmap_compose. reflexivity.
  Defined.

  Proposition compose_id_left :
    forall {A B} (f : m A B), compose (id B) f = f.
  Proof.
    intros. unfold compose, id. simpl.
    apply meq; cbn. rewrite L.compose_id_left; reflexivity.
    rewrite C.compose_id_left; reflexivity.
  Qed.

  Proposition compose_id_right :
    forall {A B} (f : m A B), compose f (id A) = f.
  Proof.
    intros. unfold compose, id. simpl.
    apply meq; cbn. rewrite L.compose_id_right; reflexivity.
    rewrite C.compose_id_right; reflexivity.
  Qed.

  Proposition compose_assoc :
    forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
    compose (compose h g) f = compose h (compose g f).
  Proof.
    intros. unfold compose. simpl.
    apply meq; cbn. rewrite L.compose_assoc; reflexivity.
    rewrite C.compose_assoc; reflexivity.
  Qed.

  Include CategoryTheory.
End LCoalg.

Module LCoalgWithPullbacks
  (Lab : Category) (PbLab : Pullbacks Lab)
  (St : Category) (PbSt : Pullbacks St)
  (F : BifunctorDefinition Lab St St)
  (FPb : BifunctorPreservesPullbacks Lab PbLab St PbSt St PbSt F)
  <: CategoryWithPullbacks.

  (* The category of coalgebras *)
  Module C := LCoalg Lab St F.

  (* Pullbacks for coalgebras, computed componentwise *)
  Module Pb : Pullbacks C.
    Import C.
    Import PbLab.
    Import PbSt.

    Section PbProd.
      Variables (α β γ : t) (f : m α γ) (g : m β γ).

      (* The pullback of labels and states *)
      Definition labP := PbLab.pb_prod (morL f) (morL g).
      Definition stP := PbSt.pb_prod (morS f) (morS g).

      (* F(labP, stP) is a pullback by preservation *)
      Definition F_pb : PbSt.IsPullback
            (F.fmap (morL f) (morS f)) (F.fmap (morL g) (morS g))
            (F.fmap (PbLab.pb_p1 (morL f) (morL g)) (PbSt.pb_p1 (morS f) (morS g)))
            (F.fmap (PbLab.pb_p2 (morL f) (morL g)) (PbSt.pb_p2 (morS f) (morS g))) :=
        FPb.preserves_pb_joint
          (PbLab.pb_is_pb (morL f) (morL g))
          (PbSt.pb_is_pb (morS f) (morS g)).

      (* The cone condition: both paths go to γ.step ∘ (common morphism) *)
      Definition step_cone : St.compose (F.fmap (morL f) (morS f)) (St.compose (step α) (PbSt.pb_p1 (morS f) (morS g)))
                    = St.compose (F.fmap (morL g) (morS g)) (St.compose (step β) (PbSt.pb_p2 (morS f) (morS g))).
      Proof.
        (* Use simulation conditions and pullback square *)
        rewrite <- !St.compose_assoc.
        rewrite <- (coalg_sim_cond f).
        rewrite <- (coalg_sim_cond g).
        rewrite !St.compose_assoc.
        f_equal.
        exact (PbSt.pb_square (morS f) (morS g)).
      Defined.

      (* The step map for the pullback coalgebra *)
      Definition pb_step : St.m stP (F.omap labP stP) :=
        PbSt.is_pb_pair F_pb
          (St.compose (step α) (PbSt.pb_p1 (morS f) (morS g)))
          (St.compose (step β) (PbSt.pb_p2 (morS f) (morS g)))
          step_cone.
    End PbProd.

    Definition pb_prod {α β γ : t} (f : m α γ) (g : m β γ) : t :=
      {|
        labels := PbLab.pb_prod (morL f) (morL g);
        states := PbSt.pb_prod (morS f) (morS g);
        step := pb_step α β γ f g;
      |}.

    Program Definition pb_p1 {α β γ : t}
      (f : m α γ) (g : m β γ) : m (pb_prod f g) α :=
    {|
      morL := PbLab.pb_p1 (morL f) (morL g);
      morS := PbSt.pb_p1 (morS f) (morS g);
    |}.
    Next Obligation.
      unfold pb_step.
      rewrite (PbSt.is_pb_p1_pair (F_pb α β γ f g)).
      reflexivity.
    Defined.

    Program Definition pb_p2 {α β γ : t}
      (f : m α γ) (g : m β γ) : m (pb_prod f g) β :=
    {|
      morL := PbLab.pb_p2 (morL f) (morL g);
      morS := PbSt.pb_p2 (morS f) (morS g);
    |}.
    Next Obligation.
      unfold pb_step.
      rewrite (PbSt.is_pb_p2_pair (F_pb α β γ f g)).
      reflexivity.
    Defined.

    Definition pb_cone {α β γ : t} (f : m α γ) (g : m β γ)
      {δ} (ll : m δ α) (rl : m δ β) : Prop :=
      C.compose f ll = C.compose g rl.

    Program Definition pb_pair {α β γ : t} {f : m α γ} {g : m β γ}
      {δ : t} {ll : m δ α} {rl : m δ β}
      (sq : pb_cone f g ll rl) : m δ (pb_prod f g) :=
    {|
      morL := PbLab.pb_pair (ll := morL ll) (rl := morL rl) _;
      morS := PbSt.pb_pair (ll := morS ll) (rl := morS rl) _;
    |}.
    Next Obligation.
      unfold pb_cone, PbLab.pb_cone in *.
      inversion sq. reflexivity.
    Qed.
    Next Obligation.
      unfold pb_cone, PbSt.pb_cone in *.
      inversion sq. reflexivity.
    Qed.
    Next Obligation.
      (* Both sides are maps into pullback F(labP, stP), show they equal the same is_pb_pair *)
      set (ll_cone := St.compose (step α) (morS ll)).
      set (rl_cone := St.compose (step β) (morS rl)).

      (* Need a proof that ll_cone and rl_cone form a cone *)
      assert (cone_eq : St.compose (F.fmap (morL f) (morS f)) ll_cone
                      = St.compose (F.fmap (morL g) (morS g)) rl_cone).
      { unfold ll_cone, rl_cone.
        rewrite <- !St.compose_assoc.
        rewrite <- (coalg_sim_cond f), <- (coalg_sim_cond g).
        rewrite !St.compose_assoc.
        f_equal.
        unfold pb_cone in sq. inversion sq. reflexivity. }

      transitivity (PbSt.is_pb_pair (F_pb α β γ f g) ll_cone rl_cone cone_eq).
      - (* LHS = is_pb_pair *)
        apply (PbSt.is_pb_uni (F_pb α β γ f g)).
        + unfold pb_step, ll_cone.
          rewrite <- St.compose_assoc.
          rewrite (PbSt.is_pb_p1_pair (F_pb α β γ f g)).
          rewrite St.compose_assoc.
          rewrite PbSt.pb_p1_pair. reflexivity.
        + unfold pb_step, rl_cone.
          rewrite <- St.compose_assoc.
          rewrite (PbSt.is_pb_p2_pair (F_pb α β γ f g)).
          rewrite St.compose_assoc.
          rewrite PbSt.pb_p2_pair. reflexivity.
      - (* is_pb_pair = RHS *)
        symmetry.
        apply (PbSt.is_pb_uni (F_pb α β γ f g)).
        + unfold ll_cone.
          rewrite <- St.compose_assoc.
          rewrite <- F.fmap_compose.
          rewrite !PbLab.pb_p1_pair, !PbSt.pb_p1_pair.
          symmetry. exact (coalg_sim_cond ll).
        + unfold rl_cone.
          rewrite <- St.compose_assoc.
          rewrite <- F.fmap_compose.
          rewrite !PbLab.pb_p2_pair, !PbSt.pb_p2_pair.
          symmetry. exact (coalg_sim_cond rl).
    Defined.

    Proposition pb_square : forall {α β γ : t} (f : m α γ) (g : m β γ),
      pb_cone f g (pb_p1 f g) (pb_p2 f g).
    Proof.
      intros. unfold pb_cone.
      apply meq; cbn.
      apply PbLab.pb_square. apply PbSt.pb_square.
    Qed.

    Proposition pb_p1_pair : forall {α β γ : t} {f : m α γ} {g : m β γ}
      {δ : t} {ll : m δ α} {rl : m δ β} (sq : pb_cone f g ll rl),
      C.compose (pb_p1 f g) (pb_pair sq) = ll.
    Proof.
      intros. apply meq. apply PbLab.pb_p1_pair. apply PbSt.pb_p1_pair.
    Qed.

    Proposition pb_p2_pair : forall {α β γ : t} {f : m α γ} {g : m β γ}
      {δ : t} {ll : m δ α} {rl : m δ β} (sq : pb_cone f g ll rl),
      C.compose (pb_p2 f g) (pb_pair sq) = rl.
    Proof.
      intros. apply meq. apply PbLab.pb_p2_pair. apply PbSt.pb_p2_pair.
    Qed.

    Proposition pb_pair_uni : forall {α β γ : t} {f : m α γ} {g : m β γ}
      {δ : t} {ll : m δ α} {rl : m δ β}
      (sq : C.compose f ll = C.compose g rl)
      {p : m δ (pb_prod f g)},
      C.compose (pb_p1 f g) p = ll ->
      C.compose (pb_p2 f g) p = rl ->
      pb_pair sq = p.
    Proof.
      intros. apply meq; cbn.
      - apply PbLab.pb_pair_uni. exact (f_equal morL H). exact (f_equal morL H0).
      - apply PbSt.pb_pair_uni. exact (f_equal morS H). exact (f_equal morS H0).
    Qed.

    Include PullbacksTheory C.
  End Pb.

  Include C.
End LCoalgWithPullbacks.