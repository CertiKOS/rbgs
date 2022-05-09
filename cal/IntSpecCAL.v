From Coq Require Import
     List Lia.
From models Require Import
     IntSpec.
From lattices Require Import
     Upset Downset FCD.
From structures Require Import
     Effects Lattice.
From cal Require Import RefConv.
From compcert Require Import Coqlib.

Unset Asymmetric Patterns.

(** ** Auxiliaries *)

Import ISpec.

Class esig_iso {A B: esig} (X : poset_adjunction A B) :=
  {
    iso_inv_l : left_arrow X @ right_arrow X = identity;
    iso_inv_r : right_arrow X @ left_arrow X = identity;
  }.

(** Some auxiliary definitions *)
Inductive assoc {A B C: Type}: A * (B * C) -> A * B * C -> Prop :=
| assoc_intro a b c: assoc (a, (b, c)) ((a, b), c).
Inductive sig_assoc {E: esig} {S1 S2: Type}: rc_rel (E#(S1*S2)) (E#S1#S2) :=
| sig_assoc_intro ar (m: E ar) s1 s2 :
  sig_assoc _ (m # (s1, s2)) _ ((m # s1) # s2) assoc.
Inductive eq_comm {A B C: Type}: A * B * C -> A * C * B -> Prop :=
| eq_comm_intro a b c: eq_comm ((a, b), c) ((a, c), b).
Inductive sig_comm {E: esig} {S1 S2: Type}: rc_rel (E#S1#S2) (E#S2#S1) :=
| sig_comm_intro ar (m: E ar) s1 s2:
  sig_comm _ (m # s1 # s2) _ (m # s2 # s1) eq_comm.

Inductive comm {A B: Type}: A * B -> B * A -> Prop :=
| comm_intro a b: comm (a, b) (b, a).
Definition st_comm {E: esig} {S1 S2: Type}: rc_rel (E#(S1*S2)) (E#(S2*S1)) :=
  (rc_id * rel_rc comm)%rc.
Definition st_assoc {E: esig} {S1 S2 S3: Type}: rc_rel (E#(S1*(S2*S3))) (E#(S1*S2*S3)) :=
  (rc_id * rel_rc assoc)%rc.

(** Using type inference to make twisting on types more ergonomic *)
Class StrategyHelper E F := h: E ~> F.

Global Instance sig_assoc_right {E} {S1 S2} :
  StrategyHelper (E#S1#S2) (E#(S1*S2)) := right_arrow sig_assoc.

Notation "f @@ g" := (f @ h @ g).

Open Scope rc_scope.

Lemma assoc_inverse {E S1 S2}:
  left_arrow (@sig_assoc E S1 S2) @ right_arrow sig_assoc = identity.
Proof.
  apply antisymmetry. apply epsilon.
  cbn. unfold rc_adj_left, rc_adj_right, compose, identity.
  intros ? m. destruct m as [? ? [? ? m [s1]] [s2]].
  sup_mor. eapply sup_at.
  sup_mor. eapply sup_at.
  sup_mor. eapply fsup_at. rc_econstructor.
  unfold int at 1 3.
  sup_intro [[[n t1] t2]|].
  + apply (sup_at (Some (n, (t1, t2)))). fcd_simpl.
    sup_mor. apply join_r.
    inf_intro (x & Hx). inv Hx. fcd_simpl.
    inf_intro ?. inf_intro ?.
    inf_intro (R & HR). rc_elim (inv) HR. depsubst. clear_hyp.
    intm. unfold int.
    sup_mor. apply (sup_at (Some (n, t1, t2))). fcd_simpl.
    apply join_r. sup_mor. eapply fsup_at. apply Hsub. constructor.
    fcd_simpl. sup_mor. apply (sup_at eq_refl). now fcd_simpl.
  + apply (sup_at None). fcd_simpl.
    inf_intro ?. inf_intro ?.
    inf_intro (R & HR). rc_elim (inv) HR. depsubst. clear_hyp.
    intm. unfold int.
    sup_mor. apply (sup_at None). fcd_simpl. reflexivity.
Qed.

Lemma assoc_inverse' {E S1 S2}:
  right_arrow (@sig_assoc E S1 S2) @ left_arrow sig_assoc = identity.
Proof.
Admitted.

(** * CAL in the Strategy World *)
Close Scope Z_scope.

Record strategy_layer {E1 E2} {S1 S2} (U: Type) (L1: 0 ~> E1 # S1) (L2: 0 ~> E2 # S2) :=
  {
    strategy_impl: E1 ~> E2 # U;
    strategy_rel: S2 -> U * S1 -> Prop;

    (* L₂ ⊑ (E₂@R)_ ∘ (Σ@S₁) ∘ L₁ *)
    strategy_layer_ref:
      L2 [= right_arrow (rc_id * rel_rc strategy_rel) @@ slift strategy_impl @ L1;
  }.
Arguments strategy_impl {_ _ _ _ _ _ _}.
Arguments strategy_rel {_ _ _ _ _ _ _}.
Arguments strategy_layer_ref {_ _ _ _ _ _ _}.

(** ** Composition *)
Close Scope bool_scope.

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

Section PARAMETRICITY.

  Open Scope rc_scope.
  Context {S1 S2: Type} (R: S2 -> S1 -> Prop).
  Context {E1 E2: esig} (f: E1 ~> E2).

  (** f@S1 ∘ E1@R ⊑ E2@R ∘ f@S2 *)
  Lemma state_commute:
    slift (S:=S2) f @ right_arrow (rc_id (E:=E1) * rel_rc R) [=
      right_arrow (rc_id (E:=E2) * rel_rc R) @ slift (S:=S1) f.
  Proof.
    intros ar es2. destruct es2 as [ ? ? e2 [ s2 ] ].
    unfold compose. cbn. unfold rc_adj_right.
    inf_intro ar. inf_intro [ ? ? e2' [ s1 ] ]. inf_intro [Rx HRx].
    rc_inversion HRx. depsubst. clear_hyp. clear Hrel.
    rc_destruct H2. intm.
    rc_inversion H13. depsubst. clear_hyp. clear Hrel.
    generalize (f _ m). intros t.
    edestruct (FCD.join_meet_dense t) as (I & J & c & Hc). subst t.
    unfold srun.
    sup_intro i. apply (sup_at i).
    inf_intro j. apply (inf_at j).
    fcd_simpl. revert s1 s2 H4. induction (c i j); intros s1 s2 Hs; cbn.
    - fcd_simpl. sup_mor. eapply (fsup_at (v, s2)).
      + apply Hsub; split; eauto.
      + fcd_simpl. reflexivity.
    - fcd_simpl.
      inf_mor. eapply inf_at.
      inf_mor. apply (inf_at (st m0 s1)).
      inf_mor. eapply finf_at. rc_econstructor; rc_econstructor; eauto.
      sup_mor. sup_intro [ [ n s1' ] | ].
      + fcd_simpl. sup_mor. sup_mor. apply join_lub.
        * fcd_simpl. reflexivity.
        * sup_intro [ x' s2' ]. fcd_simpl.
          apply join_lub.
          -- reflexivity.
          -- sup_mor. apply bot_lb.
      + fcd_simpl. reflexivity.
    (* an angelic choice over all possible replies *)
    - sup_intro [ s2' | ].
      + rewrite apply_fmap_cons.
        inf_mor. eapply inf_at.
        inf_mor. apply (inf_at (st m0 s1)).
        inf_mor. eapply finf_at. rc_econstructor; rc_econstructor; eauto.
        unfold int at 2. sup_intro [ [ n' s1' ] | ].
        * apply (sup_at (Some s1')).
          fcd_simpl. sup_mor. sup_mor. apply join_lub.
          -- fcd_simpl. destruct p; cbn.
             ++ fcd_simpl. apply join_l. reflexivity.
             ++ fcd_simpl. apply join_l. reflexivity.
             ++ unfold FCD.map. sup_mor.
                apply (sup_at None). fcd_simpl.
                apply join_l. reflexivity.
          (* an angelic choice by R *)
          -- sup_intro [ [ n'' s2'' ] Hx ].
             destruct Hx. cbn [fst snd] in *. subst. fcd_simpl.
             apply join_lub.
             ++ destruct p; cbn.
                ** fcd_simpl. apply join_l. reflexivity.
                ** fcd_simpl. apply join_l. reflexivity.
                ** unfold FCD.map. sup_mor.
                   apply (sup_at None). fcd_simpl.
                   apply join_l. reflexivity.
             ++ sup_intro Heq. inversion Heq. subst. clear Heq.
                specialize (IHp _ _ H0). rewrite IHp. clear IHp.
                unfold FCD.map, bind, t. cbn. rewrite !FCD.ext_ext.
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
                  - intros pc. fcd_simpl. apply join_r. reflexivity.
                }
        * apply (sup_at None). fcd_simpl. reflexivity.
      + apply (sup_at None). fcd_simpl.
        inf_mor. eapply inf_at.
        inf_mor. apply (inf_at (st m0 s1)).
        inf_mor. eapply finf_at. rc_econstructor; rc_econstructor; eauto.
        unfold int. sup_intro [ [ n' s1' ] | ].
        * fcd_simpl. sup_mor. sup_mor.
          apply join_lub.
          -- fcd_simpl. reflexivity.
          -- sup_intro [ [ n'' s2' ] Hx ].
             destruct Hx. cbn [fst snd] in *. subst.
             fcd_simpl. apply join_lub.
             ++ reflexivity.
             ++ sup_mor. apply bot_lb.
        * fcd_simpl. reflexivity.
  Qed.

End PARAMETRICITY.

Global Instance sig_assoc_left {E} {S1 S2} :
  StrategyHelper (E#(S1*S2)) (E#S1#S2) := left_arrow sig_assoc.

Global Instance st_assoc_right {E} {S1 S2 S3} :
  StrategyHelper (E#(S1*S2*S3)) (E#(S1*(S2*S3))) := right_arrow st_assoc.

Global Instance st_assoc_left {E} {S1 S2 S3} :
  StrategyHelper (E#(S1*(S2*S3))) (E#(S1*S2*S3)) := left_arrow st_assoc.

(** Stateful sequential composition of strategies *)
Definition stateful_compose {E F G U1 U2} (f: F ~> G#U1) (g: E ~> F#U2) : E ~> G#(U1*U2) :=
  h @ slift f @ g.

Lemma rel_compose_ref {A B C X Y E} (rel1 : B -> (Y * C) -> Prop) (rel2 : A -> (X * B) -> Prop):
  right_arrow (rc_id(E:=E) * rel_rc rel2)
    @@ right_arrow (rc_id * rel_rc rel1) @@ h
    [= right_arrow (rc_id * rel_rc (rel_compose rel2 (rel_compose (eq * rel1) assoc))).
Proof.
  cbn. intros ? [? ? e [a]]. unfold rc_adj_right, compose.
  apply inf_iff. intros ?.
  apply inf_iff. intros [? ? e' [[[x y] c]]].
  apply inf_iff. intros [Rc HRc]. cbn.
  rc_elim (inv) HRc. depsubst. clear_hyp. rename Hsub into HRc.
  rc_destruct H2. rename Hsub into HR1.
  rc_elim (inv) H13. depsubst. clear_hyp. rename Hsub into HR2.
  destruct H3 as ((x', b) & Hrel2 & Hx).
  destruct Hx as ((x'', (y', c')) & (Hx & Hrel1) & Hy).
  cbn in Hx, Hrel1. inv Hy.
  inf_mor. eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
  { rc_econstructor; rc_econstructor. eauto. } intm.
  inf_mor. eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
  { rc_econstructor. } intm.
  inf_mor. eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
  { rc_econstructor; rc_econstructor. eauto. } intm.
  unfold rc_adj_left.
  sup_intro ?. sup_intro p. sup_intro (Rp & HRp).
  destruct p. destruct e0. destruct p. destruct  p.
  rc_elim (inv) HRp. depsubst. clear_hyp. rename Hsub into Hp.
  intm.
  inf_mor. eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
  { rc_econstructor; rc_econstructor. constructor. } intm.
  sup_intro [[n [[x' y'] c']]|].
  - fcd_simpl. apply join_lub.
    + apply (sup_at None). fcd_simpl. reflexivity.
    + apply (sup_at (Some (n, ((x', y'), c')))).
      fcd_simpl. apply join_r. rstep.
      sup_intro ((?, (?, (?, ?))) & Hw). inv Hw.
      cbn in H, H0. inv H0. fcd_simpl.
      inf_mor. eapply (finf_at (_, _, (_, _))).
      { apply Hp. constructor. } fcd_simpl.
      sup_intro (((?, ?), ?) & Hw). inv Hw. cbn in H, H0. inv H. fcd_simpl.
      sup_intro ((?,  (?, ?)) & Hw). inv Hw. fcd_simpl.
      sup_intro ((?, ?) & (Hw1 & Hw2)). cbn in Hw1, Hw2. subst. fcd_simpl.
      eapply (fsup_at (_, _)).
      {
        apply HRc. split; cbn.
        apply HR1. reflexivity.
        apply HR2. eexists; split. apply Hw2.
        eexists (_, (_, _)); split; constructor; eauto.
      }
      reflexivity.
  - apply (sup_at None). fcd_simpl. reflexivity.
Qed.

Lemma bar {E F: esig} {S1 S2} (f: E ~> F):
  slift(S:=S1*S2) f [= right_arrow sig_assoc @ slift (slift f) @ left_arrow sig_assoc.
Proof.
  intros ? [? ? m [[s1 s2]]]. cbn.
  unfold compose, rc_adj_right, rc_adj_left.
  inf_intro ?. inf_intro m'. inf_intro [ R HR ].
  rc_inversion HR. depsubst. clear_hyp. clear Hrel. intm.
  generalize (f _ m). intros t.
  edestruct (FCD.join_meet_dense t) as (I & J & c & Hc). subst t.
  sup_intro i. apply (sup_at i).
  inf_intro j. apply (inf_at j). fcd_simpl.
  revert s1 s2. induction (c i j); intros s1 s2.
  - fcd_simpl. sup_mor. eapply fsup_at.
    { apply Hsub. constructor. }
    fcd_simpl. reflexivity.
  - fcd_simpl.
    sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
    { rc_econstructor. }
    intm. sup_mor. sup_mor.
    apply (sup_at None). fcd_simpl. reflexivity.
  - cbn. apply sup_iff. intros [ [ x1 x2 ] | ].
    + sup_mor. apply (sup_at (Some x1)).
      rewrite IHp.
      generalize (stateful_play x1 p). intros px.
      edestruct (FCD.join_meet_dense px) as (I' & J' & c' & Hc'). subst px.
      sup_intro i'. apply (sup_at i').
      inf_intro j'. apply (inf_at j'). fcd_simpl.
      sup_mor. apply (sup_at (Some x2)).
      generalize (stateful_play x2 (c' i' j')). intros py.
      edestruct (FCD.join_meet_dense py) as (I'' & J'' & c'' & Hc''). subst py.
      sup_intro i''. apply (sup_at i'').
      inf_intro j''. apply (inf_at j''). fcd_simpl.
      match goal with
      | [ |- context[ papply ?f (c'' i'' j'') ] ] => set (fx := papply f (c'' i'' j''))
      end.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { rc_econstructor. }
      intm. unfold int at 3.
      sup_mor. apply (sup_at (Some (n, (x1, x2)))). fcd_simpl. apply join_r.
      inf_intro [ n' Hn ]. inv Hn. fcd_simpl.
      sup_mor. eapply (sup_at eq_refl). reflexivity.
    + sup_mor. apply (sup_at None). fcd_simpl.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { rc_econstructor. }
      intm. sup_mor. sup_mor. apply (sup_at None). fcd_simpl. reflexivity.
Qed.

Lemma assoc_lift {E F S1 S2} (f: E ~> F):
  slift f @ right_arrow sig_assoc [= right_arrow sig_assoc @ slift(S:=S2) (slift(S:=S1) f).
Proof.
  rewrite bar. rewrite !compose_assoc.
  rewrite epsilon. rewrite compose_unit_r. reflexivity.
Qed.

Lemma assoc_property {E S1 S2 S3}:
  right_arrow sig_assoc [=
    left_arrow sig_assoc @ right_arrow (st_assoc (E:=E) (S1:=S1) (S2:=S2) (S3:=S3))
                @ right_arrow sig_assoc @ slift (right_arrow sig_assoc).
Proof.
  intros ? [? ? [? ? m [s1]] [[s2 s3]]]. cbn.
  unfold rc_adj_right, rc_adj_left, compose.
  eapply inf_at. eapply inf_at. eapply finf_at.
  { rc_econstructor. }
  sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
  { rc_econstructor. } intm.
  inf_intro ?. inf_intro [? ? m' [[[t1 t2] t3]]].
  inf_intro (Rx & HRx).
  rc_elim (inv) HRx. depsubst. clear_hyp. rename Hsub into HRx.
  rc_destruct H2. rename Hsub into HR1.
  rc_elim (inv) H13. depsubst. inv H2. rename Hsub into HR2.
  intm.
  inf_intro ?. inf_intro [? ? [? ? m' [[s1 s2]]] [s3]].
  inf_intro (Ry & HRy).
  rc_elim (inv) HRy. depsubst. clear_hyp. rename Hsub into HRy.
  intm.
  inf_intro ?. inf_intro [? ? [? ? m' [t1]] [t2]].
  inf_intro (Rz & HRz).
  rc_elim (inv) HRz. depsubst. clear_hyp. rename Hsub into HRz.
  intm. sup_intro [[[[n x1] x2] x3]|].
  - fcd_simpl. apply join_lub.
    + apply (sup_at None). fcd_simpl. reflexivity.
    + apply (sup_at (Some (n, x1, x2, x3))). fcd_simpl.
      apply join_r. rstep.
      apply sup_iff. intros (p & Hp). cbn. inv Hp.
      sup_mor. eapply fsup_at.
      { apply HRz. constructor. }
      fcd_simpl.
      sup_mor. eapply fsup_at.
      { apply HRy. constructor. }
      fcd_simpl.
      sup_mor. eapply (fsup_at (_, (_, (_, _)))).
      { apply HRx. split; cbn.
        apply HR1. reflexivity.
        apply HR2. constructor. }
      fcd_simpl.
      inf_intro (p & Hp). inv Hp. fcd_simpl. reflexivity.
  - apply (sup_at None). fcd_simpl. reflexivity.
Qed.

Lemma assoc_property' {E S1 S2 S}:
  left_arrow sig_assoc @ left_arrow st_assoc @ right_arrow sig_assoc @ right_arrow sig_assoc [=
  slift (S:=S) (right_arrow (sig_assoc (E:=E) (S1:=S1) (S2:=S2))).
Proof.
  rewrite assoc_property.
  rewrite <- (compose_assoc _ (left_arrow sig_assoc)). rewrite assoc_inverse'.
  rewrite compose_unit_l.
  rewrite <- (compose_assoc _ (right_arrow st_assoc)). rewrite epsilon.
  rewrite compose_unit_l.
  rewrite <- compose_assoc. rewrite epsilon.
  rewrite compose_unit_l. reflexivity.
Qed.

Lemma stateful_compose_ref {E F G U1 U2 S} (f: F ~> G#U1) (g: E ~> F # U2):
  h @@ h @ slift f @@ slift g [= slift (S:=S) (stateful_compose f g).
Proof.
  unfold stateful_compose.
  unfold h, sig_assoc_left, sig_assoc_right, st_assoc_left.
  rewrite !slift_compose. rewrite <- !compose_assoc.
  apply compose_proper_ref. 2: reflexivity.
  rewrite !compose_assoc.
  rewrite assoc_lift. rewrite <- !compose_assoc.
  apply compose_proper_ref. 2: reflexivity.
  rewrite !compose_assoc.
  apply assoc_property'.
Qed.

Section COMP.

  Context {E1 E2 E3} {S1 S2 S3 U1 U2}
          (L1: 0 ~> E1 # S1) (L2: 0 ~> E2 # S2) (L3: 0 ~> E3 # S3)
          (C1: strategy_layer U1 L1 L2)
          (C2: strategy_layer U2 L2 L3).

  Local Obligation Tactic := idtac.

  Program Definition strategy_layer_compose: strategy_layer (U2*U1) L1 L3 :=
    {|
      strategy_impl := stateful_compose (strategy_impl C2) (strategy_impl C1);
      strategy_rel := rel_compose (strategy_rel C2) (rel_compose (eq * strategy_rel C1) assoc);
    |}.
  Next Obligation.
    destruct C1 as [impl1 rel1 ref1].
    destruct C2 as [impl2 rel2 ref2].
    cbn - [LatticeProduct.cdlat_prod right_arrow left_arrow].
    rewrite ref2. clear ref2.
    rewrite ref1. clear ref1.
    rewrite <- !compose_assoc.
    apply compose_proper_ref. 2: reflexivity.
    rewrite !compose_assoc.

    rewrite <- rel_compose_ref. rewrite <- stateful_compose_ref.
    unfold stateful_compose, h,
      sig_assoc_right, sig_assoc_left, st_assoc_right, st_assoc_left.
    rewrite <- (compose_assoc _ _ (slift impl2)).
    rewrite state_commute. rewrite !compose_assoc.
    apply compose_proper_ref. reflexivity.
    apply compose_proper_ref. reflexivity.
    apply compose_proper_ref. reflexivity.
    setoid_rewrite <- (compose_assoc _ (left_arrow sig_assoc) (right_arrow sig_assoc)).
    rewrite <- eta. rewrite compose_unit_l.
    setoid_rewrite <- (compose_assoc _ (left_arrow st_assoc) (right_arrow st_assoc)).
    rewrite <- eta. rewrite compose_unit_l.
    setoid_rewrite <- (compose_assoc _ (right_arrow sig_assoc) (left_arrow sig_assoc)).
    rewrite assoc_inverse. rewrite compose_unit_l.
    reflexivity.
Qed.

End COMP.
