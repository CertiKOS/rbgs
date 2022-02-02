From Coq Require Import
     List Lia.
From models Require Import
     IntSpec.
From examples Require Import
     CAL CompCertIntSpec RefConv
     BoundedQueueCode.
From lattices Require Import
     Upset Downset FCD.
From structures Require Import
     Effects Lattice.
From compcert Require Import
     AST Values Memory
     Globalenvs
     LanguageInterface
     Smallstep.
From compcertox Require Import
     Lifting CModule.
Import ListNotations ISpec.

Unset Asymmetric Patterns.

Ltac clear_hyp :=
  repeat match goal with
         | [ H : (?t = ?t)%type |- _ ] => clear H
         end.

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

  Local Opaque normalize_rc.

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

(** The language interface "C simple" which does not include the memory *)
Inductive c_esig : esig :=
| c_event : val -> signature -> list val -> c_esig val.

Inductive c_rc: rc_rel (c_esig # mem) li_c :=
| c_rc_intro vf sg args e_c e_s m:
  let R := (fun '(r, m) c_r => c_r = cr r m) in
  e_c = c_event vf sg args -> e_s = state_event m ->
  c_rc _ (esig_tens_intro e_c e_s) _ (li_sig (cq vf sg args m)) R.

(** Some auxiliary definitions *)
Notation "m # s" := (esig_tens_intro m (state_event s)) (at level 40, left associativity).

Inductive assoc {A B C: Type}: A * (B * C) -> A * B * C -> Prop :=
| assoc_intro a b c: assoc (a, (b, c)) ((a, b), c).
Inductive sig_assoc {E: esig} {S1 S2: Type}: rc_rel (E#(S1*S2)) (E#S1#S2) :=
| sig_assoc_intro ar (m: E ar) s1 s2 :
  sig_assoc _ (m # (s1, s2)) _ ((m # s1) # s2) assoc.

Inductive comm {A B: Type}: A * B -> B * A -> Prop :=
| comm_intro a b: comm (a, b) (b, a).
Definition st_comm {E: esig} {S1 S2: Type}: rc_rel (E#(S1*S2)) (E#(S2*S1)) :=
  (rc_id * rel_rc comm)%rc.
Definition st_assoc {E: esig} {S1 S2 S3: Type}: rc_rel (E#(S1*(S2*S3))) (E#(S1*S2*S3)) :=
  (rc_id * rel_rc assoc)%rc.

Inductive eq_comm {A B C: Type}: A * B * C -> A * C * B -> Prop :=
| eq_comm_intro a b c: eq_comm ((a, b), c) ((a, c), b).
Inductive sig_comm {E: esig} {S1 S2: Type}: rc_rel (E#S1#S2) (E#S2#S1) :=
| sig_comm_intro ar (m: E ar) s1 s2:
  sig_comm _ (m # s1 # s2) _ (m # s2 # s1) eq_comm.
Inductive empty_rc {A: Type}: rc_rel 0 (0#A) := .

Open Scope rc_scope.

Definition slift' {E F: esig} {U S: Type} (f: E#U ~> F#U) : E#(U*S) ~> F#(U*S) :=
  right_arrow sig_assoc @ slift f @ left_arrow sig_assoc.
Definition slift_layer {E: esig} {S U: Type} (f: 0 ~> E#S) : 0 ~> E#(U*S) :=
  right_arrow st_comm @ right_arrow sig_assoc @ slift f @ left_arrow empty_rc.

Record strategy_layer {E1 E2} {S1 S2} (U: Type) (L1: 0 ~> E1 # S1) (L2: 0 ~> E2 # S2) :=
  {
    M: E1 # U ~> E2 # U;
    R: S2 -> U * S1 -> Prop;

    simulation:
    L2 [= right_arrow (rc_id * rel_rc R)
       @ right_arrow sig_assoc
       @ slift M
       @ right_arrow sig_comm
       @ slift L1
       @ left_arrow empty_rc;

  }.
Arguments M {_ _ _ _ _ _ _}.
Arguments R {_ _ _ _ _ _ _}.
Arguments simulation {_ _ _ _ _ _ _}.

(*
Lemma lift_strategy_simulation {E1 E2} {S1 S2 U} {L1: 0 ~> E1 # S1} {L2: 0 ~> E2 # S2}
      (C: strategy_layer U L1 L2) (K: Type):
  slift_layer (U:=K) L2 [=
    right_arrow (rc_id * rel_rc (rel_compose (eq * (R C)) assoc))
                @ slift' (right_arrow st_comm @ slift' (M C) @ left_arrow st_comm)
                @ slift_layer L1.
Proof.
  intros ar m. unfold slift_layer. cbn.
  destruct m as [ ? ? m2 [ [ k s2 ] ] ].
  unfold compose at 1. unfold rc_adj_right at 2.
  inf_mor. eapply inf_at.
  inf_mor. eapply (inf_at (m2 # (s2, k))).
  inf_mor. eapply finf_at.
  { rc_econstructor; rc_econstructor. constructor. }
  intm.
  unfold compose at 3. unfold rc_adj_right at 2.
  inf_mor. eapply inf_at.
  inf_mor. eapply (inf_at (m2 # s2 # k)).
  inf_mor. eapply finf_at.
  { rc_econstructor. }
  intm.
  unfold compose at 4.
  pose proof (simulation C) as HC.
  eapply slift_proper_ref in HC.
  specialize (HC _ (m2 # s2 # k)). rewrite HC. clear HC.
Admitted.
*)

Require Import compcert.lib.Coqlib.

Instance apply_mor {E S A} (s: S) :
  CDL.Morphism (@srun E S A s).
Proof.
  unfold srun. split.
  - intros x y. rewrite Sup.mor. reflexivity.
  - intros x y. rewrite Inf.mor. reflexivity.
Qed.

Instance map_mor {A B: poset} (f: A -> B) :
  CDL.Morphism (@FCD.map A B f).
Proof. unfold FCD.map. typeclasses eauto. Qed.

Local Opaque normalize_rc.
Close Scope Z_scope.

Lemma foo {E: esig} {S1 S2 S3 U: Type} (R: S1 -> S2 * S3 -> Prop):
  right_arrow sig_comm @ slift (right_arrow (rc_id * rel_rc R)) [=
    right_arrow (rc_id(E:=E#U) * rel_rc R) @ right_arrow sig_comm.
Proof.
  intros ? [ ? ? [ ? ? m [ u ] ] [ s1 ] ]. cbn.
  unfold compose, rc_adj_right.
  inf_intro ?. inf_intro m'. inf_intro [ Rx HRx ].
  rc_destruct HRx. rc_destruct H. rc_destruct H0.
  destruct m0 as [ ? ? e [ s ]].
  eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
  { rc_econstructor. }
  intm.
  inf_intro ?. inf_intro m'. inf_intro [ Ry HRy ].
  rc_inversion HRy. depsubst. clear_hyp. clear Hrel.
  eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
  { rc_econstructor; rc_econstructor; eauto. }
  intm. apply bind_proper_ref. 2: reflexivity.
  intros [ ? ? ].
  sup_intro [ n Hn ]. inv Hn. destruct n. destruct p.
  cbn [fst snd] in *. subst. eapply fsup_at.
  { apply Hsub2. constructor. }
  fcd_simpl.
  sup_intro [ n Hn ]. inv Hn.
  eapply fsup_at.
  { apply Hsub. instantiate (1 := (_, _)). split; eauto.
    apply Hsub0. reflexivity. }
  fcd_simpl. reflexivity.
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

Lemma baz {E F: esig} {S1 S2} (f: E ~> F):
  slift(S:=S1) (slift(S:=S2) f) [= right_arrow sig_comm @ slift(S:=S2) (slift(S:=S1) f) @ right_arrow sig_comm.
Proof.
Admitted.

Lemma xxx {E F: esig} {S1 S2} (f: E ~> F):
  slift(S:=S1) (slift(S:=S2) f) [=
    left_arrow sig_comm @ left_arrow sig_assoc @ (slift f) @ right_arrow sig_assoc @ right_arrow sig_comm.
Proof.
Admitted.

(** Stateful sequential composition of strategies *)
Definition st_compose {E F G} {U1 U2} (f: F#U1 ~> G#U1) (g: E#U2 ~> F#U2) : E#(U1*U2) ~> G#(U1*U2) :=
  right_arrow sig_assoc @ slift f @ right_arrow sig_comm @ slift g @ right_arrow sig_comm @ left_arrow sig_assoc.

Lemma slift_compose {E F G S} (f: F ~> G) (g: E ~> F):
  slift (S:=S) (f @ g) = slift f @ slift g.
Proof.
  apply antisymmetry.
  - intros ? [ ? ? m [ s ] ]. cbn.
    unfold compose. cbn. rewrite srun_slift. reflexivity.
  - intros ? [ ? ? m [ s ] ]. cbn.
    unfold compose. cbn. rewrite srun_slift. reflexivity.
Qed.

Section COMP.

  Context {E1 E2 E3} {S1 S2 S3 U1 U2}
          (L1: 0 ~> E1 # S1) (L2: 0 ~> E2 # S2) (L3: 0 ~> E3 # S3)
          (C1: strategy_layer U1 L1 L2)
          (C2: strategy_layer U2 L2 L3).

  Local Obligation Tactic := idtac.

  Program Definition strategy_layer_compose: strategy_layer (U2*U1) L1 L3 :=
    {|
      M := st_compose (M C2) (M C1);
      R := rel_compose (R C2) (rel_compose (eq * R C1) assoc);
    |}.
  Next Obligation.
    pose proof (simulation C1) as CS1.
    pose proof (simulation C2) as CS2.
    eapply slift_proper_ref in CS1.
    rewrite CS1 in CS2. clear CS1.
    etransitivity; eauto. clear CS2.
    rewrite !slift_compose. rewrite !compose_assoc.

    setoid_rewrite <- (compose_assoc _ _ (right_arrow sig_comm)).
    setoid_rewrite foo. rewrite !compose_assoc.
    setoid_rewrite <- (compose_assoc _ _ (slift (M C2))).
    setoid_rewrite state_commute. rewrite !compose_assoc.
    unfold st_compose. rewrite !slift_compose. rewrite !compose_assoc.


    rewrite <- (compose_unit_l (slift (slift (M C2)))).
    rewrite <- (epsilon sig_assoc). rewrite !compose_assoc.

    setoid_rewrite <- (compose_assoc _ (right_arrow (rc_id * rel_rc (R C1))) _).
    setoid_rewrite <- (compose_assoc _ (left_arrow sig_assoc) _).
    setoid_rewrite <- (compose_assoc _ (_ @ _) _).
    setoid_rewrite <- (compose_assoc _ (_ @ _) _).
    apply compose_proper_ref.
    {
      intros ?  [ ? ? m3 [ s3 ] ]. cbn.
      unfold compose at 1 3. unfold rc_adj_right at 3 6.
      inf_intro ?. inf_intro [ ? ? m3' [ [ [ u2 u1 ] s1 ] ] ].
      inf_intro [ Rx HR ]. rc_destruct HR. rc_destruct H.
      rc_destruct H0. inv H. destruct H0 as [ HR HRc ].
      inv HRc. destruct H as [ HRx HRc ]. inv HRx. inv HRc.
      destruct x. cbn [fst snd] in *. subst. intm.

      eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
      { rc_econstructor; rc_econstructor; eauto. }
      intm. unfold compose at 2. unfold rc_adj_right at 4.
      inf_mor. eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
      { rc_econstructor. }
      intm. unfold rc_adj_right at 4.
      inf_mor. eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
      { rc_econstructor; rc_econstructor; eauto. }
      intm. unfold compose at 4. unfold rc_adj_right at 7.
      inf_intro ?. inf_intro m'. inf_intro [ Ra HRa ].
      rc_inversion HRa. depsubst. clear_hyp. clear Hrel.
      intm. unfold compose at 5. cbn. unfold rc_adj_right at 7.
      inf_intro ?. inf_intro m'. inf_intro [ Rb HRb ].
      rc_inversion HRb. depsubst. clear_hyp. clear Hrel.
      intm. unfold rc_adj_left at 4.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { rc_econstructor. }
      intm. apply bind_proper_ref. 2: reflexivity.
      intros x.
      sup_intro [ n Hn ]. inv Hn. destruct x. destruct n. cbn [fst snd] in *. subst.
      inf_intro [ n Hn ]. inv Hn.
      fcd_simpl.
      sup_intro [ n Hn ]. inv Hn.
      eapply fsup_at.
      { apply Hsub3. constructor. }
      fcd_simpl. sup_intro [ n Hn ].
      inv Hn. destruct n. cbn [fst snd] in *. subst.
      eapply fsup_at.
      { apply Hsub2. constructor. }
      fcd_simpl.
      sup_mor. eapply fsup_at.
      { apply Hsub. instantiate (1 := (_, _)). split.
        - apply Hsub0. reflexivity.
        - apply Hsub1. cbn.
          eexists; split; eauto.
          eexists; split; eauto.
          split; eauto. instantiate (1 := (_, _)). reflexivity.
          cbn. eauto. constructor. }
      fcd_simpl. reflexivity.
    }

    rewrite bar. rewrite !compose_assoc.
    apply compose_proper_ref. reflexivity.
    apply compose_proper_ref. reflexivity.
    rewrite baz. rewrite !compose_assoc.
    setoid_rewrite <- (compose_assoc _ (right_arrow sig_comm) (slift (right_arrow sig_assoc))).
    setoid_rewrite <- (compose_assoc _ (_ @ _) _).
    setoid_rewrite <- (compose_assoc _ (_ @ _) _).
    apply compose_proper_ref.
    {
      intros ? [ ? ? [ ? ? [ ? ? m [ u2 ] ] [ u1 ] ] [ s1 ] ]. cbn.
      unfold rc_adj_right.
      inf_intro ?. inf_intro m'. inf_intro [ R HR ].
      rc_destruct HR. intm.
      unfold compose. unfold rc_adj_left.
      sup_intro ?. sup_intro m'. sup_intro [ Ra HR ].
      rc_inversion HR. depsubst. clear_hyp.
      inv Hrel. depsubst. intm.
      inf_mor. eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
      { rc_econstructor. }
      intm. inf_mor. eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
      { rc_econstructor. }
      intm. inf_mor. eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
      { rc_econstructor. }
      intm. apply bind_proper_ref. 2: reflexivity.
      intros x. destruct x.
      sup_intro [ n Hn ]. inv Hn. fcd_simpl.
      sup_intro [ n Hn ]. inv Hn. fcd_simpl.
      sup_intro [ n Hn ]. inv Hn. fcd_simpl.
      eapply fsup_at.
      { apply Hsub. constructor. }
      inf_mor. eapply finf_at.
      { apply Hsub0. constructor. }
      fcd_simpl. reflexivity.
    }
    apply compose_proper_ref. reflexivity.
    rewrite xxx. rewrite !compose_assoc.
    setoid_rewrite <- (compose_assoc _ (left_arrow sig_assoc) _).
    setoid_rewrite <- (compose_assoc _ (right_arrow sig_comm) _).
    setoid_rewrite <- (compose_assoc _ (_ @ _) _).
    setoid_rewrite <- (compose_assoc _ (_ @ _) _).
    apply compose_proper_ref.
    {
      intros ? [ ? ? [ ? ? [ ? ? m [ u1 ] ] [ u2 ] ] [ s1 ] ]. cbn.
      unfold compose, rc_adj_right. cbn.
      inf_intro ?. inf_intro m'. inf_intro [ R HR ].
      rc_destruct HR.
      eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
      { rc_econstructor. }
      intm. inf_mor. eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
      { rc_econstructor. }
      intm. unfold rc_adj_left.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { rc_econstructor. }
      apply sup_iff. intros ?. sup_intro m'. sup_intro [ Ra HRa ].
      rc_inversion HRa. depsubst. clear_hyp.
      inv Hrel. depsubst. clear_hyp. intm.
      sup_intro ?. sup_intro m'. sup_intro [ Rb HRb ].
      rc_inversion HRb. depsubst. clear_hyp.
      inv Hrel. depsubst. clear_hyp. intm.
      inf_intro ?. inf_intro m'. inf_intro [ Rc HRc ].
      rc_inversion HRc. depsubst. clear_hyp. clear Hrel. intm.
      apply bind_proper_ref. 2: reflexivity.
      intros [ [? ?] [? ?] ]. inf_mor. eapply finf_at.
      { apply Hsub1. constructor. }
      sup_mor. eapply fsup_at.
      { apply Hsub2. constructor. }
      fcd_simpl.
      inf_mor. eapply finf_at.
      { apply Hsub0. constructor. }
      eapply inf_iff. intros [ n Hn ]. cbn. inv Hn.
      fcd_simpl.
      sup_intro [ n Hn ]. inv Hn.
      eapply fsup_at.
      { apply Hsub. constructor. }
      fcd_simpl.
      sup_intro [ n Hn ]. inv Hn. fcd_simpl. reflexivity.
    }
    apply compose_proper_ref. reflexivity.
    rewrite !compose_assoc.
    intros ? [ ? ? [ ] ].
  Qed.

End COMP.



Inductive lts_state_rc {S: Type}: rc_rel (c_esig # (mem * S)) (li_c @ S)%li :=
| lts_state_rc_intro vf sg args m s (qs: query (li_c @ S)) qe:
  let R := (fun '(r, (m, s)) '(r', s') => r' = cr r m /\ s = s') in
  qs = (cq vf sg args m, s) ->
  qe = st (c_event vf sg args) (m, s) ->
  lts_state_rc _ qe _ (li_sig qs) R.

Definition overlay_rc {E: esig} {S1 S2: Type} (rc: E <=> c_esig) (rel: S2 -> mem * S1 -> Prop):
  E # S2 <=> c_esig # (mem * S1)%type := rc * rel_rc rel.

Inductive st_mem_rc {S: Type}: rc_rel (s_esig S) (s_esig (mem * S)) :=
| st_mem_rc_intro s m:
  let R := (fun s' '(m', t') => s' = t' /\ m = m') in
  st_mem_rc _ (state_event s) _ (state_event (m, s)) R.

Definition underlay_rc {E: esig} {S: Type} (rc: E <=> c_esig):
  E # S <=> c_esig # (mem * S) := rc * st_mem_rc.

Close Scope Z_scope.
(** ** Construction of a certified abstraction layer *)
Record certi_layer {E1 E2: esig} {S1 S2: Type} {se: Genv.symtbl} :=
  {
    L1: 0 ~> E1 * s_esig S1;    (** underlay *)
    L1_rc: E1 <=> c_esig;
    L2: 0 ~> E2 * s_esig S2;    (** overlay *)
    L2_rc: E2 <=> c_esig;
    module: list Clight.program;
    sk: AST.program unit unit;
    abs_rel: S2 -> mem * S1 -> Prop;

    layer_rel:
    L2 [= right_arrow (overlay_rc L2_rc abs_rel)
       @ right_arrow lts_state_rc
       @ ang_lts_spec (((semantics module sk) @ S1)%lts se)
       @ left_arrow lts_state_rc
       @ left_arrow (underlay_rc L1_rc)
       @ L1;
  }.

(** ** Layer Composition *)
Section COMP.

  Context {E1 E2 E3: esig} {S1 S2 S3: Type} (se: Genv.symtbl).
  Context (C1: @certi_layer E1 E2 S1 S2 se)
          (C2: @certi_layer E2 E3 S2 S3 se).
  Context (sk_comp: AST.program unit unit)
          (Hsk: Linking.link (sk C1) (sk C2) = Some sk_comp).
  Program Definition comp_certi_layer: @certi_layer E1 E3 S1 S3 se :=
    {|
      L1 := L1 C1;
      L1_rc := L1_rc C1;
      L2 := L2 C2;
      L2_rc := L2_rc C2;
      module := module C1 ++ module C2;
      sk := sk_comp;
      (* This is probably wrong *)
      abs_rel :=
      fun s3 '(m, s1) =>
        exists s2, (abs_rel C1) s2 (m, s1)
              /\ (abs_rel C2) s3 (m, s2);
    |}.
  Next Obligation.
  Admitted.

End COMP.
