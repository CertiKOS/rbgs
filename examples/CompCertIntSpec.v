From Coq Require Import
     Relations
     RelationClasses
     List.
From models Require Import
     IntSpec.
From compcert Require Import
     Coqlib
     LanguageInterface
     Events
     Globalenvs
     Smallstep.
From lattices Require Import
     FCD.
From structures Require Import
     Effects
     Lattice.

(** * Embed CompCert Semantics into Game Semantics *)

(** ** Embed Language Interfaces *)
Section SIG.

  Variable li: language_interface.
  (* May need to consider the symbol table in the future *)
  Inductive sig: esig :=
  | li_sig: query li -> sig (reply li).

End SIG.

Arguments li_sig {_} _.
Coercion sig: language_interface >-> esig.
Coercion li_sig: query >-> sig.

Import ISpec.

(** The primitive operator that triggers a query *)
Definition query_int {li} (q: query li): ispec li _ := @int (sig li) _ q.
(* The expected type of the first argument of @int is a general type constructor
   E: Type -> Type instead of [esig], so the coercion does not work *)

(** ** Embed Labelled Tranition Systems *)
Section LTS.

  Context {liA liB state} (L: lts liA liB state).

  (** *** Demonic Interpretation *)
  Section DEM.

    (** One way to think about demonic and angelic interpretation is via the
      refinement relation: the computation is more refined if it is more
      angelically non-deterministic or less demonically non-deterministic. We
      will consider a refinement of the computation to be an implementation with
      less non-deterministic choices, thus the demonic interpretation is
      used. The demonic view corresponds to the backward simulation.

      However, the problem with the compcert semantics is that when there are no
      possible transitions, the choice should be interpreted angelically as ⊥,
      rather than demonically as ⊤. Therefore, we rely on assertions.

      Since recursive definition in Coq is required to be terminating, we use
      the number of execution steps as the decreasing argument. If the
      transition does not finish within the number of steps, it
      crashes. Eventually, we use an angelic choice over the number of steps. *)

    Fixpoint dem_lts_spec' (n: nat) (s: state): ispec liA (reply liB) :=
      match n with
      | O => bot
      | S n =>
          _ <- assert (safe L s);
          (* internal step *)
          (inf { s' | Step L s E0 s' }, dem_lts_spec' n s') &&
          (* external call *)
          (inf { q | at_external L s q },
           r <- query_int q;
           _ <- assert (exists s', after_external L s r s');
           inf { s' | after_external L s r s' }, dem_lts_spec' n s') &&
          (* final state *)
          (inf { r | final_state L s r }, ret r)
      end.

    Definition dem_lts_spec: subst liA liB :=
      fun _ '(li_sig q) => sup n,
        _ <- assert (exists s, initial_state L q s);
        inf { s | initial_state L q s }, dem_lts_spec' n s.

  End DEM.

  (** *** Angelic Semantics *)
  Section ANG.

    Fixpoint ang_lts_spec' (n: nat) (s: state): ispec liA (reply liB) :=
      match n with
      | O => bot
      | S n =>
          (* internal step *)
          (sup { s' | Star L s E0 s' }, ang_lts_spec' n s') ||
          (* external call *)
          (sup { q | at_external L s q },
           r <- query_int q;
           sup { s' | after_external L s r s' }, ang_lts_spec' n s') ||
          (* final step *)
          (sup { r | final_state L s r }, ret r)
      end.

    Definition ang_lts_spec: subst liA liB :=
      fun _ '(li_sig q) => sup n,
        sup { s | initial_state L q s }, ang_lts_spec' n s.

  End ANG.

  (** The two interpretations coincide when the computation has at most one
    behavior, i.e. when the LTS is deterministic *)
  Section DET.
    Context (se: Genv.symtbl).
    Hypothesis DET: lts_determinate L se.

    Lemma det_lts_spec_equiv:
      ang_lts_spec = dem_lts_spec.
    Proof.
      apply antisymmetry.
      - intros ? [q]. cbn. apply sup_lub. intros i.
        unfold assert.
    Abort.

  End DET.

  (* Definitions for defining the embedding through the play instead of
     interaction primitives. Not used for now *)
  (* Inductive state_exec: state -> query liA + reply liB -> Prop :=
  | state_exec_step s s' e:
      Step L s E0 s' ->
      state_exec s' e ->
      state_exec s e
  | state_exec_final s r:
      final_state L s r ->
      state_exec s (inr r)
  | state_exec_external s q:
      at_external L s q ->
      state_exec s (inl q).

  Inductive lts_play: state -> play liA (reply liB) -> Prop :=
  | lts_play_step s s' p:
    Step L s E0 s' ->
    lts_play s' p ->
    lts_play s p
  | lts_play_ret s r:
    final_state L s r ->
    lts_play s (pret r)
  | lts_play_query s q r (p: play liA (reply liB)) s':
    lts_play s' p ->
    at_external L s q ->
    after_external L s r s' ->
    lts_play s (pcons (li_sig q) r p). *)

End LTS.

(** ** Embed Calling Conventions *)
Section CC.

  (** We treat liB as the implementation. *)
  Context {liA liB} (cc: callconv liA liB).

  (** Translate a low level liB to high level liA. The first choice is made
    angelically because 1) there is usually at most one abstract representation;
    2) a more refined computation includes behaviors on more abstract
    representations, which means the computation is described from more angles.

    The second choice is made demonically because for an abstract state, its
    refinement implements one of the concrete representations.

    As for the choice of worlds, ... *)
  Definition cc_up: subst liA liB :=
    fun _ '(li_sig qb) =>
      sup w, sup { qa | match_query cc w qa qb },
      query_int qa >>= (fun ra => inf { rb | match_reply cc w ra rb }, ret rb).

  (** Translate high level liA into low level liB *)
  Definition cc_down: subst liB liA :=
    fun _ '(li_sig qa) =>
      inf w, inf { qb | match_query cc w qa qb },
      query_int qb >>= (fun rb => sup { ra | match_reply cc w ra rb }, ret ra).

End CC.

Instance bind_proper {E:esig} {A B}:
  Proper (pointwise_relation A eq ==> eq ==> eq) (@bind E A B).
Proof.
  intros f1 f2 Hf a1 a2 Ha. unfold bind.
  rewrite Hf. rewrite Ha. reflexivity.
Qed.

(* Note: it's hard to imply the [esig] from the context, since
   higher-order unification is generally difficult, i.e. to imply [E] from [E X] *)
Global Instance emb_pcons_monotonic {li: language_interface} {V: Type} (m: query li) (n: reply li):
  PosetMorphism (fun s: play li V => FCD.emb (@pcons (sig li) _ _ m n s)).
Proof.
  split. intros x y Hxy.
  rstep. now constructor.
Qed.

Global Instance ext_monotonic {C: poset} {L: cdlattice} (f: C -> L):
  PosetMorphism (FCD.ext f).
Proof.
  apply CDL.mor_ref. typeclasses eauto.
Qed.

(* TODO: *)
Global Instance ext_proper {C: poset} {L: cdlattice}:
  Proper ((pointwise_relation _ ref) ++> ref ++> ref) (@FCD.ext C L).
Proof.
  intros f1 f2 Hf a1 a2 Ha.
Admitted.

Import Upset Downset.

(** ** Monotonicity of Embedding *)
Section FSIM.

  Context {liA1 liA2} (ccA: callconv liA1 liA2).
  Context {liB1 liB2} (ccB: callconv liB1 liB2).
  Context (se1 se2: Genv.symtbl).
  Context {state1 state2: Type}.
  Context (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2).
  Context (index: Type) (order: index -> index -> Prop)
          (match_states: index -> state1 -> state2 -> Prop).
  Hypothesis FSIM: forall wB, fsim_properties ccA ccB se1 se2 wB L1 L2 index order match_states.

  Lemma ang_fsim_embed:
    ang_lts_spec L1 [= (cc_down ccB) @ ang_lts_spec L2 @ (cc_up ccA).
  Proof.
    intros k [qb1]. unfold ISpec.compose.
    unfold ang_lts_spec at 1.
    apply sup_iff. intros steps.
    apply sup_iff. intros [s H1]. cbn.
    unfold finf. rewrite (proj2 (apply_mor _)).
    apply inf_iff. intros wB. specialize (FSIM wB).
    rewrite (proj2 (apply_mor _)).
    apply inf_iff. intros [qb2 Hqb].
    unfold query_int. intm.
    setoid_rewrite (proj1 (apply_mor _)).
    setoid_rewrite apply_ret.
    setoid_rewrite (proj1 (apply_mor _)).
    unfold bind. rewrite (proj1 FCD.ext_mor).
    apply sup_at with (i := steps).
    setoid_rewrite (proj1 FCD.ext_mor).
    edestruct (fsim_match_initial_states FSIM) as (i & s2 & H2 & Hs); eauto.
    eapply (sup_at (exist _ s2 H2)). cbn.
    clear H1 H2 Hqb. revert i s s2 Hs.
    induction steps; eauto using bot_lb.
    intros i s1 s2 Hs. cbn.
    repeat apply join_lub.
    - apply sup_iff. intros [s1' Hstep]. cbn.
      rewrite !Sup.mor_join.
      apply join_l. apply join_l.
      assert (exists i s2', Star L2 s2 E0 s2' /\ match_states i s1' s2') as (i' & s2' & Hstep2 & Hs').
      {
        revert i s2 Hs. pattern s1, s1'. eapply star_E0_ind; eauto; clear s1 s1' Hstep.
        - intros s1 i s2 Hs. exists i, s2; split; eauto using star_refl.
        - intros s1 s1' s1'' Hstep1 IHstar i s2 Hs.
          edestruct (simulation_star FSIM) as (i' & s2' & Hstep2 & Hs'); eauto using star_one.
          specialize (IHstar _ _ Hs') as (i'' & s2'' & Hstep2' & Hs'').
          eexists i'', s2''. split; eauto.
          eapply star_trans; eauto.
      }
      setoid_rewrite (proj1 (apply_mor _)).
      setoid_rewrite (proj1 FCD.ext_mor).
      eapply (sup_at (exist _ s2' Hstep2)). cbn.
      specialize (IHsteps _ _ _ Hs'). apply IHsteps.
    - apply sup_iff. intros [qa1 H1]. cbn.
      rewrite !Sup.mor_join.
      apply join_l. apply join_r.
      edestruct @fsim_match_external as (w & qa2 & H2 & Hqa & _ & Hrx); eauto.
      setoid_rewrite (proj1 (apply_mor _)).
      setoid_rewrite (proj1 FCD.ext_mor) at 2.
      eapply (sup_at (exist _ qa2 H2)). cbn.
      rewrite apply_bind. unfold query_int.
      rewrite apply_int_r.
      unfold bind. unfold cc_up at 2.
      setoid_rewrite (proj1 FCD.ext_mor) at 2.
      setoid_rewrite (proj1 FCD.ext_mor) at 2.
      eapply (sup_at w).
      setoid_rewrite (proj1 FCD.ext_mor) at 2.
      setoid_rewrite (proj1 FCD.ext_mor) at 2.
      eapply (sup_at (exist _ qa1 Hqa)). cbn.
      unfold query_int. unfold bind.
      setoid_rewrite (proj1 FCD.ext_mor) at 1.
      apply sup_iff. intros [ra1|].
      + rewrite FCD.ext_ana. cbn.
        apply join_lub.
        * setoid_rewrite (proj1 FCD.ext_mor).
          setoid_rewrite (proj1 FCD.ext_mor).
          setoid_rewrite (proj1 FCD.ext_mor).
          apply (sup_at (Some ra1)).
          rewrite FCD.ext_ana. cbn.
          rewrite !Sup.mor_join.
          apply join_l.
          rewrite FCD.ext_ana. cbn.
          rewrite FCD.ext_ana. cbn. reflexivity.
        * setoid_rewrite (proj1 FCD.ext_mor) at 3.
          setoid_rewrite (proj1 FCD.ext_mor) at 2.
          setoid_rewrite (proj1 FCD.ext_mor) at 2.
          apply (sup_at (Some ra1)).
          rewrite FCD.ext_ana. cbn.
          rewrite !Sup.mor_join.
          apply join_r.
          setoid_rewrite (proj2 FCD.ext_mor).
          setoid_rewrite (proj2 FCD.ext_mor).
          setoid_rewrite (proj2 FCD.ext_mor).
          apply inf_iff. intros [ra2 Hr]. cbn.
          unfold ret at 2. cbn.
          setoid_rewrite FCD.ext_ana.
          setoid_rewrite FCD.ext_ana. cbn.
          rewrite !Sup.mor_join.
          apply join_r.
          setoid_rewrite (proj1 FCD.ext_mor).
          apply sup_iff. intros [s' H1'].
          specialize (Hrx _ _ _ Hr H1') as (i' & s2' & H2' & Hs'). cbn.
          setoid_rewrite (proj1 FCD.ext_mor).
          setoid_rewrite (proj1 FCD.ext_mor).
          apply (sup_at (exist _ s2' H2')). cbn.
          specialize (IHsteps _ _ _ Hs').
          etransitivity.
          pose proof (@ext_monotonic) as H.
          match goal with
          | |- context[FCD.ext ?f] =>
              set (h := f)
          end.
          specialize (H  _ _ h).
          destruct H as [H].
          cbn in *. eapply H. apply IHsteps.
          rewrite FCD.ext_ext.
          rewrite @FCD.ext_ext; try typeclasses eauto.
          match goal with
          | |- ref (FCD.ext ?f _) (FCD.ext ?g _) =>
              set (f1 := f); set (f2 := g);
              assert (pointwise_relation _ ref f1 f2)
          end.
          {
            intros p. subst f1. subst f2. cbn.
            rewrite FCD.ext_ana. cbn.
            apply join_r. reflexivity.
          }
          (* apply FunctionalExtensionality.functional_extensionality. *)
          eapply ext_proper. eauto. reflexivity.
      + rewrite FCD.ext_ana. cbn.
        setoid_rewrite (proj1 FCD.ext_mor).
        setoid_rewrite (proj1 FCD.ext_mor).
        setoid_rewrite (proj1 FCD.ext_mor).
        apply (sup_at None).
        setoid_rewrite FCD.ext_ana. cbn.
        setoid_rewrite FCD.ext_ana. cbn.
        setoid_rewrite FCD.ext_ana. cbn.
        reflexivity.
    - apply sup_iff. intros [rb1 H1]. cbn.
      rewrite !Sup.mor_join. apply join_r.
      edestruct @fsim_match_final_states as (rb2 & H2 & Hr); eauto.
      setoid_rewrite (proj1 (apply_mor _)).
      setoid_rewrite (proj1 FCD.ext_mor).
      apply (sup_at (exist _ rb2 H2)). cbn.
      rewrite apply_ret.
      unfold ret at 3. rewrite FCD.ext_ana. cbn.
      apply (sup_at (exist _ rb1 Hr)). cbn.
      reflexivity.
  Qed.

End FSIM.
(* We may not be able to prove the order-embedding *)
