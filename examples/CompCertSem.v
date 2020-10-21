Require Import Relations RelationClasses.
Require Import List.
Require Import compcert.common.LanguageInterface.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import models.Coherence.

Unset Program Cases.
Local Obligation Tactic := cbn.


(** * Coherence spaces for CompCertO semantics *)

(** ** Language interfaces *)

Coercion li_space (li : language_interface) : space :=
  input (query li) ;; output (reply li).

(** ** CompCert events *)

(*
Inductive ev_coh : relation event :=
  | Event_syscall_coh s1 s2 args1 args2 res1 res2 :
      (s1 = s2 -> args1 = args2 -> res1 = res2) ->
      ev_coh (Event_syscall s1 args1 res1) (Event_syscall s2 args2 res2)
  | Event_vload_coh ...

Program Definition Ev :=
  {|
    token := event;
    coh e1 e2 := 
*)


(** * CompCert semantics *)

(** Note that Reddy's object semantics have a rather coarse-grained
  handling of undefined behaviors, which is inherited by our CompCert
  semantics. Silent divergence and undefined behaviors are also
  conflated.

  The preliminary definition below loses information about the domains
  of component, which would make it impossible to define mutually
  recursive horizontal composition in a satisfactory way. However for
  now we don't need it so we don't care. Ultimately we could
  incoroporate it in the type of the semantics by using
  [input (query li) ;; (1 + output (reply li)] instead of [li_space]
  for the codomain.

  Finally, everything in CompCertO happens in the context of a global
  symbol table, so we need to specify one to get the component's
  semantics. Again this could be an [input Genv.symtbl ;; ...] component
  in the interaction but for now this is the simpler approach. *)

(** ** Semantics of transition systems *)

Section LTS.
  Context {liA liB S} (L : lts liA liB S).

  (** [lts_trace s t r] asserts that the transition system [L] reaches
    a final state with reply [r] from the state [s], with the sequence
    of external calls encoded by the trace [t]. *)

  Inductive lts_trace : S -> token !liA -> reply liB -> Prop :=
    | lts_trace_final (s : S) (r : reply liB) :
        final_state L s r ->
        lts_trace s nil r
    | lts_trace_step (s s' : S) (t : token !liA) (r : reply liB) :
        Step L s E0 s' ->
        lts_trace s' t r ->
        lts_trace s t r
    | lts_trace_external s qx rx s' t r :
        at_external L s qx ->
        after_external L s rx s' ->
        lts_trace s' t r ->
        lts_trace s ((qx, rx) :: t) r.

  Inductive lts_lmaps : token !liA -> token liB -> Prop :=
    | lts_lmaps_intro q s t r :
        valid_query L q = true ->
        initial_state L q s ->
        lts_trace s t r ->
        lts_lmaps t (q, r).

End LTS.

Section SEMANTICS.
  Context {liA liB} (L : semantics liA liB) (HL : determinate L).

  Program Definition compcerto_lmap se : !liA --o liB :=
    {|
      lmaps := lts_lmaps (L se);
    |}.
  Next Obligation.
    (* ... *)
  Admitted.
  Next Obligation.
    (* ... *)
  Admitted.

  (** XXX ^ this is probably a situation where grouping the two
    properties of linear maps would be useful so that we only have to
    do the funky induction once, event though it would make it a hint
    more complicated. *)

End SEMANTICS.

(** ** Clight semantics *)

(** As an example, here is the semantics of Clight programs in terms
  of linear maps. *)

Require Clight.

(** We will need to prove this or the result may not be a linear map. *)

Lemma clight_determinate p :
  determinate (Clight.semantics1 p).
Proof.
Admitted.

Definition clight (p : Clight.program) se : !li_c --o li_c :=
  compcerto_lmap (Clight.semantics1 p) (clight_determinate p) se.

(** ** Soundness of forward simulations *)

(** Since for now, our model doesn't support abstraction, we can only
  consider simulations which use the [cc_id] simulation convention. *)

Section FSIM.
  Context {liA liB} (L1 L2 : semantics liA liB).
  Context (H1 : determinate L1).
  Context (H2 : determinate L2).
  Context (FSIM : forward_simulation 1 1 L1 L2).
  Context (se : Genv.symtbl) (Hse : Genv.valid_for (skel L1) se).

  (** XXX: we need a notion of refinement on linear maps themselves,
    or perhaps just define linear maps as cliques in the function
    space. *)

  Lemma fsim_sound :
    forall t u,
      compcerto_lmap L1 H1 se t u ->
      compcerto_lmap L2 H2 se t u.
  Proof.
    intros t u Ht.
    destruct FSIM as [[ind ord match_states _ H _]]. cbn in *.
    specialize (H se se tt eq_refl Hse).
    destruct Ht as [q s1 t1 r Hq1 Hs1 Ht1].
    edestruct @fsim_match_initial_states as (i & s2 & Hs2 & Hs);
      eauto; try reflexivity.
    econstructor.
    - erewrite fsim_match_valid_query; eauto. reflexivity.
    - eauto.
    - clear - H Hs Ht1. revert i s2 Hs.
      induction Ht1; cbn; intros.
      + (* final state *)
        edestruct @fsim_match_final_states as (xr & Hs2 & Hxr); eauto.
        destruct Hxr.
        constructor; auto.
      + (* step *)
        edestruct @simulation_star as (j & s2' & Hs2' & Hs'); eauto using star_one.
        revert Hs'. pattern s2, s2'.
        eapply star_E0_ind; eauto using lts_trace_step.
      + (* external interaction *)
        edestruct @fsim_match_external as (w & xq & Hq2 & Hxq & _ & Hrx); eauto.
        destruct Hxq.
        edestruct Hrx as (j & s2' & Hs2' & Hs'); cbn; eauto using lts_trace_external.
  Qed.
End FSIM.
