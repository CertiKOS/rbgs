(** Preliminary experiments about incorporating state encapsulation into
  CompCert languages *)

From compcert Require Import
     AST Coqlib Maps Values Integers Errors Events
     LanguageInterface Smallstep Globalenvs Memory Floats.
From compcert Require Import
     CategoricalComp.
From compcertox Require Import
     TensorComp Lifting.
From coqrel Require Import RelClasses.

Set Asymmetric Patterns.
Set Implicit Arguments.
Generalizable All Variables.

Typeclasses eauto := 20.

(** * State Encapsulation of CompCert LTS *)

(** ------------------------------------------------------------------------- *)
(** ** Preliminaries *)
Class PSet (T: Type) : Type :=
  pset_init : Genv.symtbl -> T.

Arguments pset_init _ {_}.

Instance pset_unit: PSet unit :=
  { pset_init _ := tt }.

Instance pset_prod `{PSet A} `{PSet B} : PSet (A * B) | 8 :=
  { pset_init se := (pset_init A se, pset_init B se) }.

Record ReflTranRel (X: Type) :=
  {
    rel :> X -> X -> Prop;
    rel_refl : Reflexive rel;
    rel_tran : Transitive rel;
  }.
Existing Instance rel_refl.
Existing Instance rel_tran.

Class Lens (T A: Type) :=
  {
    get : T -> A;
    set : T -> A -> T;
    get_set : forall t a, get (set t a) = a;
    set_get : forall t, set t (get t) = t;
    set_set : forall t a1 a2, set (set t a1) a2 = set t a2;
  }.

Program Instance lens_id {T: Type} : Lens T T :=
  {
    get t := t;
    set _ t := t;
  }.

Program Instance lens_fst {U V} : Lens (U * V) U :=
  {
    get '(u, v) := u;
    set '(_, v) u := (u, v);
  }.

Program Instance lens_snd {U V} : Lens (U * V) V :=
  {
    get '(u, v) := v;
    set '(u, _) v := (u, v);
  }.

Program Instance lens_unit {T} : Lens T unit :=
  {
    get _ := tt;
    set t tt := t;
  }.
Next Obligation. intros; try easy. now destruct a. Defined.

Program Instance lens_prod {T S A B: Type} `(Lens T A) `(Lens S B) : Lens (T * S) (A * B) :=
  {
    get '(t, s) := (get t, get s);
    set '(t, s) '(a, b) := (set t a, set s b);
  }.
Next Obligation. now rewrite !get_set. Defined.
Next Obligation. now rewrite !set_get. Defined.
Next Obligation. now rewrite !set_set. Defined.

Program Instance lens_comp {U V W: Type} `(Lens U V) `(Lens V W) : Lens U W :=
  {
    get u := get (get u);
    set u w := set u (set (get u) w);
  }.
Next Obligation. now rewrite !get_set. Defined.
Next Obligation. now rewrite !set_get. Defined.
Next Obligation. rewrite !get_set. rewrite !set_set. reflexivity. Defined.

(* A generalized version of Kripke world *)
Class World (T: Type) :=
  {
    w_state : Type;
    w_pset : PSet w_state;
    w_lens : Lens T w_state;
    (* internal transition step *)
    w_int_step : ReflTranRel w_state;
    (* external transition step *)
    w_ext_step : ReflTranRel w_state;
  }.

Existing Instance w_lens.
Arguments w_state {_} _.
Arguments w_pset {_} _.

Arguments w_int_step {_ _}.
Arguments w_ext_step {_ _}.
Infix "*->" := w_int_step (at level 60, no associativity).
Infix ":->" := w_ext_step (at level 60, no associativity).
Existing Instance w_pset | 10.

Module W.
Local Instance world_unit {T: Type} : World T :=
  {
    w_state := unit;
    w_lens := lens_unit;
    w_int_step := {| rel s t := True; |};
    w_ext_step := {| rel s t := True |};
  }.
End W.

Section PROD.
  Context `(WA: World A) `(WB: World B).
  Program Instance world_prod: World (A * B) :=
    {
      w_state := @w_state A _ * @w_state B _;
      w_lens := lens_prod w_lens w_lens;
      w_int_step := {| rel := Relators.prod_rel w_int_step w_int_step |};
      w_ext_step := {| rel := Relators.prod_rel w_ext_step w_ext_step |};
    }.

  Lemma ext_step_prod (a1 a2: w_state WA) (b1 b2: w_state WB):
    (a1, b1) :-> (a2, b2) <-> a1 :-> a2 /\ b1 :-> b2.
  Proof.
    split.
    - intros H. inv H. cbn in *. split; eauto.
    - intros [X Y]. split; eauto.
  Qed.

  Lemma int_step_prod (a1 a2: w_state WA) (b1 b2: w_state WB):
    (a1, b1) *-> (a2, b2) <-> a1 *-> a2 /\ b1 *-> b2.
  Proof.
    split.
    - intros H. inv H. cbn in *. split; eauto.
    - intros [X Y]. split; eauto.
  Qed.

End PROD.
Arguments world_prod {_} _ {_} _.

Section SYMTBL.

  Context `{W: World T}.

  Instance symtbl_world  : World (Genv.symtbl * T) :=
    {
      w_state := @w_state T _;
      w_lens := lens_comp lens_snd w_lens;
      w_int_step := w_int_step;
      w_ext_step := w_ext_step;
    }.

End SYMTBL.

Instance pset_world `{PSet T} : World T :=
  {
    w_state := T;
    w_lens := lens_id;
    w_int_step := {| rel t1 t2 := True |};
    w_ext_step := {| rel := eq |};
  }.
Arguments pset_world _ {_}.

(** ------------------------------------------------------------------------- *)
(** ** Semantics with Encapsulation *)
Record esemantics {liA liB} := {
    pstate : Type;              (** persistent state *)
    pstate_pset : PSet pstate;
    esem :> semantics liA (liB @ pstate)
  }.
Arguments esemantics : clear implicits.
Infix "+->" := esemantics (at level 70).
Existing Instance pstate_pset.

(** *** Composition *)

Definition comp_esem' `(L1: liB +-> liC) `(L2: liA +-> liB) sk : liA +-> liC :=
  {|
    pstate := pstate L1 * pstate L2;
    esem := $(comp_semantics' (L1 @ pstate L2) L2 sk);
  |}.

Definition comp_esem `(L1: liB +-> liC) `(L2: liA +-> liB) : option (liA +-> liC) :=
  match comp_semantics $(L1 @ pstate L2) L2 with
  | Some L => Some {| pstate := pstate L1 * pstate L2; esem := L; |}
  | None => None
  end.

(** *** Construction *)

Definition semantics_embed `(L: semantics liA liB) : liA +-> liB :=
  {| pstate := unit; esem := semantics_map L lf (li_iso_inv _); |}.

(** ------------------------------------------------------------------------- *)
(** ** Stateful Simulation Convention and Simulation *)
Require Import Relation_Operators.

Module ST.

  Record callconv  {li1 li2} :=
    mk_callconv {
      ccworld : Type;
      ccworld_world : World ccworld;
      match_senv : ccworld -> Genv.symtbl -> Genv.symtbl -> Prop;
      match_query : ccworld -> query li1 -> query li2 -> Prop;
      match_reply : ccworld -> reply li1 -> reply li2 -> Prop;
      match_senv_public_preserved:
        forall w se1 se2,
        match_senv w se1 se2 ->
        forall id, Genv.public_symbol se2 id = Genv.public_symbol se1 id;
      match_senv_valid_for:
        forall w se1 se2 sk,
        match_senv w se1 se2 ->
        Genv.valid_for sk se1 <->
        Genv.valid_for sk se2;
      match_senv_symbol_address:
        forall w se1 se2, match_senv w se1 se2 ->
        forall q1 q2, match_query w q1 q2 ->
        forall i, Genv.symbol_address se1 i Ptrofs.zero = entry q1 <->
           Genv.symbol_address se2 i Ptrofs.zero = entry q2;
      match_query_defined:
        forall w q1 q2,
          match_query w q1 q2 ->
          entry q1 <> Vundef <-> entry q2 <> Vundef;
    }.
  Arguments callconv: clear implicits.
  Existing Instance ccworld_world | 3.

  Hint Resolve match_senv_public_preserved match_senv_valid_for
               match_senv_symbol_address match_query_defined: scc.

  Definition ccstate `(cc: callconv li1 li2) := w_state (ccworld_world cc).
  Definition ccstate_init `(cc: callconv li1 li2) := pset_init (ccstate cc).

  Program Definition callconv_lift
          `(cc: callconv li1 li2) `{PSet U} `{PSet V} : callconv (li1@U) (li2@V) :=
    {|
      ccworld := ccworld cc * (U * V);
      ccworld_world := world_prod (ccworld_world cc) (world_prod (pset_world U) (pset_world V));
      match_senv '(w, (u, v)) se1 se2 := match_senv cc w se1 se2;
      match_query '(w, (u, v)) '(q1, uq) '(q2, vq) :=
        match_query cc w q1 q2 /\ u = uq /\ v = vq;
      match_reply '(w, (u, v)) '(q1, uq) '(q2, vq) :=
        match_reply cc w q1 q2 /\ u = uq /\ v = vq;
    |}.
  Next Obligation. eauto with scc. Qed.
  Next Obligation. eauto with scc. Qed.
  Next Obligation. eauto with scc. Qed.
  Next Obligation. eauto with scc. Qed.

  Program Definition cc_compose {li1 li2 li3}
          (cc12: callconv li1 li2) (cc23: callconv li2 li3) :=
    {|
      ccworld := Genv.symtbl * (ccworld cc12 * ccworld cc23);
      ccworld_world := @symtbl_world _ (world_prod (ccworld_world cc12) (ccworld_world cc23));
      match_senv '(se2, (w12, w23)) se1 se3 :=
        match_senv cc12 w12 se1 se2 /\ match_senv cc23 w23 se2 se3;
      match_query '(se2, (w12, w23)) q1 q3 :=
      exists q2, match_query cc12 w12 q1 q2 /\ match_query cc23 w23 q2 q3;
      match_reply '(se2, (w12, w23)) r1 r3 :=
      exists r2, match_reply cc12 w12 r1 r2 /\ match_reply cc23 w23 r2 r3;
    |}.
  Next Obligation. eauto with scc. Qed.
  Next Obligation.
    etransitivity; eapply match_senv_valid_for; eauto.
  Qed.
  Next Obligation.
    etransitivity; eapply match_senv_symbol_address; eauto.
  Qed.
  Next Obligation.
    etransitivity; eapply match_query_defined; eauto.
  Qed.

  (** Stateful Simulation *)
  Section FSIM.

    Context {liA1 liA2} (ccA: callconv liA1 liA2).
    Context {liB1 liB2} (ccB: callconv liB1 liB2).
    Context (se1 se2: Genv.symtbl).
    Context (sa: ccstate ccA) (sb: ccstate ccB) (wb: ccworld ccB)
            (winv:  ccstate ccA -> ccstate ccB -> Prop).
    Context {state1 state2: Type}.

    (* There is supposed to be a relation between the wB and wA, which is
       re-established at the end *)
    Record fsim_properties
           (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2)
           (index: Type) (order: index -> index -> Prop)
           (match_states: ccstate ccA -> ccstate ccB -> index -> state1 -> state2 -> Prop) :=
      {
        fsim_match_initial_states:
          forall q1 q2 s1 sb', sb :-> sb' -> match_query ccB (set wb sb') q1 q2 -> initial_state L1 q1 s1 ->
          match_senv ccB (set wb sb') se1 se2 ->
          exists i, exists s2, initial_state L2 q2 s2 /\
          exists sa' sb'', sa :-> sa' /\ sb' *-> sb'' /\ match_states sa' sb'' i s1 s2;
        fsim_match_final_states:
          forall sa sb i s1 s2 r1, match_states sa sb i s1 s2 -> final_state L1 s1 r1 ->
          exists r2, final_state L2 s2 r2 /\
          exists sb', sb *-> sb' /\ match_reply ccB (set wb sb') r1 r2 /\ winv sa sb';
        fsim_match_external:
          forall sa sb i s1 s2 q1, match_states sa sb i s1 s2 -> at_external L1 s1 q1 ->
          exists q2, at_external L2 s2 q2 /\ exists sa' wa', sa :-> sa' /\ get wa' = sa' /\
          match_query ccA wa' q1 q2 /\ match_senv ccA wa' se1 se2 /\
          forall r1 r2 s1' sa'', sa' *-> sa'' -> match_reply ccA (set wa' sa'') r1 r2 ->
          after_external L1 s1 r1 s1' ->
          exists i' s2', after_external L2 s2 r2 s2' /\
          exists sa''' sb', sa'' :-> sa''' /\ sb *-> sb' /\ match_states sa''' sb' i' s1' s2';
        fsim_simulation:
          forall s1 t s1', Step L1 s1 t s1' ->
          forall sa sb i s2, match_states sa sb i s1 s2 ->
          exists i', exists s2', (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i)) /\
          exists sa' sb', sa :-> sa' /\ sb *-> sb' /\ match_states sa' sb' i' s1' s2';
      }.
    Arguments fsim_properties : clear implicits.

    Lemma fsim_simulation':
      forall L1 L2 index order match_states, fsim_properties L1 L2 index order match_states ->
      forall i s1 t s1', Step L1 s1 t s1' ->
      forall sa sb s2, match_states sa sb i s1 s2 ->
      exists i' sa' sb', sa :-> sa' /\ sb *-> sb' /\
      ((exists s2', Plus L2 s2 t s2' /\ match_states sa' sb' i' s1' s2')
      \/ (order i' i /\ t = E0 /\ match_states sa' sb' i' s1' s2)).
    Proof.
      intros. exploit @fsim_simulation; eauto.
      intros (i' & s2' & A & wai & wbi & Hai & Hbi & B).
      exists i', wai, wbi. repeat split; eauto.
      destruct A.
      left; exists s2'; auto.
      destruct H2. inv H2.
      right; eauto.
      left; exists s2'; split; auto. econstructor; eauto.
    Qed.

    Section SIMULATION_SEQUENCES.

      Context L1 L2 index order match_states
              (S: fsim_properties L1 L2 index order match_states).

      Lemma simulation_star:
        forall s1 t s1', Star L1 s1 t s1' ->
        forall sa sb i s2, match_states sa sb i s1 s2 ->
        exists sa' sb' i', exists s2', Star L2 s2 t s2' /\
        sa :-> sa' /\ sb *-> sb' /\ match_states sa' sb' i' s1' s2'.
      Proof.
        induction 1; intros.
        eexists _, _, i; exists s2; repeat split; auto. apply star_refl.
        reflexivity. reflexivity. assumption.
        exploit fsim_simulation; eauto.
        intros (i' & s2' & A & wai & wbi & Hai & Hbi & B).
        exploit IHstar; eauto.
        intros (waj & wbj & i'' & s2'' & Hx & Haj & Hbj & C).
        exists waj, wbj, i''; exists s2''; repeat split; auto.
        eapply star_trans; eauto.
        intuition auto. apply plus_star; auto.
        all: etransitivity; eauto.
      Qed.

      Lemma simulation_plus:
        forall s1 t s1', Plus L1 s1 t s1' ->
        forall sa sb i s2, match_states sa sb i s1 s2 ->
        exists sa' sb' i', sa :-> sa' /\ sb *-> sb' /\
        ((exists s2', Plus L2 s2 t s2' /\ match_states sa' sb' i' s1' s2') \/
        clos_trans _ order i' i /\ t = E0 /\ match_states sa' sb' i' s1' s2).
      Proof.
        induction 1 using plus_ind2; intros.
        (* base case *)
        - exploit fsim_simulation'; eauto.
          intros (i' & wai & wbi & Hai & Hbi & A).
          exists wai, wbi, i'. repeat split; eauto.
          destruct A.
          left; auto.
          right; intuition.
        (* inductive case *)
        - exploit fsim_simulation'; eauto.
          intros (i' & wai & wbi & Hai & Hbi & A).
          destruct A as [[s2' [A B]] | [A [B C]]].
          + exploit simulation_star. apply plus_star; eauto. eauto.
            intros (waj & wbj & i'' & s2'' & P & Haj & Hbj & Q).
            exists waj, wbj, i''. repeat split. 1-2: etransitivity; eauto.
            left; exists s2''; split; auto. eapply plus_star_trans; eauto.

          + exploit IHplus; eauto.
            intros (waj & wbj & i'' & Haj & Hbj & P).
            destruct P as [[s2'' [P Q]] | [P [Q R]]].
            * subst.
              exists waj, wbj, i''. repeat split. 1-2: etransitivity; eauto.
              left; exists s2''; auto.
            * subst.
              exists waj, wbj, i''. repeat split. 1-2: etransitivity; eauto.
              right; intuition auto.
              eapply t_trans; eauto. eapply t_step; eauto.
      Qed.

    End SIMULATION_SEQUENCES.
  End FSIM.

  Arguments fsim_properties {_ _} _ {_ _} _ _ _ _ _ _ _ {_ _} L1 L2 index order match_states.

  Record fsim_components {liA1 liA2} (ccA: callconv liA1 liA2)
         {liB1 liB2} (ccB: callconv liB1 liB2) L1 L2 :=
    Forward_simulation {
        fsim_index: Type;
        fsim_order: fsim_index -> fsim_index -> Prop;
        fsim_match_states: _;
        fsim_invariant: ccstate ccA -> ccstate ccB -> Prop;

        fsim_invariant_env_step:
          forall sa sb, fsim_invariant sa sb -> forall sb', sb :-> sb' -> fsim_invariant sa sb';
        fsim_skel: skel L1 = skel L2;
        fsim_initial_world:
          forall se, fsim_invariant (ccstate_init ccA se) (ccstate_init ccB se);
        fsim_footprint: forall i, footprint L1 i <-> footprint L2 i;
        fsim_lts
          sa wb se1 se2:
          ST.match_senv ccB wb se1 se2 ->
          Genv.valid_for (skel L1) se1 ->
          fsim_invariant sa (get wb) ->
          fsim_properties ccA ccB se1 se2 sa (get wb) wb
            fsim_invariant (activate L1 se1) (activate L2 se2)
            fsim_index fsim_order (fsim_match_states se1 se2 wb);
        fsim_order_wf:
          well_founded fsim_order;
      }.
  Arguments Forward_simulation {_ _ ccA _ _ ccB L1 L2 fsim_index}.

  Definition forward_simulation {liA1 liA2} ccA {liB1 liB2} ccB L1 L2 :=
    inhabited (@fsim_components liA1 liA2 ccA liB1 liB2 ccB L1 L2).

End ST.
Arguments ST.callconv_lift {_ _} _ _ {_} _ {_}.

(** Normalized Stateful Simulation *)
Module STCAT.
  Definition forward_simulation {liA1 liA2} (ccA: ST.callconv liA1 liA2)
             {liB1 liB2} (ccB: ST.callconv liB1 liB2) L1 L2 :=
    ST.forward_simulation ccA ccB (normalize_sem L1) (normalize_sem L2).
End STCAT.

(** Simulations between components with encapsulated states *)
Module E.
  Definition forward_simulation {liA1 liA2} (ccA: ST.callconv liA1 liA2)
             {liB1 liB2} (ccB: ST.callconv liB1 liB2)
             (L1: liA1 +-> liB1) (L2: liA2 +-> liB2) :=
    STCAT.forward_simulation ccA (ST.callconv_lift ccB (pstate L1) (pstate L2)) L1 L2.
End E.

(** ------------------------------------------------------------------------- *)
(** * Properties about Stateful Simulations *)

(** ** Embedding Stateless Simulations *)

Program Definition callconv_embed {liA liB} (cc: callconv liA liB) : ST.callconv liA liB :=
  {|
    ST.ccworld := ccworld cc;
    ST.ccworld_world := W.world_unit;
    ST.match_senv := match_senv cc;
    ST.match_query := match_query cc;
    ST.match_reply := match_reply cc;
  |}.
Next Obligation.
  eapply match_senv_public_preserved; eauto.
Qed.
Next Obligation.
  eapply match_senv_valid_for; eauto.
Qed.
Next Obligation.
  eapply match_senv_symbol_address; eauto.
Qed.
Next Obligation.
  eapply match_query_defined; eauto.
Qed.
Notation "& cc" := (callconv_embed cc) (at level 0).

Theorem fsim_embed:
  forall `(ccA: callconv liA1 liA2) `(ccB: callconv liB1 liB2) L1 L2,
    forward_simulation ccA ccB L1 L2 -> ST.forward_simulation &ccA &ccB L1 L2.
Proof.
  intros * [H]. destruct H. constructor.
  eapply ST.Forward_simulation
    with fsim_order
         (fun se1 se2 wb _ _ i s1 s2 =>
            fsim_match_states se1 se2 wb i s1 s2
            /\ match_senv ccB wb se1 se2)
         (fun _ _ => True); try easy.
  cbn. intros wa wb se1 se2 Hse0 Hsk []. constructor.
  - intros * Hw Hq Hs Hse. specialize (fsim_lts _ _ _ Hse Hsk).
    edestruct (fsim_match_initial_states fsim_lts) as (ix & sx & A & B); eauto.
    exists ix, sx. split;  eauto.
    exists tt, tt. repeat split; easy.
  - intros ? * [Hs Hse] Hr. specialize (fsim_lts _ _ _ Hse Hsk).
    edestruct (fsim_match_final_states fsim_lts) as (rx & A & B); eauto.
    exists rx. split; eauto.
    exists tt. repeat split; easy.
  - intros * [Hs Hse] Hq. specialize (fsim_lts _ _ _ Hse Hsk).
    edestruct (fsim_match_external fsim_lts) as (wx & qx & A & B & C & D); eauto.
    exists qx. split; eauto.
    exists tt, wx. repeat split;  eauto.
    intros * Hw Hr Hrs.
    edestruct D as (iy & sy & E & F);  eauto.
    exists iy, sy. split. eauto.
    exists tt, tt. repeat split; easy.
  - intros * HS * [Hs Hse]. specialize (fsim_lts _ _ _ Hse Hsk).
    edestruct (fsim_simulation fsim_lts) as (ix & sx & A & B); eauto.
    exists ix, sx. split. eauto.
    exists tt, tt. repeat split; easy.
Qed.

(** ** Lifting Simulations with Additional States *)

Section LIFT.

  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          `(X: ST.fsim_components ccA ccB L1 L2).
  Context `{PSet K1} `{PSet K2}.

  Lemma st_fsim_lift': ST.forward_simulation
                        (ST.callconv_lift ccA K1 K2)
                        (ST.callconv_lift ccB K1 K2)
                        (L1@K1) (L2@K2).
  Proof.
    constructor.
    eapply ST.Forward_simulation with
      (ST.fsim_order X)
      (fun se1 se2 '(wb0, _) '(wa, (k1a, k2a)) '(wb, (k1b, k2b)) i '(s1, k1) '(s2, k2) =>
         ST.fsim_match_states X se1 se2 wb0 wa wb i s1 s2 /\
           k1a = k1 /\ k1b = k1 /\ k2a = k2 /\ k2b = k2)
      (fun '(wa, (k1a, k2a)) '(wb, (k1b, k2b)) => ST.fsim_invariant X wa wb /\ k1a = k1b /\ k2a = k2b).
    - intros [wa [k1a k2a]] [wb [k1b k2b]] (INV & -> & ->) [wb' [k1b' k2b']] W.
      inv W. cbn in *. inv H2. cbn in *. subst.
      split. eapply ST.fsim_invariant_env_step; eauto. easy.
    - apply X.
    - cbn. repeat split; eauto. apply X.
    - intros i. cbn. apply X.
    - intros [wa [k1a k2a]] [wb [k1b k2b]] se1 se2 Hse0 Hse (I & HK1 & HK2).
      subst. econstructor; cbn in *.
      + intros. eprod_crush. subst.
        pose proof (ST.fsim_lts X) as HX.
        edestruct @ST.fsim_match_initial_states as (idx & s' & Hs' & Hs); eauto.
        destruct Hs as (wa' & wb'' & W1 & W2 & HS).
        eexists idx, (s', _). repeat split; eauto.
        eexists (wa', (_, _)), (wb'', (_, _)). repeat split; eauto.
      + intros. eprod_crush. subst.
        pose proof (ST.fsim_lts X) as HX.
        edestruct @ST.fsim_match_final_states as (r' & H' & Hr'); eauto.
        destruct Hr' as (wb' & W & Hr' & INV).
        eexists (r', _). repeat split; eauto.
        eexists (wb', (_, _)). repeat split; eauto.
      + intros. eprod_crush. subst.
        pose proof (ST.fsim_lts X).
        edestruct @ST.fsim_match_external
          as (q' & H' & sa' & wa' & WA & Hget & Hq' & HSE & HH); eauto. subst.
        eexists (q', _). repeat split; eauto.
        eexists (get wa', (_, _)), (wa', (_, _)). repeat split; eauto.
        intros. eprod_crush. subst.
        edestruct HH as (i' & s2' & Haft & Hs); eauto.
        destruct Hs as (wa'' & wb' & WA' & WB & HS).
        eexists i', (s2', _). repeat split; eauto.
        eexists (wa'', (_, _)), (wb', (_, _)). repeat split; eauto.
      + intros. eprod_crush. subst.
        pose proof (ST.fsim_lts X).
        edestruct @ST.fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
        destruct Hs' as (wa' & wb' & WA & WB & HS).
        destruct Hs2'.
        * eexists idx', (s2', _). split.
          -- left. apply lifting_step_plus; eauto.
          -- eexists (wa', (_, _)), (wb', (_, _)).
             repeat split; eauto.
        * eexists idx', (s2', _). split.
          -- right. split. apply lifting_step_star; eauto. all: apply H4.
          -- eexists (wa', (_, _)), (wb', (_, _)).
             repeat split; eauto.
    - apply X.
  Qed.

End LIFT.

Lemma st_fsim_lift `(ccA: ST.callconv liA1 liA2) `(ccB: ST.callconv liB1 liB2)
      L1 L2 `{PSet K1} `{PSet K2}:
  ST.forward_simulation ccA ccB L1 L2 ->
  ST.forward_simulation (ST.callconv_lift ccA K1 K2)
                        (ST.callconv_lift ccB K1 K2)
                        (L1@K1) (L2@K2).
Proof. intros [X]. apply st_fsim_lift'. apply X. Qed.


(** The composition can be represented by the diagram:

  A₁ ———Ls₂——>> B₁ ———Ls₁——>> C₁
  |             |             |
 ccA           ccB           ccC
  |             |             |
  A₂ ———Lt₂——>> B₂ ———Lt₂—–>> C₂

 *)
(** ** Composition of Stateful Simulations *)

Section FSIM.
  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          `(ccC: ST.callconv liC1 liC2)
          (L1s: semantics liB1 liC1) (L2s: semantics liA1 liB1)
          (L1t: semantics liB2 liC2) (L2t: semantics liA2 liB2).
  Context (HL1: ST.fsim_components ccB ccC L1s L1t)
          (HL2: ST.fsim_components ccA ccB L2s L2t)
          (se1: Genv.symtbl) (se2: Genv.symtbl)
          (sa0: ST.ccstate ccA) (sc0: ST.ccstate ccC)
          (wc0: ST.ccworld ccC).

  Variant index := | index1: ST.fsim_index HL1 -> index
                   | index2: ST.fsim_index HL1 -> ST.fsim_index HL2 -> index.

  Variant order: index -> index -> Prop :=
    | order1 i1 i1': ST.fsim_order HL1 i1 i1' ->
                     order (index1 i1) (index1 i1')
    | order2 i1 i2 i2': ST.fsim_order HL2 i2 i2' ->
                        order (index2 i1 i2) (index2 i1 i2').

  Inductive match_states : ST.ccstate ccA -> ST.ccstate ccC -> index ->
                          comp_state L1s L2s -> comp_state L1t L2t -> Prop :=
  | match_st1 sa sb sc i1 s1 s1'
    (MST: ST.fsim_match_states HL1 se1 se2 wc0 sb sc i1 s1 s1')
    (MINV: ST.fsim_invariant HL2 sa sb):
    match_states  sa sc (index1 i1) (st1 L1s L2s s1) (st1 L1t L2t s1')
  | match_st2 sa sb sc i1 i2 s1 t1 s2 t2 sa0 wb0
    (MST: ST.fsim_match_states HL2 se1 se2 wb0 sa sb i2 s2 t2)
    (MINV: ST.fsim_invariant HL2  sa0  (get wb0))
    (MSE: ST.match_senv ccB wb0 se1 se2)
    (MR: forall r1 r2 (s1' : state L1s) sb',
        sb *-> sb' ->
        ST.match_reply ccB (set wb0 sb') r1 r2 ->
        after_external (L1s se1) s1 r1 s1' ->
        exists (i' : ST.fsim_index HL1) (t1' : state L1t),
          after_external (L1t se2) t1 r2 t1' /\
            exists sb'' sc', sb' :-> sb'' /\ sc *-> sc' /\
            ST.fsim_match_states HL1 se1 se2 wc0 sb'' sc' i' s1' t1'):
    match_states sa sc (index2 i1 i2) (st2 L1s L2s s1 s2) (st2 L1t L2t t1 t2).

  Definition inv : ST.ccstate ccA -> ST.ccstate ccC -> Prop :=
    fun sa sc => exists sb, ST.fsim_invariant HL1 sb sc /\ ST.fsim_invariant HL2 sa sb.

  Lemma st_fsim_lcomp' sk sk':
    ST.match_senv ccC wc0 se1 se2 ->
    inv sa0 sc0 -> get wc0 = sc0 ->
    Genv.valid_for (skel L1s) se1 -> Genv.valid_for (skel L2s) se1 ->
    ST.fsim_properties ccA ccC se1 se2 sa0 sc0 wc0 inv
                       (comp_semantics' L1s L2s sk se1)
                       (comp_semantics' L1t L2t sk' se2)
                       index order match_states.
  Proof.
    intros HSE0 (sb0 & INV1 & INV2) <- HSK1 HSK2. constructor.
    - intros q1 q2 s1 wc WC Hq H Hse. inv H.
      pose proof (ST.fsim_lts HL1).
      edestruct @ST.fsim_match_initial_states as (idx & s' & Hs' & Hs); eauto.
      destruct Hs as (wb & wc' & W1 & W2 & HS).
      exists (index1 idx), (st1 L1t L2t s').
      split. econstructor; eauto.
      exists sa0, wc'. repeat split; eauto. reflexivity.
      econstructor. apply HS. eapply ST.fsim_invariant_env_step; eauto.
    - intros wa wb i s1 s2 r1 Hs Hf. inv Hf. inv Hs.
      pose proof (ST.fsim_lts HL1).
      edestruct @ST.fsim_match_final_states as (r' & H' & Hr'); eauto.
      destruct Hr' as (wc' & W & Hr' & INV).
      exists r'. split. econstructor; eauto.
      exists wc'. repeat split; eauto.
      exists sb. split; eauto.
    - intros wa wc i s1 s2 q1 Hs H. inv H. inv Hs.
      pose proof (ST.fsim_lts HL2).
      edestruct @ST.fsim_match_external
        as (q' & H' & sa' & wa' & Hget & WA & Hq' & HSE & HH); eauto. subst.
      exists q'. split. econstructor; eauto.
      exists (get wa'), wa'. repeat split; eauto.
      intros r1 r2 xs1 wa'' WA' Hr HH'. inv HH'.
      specialize (HH _ _ _ _ WA' Hr H5) as (i2' & xs2 & Haft & Hss).
      destruct Hss as (wa''' & wb' & WA'' & WB & HS).
      eexists (index2 i1 i2'), (st2 L1t L2t _ _).
      split. econstructor; eauto.
      exists wa''', wc. repeat split; eauto. reflexivity.
      econstructor; eauto.
      intros ? ? ? wb'' WB''. apply MR. etransitivity; eauto.
    - intros s1 t s2 Hstep wa wc idx t1 Hs.
      inv Hstep; inv Hs.
      + pose proof (ST.fsim_lts HL1).
        edestruct @ST.fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
        destruct Hs' as (wb' & wc' & WB & WC & HS).
        exists (index1 idx'), (st1 L1t L2t s2'). split.
        * destruct Hs2'; [ left | right ].
          apply plus_internal1. auto.
          split. apply star_internal1. apply H1. constructor; apply H1.
        * exists wa, wc'. repeat split; eauto. reflexivity.
          econstructor; eauto. eapply @ST.fsim_invariant_env_step; eauto.
      + pose proof (ST.fsim_lts HL2).
        edestruct @ST.fsim_simulation as (idx' & xs2' & Hs2' & Hs'); eauto.
        destruct Hs' as (wa' & wb' & WA & WB & HS).
        exists (index2 i1 idx'), (st2 L1t L2t t0 xs2'). split.
        * destruct Hs2'; [ left | right ].
          -- apply plus_internal2. auto.
          -- split. apply star_internal2. apply H1.
             constructor. apply H1.
        * exists wa', wc. repeat split; eauto. reflexivity.
          econstructor; eauto.
          intros r1 r2 sr wb'' WB'. apply MR. etransitivity; eauto.
      + pose proof (ST.fsim_lts HL1) as X.
        edestruct @ST.fsim_match_external
          as (q' & H' & sb' & wb' & Hget & WB & Hq' & Hse & HH); eauto. subst.
        clear X.
        pose proof (ST.fsim_lts HL2).
        specialize (H1 wa wb').
        exploit H1. eauto. eauto. eapply ST.fsim_invariant_env_step; eauto.
        clear H1. intros H1.
        edestruct @ST.fsim_match_initial_states as (i2 & s' & Hs' & Hs). apply H1.
        reflexivity. rewrite set_get. eauto. eauto. rewrite set_get. eauto.
        destruct Hs as (wa' & wb'' & WA & WB' & Hs).
        exists (index2 i1 i2), (st2 L1t L2t s1' s'). split.
        * left. apply plus_one. eapply step_push; eauto.
        * exists wa', wc. repeat split; eauto. reflexivity.
          econstructor; eauto.
          eapply ST.fsim_invariant_env_step; eauto.
          intros r1 r2 sr wb''' WB'' HR Haft.
          specialize (HH r1 r2 sr wb'''). apply HH. etransitivity; eauto.
          exact HR. exact Haft.
      + pose proof (ST.fsim_lts HL2).
        edestruct @ST.fsim_match_final_states as (r' & H' & Hr'); eauto.
        edestruct Hr' as (wb' & WB & Hr & INV).
        edestruct MR as (idx & t1 & HH & HX); eauto.
        destruct HX as (wb'' & wc' & WB' & WC & HS).
        exists (index1 idx), (st1 L1t L2t t1). split.
        * left. apply plus_one. eapply step_pop; eauto.
        * exists wa, wc'. repeat split; eauto. reflexivity.
          econstructor. exact HS.
          eapply ST.fsim_invariant_env_step; eauto.
  Qed.

End FSIM.

Section COMP.

  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          `(ccC: ST.callconv liC1 liC2)
          (L1s: semantics liB1 liC1) (L2s: semantics liA1 liB1)
          (L1t: semantics liB2 liC2) (L2t: semantics liA2 liB2).
  Context (HL1: ST.forward_simulation ccB ccC L1s L1t)
          (HL2: ST.forward_simulation ccA ccB L2s L2t).
  Context `(HLs: comp_semantics L1s L2s = Some Ls)
          Lt (HLt: comp_semantics L1t L2t = Some Lt).

  Lemma st_fsim_lcomp : ST.forward_simulation ccA ccC Ls Lt.
  Proof.
    destruct HL1 as [Ha]. destruct HL2 as [Hb].
    unfold comp_semantics, option_map in HLs, HLt.
    destruct (Linking.link (skel L1s) (skel L2s)) as [sk1|] eqn:Hsk1; try discriminate. inv HLs.
    destruct (Linking.link (skel L1t) (skel L2t)) as [sk2|] eqn:Hsk2; try discriminate. inv HLt.
    constructor.
    eapply ST.Forward_simulation
      with (@order _ _ ccA _ _ ccB _ _ ccC L1s L2s L1t L2t Ha Hb)
           (@match_states _ _ ccA _ _ ccB _ _ ccC L1s L2s L1t L2t Ha Hb)
           (@inv _ _ ccA _ _ ccB _ _ ccC L1s L2s L1t L2t Ha Hb).
    - intros wa wc (wb & I1 & I2) wc' WC.
      exists wb; split; eauto.
      eapply ST.fsim_invariant_env_step; eauto.
    - destruct Ha. destruct Hb. cbn. congruence.
    - intros se. unfold inv.
      exists (ST.ccstate_init ccB se). split. apply Ha. apply Hb.
    - cbn. intros i. destruct Ha, Hb.
      rewrite fsim_footprint, fsim_footprint0. reflexivity.
    - intros wa wc se1 se2 Hse0 Hse INV.
      apply Linking.link_linkorder in Hsk1.
      apply Linking.link_linkorder in Hsk2.
      eapply st_fsim_lcomp'; eauto.
      eapply Genv.valid_for_linkorder. apply Hsk1. auto.
      eapply Genv.valid_for_linkorder. apply Hsk1. auto.
    - clear - Ha Hb. intros [|].
      + induction (ST.fsim_order_wf Ha f). constructor.
        intros. inv H1. apply H0. auto.
      + induction (ST.fsim_order_wf Hb f0). constructor.
        intros. inv H1. apply H0. auto.
  Qed.

  (* TODO: clean up the copy-paste *)
  Lemma st_fsim_lcomp_sk sk:
    Linking.linkorder (skel L1s) sk ->
    Linking.linkorder (skel L2s) sk ->
    ST.forward_simulation ccA ccC (comp_semantics' L1s L2s sk) (comp_semantics' L1t L2t sk).
  Proof.
    destruct HL1 as [Ha]. destruct HL2 as [Hb].
    intros Hsk1 Hsk2. constructor.
    eapply ST.Forward_simulation
      with (@order _ _ ccA _ _ ccB _ _ ccC L1s L2s L1t L2t Ha Hb)
           (@match_states _ _ ccA _ _ ccB _ _ ccC L1s L2s L1t L2t Ha Hb)
           (@inv _ _ ccA _ _ ccB _ _ ccC L1s L2s L1t L2t Ha Hb).
    - intros wa wc (wb & I1 & I2) wc' WC.
      exists wb; split; eauto.
      eapply ST.fsim_invariant_env_step; eauto.
    - destruct Ha. destruct Hb. cbn. congruence.
    - intros se. unfold inv.
      exists (ST.ccstate_init ccB se). split. apply Ha. apply Hb.
    - cbn. intros i. destruct Ha, Hb.
      rewrite fsim_footprint, fsim_footprint0. reflexivity.
    - intros wa wc se1 se2 Hse0 Hse INV.
      eapply st_fsim_lcomp'; eauto.
      eapply Genv.valid_for_linkorder; eauto.
      eapply Genv.valid_for_linkorder; eauto.
    - clear - Ha Hb. intros [|].
      + induction (ST.fsim_order_wf Ha f). constructor.
        intros. inv H1. apply H0. auto.
      + induction (ST.fsim_order_wf Hb f0). constructor.
        intros. inv H1. apply H0. auto.
  Qed.

End COMP.

(** ------------------------------------------------------------------------- *)
(** ** Composition of Stateful Simulation Conventions *)

(** The composition can be represented by the diagram:

  A♯ ———L♯ ——>>B♯
  |            |
 ccA₁         ccB₁
  |            |
  A♮ ———L♮ ——>> B♮
  |            |
 ccA₂         ccB₂
  |            |
  A♭ ———L♭ ——>> B♭

 *)
Section COMP_FSIM.

  Context `(ccA1: ST.callconv liAs liAn) `(ccA2: ST.callconv liAn liAf)
          `(ccB1: ST.callconv liBs liBn) `(ccB2: ST.callconv liBn liBf)
          (Ls: semantics liAs liBs) (Ln: semantics liAn liBn) (Lf: semantics liAf liBf).
  Context (H1: ST.fsim_components ccA1 ccB1 Ls Ln)
          (H2: ST.fsim_components ccA2 ccB2 Ln Lf).

  Inductive compose_fsim_match_states se1 se3:
    ST.ccworld (ST.cc_compose ccB1 ccB2) ->
    ST.ccstate (ST.cc_compose ccA1 ccA2) ->
    ST.ccstate (ST.cc_compose ccB1 ccB2) ->
    (ST.fsim_index H2 * ST.fsim_index H1) ->
    state Ls -> state Lf -> Prop :=
  | compose_match_states_intro se2 s1 s2 s3 i1 i2 wa1 wa2 wb1 wb2 wb10 wb20
    (HS1: ST.fsim_match_states H1 se1 se2 wb10 wa1 wb1 i1 s1 s2)
    (HS2: ST.fsim_match_states H2 se2 se3 wb20 wa2 wb2 i2 s2 s3):
    compose_fsim_match_states se1 se3 (se2, (wb10, wb20)) (wa1, wa2) (wb1, wb2) (i2, i1) s1 s3.

  Inductive compose_fsim_inv:
    ST.ccstate (ST.cc_compose ccA1 ccA2) -> ST.ccstate (ST.cc_compose ccB1 ccB2) -> Prop :=
  | compose_fsim_inv_intro wa1 wa2 wb1 wb2
      (INV1: ST.fsim_invariant H1 wa1 wb1)
      (INV2: ST.fsim_invariant H2 wa2 wb2):
    compose_fsim_inv (wa1, wa2) (wb1, wb2).

  Lemma st_fsim_vcomp':
    ST.fsim_components (ST.cc_compose ccA1 ccA2) (ST.cc_compose ccB1 ccB2) Ls Lf.
  Proof.
    (* destruct H1 as [ index1 order1 match_states1 inv1 A1 B1 C1 D1 E1 F1 ]. *)
    (* destruct H2 as [ index2 order2 match_states2 inv2 A2 B2 C2 D2 E2 F2 ]. *)
    (* set (ff_index := (index2 * index1)%type). *)
    set (ff_order := lex_ord (Relation_Operators.clos_trans
                                _ (ST.fsim_order H2)) (ST.fsim_order H1)).
    (* set (ff_match_states := *)
    (*        fun se1 se3 '(ose, wa1, wa2) '(o, wb1, wb2) '(i2, i1) s1 s3 => *)
    (*          match ose with *)
    (*          | Some se2 => *)
    (*              exists s2, match_states1 se1 se2 wa1 wb1 i1 s1 s2 /\ *)
    (*                      match_states2 se2 se3 wa2 wb2 i2 s2 s3 *)
    (*          | None => False *)
    (*          end). *)

    (* set (ff_inv := fun '(x, wa1, wa2) '(y, wb1, wb2) => inv1 wa1 wb1 /\ inv2 wa2 wb2). *)

    (* replace (ST.fsim_index H2 * ST.fsim_index H1)%type *)
    (*   with ff_index in ff_match_states. *)
    (* 2: { subst ff_index. rewrite X1. rewrite X2. reflexivity. } *)
    (* clear X1 X2. *)
    apply ST.Forward_simulation with ff_order compose_fsim_match_states compose_fsim_inv.
    - intros [wa1 wa2] [wb1 wb2] I [wb1' wb2'] W.
      inv I. inv W. cbn in *.
      split; eapply ST.fsim_invariant_env_step; eauto.
    - rewrite (ST.fsim_skel H1); apply (ST.fsim_skel H2).
    - cbn in *. econstructor.
      apply ST.fsim_initial_world. apply ST.fsim_initial_world.
    - intros i. rewrite (ST.fsim_footprint H1). apply (ST.fsim_footprint H2).
    - intros [wa1 wa2] [se2 [wb1 wb2]] se1 se3 [Hse01 Hse02] Hse1 I.
      cbn in I. inv I.
      pose proof (@ST.fsim_lts _ _ _ _ _ _ _ _ H1 wa1 wb1 se1 se2 Hse01 Hse1 INV1) as X1.
      assert (Hse2: Genv.valid_for (skel Ln) se2).
      { rewrite <- (ST.fsim_skel H1). rewrite <- @ST.match_senv_valid_for; eauto. }
      pose proof (@ST.fsim_lts _ _ _ _ _ _ _ _ H2 wa2 wb2 se2 se3 Hse02 Hse2 INV2) as X2.
      clear Hse1 Hse2. constructor.
      + intros q1 q3 s1 (wb1' & wb2') WB (q2 & Hq12 & Hq23) Hi Hse.
        destruct Hse as (Hse1 & Hse2). inv WB. cbn in *.
        edestruct (@ST.fsim_match_initial_states liAs) as (i & s2 & A & B); eauto.
        edestruct (@ST.fsim_match_initial_states liAn) as (i' & s3 & C & D); eauto.
        destruct B as (wa1' & wb1'' & WA1 & WB1' & B).
        destruct D as (wa2' & wb2'' & WA2 & WB2' & D).
        eexists (i', i), s3. split; eauto.
        eexists (wa1', wa2'), (wb1'', wb2''). repeat split; eauto.
        econstructor; eauto.
      + intros (wa1' & wa2') (wb1' & wb2') (i2, i1) s1 s3 r1 Hs H.
        inv Hs.
        edestruct (@ST.fsim_match_final_states liAs) as (r2 & Hr2 & A); eauto.
        edestruct (@ST.fsim_match_final_states liAn) as (r3 & Hr3 & B); eauto.
        destruct A as (wb1'' & WB1' & R1 & I1).
        destruct B as (wb2'' & WB2' & R2 & I2).
        exists r3. repeat split; eauto.
        eexists (wb1'', wb2''). repeat split; eauto.
        econstructor; eauto.
      + intros (wa1' & wa2') (wb1' & wb2') (i2, i1) s1 s3 q1 Hs H.
        inv Hs.
        edestruct (@ST.fsim_match_external liAs)
          as (q2 & Hq2 & wax & xx & Hxx & Hwx & Hq12 & HSE12 & Hk12); eauto.
        edestruct (@ST.fsim_match_external liAn)
          as (q3 & Hq3 & way & yy & Hyy & Hwy & Hq23 & HSE23 & Hk23); eauto.
        exists q3. repeat split; eauto. eexists (wax, way), (se2, (xx, yy)).
        subst. repeat split; eauto.
        * econstructor; eauto.
        * intros r1 r3 s1' (wai & waj) Hw (r2 & Hr12 & Hr23) HH. inv Hw. cbn in *.
          edestruct Hk12 as (i2' & s2' & Hs2' & wam & wbm & Ham & Hbm & Hm); eauto.
          edestruct Hk23 as (i1' & s3' & Hs3' & wan & wbn & Han & Hbn & Hn); eauto.
          eexists (_, _), _. repeat split; eauto.
          eexists (_, _), (_, _). repeat split; eauto.
          econstructor; eauto.
      + intros s1 t s1' Hstep (wai & waj) (wbi & wbj) (i2, i1) s3 Hs.
        inv Hs.
        edestruct (@ST.fsim_simulation' liAs) as (i1' & waii & wbii & Hai & Hbi & Hx); eauto.
        destruct Hx as [[s2' [A B]] | [A [B C]]].
        * (* L2 makes one or several steps. *)
          edestruct (@ST.simulation_plus liAn) as (wak & wbk & i2' & Hak & Hbk & X); eauto.
          destruct X as [[s3' [P Q]] | [P [Q R]]].
          -- (* L3 makes one or several steps *)
            exists (i2', i1'); exists s3'; split.
            left; eauto.
            eexists (_, _), (_, _). repeat split; eauto.
            econstructor; eauto.
          -- (* L3 makes no step *)
            exists (i2', i1'); exists s3; split.
            right; split. subst t; apply star_refl. red. left. auto.
            eexists (_, _), (_, _). repeat split; eauto.
            econstructor; eauto.
        * (* L2 makes no step *)
          exists (i2, i1'); exists s3; split.
          right; split. subst t; apply star_refl. red. right. auto.
          eexists (_, _), (_, _). repeat split; eauto.
          1-2: cbn; reflexivity.
          econstructor; eauto.
    - unfold ff_order.
      apply wf_lex_ord. apply Transitive_Closure.wf_clos_trans.
      eapply (ST.fsim_order_wf H2). eapply (ST.fsim_order_wf H1).
  Qed.

End COMP_FSIM.

Lemma st_fsim_vcomp
  `(ccA1: ST.callconv liAs liAn) `(ccA2: ST.callconv liAn liAf)
  `(ccB1: ST.callconv liBs liBn) `(ccB2: ST.callconv liBn liBf)
  (Ls: semantics liAs liBs) (Ln: semantics liAn liBn) (Lf: semantics liAf liBf):
  ST.forward_simulation ccA1 ccB1 Ls Ln ->
  ST.forward_simulation ccA2 ccB2 Ln Lf ->
  ST.forward_simulation (ST.cc_compose ccA1 ccA2) (ST.cc_compose ccB1 ccB2) Ls Lf.
Proof.
  intros [X] [Y]. constructor. eapply st_fsim_vcomp'; eauto.
Qed.

(** ------------------------------------------------------------------------- *)
(** ** Left and Right Unit Laws *)

Section ID_FSIM.

  Context `(cc: ST.callconv liA liB) (sk: AST.program unit unit).
  Inductive sf_ms se1 se2 w: ST.ccstate cc ->  ST.ccstate cc ->
                   @state liA _ (id_semantics sk) ->
                   @state liB _ (id_semantics sk) -> Prop :=
  | sf_ms_q s q1 q2:
    ST.match_senv cc (set w s) se1 se2 ->
    ST.match_query cc (set w s) q1 q2 -> sf_ms se1 se2 w s s (st_q q1) (st_q q2)
  | sf_ms_r s r1 r2:
    ST.match_reply cc (set w s) r1 r2 -> sf_ms se1 se2 w s s (st_r r1) (st_r r2).
  Hint Constructors sf_ms.

  Lemma id_self_fsim :
    ST.forward_simulation cc cc (id_semantics sk) (id_semantics sk).
  Proof.
    constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_:unit) => 0))
      (fun se1 se2 w sa sb _ => sf_ms se1 se2 w sa sb)
      (fun w1 w2 => w1 :-> w2);
      try reflexivity.
    - intros. etransitivity; eauto.
    - intros wa wb se1 se2 Hse0 Hse Hw. constructor.
      + intros q1 q2 s1 wb1 Hb Hq H HE. inv H. exists tt.
        eexists. split. constructor.
        exists wb1, wb1. repeat split; eauto; try easy.
        etransitivity; cbn; eauto.
      + intros wa1 wb1 [] s1 s2 r1 Hs H. inv H. inv Hs.
        eexists. split. constructor.
        exists wb1. repeat split; easy.
      + intros wa1 wb1 [] s1 s2 q1 Hs H. inv H. inv Hs.
        eexists. split. constructor.
        exists wb1, (set wb wb1).
        split. reflexivity.
        split. now rewrite get_set.
        split; eauto. split; eauto.
        intros r1 r2 s1' wb2 Hb Hr H. inv H.
        eexists tt, _. split. constructor.
        rewrite set_set in Hr.
        exists wb2, wb2. repeat split; eauto. reflexivity.
      + intros. easy.
    - apply well_founded_ltof.
  Qed.

End ID_FSIM.

Section CAT_SIM.

  Lemma st_normalize_fsim `(ccA: ST.callconv liA1 liA2)
        `(ccB: ST.callconv liB1 liB2) L1 L2:
    ST.forward_simulation ccA ccB L1 L2 ->
    STCAT.forward_simulation ccA ccB L1 L2.
  Proof.
    intros H. unfold STCAT.forward_simulation, normalize_sem.
    assert (Hsk: skel L1 = skel L2).
    { destruct H. apply (ST.fsim_skel X). }
    unfold left_comp_id, right_comp_id. rewrite Hsk.
    eapply st_fsim_lcomp_sk.
    - apply id_self_fsim.
    - eapply st_fsim_lcomp_sk.
      + exact H.
      + apply id_self_fsim.
      + rewrite Hsk. apply Linking.linkorder_refl.
      + rewrite <- Hsk. apply CategoricalComp.id_skel_order.
    - apply CategoricalComp.id_skel_order.
    - apply Linking.linkorder_refl.
  Qed.

  Lemma st_fsim_left_unit1 `(L: semantics liA liB):
    STCAT.forward_simulation &1 &1 L (1 o L).
  Proof. apply fsim_embed. apply CAT.left_unit_1. Qed.

  Lemma st_fsim_left_unit2 `(L: semantics liA liB):
    STCAT.forward_simulation &1 &1 (1 o L) L.
  Proof. apply fsim_embed. apply CAT.left_unit_2. Qed.

  Lemma st_fsim_right_unit1 `(L: semantics liA liB):
    STCAT.forward_simulation &1 &1 L (L o 1).
  Proof. apply fsim_embed. apply CAT.right_unit_1. Qed.

  Lemma st_fsim_right_unit2 `(L: semantics liA liB):
    STCAT.forward_simulation &1 &1 (L o 1) L.
  Proof. apply fsim_embed. apply CAT.right_unit_2. Qed.

  Section CC_UNIT.
    Context `(ccA: ST.callconv liA1 liA2) `(ccB: ST.callconv liB1 liB2).
    Lemma cc_right_unit L1 L2:
      ST.forward_simulation (ST.cc_compose ccA &1) (ST.cc_compose ccB &1) L1 L2 ->
      ST.forward_simulation ccA ccB L1 L2.
    Proof.
      intros [X]. constructor.
      eapply ST.Forward_simulation with
        (ST.fsim_order X)
        (fun se1 se2 w0 w1 w2 => ST.fsim_match_states X se1 se2 (se2, (w0, tt)) (w1, tt) (w2, tt))
        (fun w1 w2 => ST.fsim_invariant X (w1, tt) (w2, tt));
        try apply X.
      - intros. eapply ST.fsim_invariant_env_step; eauto.
        split; eauto. reflexivity.
      - intros wa wb se1 se2 Hse0 Hse HI.
        assert (Hse0': ST.match_senv (ST.cc_compose ccB & (1)) (se2, (wb, tt)) se1 se2).
        { constructor; eauto. constructor. }
        pose proof (@ST.fsim_lts _ _ _ _ _ _ _ _
                      X (wa, tt) (se2, (wb, tt)) se1 se2 Hse0' Hse HI) as H.
        constructor.
        + intros. exploit @ST.fsim_match_initial_states; eauto.
          (* ext_step *)
          instantiate (1 := (_, _)). split; cbn; eauto.
          (* query *)
          econstructor. split; eauto. constructor.
          (* senv *)
          econstructor; eauto. econstructor.
          intros. cbn in *. eprod_crush.
          eexists _, _. split; eauto.
        + intros. exploit @ST.fsim_match_final_states; eauto.
          intros. cbn in *. eprod_crush. subst.
          eexists. split; eauto.
        + intros. exploit @ST.fsim_match_external; eauto.
          intros. cbn in *. eprod_crush. subst.
          eexists. split; eauto.
          eexists _, _; repeat split; eauto.
          intros. cbn in *.
          exploit H9; eauto.
          instantiate (1 := (_, _)). split; cbn; eauto.
          cbn. eexists. split; eauto.
          intros. eprod_crush.
          eexists _, _. split; eauto.
        + intros. exploit @ST.fsim_simulation; eauto.
          intros. cbn in *. eprod_crush.
          eexists _, _. split; eauto.
          Unshelve. all: exact tt.
    Qed.

    Lemma cc_left_unit L1 L2:
      ST.forward_simulation (ST.cc_compose &1 ccA) (ST.cc_compose &1 ccB) L1 L2 ->
      ST.forward_simulation ccA ccB L1 L2.
    Proof.
      intros [X]. constructor.
      eapply ST.Forward_simulation with
        (ST.fsim_order X)
        (fun se1 se2 w0 w1 w2 => ST.fsim_match_states X se1 se2 (se1, (tt, w0)) (tt, w1) (tt, w2))
        (fun w1 w2 => ST.fsim_invariant X (tt, w1) (tt, w2));
        try apply X.
      - intros. eapply ST.fsim_invariant_env_step; eauto.
        split; eauto. reflexivity.
      - intros wa wb se1 se2 Hse0 Hse HI.
        assert (Hse0': ST.match_senv (ST.cc_compose & (1) ccB) (se1, (tt, wb)) se1 se2).
        { constructor; eauto. constructor. }
        pose proof (@ST.fsim_lts _ _ _ _ _ _ _ _
                      X (tt, wa) (se1, (tt, wb)) se1 se2 Hse0' Hse HI) as H.
        constructor.
        + intros. exploit @ST.fsim_match_initial_states; eauto.
          (* ext_step *)
          instantiate (1 := (_, _)). split; cbn; eauto.
          (* query *)
          econstructor. split; eauto. constructor.
          (* senv *)
          econstructor; eauto. econstructor.
          intros. cbn in *. eprod_crush.
          eexists _, _. split; eauto.
        + intros. exploit @ST.fsim_match_final_states; eauto.
          intros. cbn in *. eprod_crush. subst.
          eexists. split; eauto.
        + intros. exploit @ST.fsim_match_external; eauto.
          intros. cbn in *. eprod_crush. subst.
          eexists. split; eauto.
          eexists _, _; repeat split; eauto.
          intros. cbn in *.
          exploit H9; eauto.
          instantiate (1 := (_, _)). split; cbn; eauto.
          cbn. eexists. split; eauto.
          intros. eprod_crush.
          eexists _, _. split; eauto.
        + intros. exploit @ST.fsim_simulation; eauto.
          intros. cbn in *. eprod_crush.
          eexists _, _. split; eauto.
          Unshelve. all: exact tt.
    Qed.

  End CC_UNIT.

  Lemma st_cat_fsim_lcomp_sk
        `(ccA: ST.callconv liA1 liA2)
        `(ccB: ST.callconv liB1 liB2)
        `(ccC: ST.callconv liC1 liC2)
        L1s L2s L1t L2t sk:
    STCAT.forward_simulation ccB ccC L1s L1t ->
    STCAT.forward_simulation ccA ccB L2s L2t ->
    Linking.linkorder (skel L1s) sk ->
    Linking.linkorder (skel L2s) sk ->
    STCAT.forward_simulation ccA ccC
                             (comp_semantics' L1s L2s sk)
                             (comp_semantics' L1t L2t sk).
  Proof.
    intros X Y HSK1 HSK2. exploit @st_fsim_lcomp_sk.
    apply X. apply Y. apply HSK1. apply HSK2. intros Z. clear X Y.
    unfold STCAT.forward_simulation.
    assert (HX: ST.forward_simulation
                &1 &1 (normalize_sem (comp_semantics' L1s L2s sk))
                      (comp_semantics' (normalize_sem L1s) (normalize_sem L2s) sk)).
    { apply fsim_embed. apply normalize_comp_fsim_sk1. }
    assert (HY: ST.forward_simulation
                &1 &1 (comp_semantics' (normalize_sem L1t) (normalize_sem L2t) sk)
                      (normalize_sem (comp_semantics' L1t L2t sk))).
    { apply fsim_embed. apply normalize_comp_fsim_sk2. }
    exploit @st_fsim_vcomp. apply HX. apply Z. intros HZ. clear HX Z.
    exploit @st_fsim_vcomp. apply HZ. apply HY. intros H. clear HZ HY.
    apply cc_left_unit. apply cc_right_unit. apply H.
  Qed.

End CAT_SIM.

(** ------------------------------------------------------------------------- *)
(** ** Refinement between Stateful Simulation Conventions *)

Definition st_ccref {li1 li2} (cc1 cc2: ST.callconv li1 li2) : Prop :=
  STCAT.forward_simulation cc2 cc1 1 1.

(** A simplified condition for sim. conv. refinement given the situation that
    their states are isomorphic *)


Section REFL.
  Context {li1 li2} (cc: ST.callconv li1 li2).

  Inductive refl_ms se1 se2 w : ST.ccstate cc -> ST.ccstate cc -> @state li1 li1 1 -> @state li2 li2 1 -> Prop :=
  | refl_ms_q s q1 q2:
    ST.match_senv cc (set w s) se1 se2 ->
    ST.match_query cc (set w s) q1 q2 -> refl_ms se1 se2 w s s (st_q q1) (st_q q2)
  | refl_ms_r s r1 r2:
    ST.match_reply cc (set w s) r1 r2 -> refl_ms se1 se2 w s s (st_r r1) (st_r r2).
  Hint Constructors refl_ms.

  Lemma st_ccref_refl: st_ccref cc cc.
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0))
      (fun se1 se2 w0 wa wb _ => refl_ms se1 se2 w0 wa wb)
      (fun sa sb => sa :-> sb); try easy.
    - intros. etransitivity; eauto.
    - intros * Hse0 Hsk HI. constructor.
      + intros * Hw Hq Hs Hse. inv Hs.
        eexists tt, _. split. constructor.
        eexists _, _.
        repeat split. 3: econstructor;  eauto.
        etransitivity; eauto. reflexivity.
      + intros * [ ] * Hs Hr. inv Hr. inv Hs.
        eexists. split. econstructor.
        eexists.  repeat split;  try easy.
      + intros * [ ] * Hs Hq. inv Hq. inv Hs.
        eexists. split. constructor.
        eexists _, _. repeat split; eauto. now rewrite get_set.
        inv H2. rewrite get_set in H.
        eexists _. split. constructor.
        rewrite set_set in H1.
        eexists  _, _. repeat split; eauto. reflexivity.
      + intros; easy.
  Qed.

End REFL.

(** ** Left and Right Unit Laws for Sim. Conv. *)

Section CC_UNIT.

  Context `(cc: ST.callconv liA liB).

  Inductive lu_inv: ST.ccstate cc -> ST.ccstate cc -> Prop :=
  | lu_inv_intro wa wb:
    wa :-> wb -> lu_inv wa wb.
  Inductive lu_ms se1 se2 w0: ST.ccstate cc -> ST.ccstate cc -> @state liA liA 1 -> @state liB liB 1 -> Prop :=
  | lu_ms_q s q1 q2:
    ST.match_senv cc (set w0 s) se1 se2 ->
    ST.match_query cc (set w0 s) q1 q2 -> lu_ms se1 se2 w0 s s (st_q q1) (st_q q2)
  | lu_ms_r s r1 r2:
    ST.match_reply cc (set w0 s) r1 r2 -> lu_ms se1 se2 w0 s s (st_r r1) (st_r r2).
  Hint Constructors lu_ms lu_inv.

  Lemma ccref_left_unit1:
    st_ccref cc (ST.cc_compose &1 cc).
  Proof.
    unfold st_ccref. apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun se1 se2 w0 '(_, w1) w2 _ => lu_ms se1 se2 w0 w1 w2)
      (fun '(_, w1) w2 => lu_inv w1 w2); try easy.
    - intros [? wa] wb I wb1 Hb. inv I.
      constructor. etransitivity; eauto.
    - intros [? wa] wb se1 se2 Hse0 HSE I. constructor.
      + intros q1 q2 s1 wb1 Hb Hq H. inv H. exists tt, (st_q q2).
        split. constructor.
        exists (tt, wb1), wb1. repeat split; cbn; eauto; try easy.
        inv I. etransitivity; eauto.
      + intros [? wa1] wb1 [] s1 s2 r1 Hs H. inv H. inv Hs.
        exists r2. split. constructor.
        exists wb1. repeat split; easy.
      + intros [? wa1] wb1 [] s1 s2 q1 Hs H. inv H. inv Hs.
        exists q2. split. constructor.
        exists (tt, wb1). repeat split; try easy.
        eexists (_, (_, _)). cbn. repeat split; eauto. easy. now rewrite get_set.
        intros r1 r2 s1' [? wa2] [? Ha] Hr HX. cbn in *.
        destruct Hr as (x & HR1 & HR2).
        inv HR1. inv HX.
        exists tt, (st_r r2). repeat split.
        exists (tt, wa2), wa2.
        repeat split; eauto. easy.
        constructor. now rewrite set_set in HR2.
      + intros. easy.
        Unshelve. exact tt.
  Qed.

  Lemma ccref_left_unit2:
    st_ccref (ST.cc_compose &1 cc) cc.
  Proof.
    unfold st_ccref. apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0))
      (fun se1 se2 '(_, (_, w0)) w1 '(_, w2) _ => lu_ms se1 se2 w0 w1 w2)
      (fun w1 '(_, w2) => lu_inv w1 w2); try easy.
    - intros wa [? wb] I [? wb1] [? Hb]. inv I.
      constructor. etransitivity; eauto.
    - intros wa [? wb] se1 se2 Hse0 Hsk I. destruct wb as (? & wb). constructor; cbn in *.
      + intros q1 q2 s1 [? wb1] [_ Hb] Hq H. inv H. exists tt, (st_q q2).
        split. constructor. destruct H. subst.
        destruct Hq as (x & HQ1 & HQ2). subst.
        eexists wb1, (tt, wb1). repeat split; try easy.
        inv I. etransitivity; eauto.
        constructor; eauto.
      + intros wa1 [? wb1] [] s1 s2 r1 Hs H. inv H. inv Hs.
        exists r2. split. constructor.
        eexists (tt, wb1). repeat split; try easy.
        eexists; split; eauto.
      + intros wa1 [? wb1] [] s1 s2 q1 Hs H. inv H. inv Hs.
        exists q2. split. constructor.
        exists wb1, (set wb wb1). repeat split; try easy. now rewrite get_set.
        intros r1 r2 s1' wa2 Ha Hr HX. inv HX.
        exists tt, (st_r r2). repeat split.
        exists wa2, (tt, wa2).
        repeat split; eauto. reflexivity.
        constructor. now rewrite set_set in Hr.
      + intros. easy.
  Qed.

  Lemma ccref_right_unit1:
    st_ccref cc (ST.cc_compose cc &1).
  Proof.
  Proof.
    unfold st_ccref. apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0))
      (fun se1 se2 w0 '(w1, _) w2 _ => lu_ms se1 se2 w0 w1 w2)
      (fun '(w1, _) w2 => lu_inv w1 w2); try easy.
    - intros [wa _] wb I wb1 Hb. inv I.
      constructor. etransitivity; eauto.
    - intros [wa ?] wb se1 se2 Hse0 Hsk I. constructor.
      + intros q1 q2 s1 wb1 Hb Hq H. inv H. exists tt, (st_q q2).
        split. constructor.
        exists (wb1, tt), wb1. repeat split; try easy.
        inv I. etransitivity; eauto.
        constructor; eauto.
      + intros [wa1 ?] wb1 [] s1 s2 r1 Hs H. inv H. inv Hs.
        exists r2. split. constructor.
        exists wb1. repeat split; easy.
      + intros [wa1 ?] wb1 [] s1 s2 q1 Hs H. inv H. inv Hs.
        exists q2. split. constructor.
        eexists (wb1, tt), (_, (set wb wb1, _)). repeat split; try easy.
        cbn. now rewrite get_set.
        eexists. split; eauto. reflexivity.
        intros r1 r2 s1' [wa2 ?] [Ha ?] Hr HX.
        destruct Hr as (x & HR1 & HR2).
        inv HR2. inv HX.
        exists tt, (st_r r2). repeat split.
        exists (wa2, tt), wa2.
        repeat split; eauto. reflexivity.
        constructor. now rewrite set_set in HR1.
      + intros. easy.
        Unshelve. exact  tt.
  Qed.

  Lemma ccref_right_unit2:
    st_ccref (ST.cc_compose cc &1) cc.
  Proof.
    unfold st_ccref. apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0))
      (fun se1 se2 '(_, (w0, _)) w1 '(w2, _) _ => lu_ms se1 se2 w0 w1 w2)
      (fun w1 '(w2, _) => lu_inv w1 w2); try easy.
    - intros wa [wb ?] I [wb1 ?] [Hb ?]. inv I.
      constructor. etransitivity; eauto.
    - intros wa (se & wb & ?) se1 se2 Hse0 Hsk I. constructor; cbn in  *.
      + intros q1 q2 s1 [wb1 ?] [Hb _] Hq H. inv H. exists tt, (st_q q2).
        split. constructor.
        destruct Hq as (x & HQ1 & HQ2). destruct H. subst.
        eexists wb1, (wb1, tt). repeat split; try easy.
        inv I. etransitivity; eauto.
        constructor; eauto.
      + intros wa1 [wb1 ?] [] s1 s2 r1 Hs H. inv H. inv Hs.
        exists r2. split. constructor.
        eexists (wb1, tt). repeat split; try easy.
        eexists; split; eauto.
      + intros wa1 [wb1 ?] [] s1 s2 q1 Hs H. inv H. inv Hs.
        exists q2. split. constructor.
        exists wb1, (set wb wb1). repeat split; try easy.
        now  rewrite get_set.
        intros r1 r2 s1' wa2 Ha Hr HX. inv HX.
        exists tt, (st_r r2). repeat split.
        exists wa2, (wa2, tt).
        repeat split; eauto. reflexivity.
        constructor. now rewrite set_set in  Hr.
      + intros. easy.
  Qed.

End CC_UNIT.


(** ------------------------------------------------------------------------- *)
(** ** Monotonicity of Sim. Conv. *)

(** The property can be represented as:

         A♯ ———L♯ ——>>B♯
         |            |
 ccA' ⊒ ccA          ccB ⊑ ccB'
         |            |
         A♭ ———L♭ ——>> B♭

 *)

Require Import LogicalRelations.

Instance st_fsim_preo {li1 li2}:
  PreOrder (ST.forward_simulation &(@cc_id li1) &(@cc_id li2)).
Proof.
  split.
  - intros L. apply fsim_embed. reflexivity.
  - intros L1 L2 L3 H12 H23.
    exploit @st_fsim_vcomp. apply H12. apply H23.
    intros H. apply cc_right_unit. apply H.
Qed.

Instance st_fsim_proper `(ccA: ST.callconv liA1 liA2) `(ccB: ST.callconv liB1 liB2):
  Proper ((ST.forward_simulation &1 &1) --> (ST.forward_simulation &1 &1) ++> impl)
         (ST.forward_simulation ccA ccB).
Proof.
  intros X Y HXY A B HAB HL.
  exploit @st_fsim_vcomp. exact HXY. exact HL. intros HL'.
  exploit @st_fsim_vcomp. exact HL'. exact HAB. intros HL''.
  apply (cc_left_unit (cc_right_unit HL'')).
Qed.

Global Instance ccref_preo li1 li2:
  PreOrder (@st_ccref li1 li2).
Proof.
  split.
  - intros cc. eapply st_ccref_refl.
  - intros cc1 cc2 cc3 H12 H23.
    unfold st_ccref in *.
    exploit @st_fsim_lcomp_sk. apply H12. apply H23.
    1-2: apply Linking.linkorder_refl. cbn. intros X.
    match type of X with
    | ST.forward_simulation _ _ ?x ?y =>
        set (LX := x); set (LY := y)
    end.
    assert (Y: forward_simulation 1 1 (normalize_sem 1) LX).
    {
      subst LX.
      etransitivity. 2: apply assoc1.
      etransitivity. apply CAT.right_unit_1.
      etransitivity. apply CAT.right_unit_1.
      etransitivity. apply CAT.right_unit_1.
      eapply categorical_compose_simulation'. reflexivity.
      etransitivity. 2: apply assoc2.
      etransitivity. 2: apply assoc2.
      eapply categorical_compose_simulation'. 2: reflexivity.
      eapply categorical_compose_simulation'. 2: reflexivity.
      eapply categorical_compose_simulation'. 1-2: reflexivity.
      all: apply Linking.linkorder_refl.
    }
    assert (Z: forward_simulation 1 1 LY (normalize_sem 1)).
    {
      subst LY.
      etransitivity. 2: apply CAT.right_unit_2.
      etransitivity. 2: apply CAT.right_unit_2.
      etransitivity. 2: apply CAT.right_unit_2.
      etransitivity. apply assoc2.
      eapply categorical_compose_simulation'. reflexivity.
      etransitivity. apply assoc1.
      etransitivity. apply assoc1.
      eapply categorical_compose_simulation'. 2: reflexivity.
      eapply categorical_compose_simulation'. 2: reflexivity.
      eapply categorical_compose_simulation'. 1-2: reflexivity.
      all: apply Linking.linkorder_refl.
    }
    unfold STCAT.forward_simulation.
    rewrite -> (fsim_embed Y). rewrite <- (fsim_embed Z). apply X.
Qed.

Global Instance st_fsim_ccref:
  Monotonic
    (@STCAT.forward_simulation)
    (forallr - @ liA1, forallr - @ liA2, st_ccref ++>
     forallr - @ liB1, forallr - @ liB2, st_ccref -->
     subrel).
Proof.
  intros liA1 liA2 ccA1 ccA2 HA
         liB1 liB2 ccB1 ccB2 HB L1 L2 H.
  assert (Hsk: skel L1 = skel L2).
  { destruct H. apply X. }
  unfold flip, st_ccref in *.
  exploit @st_cat_fsim_lcomp_sk. exact H. exact HA.
  apply Linking.linkorder_refl. apply CategoricalComp.id_skel_order.
  intros HC.
  exploit @st_cat_fsim_lcomp_sk. exact HB. exact HC.
  apply CategoricalComp.id_skel_order. apply Linking.linkorder_refl.
  cbn. intros X. rewrite Hsk in X at 3 4. clear -X.
  assert (Y: STCAT.forward_simulation &1 &1 L1 (1 o L1 o 1)).
  {
    exploit @st_fsim_vcomp.
    apply st_fsim_right_unit1. apply st_fsim_left_unit1.
    apply cc_left_unit.
  }
  assert (Z: STCAT.forward_simulation &1 &1 (1 o L2 o 1) L2).
  {
    exploit @st_fsim_vcomp.
    apply st_fsim_left_unit2. apply st_fsim_right_unit2.
    apply cc_left_unit.
  }
  exploit @st_fsim_vcomp. exact Y. exact X. clear Y X. intros W.
  exploit @st_fsim_vcomp. exact W. exact Z. clear W Z. intros X.
  apply (cc_left_unit (cc_right_unit X)).
Qed.

(** ------------------------------------------------------------------------- *)
(** * Encapsulation Properties *)

(** ** Composition of Components with Encapsulated States *)

Section LI_FUNC.

  Program Definition callconv_map
          `(F: LiIso liA1 liX1) `(G: LiIso liB1 liY1) cc : callconv liX1 liY1 :=
    {|
      ccworld := ccworld cc;
      match_query w q1 q2 := match_query cc w (fq F q1) (fq G q2);
      match_reply w r1 r2 :=
        exists r1' r2', r1 = fr F r1' /\ r2 = fr G r2' /\ match_reply cc w r1' r2';
      match_senv := match_senv cc;
    |}.
  Next Obligation. eauto using match_senv_public_preserved. Qed.
  Next Obligation. eauto using match_senv_valid_for. Qed.
  Next Obligation.
    erewrite (entry_same _ q1). erewrite (entry_same _ q2).
    eauto using match_senv_symbol_address.
  Qed.
  Next Obligation.
    erewrite (entry_same _ q1). erewrite (entry_same _ q2).
    eauto using match_query_defined.
  Qed.

  Program Definition st_callconv_map
          `(F: LiIso liA1 liX1) `(G: LiIso liB1 liY1) cc : ST.callconv liX1 liY1 :=
    {|
      ST.ccworld := ST.ccworld cc;
      ST.match_query w q1 q2 := ST.match_query cc w (fq F q1) (fq G q2);
      ST.match_reply w r1 r2 :=
        exists r1' r2', r1 = fr F r1' /\ r2 = fr G r2' /\
                     ST.match_reply cc w r1' r2';
      ST.match_senv := ST.match_senv cc
    |}.
  Next Obligation. eauto with scc. Qed.
  Next Obligation. eauto with scc. Qed.
  Next Obligation.
    erewrite (entry_same _ q1). erewrite (entry_same _ q2). eauto with scc.
  Qed.
  Next Obligation.
    erewrite (entry_same _ q1). erewrite (entry_same _ q2). eauto with scc.
  Qed.

  Context `(F1: LiIso liA1 liX1) `(G1: LiIso liB1 liY1)
          `(F2: LiIso liA2 liX2) `(G2: LiIso liB2 liY2).

  (** Generalized version of map_monotonicity in Tensorcomp.v *)
  Section NO_STATE.
    Context (cc1: callconv liA1 liB1) (cc2: callconv liA2 liB2).
    Lemma map_monotonicity_cc L1 L2:
      forward_simulation cc1 cc2 L1 L2 ->
      forward_simulation (callconv_map F1 G1 cc1) (callconv_map F2 G2 cc2)
                         (semantics_map L1 F1 F2) (semantics_map L2 G1 G2).
    Proof.
      intros [[]]. constructor. econstructor; eauto.
      instantiate (1 := fsim_match_states).
      intros. exploit fsim_lts; eauto.
      intros HL. constructor.
      - intros. cbn in *.
        exploit @fsim_match_initial_states; eauto.
      - intros. cbn in *. eprod_crush. subst.
        exploit @fsim_match_final_states; eauto.
        intros X. eprod_crush.
        eexists. repeat split; eauto.
      - intros. cbn in *.
        exploit @fsim_match_external; eauto.
        intros. eprod_crush.
        edestruct (@fq_surj _ _ G1 x0). subst.
        eexists x, _. repeat split; eauto.
        intros. eprod_crush. subst.
        eapply fr_inj in H8. subst.
        exploit @H6; eauto. intros. eprod_crush.
        eexists _, _. repeat split; eauto.
      - intros. exploit @fsim_simulation; eauto.
    Qed.
  End NO_STATE.

  Section STATE.
    Context (cc1: ST.callconv liA1 liB1) (cc2: ST.callconv liA2 liB2).
    Lemma st_map_monotonicity_cc L1 L2:
      ST.forward_simulation cc1 cc2 L1 L2 ->
      ST.forward_simulation (st_callconv_map F1 G1 cc1) (st_callconv_map F2 G2 cc2)
                            (semantics_map L1 F1 F2) (semantics_map L2 G1 G2).
    Proof.
      intros [[]]. constructor. econstructor; eauto.
      instantiate (1 := fsim_match_states).
      intros. exploit fsim_lts; eauto. clear.
      intros HL. constructor.
      - intros. cbn in *.
        exploit @ST.fsim_match_initial_states; eauto.
      - intros. cbn in *. eprod_crush. subst.
        exploit @ST.fsim_match_final_states; eauto.
        intros X. eprod_crush.
        eexists. repeat split; eauto.
        eexists. repeat split; eauto.
      - intros. cbn in *.
        exploit @ST.fsim_match_external; eauto.
        intros. eprod_crush.
        edestruct (@fq_surj _ _ G1 x). subst.
        eexists. repeat split; eauto.
        eexists _, _. repeat split; eauto.
        intros. eprod_crush. subst.
        eapply fr_inj in H8. subst.
        exploit @H6; eauto. intros. eprod_crush.
        eexists _, _. repeat split; eauto.
      - intros. exploit @ST.fsim_simulation; eauto.
    Qed.
  End STATE.

End LI_FUNC.

Require Import FunctionalExtensionality.
Require Import PropExtensionality.

Lemma st_cc_map_id `(cc: ST.callconv liA liB):
  st_callconv_map li_iso_id li_iso_id cc = cc.
Proof.
  destruct cc. unfold st_callconv_map. cbn.
  f_equal.
  extensionality x. extensionality y. extensionality z.
  apply propositional_extensionality.
  2-5: apply Axioms.proof_irr.
  split.
  - intros. eprod_crush. subst. apply H1.
  - intros. eexists _, _. repeat split; eauto.
Qed.

Lemma cc_map_id `(cc: callconv liA liB):
  callconv_map li_iso_id li_iso_id cc = cc.
Proof.
  destruct cc. unfold callconv_map. cbn.
  f_equal; try apply Axioms.proof_irr.
  extensionality x. extensionality y. extensionality z.
  apply propositional_extensionality.
  split.
  - intros. eprod_crush. subst. apply H1.
  - intros. eexists _, _. repeat split; eauto.
Qed.

Section LIFT_TWICE.
  Context `{PSet S1} `{PSet S2} `{PSet T1} `{PSet T2} `(cc: ST.callconv liA liB).

  Inductive lift_twice_ms:
    Genv.symtbl -> Genv.symtbl ->
    ST.ccworld (ST.callconv_lift cc (S1 * S2) (T1 * T2)) ->
    ST.ccstate (st_callconv_map lf lf (ST.callconv_lift (ST.callconv_lift cc S1 T1) S2 T2)) ->
    ST.ccstate (ST.callconv_lift cc (S1 * S2) (T1 * T2)) ->
    @state (liA @ (S1 * S2)) _ 1 ->
    @state (liB @ (T1 * T2)) _ 1 -> Prop :=
  | lift_twice_ms_q se1 se2 w s s1 s2 t1 t2 q1 q2 s10 s20 t10 t20:
    ST.match_senv cc (set w s) se1 se2 ->
    ST.match_query cc (set w s) q1 q2 ->
    lift_twice_ms se1 se2
      (w, ((s10, s20), (t10, t20)))
      (s, (s1, t1), (s2, t2))
      (s, ((s1, s2), (t1, t2)))
      (@st_q (liA @ (S1 * S2)) (q1, (s1, s2)))
      (@st_q (liB @ (T1 * T2)) (q2, (t1, t2)))
  | lift_twice_ms_r se1 se2 w s s1 s2 t1 t2 r1 r2 s10 s20 t10 t20:
    ST.match_reply cc (set w s) r1 r2 ->
    lift_twice_ms se1 se2
      (w, ((s10, s20), (t10, t20)))
      (s, (s1, t1), (s2, t2))
      (s, ((s1, s2), (t1, t2)))
      (@st_r (liA @ (S1 * S2)) (r1, (s1, s2)))
      (@st_r (liB @ (T1 * T2)) (r2, (t1, t2))).

  Inductive lift_twice_inv:
    ST.ccstate (st_callconv_map lf lf (ST.callconv_lift (ST.callconv_lift cc S1 T1) S2 T2)) ->
    ST.ccstate (ST.callconv_lift cc (S1 * S2) (T1 * T2)) -> Prop :=
  | lift_twice_inv_intro sa sb s1 s2 t1 t2:
    sa :-> sb ->
    lift_twice_inv (sa, (s1, t1), (s2, t2)) (sb, ((s1, s2), (t1, t2))).

  Hint Constructors lift_twice_ms lift_twice_inv.

  Lemma cc_lift_twice :
    st_ccref (ST.callconv_lift cc (S1 * S2) (T1 * T2))
      (st_callconv_map lf lf (ST.callconv_lift (ST.callconv_lift cc S1 T1) S2 T2)).
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0))
      (fun se1 se2 w0 wa wb _ => lift_twice_ms se1 se2 w0 wa wb)
      (fun sa sb => lift_twice_inv sa sb); try easy.
    - intros. inv H3. cbn in *. eprod_crush.
      constructor. etransitivity; eauto.
    - intros * Hse0 Hsk HI. constructor; intros; cbn in *; eprod_crush.
      + inv HI. inv H5. eexists tt, _. split. econstructor.
        eexists (_, (_, _), (_, _)), (_, ((_, _), (_, _))).
        split. 2: split. 3: constructor; eauto.
        repeat split; cbn. etransitivity; eauto.
        repeat split; cbn. reflexivity.
      + inv H4. inv H3.
        eexists (_, (_, _)). split. constructor.
        eexists (_, (_, _, (_, _))). repeat split; cbn; eauto; reflexivity.
      + inv H4. inv H3.
        eexists (_, (_, _)). split. constructor.
        eexists (_, (_, _), (_, _)), (_, (_, _), (_, _)).
        repeat split; cbn; eauto. reflexivity. now rewrite get_set.
        inv H5. eexists _. split. constructor.
        cbn in *. eprod_crush. subst.
        eexists (_, (_, _), (_, _)), (_, (_, _, (_, _))).
        repeat split; cbn; eauto. reflexivity.
        constructor. now rewrite set_set in H4.
      + intros. easy.
  Qed.

End LIFT_TWICE.

(** ------------------------------------------------------------------------- *)

Section COMP.
  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          `(ccC: ST.callconv liC1 liC2)
          (L1s: liB1 +-> liC1) (L2s: liA1 +-> liB1)
          (L1t: liB2 +-> liC2) (L2t: liA2 +-> liB2).
  Context (HL1: E.forward_simulation ccB ccC L1s L1t)
          (HL2: E.forward_simulation ccA ccB L2s L2t)
          sk (Hsk1: Linking.linkorder (skel L1s) sk)
          (Hsk2: Linking.linkorder (skel L2s) sk).

  Theorem encap_fsim_lcomp_sk:
    E.forward_simulation ccA ccC (comp_esem' L1s L2s sk) (comp_esem' L1t L2t sk).
  Proof.
    unfold E.forward_simulation in *. unfold comp_esem in *.
    eapply st_fsim_lift with (K1:=pstate L2s) (K2:=pstate L2t) in HL1.
    exploit @st_fsim_lcomp_sk. exact HL1. exact HL2. 1-2: eauto.
    intros X. cbn. rewrite cc_lift_twice.
    unfold STCAT.forward_simulation.
    rewrite (fsim_embed (map_normalize1 _ _ _)).
    rewrite <- (fsim_embed (map_normalize2 _ _ _)).
    rewrite <- (st_cc_map_id ccA).
    eapply st_map_monotonicity_cc.
    rewrite (fsim_embed (normalize_comp_fsim_sk1 _ _ sk)).
    rewrite <- (fsim_embed (normalize_comp_fsim_sk2 _ _ sk)).
    assert (H1: ST.forward_simulation
                &1 &1 (comp_semantics' (normalize_sem (L1s @ pstate L2s)) (normalize_sem L2s) sk)
                      (comp_semantics' (normalize_sem L1s @ pstate L2s) (normalize_sem L2s) sk)).
    {
      eapply st_fsim_lcomp_sk.
      instantiate (1 := &1).
      apply fsim_embed. apply fsim_lift_normalize1.
      all: easy.
    }
    rewrite H1. clear H1.
    assert (H2: ST.forward_simulation
                &1 &1 (comp_semantics' (normalize_sem L1t @ pstate L2t) (normalize_sem L2t) sk)
                      (comp_semantics' (normalize_sem (L1t @ pstate L2t)) (normalize_sem L2t) sk)).
    {
      assert (skel L2t = skel L2s). destruct HL2. destruct X0. easy.
      assert (skel L1t = skel L1s). destruct HL1. destruct X0. easy.
      eapply st_fsim_lcomp_sk.
      instantiate (1 := &1).
      apply fsim_embed. apply fsim_lift_normalize2.
      reflexivity.
      cbn. rewrite H0. easy.
      cbn. rewrite H. easy.
    }
    rewrite <- H2. apply X.
  Qed.

End COMP.

(** ------------------------------------------------------------------------- *)

(*
(** A simplified condition for ccB ⊑ ccA, where the wB is a substructure of
    wA. Additional invariant is required on wA to constrain the redundant
    information *)
Section CCREF.

  Context {li1 li2} (ccA ccB: ST.callconv li1 li2).

  Variable F: ST.ccworld ccA -> ST.ccworld ccB.
  Variable I: ST.ccworld ccA -> Prop.
  Hypothesis F_init: F (@pset_init (ST.ccworld ccA) _) = @pset_init (ST.ccworld ccB) _.
  Hypothesis I_init: I (@pset_init (ST.ccworld ccA) _).
  Hypothesis I_ext_step: forall wa wa1, I wa -> wa :-> wa1 -> I wa1.
  Hypothesis F_int_step: forall wa1 wa2, wa1 *-> wa2 -> F wa1 *-> F wa2.
  Hypothesis F_ext_step:
    forall wa wb1, F wa :-> wb1 -> exists wa1, wa :-> wa1 /\ F wa1 = wb1.
  Hypothesis F_mq:
    forall wa q1 q2, I wa -> ST.match_query ccB (F wa) q1 q2 -> ST.match_query ccA wa q1 q2.
  Hypothesis F_mr:
    forall wa r1 r2, ST.match_reply ccA wa r1 r2 -> ST.match_reply ccB (F wa) r1 r2 /\ I wa.

  Inductive sub_inv: ST.ccworld ccA -> ST.ccworld ccB -> Prop :=
  | sub_inv_intro wa wb: I wa -> F wa :-> wb -> sub_inv wa wb.
  Inductive sub_ms: ST.ccworld ccA -> ST.ccworld ccB -> @state li1 li1 1 -> @state li2 li2 1 -> Prop :=
  | sub_ms_q q1 q2 wa wb:
    I wa -> F wa = wb -> ST.match_query ccB wb q1 q2 ->
    sub_ms wa wb (st_q q1) (st_q q2)
  | sub_ms_r r1 r2 wa wb:
    I wa -> F wa = wb -> ST.match_reply ccB wb r1 r2 ->
    sub_ms wa wb (st_r r1) (st_r r2).

  Lemma st_ccref_sub: st_ccref ccB ccA.
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => sub_ms wa wb)
      (fun wa wb => sub_inv wa wb); try easy.
    - intros. inv H. constructor; eauto. etransitivity; eauto.
    - constructor; eauto. rewrite F_init. reflexivity.
    - intros wa wb se HI. inv HI.
      constructor.
      + intros q1 q2 s1 wb1 Hb Hq Hx. exists tt. inv Hx. exists (st_q q2).
        split. constructor.
        edestruct F_ext_step as (wa1 & Ha1 & Ha2).
        etransitivity; eauto. subst.
        exists wa1, (F wa1). repeat split; try easy.
        constructor; eauto.
      + intros wa1 wb1 [] s1 s2 r1 Hs Hx. inv Hx.
        inv Hs. exists r2. split. constructor.
        exists (F wa1). repeat split; easy.
      + intros wa1 wb1 [] s1 s2 q1 Hs Hx. inv Hx. inv Hs.
        exists q2. split. constructor.
        exists wa1. split. reflexivity. split. apply F_mq; auto.
        intros r1 r2 s1' wa2 Ha2 Hr Hy.
        inv Hy. eexists tt, _. split. constructor.
        eexists wa2, (F wa2). repeat split; eauto. easy.
        constructor; eapply F_mr in Hr; easy.
      + intros. easy.
  Qed.

End CCREF.
*)

Lemma lift_comp_ccref `{PSet S1} `{PSet S2} `{PSet S3}
      `(cc1: ST.callconv liA liB) `(cc2: ST.callconv liB liC):
  st_ccref (ST.callconv_lift (ST.cc_compose cc1 cc2) S1 S3)
           (ST.cc_compose (ST.callconv_lift cc1 S1 S2) (ST.callconv_lift cc2 S2 S3)).
Proof.
(*   match goal with *)
(*   | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y) *)
(*   end. *)
(*   cbn in *. *)
(*   set (F := fun '((w1, s1, _, (w2, _, s3)):w2) => (w1, w2, s1, s3)). *)
(*   set (I := fun '((_, _, s2, (_, s2', _)):w2) => s2 = s2'). *)
(*   eapply st_ccref_sub with F I; intros; cbn in *; eprod_crush; subst; try easy. *)
(*   - cbn in *. eprod_crush. subst. eexists (_, _, _, (_, _, _)). cbn. *)
(*     repeat split; eauto. *)
(*   - cbn in *. eprod_crush. subst. *)
(*     eexists (_, _). repeat split; eauto. *)
(*   - cbn in *. eprod_crush. subst. *)
(*     repeat split; eauto. *)
(* Qed. *)
Admitted.

Section ENCAP_COMP_FSIM.

  Context `(ccA1: ST.callconv liAs liAn) `(ccA2: ST.callconv liAn liAf)
          `(ccB1: ST.callconv liBs liBn) `(ccB2: ST.callconv liBn liBf)
          (Ls: liAs +-> liBs) (Ln: liAn +-> liBn) (Lf: liAf +-> liBf).
  Context (H1: E.forward_simulation ccA1 ccB1 Ls Ln)
          (H2: E.forward_simulation ccA2 ccB2 Ln Lf).

  Theorem encap_fsim_vcomp:
    E.forward_simulation (ST.cc_compose ccA1 ccA2)
                         (ST.cc_compose ccB1 ccB2) Ls Lf.
  Proof.
    unfold E.forward_simulation in *.
    exploit @st_fsim_vcomp. exact H1. exact H2. clear.
    intros X.
    rewrite @lift_comp_ccref. apply X.
  Qed.
End ENCAP_COMP_FSIM.

(** ------------------------------------------------------------------------- *)

Lemma cc_lift_unit `(cc: ST.callconv liA liB):
  st_ccref (ST.callconv_lift cc unit unit)
           (st_callconv_map (li_iso_inv _) (li_iso_inv _) cc).
Proof.
Admitted.
(*   match goal with *)
(*   | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y) *)
(*   end. *)
(*   cbn in *. *)
(*   set (F := fun '((w, _, _):w1) => w). *)
(*   set (G := fun (w:w2) => (w, tt, tt)). *)
(*   eapply st_ccref_intro with G F; *)
(*     intros; cbn in *; eprod_crush; cbn; try easy. *)
(* Qed. *)

Lemma fsim_normalize `(ccA: callconv liA1 liA2) `(ccB: callconv liB1 liB2) L1 L2:
  forward_simulation ccA ccB L1 L2 ->
  CAT.forward_simulation ccA ccB L1 L2.
Proof.
  intros HL. assert (Hsk: skel L1 = skel L2).
  destruct HL. apply (fsim_skel X).
  unfold CAT.forward_simulation, normalize_sem, left_comp_id, right_comp_id.
  rewrite Hsk.
  eapply categorical_compose_simulation'.
  apply ccref_to_fsim. reflexivity.
  eapply categorical_compose_simulation'.
  apply HL. apply ccref_to_fsim. reflexivity.
  rewrite Hsk.  all: cbn; (apply Linking.linkorder_refl || apply CategoricalComp.id_skel_order).
Qed.

Lemma encap_fsim_embed_cat `(ccA: callconv liA1 liA2) `(ccB: callconv liB1 liB2) L1 L2:
  CAT.forward_simulation ccA ccB L1 L2 ->
  E.forward_simulation &ccA &ccB
                       (semantics_embed L1) (semantics_embed L2).
Proof.
  intros. unfold E.forward_simulation, semantics_embed. cbn.
  rewrite cc_lift_unit. rewrite <- (st_cc_map_id &ccA).
  unfold STCAT.forward_simulation.
  rewrite (fsim_embed (map_normalize1 _ (li_iso_inv li_iso_unit) _)).
  rewrite <- (fsim_embed (map_normalize2 _ (li_iso_inv li_iso_unit) _)).
  apply st_map_monotonicity_cc.
  apply fsim_embed. apply H.
Qed.

Lemma encap_fsim_embed `(ccA: callconv liA1 liA2) `(ccB: callconv liB1 liB2) L1 L2:
  forward_simulation ccA ccB L1 L2 ->
  E.forward_simulation &ccA &ccB
                       (semantics_embed L1) (semantics_embed L2).
Proof.
  intros H. apply encap_fsim_embed_cat.
  apply fsim_normalize. assumption.
Qed.

Lemma ccref_lift `{PSet K1} `{PSet K2} {li1 li2} (ccA ccB: ST.callconv li1 li2):
  st_ccref ccA ccB -> st_ccref (ST.callconv_lift ccA K1 K2) (ST.callconv_lift ccB K1 K2).
Proof.
  unfold st_ccref. intros A. unfold STCAT.forward_simulation.
  assert (X: forward_simulation 1 1 (@normalize_sem (li1@K1) _ 1) (normalize_sem 1 @ K1)).
  {
    etransitivity. 2: apply lift_categorical_comp2.
    eapply categorical_compose_simulation'. apply lift_unit1.
    etransitivity. 2: apply lift_categorical_comp2.
    eapply categorical_compose_simulation'. 1-2: apply lift_unit1.
    all: apply Linking.linkorder_refl.
  }
  assert (Y: forward_simulation 1 1 (@normalize_sem li2 _ 1 @ K2) (normalize_sem 1)).
  {
    etransitivity. apply lift_categorical_comp1.
    eapply categorical_compose_simulation'. apply lift_unit2.
    etransitivity. apply lift_categorical_comp1.
    eapply categorical_compose_simulation'. 1-2: apply lift_unit2.
    all: apply Linking.linkorder_refl.
  }
  rewrite (fsim_embed X). rewrite <- (fsim_embed Y).
  apply st_fsim_lift. apply A.
Qed.

Global Instance encap_fsim_ccref:
  Monotonic
    (@E.forward_simulation)
    (forallr - @ liA1, forallr - @ liA2, st_ccref ++>
     forallr - @ liB1, forallr - @ liB2, st_ccref -->
     subrel).
Proof.
  intros liA1 liA2 ccA1 ccA2 HA
         liB1 liB2 ccB1 ccB2 HB L1 L2 H.
  unfold E.forward_simulation in H |- *.
  rewrite <- HA.
  rewrite (ccref_lift HB).
  apply H.
Qed.

(** ------------------------------------------------------------------------- *)
(** Miscellaneous *)

Section COMP_EMBED.

  Context `(L1: semantics liB liC) `(L2: semantics liA liB)
    (sk: AST.program unit unit).

  Inductive comp_embed_ms:
    comp_state (semantics_map L1 lf (li_iso_inv li_iso_unit) @ unit) (semantics_map L2 lf (li_iso_inv li_iso_unit)) -> comp_state L1 L2 -> Prop :=
  | comp_embed_s1 s1:
    comp_embed_ms
      (st1 (semantics_map L1 lf (li_iso_inv li_iso_unit) @ unit) _ (s1, tt))
      (st1 L1 _ s1)
  | comp_embed_s2 s1 s2:
    comp_embed_ms
      (st2 (semantics_map L1 lf (li_iso_inv li_iso_unit) @ unit) _ (s1, tt) s2)
      (st2 L1 _ s1 s2).

  Lemma encap_comp_embed1:
    E.forward_simulation
      (& 1) (& 1)
      (comp_esem' (semantics_embed L1) (semantics_embed L2) sk)
      (semantics_embed (comp_semantics' L1 L2 sk)).
  Proof.
    apply st_normalize_fsim. constructor. cbn.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0))
      (fun _ _ _ _ _ _ => comp_embed_ms)
      (fun _ _ => True);
      try easy.
    intros. cbn in *. eprod_crush. constructor.
    - intros. cbn in *. eprod_crush.
      inv H3. cbn in *. eprod_crush.
      eexists tt, _. split. constructor; eauto.
      exists tt, (tt, (tt, tt, tt)). repeat split.
      constructor.
    - intros. cbn in *. eprod_crush.
      inv H3. inv H2. cbn in *. eprod_crush. inv H.
      eexists (_, tt). split. eexists. split; constructor; eauto.
      exists (tt, (tt, tt, tt)). repeat split.
    - intros. cbn in *. eprod_crush.
      inv H2. inv H. unfold id in *. cbn in *.
      eexists. split. constructor; eauto.
      exists tt, tt. repeat split. eprod_crush.
      inv H5. cbn in *. eprod_crush. unfold id in *. subst.
      eexists. split. eexists. split; eauto. constructor; eauto.
      exists tt, (tt, (tt, tt, tt)). repeat split; eauto.
      constructor.
    - intros. cbn in *. eprod_crush. inv H; inv H2;
        cbn in *; eprod_crush; eexists tt, _;
        ( split; [ left; apply plus_one
        |  exists tt, (tt, (tt, tt, tt)); repeat split; eauto; constructor ] ).
      + apply step1; eauto.
      + apply step2; eauto.
      + eapply step_push; eauto.
      + eapply step_pop; eauto.
  Qed.

  Lemma encap_comp_embed2:
    E.forward_simulation
      (& 1) (& 1)
      (semantics_embed (comp_semantics' L1 L2 sk))
      (comp_esem' (semantics_embed L1) (semantics_embed L2) sk).
  Proof.
    apply st_normalize_fsim. constructor. cbn.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0))
      (fun _ _ _ _ _ _ => flip comp_embed_ms)
      (fun _ _ => True);
      try easy.
    intros. cbn in *. eprod_crush. constructor.
    - intros. cbn in *. eprod_crush. inv H3.
      eexists tt, _. split; eauto. econstructor.
      instantiate (1 := (_, _)). econstructor; cbn; eauto.
      exists tt, (tt, (tt, (tt, tt))).
      repeat split; eauto. constructor.
    - intros. cbn in *. eprod_crush. inv H3. inv H.
      eexists (_, (tt, tt)). split.
      eexists (_, tt, tt). repeat split; eauto.
      cbn. eexists. repeat split; eauto.
      exists (tt, (tt, (tt, tt))). repeat split; eauto.
    - intros. cbn in *. eprod_crush. inv H2. inv H.
      eexists. split. constructor. unfold id. eauto.
      eexists tt. repeat split; eauto.
      eprod_crush. inv H5.
      eexists. split.
      eexists. repeat split; eauto. econstructor.
      split; eauto. reflexivity.
      exists tt, (tt, (tt, (tt, tt))). repeat split; eauto.
      constructor.
    - intros. cbn in *. eprod_crush. inv H; inv H2;
        cbn in *; eprod_crush; eexists tt, _;
        ( split; [ left; apply plus_one
        |  exists tt, (tt, (tt, (tt, tt))); repeat split; eauto; constructor ] ).
      + apply step1; eauto. split; eauto.
      + apply step2; eauto.
      + eapply step_push; eauto.
        instantiate (1 := (_, _)).
        split; eauto. reflexivity. eauto.
      + eapply step_pop; eauto.
        instantiate (1 := (_, _)).
        eexists. split; eauto. reflexivity.
        split; eauto. cbn.
        eexists. split; eauto. reflexivity.
  Qed.

End COMP_EMBED.

(** ------------------------------------------------------------------------- *)
(** Associativity *)

Section ASSOC.

  Context {liA liB liC liD} (L1: liC +-> liD)
    (L2: liB +-> liC) (L3: liA +-> liB).
  Context (sk1 sk2 sk: AST.program unit unit).

  Let L12 := comp_esem' L1 L2 sk1.
  Let L23 := comp_esem' L2 L3 sk2.
  Let L := comp_esem' L12 L3 sk.
  Let L' := comp_esem' L1 L23 sk.

  Inductive assoc_ms: (pstate L1 * pstate L2 * pstate L3) ->
                      Smallstep.state L' -> Smallstep.state L -> Prop :=
  | assoc_ms1 s1 k1 k2 k3:
    assoc_ms
      (k1, k2, k3)
      (st1 (L1 @ (pstate L2 * pstate L3)) _ (s1, (k2, k3)))
      (st1 (L12 @ pstate L3) _ (st1 (L1 @ pstate L2) _ (s1, k2), k3))
  | assoc_ms2 s1 s2 k1 k2 k3 k3':
    assoc_ms
      (k1, k2, k3)
      (st2 (L1 @ (pstate L2 * pstate L3)) L23 (s1, (k2, k3')) (st1 (L2 @ pstate L3) _ (s2, k3)))
      (st1 (L12 @ pstate L3) _ (st2 (L1 @ pstate L2) _ (s1, k2) s2, k3))
  | assoc_ms3 s1 s2 s3 k1 k2 k3 k3':
    assoc_ms
      (k1, k2, k3)
      (st2 (L1 @ (pstate L2 * pstate L3)) L23 (s1, (k2, k3')) (st2 (L2 @ pstate L3) _ (s2, k3) s3))
      (st2 (L12 @ pstate L3) _ (st2 (L1 @ pstate L2) _ (s1, k2) s2, k3) s3).

  Inductive assoc_rel {A B C: Type}: A * (B * C) -> A * B * C -> Prop :=
  | assoc_rel_intro a b c: assoc_rel (a, (b, c)) (a, b, c).

  Hint Constructors assoc_rel assoc_ms.

  Lemma encap_assoc1: E.forward_simulation (&1) (&1) L' L.
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0%nat))
      (fun _ _ _ _ '(_, (_, k2)) _ s1 s2 => assoc_ms k2 s1 s2)
      (fun _ '(_, (k1, k2)) =>  assoc_rel k1 k2); try easy.
    - intros. cbn in *. eprod_crush. inv H. eauto.
    - intros. cbn. now rewrite  Logic.or_assoc.
    - intros. cbn in *. eprod_crush. inv H1.
      constructor; intros; cbn in *; eprod_crush.
      +  inv H2. inv H1. cbn in *; eprod_crush.
         eexists tt, _. split. repeat constructor.
         instantiate (1 := (_, _)). all: cbn; eauto.
         repeat constructor.
         instantiate (1 := (_, _)). all: cbn; eauto.
         eexists tt, (tt, ((_, (_, _)), (_, _, _))).
         repeat split; eauto.
      + inv H2. inv H1. inv H. cbn in *. inv H3.
        eexists (_, (_, _, _)). split.
        * eexists (_, (_, _), _). split. reflexivity.
          repeat econstructor.
          instantiate (4 := (_, _)).
          all: cbn; eauto. reflexivity.
        * eexists (tt, ((_, (_, _)), (_, _, _))).
          repeat split; eauto.
      + inv H1. inv H2. inv H.
        eexists. split. repeat constructor. unfold id in *. eauto.
        exists tt, tt. repeat split; eauto.
        intros. destruct H3 as (? & ? & ?). unfold id in *.
        inv H4. inv H9. destruct H2. inv H3.
        eexists tt, _. split.
        * eexists. split; eauto.
          repeat constructor. cbn. unfold id. eauto.
        * eexists tt, (tt, ((_, (_, _)), (_, _, _))).
          repeat split; eauto.
      + inv H; cbn in *; eprod_crush.
        * inv H1. eexists tt, _. split.
          -- left. apply plus_one. apply step1.
             instantiate (1 := (_, _)). cbn. split; eauto.
             constructor.
             instantiate (1 := (_, _)). cbn. split; eauto.
          -- eexists tt, (tt, ((_, (_, _)), (_, _, _))).
             repeat split; eauto.
        * inv H2; inv H1; cbn in *; eprod_crush; subst.
          -- eexists tt, _. split.
             ++ left. apply plus_one. apply step1.
                instantiate (1 := (_, _)). cbn. split; eauto.
                apply step2. eauto.
             ++ eexists tt, (tt, ((_, (_, _)), (_, _, _))).
                repeat split; eauto.
          -- eexists tt, _. split.
             ++ left. apply plus_one. apply step2. eauto.
             ++ eexists tt, (tt, ((_, (_, _)), (_, _, _))).
                repeat split; eauto.
          -- eexists tt, _. split.
             ++ left. apply plus_one. eapply step_push; eauto.
                repeat constructor; eauto.
             ++ eexists tt, (tt, ((_, (_, _)), (_, _, _))).
                repeat split; eauto.
          -- eexists tt, _. split.
             ++ left. apply plus_one. eapply step_pop; eauto.
                instantiate (1 := (_, _)). cbn. split; eauto.
                eexists; split; eauto.
                unfold id. reflexivity.
                repeat constructor; eauto. reflexivity.
             ++ eexists tt, (tt, ((_, (_, _)), (_, _, _))).
                repeat split; eauto.
        * inv H3. inv H2. cbn in *. eprod_crush. inv H1.
          eexists tt, _. split.
          -- left. apply plus_one. eapply step1.
             instantiate (1 := (_, _)). cbn. split; eauto.
             eapply step_push; eauto.
             constructor; eauto.
          -- eexists tt, (tt, ((_, (_, _)), (_, _, _))).
             repeat split; eauto.
        * inv H3. inv H2. cbn in *. eprod_crush. inv H1.
          eexists tt, _. split.
          -- left. apply plus_one. eapply step1.
             instantiate (1 := (_, _)). cbn. split; eauto.
             eapply step_pop; eauto.
             instantiate (1 := (_, _)). cbn. split; cbn; eauto.
          -- eexists tt, (tt, ((_, (_, _)), (_, _, _))).
             repeat split; eauto.
             Unshelve. all: eauto.
  Qed.

  Lemma encap_assoc2: E.forward_simulation (&1) (&1) L L'.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0%nat))
      (fun _ _ _ _ '(_, (k2, _)) _ s1 s2 => assoc_ms k2 s2 s1)
      (fun _ '(_, (k1, k2)) =>  assoc_rel k2 k1); try easy.
    - intros. cbn in *. eprod_crush. inv H. eauto.
    - intros. cbn. now rewrite  Logic.or_assoc.
    - intros. cbn in *. eprod_crush. inv H1.
      Ltac arel2 := eexists tt, (tt, ((_, _, _), (_, (_, _))));
                    repeat split; eauto.
      Ltac earel2 := eexists tt, _; split; [ | arel2 ].
      constructor; intros; cbn in *; eprod_crush.
      +  inv H2. inv H1. cbn in *; eprod_crush.
         inv H2. inv H1. cbn in *; eprod_crush.
         earel2. repeat constructor. eauto.
      + inv H2. inv H1. cbn in *. eprod_crush.
        inv H2. inv H1. cbn in *. eprod_crush. inv H.
        eexists (_, (_, (_, _))). split.
        * eexists (_, _, (_, _)). split. reflexivity.
          repeat econstructor.
          all: cbn; eauto.
        * eexists (tt, ((_, _, _), (_, (_, _)))).
          repeat split; eauto.
      + inv H1. inv H. unfold id in *.
        eexists. split. repeat constructor. cbn. unfold id. eauto.
        exists tt, tt. repeat split; eauto.
        intros. destruct H3 as (? & ? & ?). inv H4.
        eexists tt, _. split.
        * eexists. split; eauto.
          repeat constructor.
          eexists; split; cbn; eauto. reflexivity. constructor; eauto.
        * arel2.
      + inv H; cbn in *; eprod_crush.
        * inv H; inv H1; cbn in *; eprod_crush; subst.
          -- earel2. left. apply plus_one. apply step1.
             constructor; eauto.
          -- eexists tt, _. split.
             ++ left. apply plus_one. apply step2. econstructor.
                instantiate (1 := (_, _)). constructor; eauto.
             ++ arel2.
          -- eexists tt, _. split.
             ++ left. apply plus_one. eapply step_push; constructor.
                instantiate (1 := (_, _)). all: cbn; eauto.
                repeat split.
                instantiate (1 := (_, _)). all: cbn; eauto.
             ++ arel2.
          -- earel2. left. apply plus_one. eapply step_pop; econstructor.
             instantiate (1 := (_, _)). all: repeat constructor; eauto.
        * inv H1. eexists tt, _. split.
          -- left. apply plus_one. apply step2.
             apply step2. eauto.
          -- arel2.
        * inv H. inv H1. eexists tt, _. split.
          -- left. apply plus_one. apply step2. eapply step_push; eauto.
             constructor; eauto.
          -- arel2.
        * unfold id in *. subst. inv H3. inv H1. eexists tt, _. split.
          -- left. apply plus_one. apply step2. eapply step_pop; eauto.
             instantiate (1 := (_, _)). constructor; eauto. reflexivity.
          -- arel2.
             Unshelve. all: eauto.
  Qed.

End ASSOC.

Section REFL.

  Lemma encap_refl {li1 li2} L:
    E.forward_simulation &(@cc_id li1) &(@cc_id li2) L L.
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0%nat))
      (fun _ _ _ _ _ _ s1 s2 => s1 = s2)
      (fun _ '(_, (k1, k2)) =>  k1 = k2); try easy.
    - intros. cbn in *. eprod_crush. reflexivity.
    - intros; cbn in *; eprod_crush.
      constructor; intros; cbn in *; eprod_crush; subst.
      + eexists tt, _. repeat split; eauto.
        eexists (tt, (_, _)). repeat split; eauto.
      + eexists (_, _). repeat split; eauto.
        eexists (tt, (_, _)). repeat split; eauto.
      + eexists. split; eauto.
        eexists tt, tt. repeat split; eauto. subst.
        eexists _. repeat split; eauto.
        eexists (tt, (_, _)). repeat split; eauto.
      + eexists tt, _. split. left. apply plus_one; eauto.
        eexists tt, (tt, (_, _)). repeat split; eauto.
        Unshelve. all: eauto.
  Qed.

End REFL.

Instance encap_preo {li1 li2}:
  PreOrder (E.forward_simulation &(@cc_id li1) &(@cc_id li2)).
Proof.
  split.
  - intros L. apply encap_refl.
  - intros L1 L2 L3 HA HB.
    setoid_rewrite ccref_left_unit1 at 2.
    rewrite <- ccref_left_unit2 at 1.
    eapply encap_fsim_vcomp; eauto.
Qed.

(** ------------------------------------------------------------------------- *)
(** Property about encapsulation primitive *)

Definition encap_prim {li} `{PSet U} : li@U +-> li :=
  {|
    pstate := U;
    esem := 1%lts;
  |}.

Arguments encap_prim {li} U {_}.

Require Import Lia.

Section COMP_PRIM.

  Context {li} `{PSet U} (L: semantics li li) (sk: AST.program unit unit).

  Let L1 := comp_esem' (encap_prim U) (semantics_embed (L @ U)) sk.
  Let L2 := comp_esem' (semantics_embed L) (encap_prim U) sk.

  Definition q1 (q: query li) (u: U): Smallstep.state (normalize_sem L1).
    refine (st1 _ _ _).
    refine (st_q _).
    refine (q, (u, tt)).
  Defined.

  Definition q2 (q: query li) (u: U): Smallstep.state (normalize_sem L2).
    refine (st1 _ _ _).
    refine (st_q _).
    refine (q, (tt, u)).
  Defined.

  Definition r1 (r: reply li) (u: U): Smallstep.state (normalize_sem L1).
    refine (st1 _ _ _).
    refine (st_r _).
    refine (r, (u, tt)).
  Defined.

  Definition r2 (r: reply li) (u: U): Smallstep.state (normalize_sem L2).
    refine (st1 _ _ _).
    refine (st_r _).
    refine (r, (tt, u)).
  Defined.

  Definition qq1 (q: query li) (u: U): Smallstep.state (normalize_sem L1).
    refine (st2 _ _ _ _).
    - refine (st_q _). refine (q, (u, tt)).
    - refine (st1 _ _ _). refine (st1 _ _ _).
      refine (st_q _, tt). refine (q, u).
  Defined.

  Definition qqs1  (q: query li) (u u': U) (s: Smallstep.state L):
    Smallstep.state (normalize_sem L1).
    refine (st2 _ _ _ _).
    - refine (st_q _). refine (q, (u, tt)).
    - refine (st1 _ _ _). refine (st2 _ _ _ _).
      + refine (st_q _, tt). refine (q, u).
      + refine (s, u').
  Defined.

  Definition qs2 (q: query li) (u u': U) (s: Smallstep.state L):
    Smallstep.state (normalize_sem L2).
    refine (st2 _ _ _ _).
    - refine (st_q _). refine (q, (tt, u)).
    - refine (st1 _ _ _). refine (st1 _ _ _).
      refine (s, u').
  Defined.

  Definition qqsq1  (q q': query li) (u u': U) (s: Smallstep.state L)
    : Smallstep.state (normalize_sem L1).
    refine (st2 _ _ _ _).
    - refine (st_q _). refine (q, (u, tt)).
    - refine (st2 _ _ _ _).
      + refine (st2 _ _ _ _).
        * refine (st_q _, tt). refine (q, u).
        * refine (s, u').
      + refine (st_q _). refine (q', u').
  Defined.

  Definition qsqq2 (q q': query li) (u u': U) (s: Smallstep.state L)
    : Smallstep.state (normalize_sem L2).
    refine (st2 _ _ _ _).
    - refine (st_q _). refine (q, (tt, u)).
    - refine (st2 _ _ _ _).
      + refine (st2 _ _ _ _).
        * refine (s, u').
        * refine (st_q _). refine (q', u').
      + refine (st_q _). refine (q', u').
  Defined.

  Definition qqsr1  (q: query li) (u u' u'': U) (s: Smallstep.state L)
    (r: reply li): Smallstep.state (normalize_sem L1).
    refine (st2 _ _ _ _).
    - refine (st_q _). refine (q, (u, tt)).
    - refine (st2 _ _ _ _).
      + refine (st2 _ _ _ _).
        * refine (st_q _, tt). refine (q, u).
        * refine (s, u').
      + refine (st_r _). refine (r, u'').
  Defined.

  Definition qsqr2 (q q': query li) (u u' u'': U) (s: Smallstep.state L)
    (r: reply li): Smallstep.state (normalize_sem L2).
    refine (st2 _ _ _ _).
    - refine (st_q _). refine (q, (tt, u)).
    - refine (st2 _ _ _ _).
      + refine (st2 _ _ _ _).
        * refine (s, u').
        * refine (st_q _). refine (q', u').
      + refine (st_r _). refine (r, u'').
  Defined.

  Definition qr1 (q: query li) (u u': U) (r: reply li)
    : Smallstep.state (normalize_sem L1).
    refine (st2 _ _ _ _).
    - refine (st_q _). refine (q, (u, tt)).
    - refine (st1 _ _ _). refine (st1 _ _ _).
      refine (st_r _, tt). refine (r, u').
  Defined.

  Inductive prim_ms:
    Smallstep.state (normalize_sem L1) ->
    Smallstep.state (normalize_sem L2) -> Prop :=
  | prim_ms1 q u: prim_ms (q1 q u) (q2 q u)
  | prim_ms1' q u: prim_ms (qq1 q u) (q2 q u)
  | prim_ms2 q u u' s: prim_ms (qqs1 q u u' s) (qs2 q u u' s)
  | prim_ms3 q u u' s q': prim_ms (qqsq1 q q' u u' s)
                            (qsqq2 q q' u u' s)
  | prim_ms4 q u s q' r u' u'': prim_ms (qqsr1 q u u' u'' s r)
                                  (qsqr2 q q' u u' u'' s r)
  | prim_ms5' q r u u': prim_ms (qr1 q u u' r) (r2 r u')
  | prim_ms5 r u: prim_ms (r1 r u) (r2 r u).

  Definition prim_measure (s: Smallstep.state (normalize_sem L1)) :=
    match s with
    | st1 (st_q _) => 1%nat
    | st2 (st_q _) (st1 (st1 (st_q _, _))) => 0%nat
    | st2 (st_q _) (st1 (st1 (st_r _, _))) => 1%nat
    | st1 (st_r _) => 0%nat
    | _ => 0%nat
    end.

  Lemma encap_comp_prim :
    E.forward_simulation (&1) (&1) L1 L2.
  Proof.
    unfold E.forward_simulation, STCAT.forward_simulation. constructor.
    eapply ST.Forward_simulation with
      (ltof _ prim_measure)
      (fun _ _ _ _ _ i s1 s2 => i = s1 /\ prim_ms s1 s2)
      (fun _ '(_, ((u1, _), (_, u2))) =>  u1 = u2).
    - intros. cbn in *. now eprod_crush.
    - easy.
    - easy.
    - intros. cbn. firstorder.
    - intros. cbn in *. eprod_crush. constructor;
        intros; cbn in *; eprod_crush.
      + inv H3. inv H2.
        eexists _, _. split. repeat constructor.
        eexists tt, (tt, (_, tt, (tt, _))).
        repeat split. constructor.
      + inv H2. inv H4. inv H3.
        eexists (_, (tt, _)). split. repeat constructor.
        eexists (tt, (_, tt, (tt, _))). repeat split; eauto.
      + inv H2. inv H4. inv H0. inv H3.
        eexists (_, _). split. repeat constructor.
        eexists tt, tt. repeat split; eauto.
        intros. inv H3. inv H8. inv H6. eprod_crush.
        eexists _, _. split. repeat constructor.
        eexists tt, (tt, (_, tt, (tt, _))).
        repeat constructor.
      + Ltac prim_rel rel :=
          eexists _, _; split; [ |
            eexists tt, (tt, (_, tt, (tt, _))); split;
            [ constructor | split ];
                            [ repeat split | split ];
                                             [ reflexivity | apply rel ] ].
        inv H3.
        (* prim_ms1 -> prim_ms2 *)
        * inv H0. inv H3. inv H3. inv H4. inv H0.
          cbn in *. eprod_crush. inv H0.
          prim_rel prim_ms1'.
          right. split. apply star_refl. unfold ltof. cbn. lia.
        (* prim_ms1' -> prim_ms2 *)
        * inv H0.
          2: { inv H4.  inv H2. destruct H0. inv H2.
               cbn in *. eprod_crush. inv H0. }
          inv H6. 2: inv H2. inv H2.
          { cbn in *. eprod_crush. inv H0. }
          cbn in *. eprod_crush. inv H2. cbn in *.
          prim_rel prim_ms2.
          left. apply plus_one. eapply step_push; repeat constructor.
          cbn. eauto.
        (* prim_ms2 -> prim_ms2/prim_ms3/prim_ms5' *)
        * inv H0.
          2: { inv H4. inv H2. cbn in *. eprod_crush. inv H2. }
          inv H6.
          {
            inv H2.
            - cbn in *. eprod_crush. subst.
              (* prim_ms2 *)
              prim_rel prim_ms2.
              left. apply plus_one.
              apply step2. apply step1. apply step1.
              split; eauto.
            - inv H4. cbn in *. eprod_crush. inv H2.
              (* prim_ms5' *)
              prim_rel  prim_ms5'.
              left. apply plus_one. eapply step_pop; repeat constructor.
              econstructor. instantiate (1 := (_, _)).
              split; repeat constructor; cbn.
              instantiate (1 := (_, _)). cbn. reflexivity.
              eexists. split; eauto.
          }
          {
            inv H3. inv H2. cbn in *. eprod_crush.
            unfold id in *. cbn in *.
            (* prim_ms3 *)
            prim_rel prim_ms3.
            left. eapply plus_two.
            - eapply step2. eapply step1. eapply step_push.
              instantiate (1 := (_, _)). cbn.
              split; cbn; eauto. constructor.
            - eapply step2. eapply step_push.
              instantiate (1 := (_, _)). cbn.
              constructor. unfold id. all: constructor.
            - reflexivity.
          }
        * (* prim_ms3 -> at_external *)
          inv H0. inv H6. inv H5. inv H3.
          cbn in *. eprod_crush. inv H4.
        * inv H0. inv H6. inv H5. 2: inv H4.
          (* prim_ms4 -> prim_ms5' *)
          inv H3. inv H7. cbn in *. eprod_crush.
          unfold id in *. inv H2. inv H0. inv H7.
          cbn in *. eprod_crush. unfold id in *. inv H0.
          prim_rel prim_ms2.
          left. eapply plus_two.
          -- eapply step2. eapply step_pop; econstructor.
             split; cbn; eauto. instantiate (1 := (_, _)). reflexivity.
             constructor. constructor.
          -- eapply step2. eapply step1.
             eapply step_pop; constructor; cbn; eauto.
             eexists; split; eauto. reflexivity.
          -- reflexivity.
        * inv H0. inv H6. inv H2. all: cbn in *; eprod_crush.
          (* prim_ms5' -> prim_ms5 *)
          { cbn in *. eprod_crush. inv H0. }
          { inv H2. } { inv H2. }
          inv H7. inv H4. inv H2. cbn in *. eprod_crush.
          inv H2. inv H3. cbn in *. inv H0.
          prim_rel prim_ms5.
          right. split. apply star_refl.
          unfold ltof. cbn. lia.
        * (* prim_ms5 -> final_state *)
          inv H0. inv H3. inv H3.
    - apply well_founded_ltof.
      Unshelve. all: eauto.
  Qed.

End COMP_PRIM.

(** ------------------------------------------------------------------------- *)
(** Obsolete FBK and REVEAL construction *)

Definition semantics_fbk `{PSet K} {liA liB} (L: liA +-> liB@K) : liA +-> liB :=
  {|
    pstate := K * pstate L; esem := $L
  |}.

(** ** Simulation Convention FBK *)
Program Definition callconv_fbk `{PSet K1} `{PSet K2}
        `(cc: ST.callconv (li1@K1) (li2@K2)): ST.callconv li1 li2 :=
  {|
    ST.ccworld := ST.ccworld cc * (K1 * K2);
    ST.ccworld_world := world_prod _ (world_prod _ _);
    ST.match_query '(w, (k1, k2)) q1 q2 := ST.match_query cc w (q1, k1) (q2, k2);
    ST.match_reply '(w, (k1, k2)) r1 r2 := ST.match_reply cc w (r1, k1) (r2, k2);
    ST.match_senv '(w, (k1, k2)) se1 se2 := ST.match_senv cc w se1 se2;
  |}.
Next Obligation. eauto with scc. Qed.
Next Obligation. eauto with scc. Qed.
Next Obligation.
  replace (entry q3) with (@entry (li1 @ K1) (q3, k)) by reflexivity.
  replace (entry q4) with (@entry (li2 @ K2) (q4, k0)) by reflexivity.
  eauto with scc.
Qed.
Next Obligation.
  replace (entry q3) with (@entry (li1 @ K1) (q3, k)) by reflexivity.
  replace (entry q4) with (@entry (li2 @ K2) (q4, k0)) by reflexivity.
  eauto with scc.
Qed.

(** ** FBK vs LIFT *)

(** A simplified condition for ccB ⊑ ccA, where wA is a substructure of wB *)
(* Section CCREF. *)

(*   Context {li1 li2} (ccA ccB: ST.callconv li1 li2). *)

(*   Variable F: ST.ccworld ccB -> ST.ccworld ccA. *)
(*   Variable I: ST.ccworld ccB -> Prop. *)
(*   Hypothesis F_init: F (@pset_init (ST.ccworld ccB) _) = @pset_init (ST.ccworld ccA) _. *)
(*   Hypothesis F_ext_step: forall x y, x :-> y -> F x :-> F y. *)
(*   Hypothesis F_int_step: *)
(*     forall wb1 wa2, F wb1 *-> wa2 -> exists wb2, wa2 = F wb2 /\ wb1 *-> wb2 /\ (I wb1 -> I wb2). *)
(*   Hypothesis F_mq: *)
(*     forall wb q1 q2, ST.match_query ccB wb q1 q2 -> ST.match_query ccA (F wb) q1 q2 /\ I wb. *)
(*   Hypothesis F_mr: *)
(*     forall wb r1 r2, I wb -> ST.match_reply ccA (F wb) r1 r2 -> ST.match_reply ccB wb r1 r2. *)

(*   Inductive super_inv: ST.ccworld ccA -> ST.ccworld ccB -> Prop := *)
(*   | super_inv_intro wa wb: wa :-> F wb -> super_inv wa wb. *)
(*   Inductive super_ms: ST.ccworld ccA -> ST.ccworld ccB -> @state li1 li1 1 -> @state li2 li2 1 -> Prop := *)
(*   | super_ms_q q1 q2 wa wb: *)
(*     I wb -> wa = F wb -> ST.match_query ccB wb q1 q2 -> *)
(*     super_ms wa wb (st_q q1) (st_q q2) *)
(*   | super_ms_r r1 r2 wa wb: *)
(*     I wb -> wa = F wb -> ST.match_reply ccB wb r1 r2 -> *)
(*     super_ms wa wb (st_r r1) (st_r r2). *)

(*   Lemma st_ccref_super: st_ccref ccB ccA. *)
(*   Proof. *)
(*     apply st_normalize_fsim. constructor. *)
(*     eapply ST.Forward_simulation with *)
(*       (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => super_ms wa wb) *)
(*       (fun wa wb => super_inv wa wb); try easy. *)
(*     - intros. inv H. constructor. etransitivity; eauto. *)
(*     - constructor. rewrite F_init. reflexivity. *)
(*     - intros wa wb se Hi. inv Hi. *)
(*       constructor. *)
(*       + intros q1 q2 s1 wb1 Hb Hq Hx. exists tt. inv Hx. exists (st_q q2). *)
(*         split. constructor. *)
(*         exists (F wb1), wb1. repeat split; try easy. *)
(*         * etransitivity; eauto. *)
(*         * constructor; eauto. apply F_mq in Hq. apply Hq. *)
(*       + intros wa1 wb1 [] s1 s2 r1 Hs Hx. inv Hx. *)
(*         inv Hs. exists r2. split. constructor. *)
(*         exists wb1. repeat split; easy. *)
(*       + intros wa1 wb1 [] s1 s2 q1 Hs Hx. inv Hx. inv Hs. *)
(*         exists q2. split. constructor. *)
(*         exists (F wb1). split. reflexivity. split. apply F_mq; auto. *)
(*         intros r1 r2 s1' wa2 Ha2 Hr Hy. *)
(*         inv Hy. eexists tt, _. split. constructor. *)
(*         destruct (F_int_step _ _ Ha2) as (wb2 & Hb1 & Hb2 & Hb3). *)
(*         eexists wa2, wb2. repeat split; try easy. *)
(*         constructor; eauto. *)
(*         apply F_mr; subst; eauto. *)
(*       + intros. easy. *)
(*   Qed. *)

(* End CCREF. *)

Lemma cc_fbk_lift1 `{PSet K1} `{PSet K2} `(cc: ST.callconv li1 li2):
  st_ccref (callconv_fbk (ST.callconv_lift cc K1 K2)) cc.
Proof.
(*   match goal with *)
(*   | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y) *)
(*   end. *)
(*   cbn in *. *)
(*   set (F := fun '((w, _, _, _, _):w1) => w). *)
(*   set (I := fun '((_, k1, k2, k1', k2'):w1) => k1 = k1' /\ k2 = k2'). *)
(*   eapply st_ccref_super with F I; *)
(*     intros; cbn in *; eprod_crush; subst; try easy. *)
(*   eexists (_, _, _, _, _). repeat split. eauto. *)
(*   Unshelve. all: eauto. *)
(* Qed. *)
Admitted.

Lemma cc_fbk_lift2 `{PSet K1} `{PSet K2} `(cc: ST.callconv li1 li2):
  st_ccref cc (callconv_fbk (ST.callconv_lift cc K1 K2)).
Proof.
(*   match goal with *)
(*   | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y) *)
(*   end. *)
(*   cbn in *. *)
(*   set (F := fun '((w, _, _, _, _):w2) => w). *)
(*   set (I := fun '((_, k1, k2, k1', k2'):w2) => k1 = k1' /\ k2 = k2'). *)
(*   eapply st_ccref_sub with F I; *)
(*     intros; cbn in *; eprod_crush; subst; try easy. *)
(*   eexists (_, _, _, _, _). repeat split. easy. *)
(* Qed. *)
Admitted.

(** A simplified condition for ccB ⊑ ccA, where wA is a substructure of wB *)
(* Section CCREF. *)

(*   Context {li1 li2} (ccA ccB: ST.callconv li1 li2). *)

(*   Variable F: ST.ccworld ccB -> ST.ccworld ccA. *)
(*   Variable I: ST.ccworld ccB -> Prop. *)
(*   Hypothesis F_init: @pset_init (ST.ccworld ccA) _ :-> F (@pset_init (ST.ccworld ccB) _). *)
(*   (* F (pset_init (ST.ccworld ccB)) = pset_init (ST.ccworld ccA). *) *)
(*   Hypothesis I_init: I (@pset_init (ST.ccworld ccB) _). *)
(*   Hypothesis I_ext_step: forall wb wb1, I wb -> wb :-> wb1 -> I wb1. *)
(*   Hypothesis F_ext_step: forall x y, x :-> y -> F x :-> F y. *)
(*   Hypothesis F_int_step: *)
(*     forall wb1 wa2, F wb1 *-> wa2 -> *)
(*                forall r1 r2, exists wb2, wa2 = F wb2 /\ wb1 *-> wb2 *)
(*                                /\ (I wb1 -> I wb2) *)
(*                                /\ (ST.match_reply ccA wa2 r1 r2 -> *)
(*                                   ST.match_reply ccB wb2 r1 r2). *)
(*   Hypothesis F_mq: *)
(*     forall wb q1 q2, I wb -> ST.match_query ccB wb q1 q2 -> ST.match_query ccA (F wb) q1 q2. *)

(*   Inductive fbk1_inv: ST.ccworld ccA -> ST.ccworld ccB -> Prop := *)
(*   | fbk1_inv_intro wa wb: I wb -> wa :-> F wb -> fbk1_inv wa wb. *)
(*   Inductive fbk1_ms: ST.ccworld ccA -> ST.ccworld ccB -> @state li1 li1 1 -> @state li2 li2 1 -> Prop := *)
(*   | fbk1_ms_q q1 q2 wa wb: *)
(*     I wb -> wa = F wb -> ST.match_query ccB wb q1 q2 -> *)
(*     fbk1_ms wa wb (st_q q1) (st_q q2) *)
(*   | fbk1_ms_r r1 r2 wa wb: *)
(*     I wb -> wa = F wb -> ST.match_reply ccB wb r1 r2 -> *)
(*     fbk1_ms wa wb (st_r r1) (st_r r2). *)

(*   Lemma st_ccref_fbk1: st_ccref ccB ccA. *)
(*   Proof. *)
(*     apply st_normalize_fsim. constructor. *)
(*     eapply ST.Forward_simulation with *)
(*       (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => fbk1_ms wa wb) *)
(*       (fun wa wb => fbk1_inv wa wb); try easy. *)
(*     - intros. inv H. constructor; eauto. etransitivity; eauto. *)
(*     - intros wa wb se Hi. inv Hi. *)
(*       constructor. *)
(*       + intros q1 q2 s1 wb1 Hb Hq Hx. exists tt. inv Hx. exists (st_q q2). *)
(*         split. constructor. *)
(*         exists (F wb1), wb1. repeat split; try easy. *)
(*         * etransitivity; eauto. *)
(*         * constructor; eauto. *)
(*       + intros wa1 wb1 [] s1 s2 r1 Hs Hx. inv Hx. *)
(*         inv Hs. exists r2. split. constructor. *)
(*         exists wb1. repeat split; easy. *)
(*       + intros wa1 wb1 [] s1 s2 q1 Hs Hx. inv Hx. inv Hs. *)
(*         exists q2. split. constructor. *)
(*         exists (F wb1). split. reflexivity. split. apply F_mq; auto. *)
(*         intros r1 r2 s1' wa2 Ha2 Hr Hy. *)
(*         inv Hy. eexists tt, _. split. constructor. *)
(*         destruct (F_int_step _ _ Ha2 r1 r2) as (wb2 & Hb1 & Hb2 & Hb3 & HR). *)
(*         eexists wa2, wb2. repeat split; try easy. *)
(*         constructor; eauto. *)
(*       + intros. easy. *)
(*   Qed. *)

(* End CCREF. *)

Lemma cc_lift_fbk1 `{PSet K1} `{PSet K2} `(cc: ST.callconv (li1@K1) (li2@K2)):
  st_ccref (ST.callconv_lift (callconv_fbk cc) K1 K2) cc.
Proof.
(*   match goal with *)
(*   | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y) *)
(*   end. *)
(*   cbn in *. *)
(*   set (F := fun '((w, _, _, _, _):w1) => w). *)
(*   set (I := fun '((_, k1, k2, k1', k2'):w1) => k1 = k1' /\ k2 = k2'). *)
(*   eapply st_ccref_fbk1 with F I; *)
(*     intros; cbn in *; eprod_crush; subst; try easy. *)
(*   eexists (_, _, _, _, _). repeat split. eauto. *)
(*   intros; cbn in *. eprod_crush. repeat split; eauto. *)
(*   cbn in *. eprod_crush. subst; eauto. *)
(* Qed. *)
Admitted.

Lemma cc_lift_fbk2 `{PSet K1} `{PSet K2} `(cc: ST.callconv (li1@K1) (li2@K2)):
  st_ccref cc (ST.callconv_lift (callconv_fbk cc) K1 K2).
Proof.
  (* match goal with *)
  (* | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y) *)
  (* end. *)
  (* cbn in *. *)
  (* set (F := fun '((w, _, _, _, _):w2) => w). *)
  (* set (I := fun '((_, k1, k2, k1', k2'):w2) => k1 = k1' /\ k2 = k2'). *)
  (* eapply st_ccref_sub with F I; *)
  (*   intros; cbn in *; eprod_crush; subst; try easy. *)
  (* eexists (_, _, _, _, _). repeat split. easy. *)
  (* cbn in *. admit. *)
  (* cbn in *. *)
Abort.

Lemma encap_fsim_fbk `{PSet K1} `{PSet K2}
      `(ccA: ST.callconv liA1 liA2) `(ccB: ST.callconv (liB1@K1) (liB2@K2)) L1 L2:
  E.forward_simulation ccA ccB L1 L2 ->
  E.forward_simulation ccA (callconv_fbk ccB) (semantics_fbk L1) (semantics_fbk L2).
Proof.
  unfold E.forward_simulation. cbn. intros HL.
  rewrite cc_lift_twice.
  unfold STCAT.forward_simulation.
  rewrite (fsim_embed (map_normalize1 _ _ _)).
  rewrite <- (fsim_embed (map_normalize2 _ _ _)).
  rewrite <- (st_cc_map_id ccA).
  eapply st_map_monotonicity_cc.
  pose proof (@ccref_lift (pstate L1) _ (pstate L2) _  _ _ _ _ (cc_lift_fbk1 ccB)) as Hcc.
  assert (X: STCAT.forward_simulation ccA (ST.callconv_lift (ST.callconv_lift (callconv_fbk ccB) K1 K2) (pstate L1) (pstate L2)) L1 L2).
  {
    rewrite Hcc. apply HL.
  }
  apply X.
Qed.

(* TODO: replace with primitive *)
(** ** REVEAL Simulation Convention *)

Program Definition cc_reveal `{PSet K} {li} : ST.callconv li (li@K) :=
  {|
    ST.ccworld := K;
    ST.match_query k q1 '(q2, kq) := q1 = q2 /\ k = kq;
    ST.match_reply k r1 '(r2, kr) := r1 = r2 /\ k = kr;
    ST.match_senv k se1 se2 := se1 = se2;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

Lemma cc_lift_reveal {li} `{PSet K1} `{PSet K2}:
  st_ccref
    (ST.callconv_lift (cc_reveal (li:=li)) (K2 * K1) K1)
    (st_callconv_map li_iso_assoc li_iso_id &1).
Proof.
(*   match goal with *)
(*   | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y) *)
(*   end. *)
(*   cbn in *. *)
(*   set (F := fun _:w1 => tt). *)
(*   set (I := fun '((k2, (kk2, k1), kk1):w1) => k1 = kk1 /\ k2 = kk2). *)
(*   eapply st_ccref_fbk1 with F I. *)
(*   all: intros; cbn in *; eprod_crush; subst; try easy. *)
(*   - eexists (_, (_, _), _). cbn in *. repeat split. *)
(*     eprod_crush. inv H2. easy. *)
(*     eprod_crush. inv H2. easy. *)
(*   - inv H1. reflexivity. *)
(* Qed. *)
Admitted.

Section REVEAL.

  Lemma sem_map_id `(L: semantics liA liB):
    L = semantics_map L lf lf.
  Proof.
    unfold semantics_map. destruct L. cbn. f_equal.
    extensionality se.
    unfold lts_map. destruct (activate se).
    cbn. f_equal.
    - extensionality x. extensionality y. extensionality z.
      apply propositional_extensionality. split.
      + intros. eexists; split; eauto. reflexivity.
      + intros. eprod_crush. subst. apply H0.
    - extensionality x. extensionality y.
      apply propositional_extensionality. split.
      + intros. eexists; split; eauto. reflexivity.
      + intros. eprod_crush. subst. apply H0.
  Qed.

  Lemma fsim_reveal `{PSet K} {liA liB} (L: liA +-> liB@K):
    E.forward_simulation &1 cc_reveal (semantics_fbk L) L.
  Proof.
    unfold E.forward_simulation. cbn. rewrite cc_lift_reveal.
    unfold STCAT.forward_simulation.
    rewrite (fsim_embed (map_normalize1 _ _ _)).
    rewrite <- (st_cc_map_id &1).
    rewrite (sem_map_id (normalize_sem L)) at 2.
    eapply st_map_monotonicity_cc.
    reflexivity.
  Qed.

End REVEAL.
