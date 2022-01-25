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

(** The language interface "C simple" which does not include the memory *)
Inductive c_esig : esig :=
| c_event : val -> signature -> list val -> c_esig val.

Inductive c_rc_rel: rc_rel (c_esig # mem) li_c :=
| c_rc_rel_intro vf sg args e_c e_s m R:
  e_c = c_event vf sg args -> e_s = state_event m ->
  subrel (fun '(r, m) c_r => c_r = cr r m) R ->
  c_rc_rel _ (esig_tens_intro e_c e_s) _ (li_sig (cq vf sg args m)) R.

Program Definition c_rc : (c_esig # mem) <=> li_c :=
  {|
    refconv_rel := c_rc_rel;
  |}.
Next Obligation.
  intros x y Hxy H. destruct H.
  econstructor; eauto. etransitivity; eauto.
Qed.

(** Some auxiliary definitions *)
Definition overlay_rc {E: esig} {S1 S2: Type} (rc: E <=> c_esig) (rel: S2 -> mem * S1 -> Prop):
  E # S2 <=> c_esig # (mem * S1)%type := rc * rel_rc rel.

Inductive lts_state_rc_rel {S: Type}: rc_rel (c_esig # (mem * S)) (li_c @ S)%li :=
| lts_state_rc_rel_intro vf sg args m s R (qs: query (li_c @ S)) qe:
  qs = (cq vf sg args m, s) ->
  qe = st (c_event vf sg args) (m, s) ->
  subrel (fun '(r, (m, s)) '(r', s') => r' = cr r m /\ s = s') R ->
  lts_state_rc_rel _ qe _ (li_sig qs) R.

Program Definition lts_state_rc {S: Type} : c_esig # (mem * S) <=> (li_c @ S)%li :=
  {|
    refconv_rel := lts_state_rc_rel;
  |}.
Next Obligation.
  intros x y Hxy H. destruct H.
  econstructor; eauto. etransitivity; eauto.
Qed.

Inductive st_mem_rc_rel {S: Type}: rc_rel (s_esig S) (s_esig (mem * S)) :=
| st_mem_rc_rel_intro s m R:
  subrel (fun s' '(m', t') => s' = t' /\ m = m') R ->
  st_mem_rc_rel _ (state_event s) _ (state_event (m, s)) R.

Program Definition st_mem_rc {S: Type}: s_esig S <=> s_esig (mem * S) :=
  {|
    refconv_rel := st_mem_rc_rel;
  |}.
Next Obligation.
  intros x y Hxy H. destruct H.
  constructor. etransitivity; eauto.
Qed.

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
