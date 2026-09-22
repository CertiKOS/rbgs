Require Import Coq.PArith.PArith.
Require Import PeanoNat.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.AtomicLTS.
Require Import examples.CAS.CASRegSpec.
Require Import examples.TSStack.TimestampSpec.


(** Implementation of the interval timestamp object from Fig. 15 and
    Appendix A.1 of the paper.

    The underlay is a single CAS register holding the shared counter [t].
    The paper's hardware interface [CAS] only has [cas] and [get]; we use
    the existing [ECASReg] signature and simply never call [set].

    [newTS] reads the counter twice.  If the two reads differ, the counter
    moved in between and the interval [[t1, t2 - 1]] is already ordered
    after every previously completed stamp.  Otherwise it tries to
    advance the counter once: on success it owns the point interval
    [[t1, t1]]; on failure some other thread advanced the counter, and a
    third read closes the interval at [[t1, t3 - 1]]. *)
Module TimestampImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import AtomicLTS.
  Import CASRegSpec.
  Import TimestampSpec.
  Import (coercions, canonicals, notations) Sig.

  Open Scope prog_scope.

  Definition ECASLayer : layer_interface :=
    {|
      li_sig := ECASReg nat;
      li_lts := @VCASReg nat;
      li_init := @Idle (ECASReg nat) nat O
    |}.

  Definition E : layer_interface := ECASLayer.

  Definition F : layer_interface := TimestampLayer.L.

  (** Fig. 15.  The paper returns the pair [(t1, t2)]; the specification
      embeds it as [TSInterval t1 t2], see [TimestampSpec.ETimestamp_ar]. *)
  Definition newTS_impl (_actor : tid) : Prog (li_sig E) TS :=
    get >= t1 =>
    get >= t2 =>
    if Nat.eqb t1 t2 then
      cas t1 (S t1) >= b =>
      if b then
        Ret (TSInterval t1 t1)
      else
        get >= t3 =>
        Ret (TSInterval t1 (t3 - 1))
    else
      Ret (TSInterval t1 (t2 - 1)).

  Definition timestamp_impl : ModuleImpl (li_sig E) (li_sig F) :=
    fun op =>
      match op with
      | newTS => newTS_impl
      end.

End TimestampImpl.
