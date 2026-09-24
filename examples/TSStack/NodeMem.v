Require Import Coq.PArith.PArith.
Require Import PeanoNat.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.AtomicLTS.
Require Import examples.Common.Heap.
Require Import examples.Common.MemSpec.
Require Import examples.Common.CASMemSpec.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.NodeMemSpec.


(** Implementation of [NodeMemSpec] over five memory objects.

    A node handle [l : Addr] is a cell of the record memory [ERecMem]
    holding the addresses of the node's four fields, each of which lives in
    its own memory:

      - value  : [EMem A]        written once, at allocation;
      - ts     : [EMem TS]       [TSTop] at allocation, set once by [setTS];
      - taken  : [ECASMem bool]  [false] at allocation, flipped by [tryTake];
      - next   : [EMem Ptr]      written once, at allocation.

    Reads are per field, so each is a single underlying read.

    [setTS] is a racy operation in the specification (two concurrent
    [nmsetTS] on the same node are an error), so a plain read, compare and
    write suffices.  [tryTake] may race with other [tryTake]s, so the taken
    flag is a CAS cell and the read is followed by a single [ccas]. *)
Module NodeMemImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import AtomicLTS.
  Import MemSpec.
  Import CASMemSpec.
  Import TimestampSpec.
  Import NodeMemSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.

    (** The record cell: addresses of (value, ts, taken, next). *)
    Definition NodeRec : Type := Addr * Addr * Addr * Addr.

    (** [MemSpec.WriteRacyMemLayer.L] is stated for [TPSimulation]; the
        TSStack development uses [TPSimulationSet], so the same layers are
        rebuilt here. *)
    Definition MemLayer (V : Type) : layer_interface :=
    {|
      li_sig := EMem V;
      li_lts := @WriteRacyMem.VMem V;
      li_init := Idle empty_heap;
    |}.

    Definition ERecMem : layer_interface := MemLayer NodeRec.
    Definition EValMem : layer_interface := MemLayer A.
    Definition ETSMem : layer_interface := MemLayer TS.
    Definition ENextMem : layer_interface := MemLayer Ptr.
    Definition ETakenMem : layer_interface := @CASMemLayer.L bool.

    Definition E : layer_interface :=
      ERecMem ⊗ₗ EValMem ⊗ₗ ETSMem ⊗ₗ ENextMem ⊗ₗ ETakenMem.

    Definition F : layer_interface := @NodeMemLayer.L A.

    Definition rec_op := Sig.op (EMem NodeRec).
    Definition val_op := Sig.op (EMem A).
    Definition ts_op := Sig.op (EMem TS).
    Definition next_op := Sig.op (EMem Ptr).
    Definition taken_op := Sig.op (ECASMem bool).

    (** [⊗ₗ] is left associative, so [E] is
        [(((Rec ⊗ Val) ⊗ TS) ⊗ Next) ⊗ Taken]. *)
    Definition in_rec (m : rec_op) : Sig.op (li_sig E) :=
      inl (inl (inl (inl m))).
    Definition in_val (m : val_op) : Sig.op (li_sig E) :=
      inl (inl (inl (inr m))).
    Definition in_ts (m : ts_op) : Sig.op (li_sig E) :=
      inl (inl (inr m)).
    Definition in_next (m : next_op) : Sig.op (li_sig E) :=
      inl (inr m).
    Definition in_taken (m : taken_op) : Sig.op (li_sig E) :=
      inr m.

    (** Allocate and initialise the four fields, then publish them through a
        fresh record cell.  The record address is the node handle. *)
    Definition malloc_impl (v : A) (next : Ptr) (_ : tid) : Prog (li_sig E) Addr :=
      in_val malloc >= lv =>
      in_val (mwrite lv v) >= _ =>
      in_ts malloc >= lts =>
      in_ts (mwrite lts TSTop) >= _ =>
      in_next malloc >= ln =>
      in_next (mwrite ln next) >= _ =>
      in_taken (cmalloc false) >= lt =>
      in_rec malloc >= l =>
      in_rec (mwrite l (lv, lts, lt, ln)) >= _ =>
      Ret l.

    Definition setTS_impl (l : Addr) (ts : TS) (_ : tid) : Prog (li_sig E) unit :=
      in_rec (mread l) >= r =>
      let '(_, lts, _, _) := r in
      (in_ts (mread lts) >= old =>
       match old with
       | TSTop => in_ts (mwrite lts ts) >= _ => Ret tt
       | TSInterval _ _ => Ret tt
       end : Prog (li_sig E) unit).

    Definition getValue_impl (l : Addr) (_ : tid) : Prog (li_sig E) A :=
      in_rec (mread l) >= r =>
      let '(lv, _, _, _) := r in
      (in_val (mread lv) >= v => Ret v : Prog (li_sig E) A).

    Definition getTS_impl (l : Addr) (_ : tid) : Prog (li_sig E) TS :=
      in_rec (mread l) >= r =>
      let '(_, lts, _, _) := r in
      (in_ts (mread lts) >= ts => Ret ts : Prog (li_sig E) TS).

    Definition getTaken_impl (l : Addr) (_ : tid) : Prog (li_sig E) bool :=
      in_rec (mread l) >= r =>
      let '(_, _, lt, _) := r in
      (in_taken (cget lt) >= taken => Ret taken : Prog (li_sig E) bool).

    Definition getNext_impl (l : Addr) (_ : tid) : Prog (li_sig E) Ptr :=
      in_rec (mread l) >= r =>
      let '(_, _, _, ln) := r in
      (in_next (mread ln) >= next => Ret next : Prog (li_sig E) Ptr).

    Definition tryTake_impl (l : Addr) (_ : tid) : Prog (li_sig E) bool :=
      in_rec (mread l) >= r =>
      let '(_, _, lt, _) := r in
      (in_taken (cget lt) >= taken =>
       if taken then Ret false
       else in_taken (ccas lt false true) >= ok => Ret ok
       : Prog (li_sig E) bool).

    Definition nodemem_impl : ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | nmalloc v next => malloc_impl v next
        | nmsetTS l ts => setTS_impl l ts
        | nmgetValue l => getValue_impl l
        | nmgetTS l => getTS_impl l
        | nmgetTaken l => getTaken_impl l
        | nmgetNext l => getNext_impl l
        | nmtryTake l => tryTake_impl l
        end.

  End Impl.
End NodeMemImpl.
