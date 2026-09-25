# Verification Plan: NodeMem over five memories

## Objective

Prove the implementation in `examples/TSStack/NodeMem.v` correct with
respect to `examples/TSStack/NodeMemSpec.v`. The production theorem is

```coq
NodeMemProof.MNodeMem :
  layer_implementation_simulation NodeMemImpl.E NodeMemImpl.F
```

with `MNodeMemLinearizable := LISim2LILin MNodeMem`, in
`examples/TSStack/NodeMemProof.v`.

## Why the underlay changed

The first implementation used `MemSpec.WriteRacyMem` for value, ts and next
and `CASMemSpec` for taken. That implementation is not provable in this
program logic, for a reason that does not depend on the proof style. During
allocation a thread holds a freshly allocated field cell that no record
references yet. In the proof state (concrete state, abstract state,
linearization map) such a cell is indistinguishable from the fresh cell of
any other thread that is allocating at the same time: the two states differ
only by which thread "owns" which address, and nothing in the state records
that. Consequently the guarantee of another thread cannot exclude that its
new record references our cell, and its pending store cannot be excluded
from racing with ours. Rely/guarantee reasoning needs the state to carry the
owner. This is the same problem that `examples/Stacks/TryStack.v` solved by
moving to `OwnedMemSpec`.

`examples/Common/OwnerMemSpec.v` is the memory used now. It comes in two
versions with the same operations: `PlainMem` (a heap, the concrete
underlay) and `OwnerMem` (the same plus a ghost owner map).
`examples/Common/OwnerMemProof.v` shows `OwnerMem` linearizable from
`PlainMem` with the identity implementation (`MOwnerMem`), so
`NodeMemProof.MNodeMemOverPlain` is NodeMem linearizable from five
concrete memories. The ghost layer is provable precisely because
allocation is atomic and initialising: the owner is recorded at the
allocation response, which is the linearization point, so there is no
window in which a fresh cell exists without an owner. Over a memory whose
allocation returns an uninitialised cell, the initialising store would
reopen the ambiguity one level down.

`OwnerMem`: cells are
allocated with their initial value (`omalloc v`), read with `oread`,
stored with the racy `owrite` (exactly the `WriteRacyMem` error) and
updated atomically with `ocas`. The state additionally carries a ghost owner
map recording the allocating thread; it never influences a step or an error.
All five NodeMem memories are instances of it: value, next and the record
are never written, ts is only stored by `setTS`, taken is only updated by
`ocas`. Because allocation initialises the cell, a node becomes visible at
the moment its record cell is allocated, and there is no in-flight state to
describe.

## Proof shape

Singleton-possibility proof in the style of `TimestampProof.v`.

* **Invariant** `I`: the abstract state is `Idle h`; the fields of every
  record are allocated and distinct records never share a ts or a taken cell
  (`IConcrete`); a pending ts store belongs to a thread inside an
  unlinearized `nmsetTS` on the node that owns the cell
  (`PendingTSWrite`); and either the racy error is reachable (`Err`) or the
  record and field memories represent the abstract heap (`Rep`).
* **Thread-local assertions**: `Defined l`, `RecIs l r` (the record read),
  `FreshVal/FreshTS/FreshTaken/FreshNext t a ...` (an allocated cell owned
  by `t`, holding its initial value, referenced by no record), and
  `TSTopSeen t l ts` (the actor's `setTS` read `TSTop`, so the abstract
  timestamp is still `TSTop` unless the error is reachable).
* **Linearization points**:
  * `nmalloc`: the response of the record allocation;
  * `nmget*`: the response of the field read;
  * `nmtryTake`: the response of the taken read when it returns `true`,
    otherwise the response of the CAS;
  * `nmsetTS`: the response of the ts read when it returns an interval (a
    no-op), otherwise the response of the store.
  Every abstract operation is linearized in one go (`ps_inv` then `ps_ret`,
  see `lin_steps`), so the abstract state is always `Idle`.

## The racy `setTS`

The specification makes two overlapping `nmsetTS` on the same node an
error, and the implementation's plain store relies on it. With a single
possibility whose abstract state is always `Idle`, that error is never
*entered*; instead the proof shows it is *reachable*: whenever two threads
are inside unlinearized `nmsetTS` on the same node, `Err` holds and
`Err_APError` produces the possibility steps (invoke one, then the racy
error for the other), which discharges the rest of the method through
`SetLogic.provable_perror`.

For `Err` to be stable, the guarantee contains a protocol: a thread inside
`nmsetTS l _` does not linearize while another thread is inside an
unlinearized `nmsetTS l _` (it takes the `Err` branch instead), and the
abstract timestamp of a node changes only when no other thread is inside an
unlinearized `nmsetTS` on it. The latter makes `TSTopSeen` stable between
the ts read and the store.

Once `Err` holds, `Rep` may fail (a store happens without an abstract
update), so `I` only asserts `Err \/ Rep`. Every method therefore ends each
linearization step in `DoneOrErr` (`Done \/ (I /\ Err)`) and applies
`provable_perror` before returning. The underlay itself never errors: the
store's racy error is excluded at the moment of the store by
`ts_write_race_or_error`, which either proves no other store is pending or
derives `Err`.

## Structure of `NodeMemProof.v`

1. Views of the five-component state (`rec_c`, `val_h`, `ts_o`, ...),
   step-shape lemmas for one `OwnerMem` component and projections of tensor
   steps to a component (`step_val`, `error_ts`, ...).
2. `I`, thread-local assertions, `G`/`R`, stability lemmas, `stableDB`.
3. Rely/guarantee side conditions, `Err_APError`, `defined_or_error`, and
   the underlay no-error lemmas.
4. Building blocks for possibility updates: `lin_steps`, unchanged-heap
   lemmas (`I_same`, `G_same`), `CI` (assertions insensitive to the control
   components and to allocation) with `ciDB`, the generic `inv_update` and
   `rec_read_res_update`, `field_read_lin`, and the "update one field cell"
   lemmas (`Rep_update_ts`, `Rep_update_taken`, `HeapRely_update_*`).
5. One `*_res_update` lemma per linearization point and one `*_triple` per
   method; the layer theorem assembles them.
