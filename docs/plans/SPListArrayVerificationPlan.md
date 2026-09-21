# Verification Plan: SPListArray over the Verified SPList Family

## Objective

Prove the SPList-array adapter in `SPListArray.v` correct with respect to
the repaired list-order specification in `SPListArraySpec.v`, using only the
production set-based simulation and logic.

The primary theorem should have the shape

```coq
MSPListArray :
  TPSimulationSet.TPSimulation.layer_implementation_simulation
    (@SPListFamilyLayer.L A D)
    (@SPListArrayLayer.L A D).
```

The resulting linearizability theorem should then compose vertically with
`SPListFamilyImpl.compose_splist_family`.

This proof does **not** establish that row list order agrees with timestamp
order. That invariant belongs to the later ListPool overlay, whose program
controls timestamp generation. SPListArray now specifies the behavior of
the row family itself: `getTop` returns the first surviving location in the
saved row order.

## Current status

The following framework and specification prerequisites are complete:

- The production set simulation supports finite abstract-only updates.
- `RGILogicSet.provable_linstep` and
  `SingletonPossibility.singleton_provable_linstep` are available.
- `Lang.ForEach` presents the structurally finite `foldM` program, and
  `RGILogicSet.provable_foreach` is its reusable proof interface.
- Parallel normalization and `CompLin` soundness compile.
- `SPListArrayState` records every row's current live order in `as_orders`.
- `CurrentScan` records `current_order`; `current_nodes` is derived from
  membership in that saved order.
- `actual_scan_order` filters the saved order against the row's current
  live order, matching `SPListSpec.actual_snapshot`.
- Array `getTop` no longer requires timestamp `lp_top` and no longer has an
  unrelated garbage-node response.
- `SPListArraySpec.vo`, `SPListArray.vo`, and `SPListArrayProof.vo` compile.
- `resetIter_adapter` demonstrates the required `provable_linstep` proof
  shape, but its invariant, stability, and update premises are not yet
  instantiated.

The implementation's operational behavior should remain unchanged unless
verification exposes a real semantic mismatch; notation-only refactoring is
allowed.

## Proof architecture

Use the singleton assertion facade for leaf-level state reasoning and the
set logic for all structural and soundness rules, following
`SPListProof.v`:

```coq
Module SetLogic := RGILogicSet.RGILogic.
Definition SI := SingletonPossibility.lift_assert source_I.
```

Here:

- the concrete source state is the indexed family map of `SPListControl`
  rows;
- the abstract state is `SPListArrayControl`;
- stable proof states at method boundaries use `ArrayReady`;
- transient `ArrayAtomicPending` states may occur inside a single
  possibility-update derivation but need not satisfy the global invariant;
- concrete rows may be `AtomicPending`, because different row operations
  can overlap while the array abstract state stays `ArrayReady`.

The four phases below are intended as compilable proof checkpoints.

## Phase 1: Representation relation and state algebra

### 1.1 Row payload and row well-formedness

Define the state saved inside either row control:

```coq
Definition row_payload (r : SPListControl) : SPListState :=
  match r with
  | Ready s => s
  | AtomicPending s _ _ => s
  end.
```

Define row well-formedness sufficient for all later correspondence lemmas:

- `NoDup (order s)`;
- every location in `order s` is defined in `nodes s`;
- a defined location is never reused by `insert`;
- `counter s` is the number of insertions represented by the row state;
- snapshots contain locations from a previously saved row order.

Only include properties actually needed by the method proofs. Avoid
reconstructing the lower-level linked-list invariant already discharged by
`SPListProof`.

### 1.2 Family/array payload correspondence

Define `represents rows a` for an indexed family state `rows` and an array
state `a`. For every `owner` in `D`, if its family row has payload `rs`,
prove the following exact correspondences:

```text
counter rs             = counter_at owner a
order rs               = order_at owner a
nodes rs loc = Some(v,ts)
                        <->
as_values a (owner,loc) = Some v
and as_timestamps a (owner,loc) = Some ts
as_garbage a (owner,loc)
                        <->
nodes rs loc is defined and loc is not in order rs
```

Also require:

- rows for all owners in `D` are present;
- array nodes outside represented rows are absent;
- row orders and array orders contain no duplicates;
- `array_live a (owner,loc)` is equivalent to `In loc (order rs)`.

Derive reusable lookup lemmas in both directions rather than unfolding the
whole relation in operation proofs.

### 1.3 Scan/snapshot correspondence

Relate a row snapshot owned by caller `actor` to the array scan entry for
that caller:

- if `scan_current p = Some c`, the row selected by `current_owner c`
  contains

  ```coq
  TMap.find actor (snapshot rs) =
    Some (current_order c, current_counter c);
  ```

- conversely, every active row snapshot has the corresponding array scan;
- an actor has at most one current row across the family;
- finished rows have cleared the corresponding row snapshot;
- `scan_seen` is the union of the sets derived from the saved orders of
  visited rows.

Prove directly that the new definition preserves scan-status behavior:

```coq
current_nodes c (owner, loc) <->
  owner = current_owner c /\ In loc (current_order c).
```

In particular:

- insertion after the snapshot gives `Ignored`;
- removal after the snapshot does not remove the node from the saved
  `current_nodes` set;
- `finish_progress` records exactly the saved snapshot membership.

### 1.4 Snapshot-order correspondence

Prove the key `getTop` bridge:

```coq
order rs = order_at owner a ->
TMap.find actor (snapshot rs) = Some (saved, count) ->
current_order c = saved ->
current_owner c = owner ->
actual_snapshot actor rs =
  Some (actual_scan_order c a, count).
```

This replaces the former, impossible timestamp-top obligation.

### 1.5 Initial state and transition algebra

Prove representation lemmas for:

- `initial_rows` versus `initial_counters` and `initial_orders`;
- `insert` versus `insert_node`;
- `setTS` versus `set_node_timestamp`;
- `remove` versus `remove_node`;
- `start_snapshot` versus `begin_scan`;
- `clear_snapshot` versus `end_scan`;
- counter preservation and monotonicity.

### Phase 1 acceptance

- All representation lemmas compile without `Admitted`.
- Initial family and array states satisfy `represents`.
- The `actual_snapshot`/`actual_scan_order` theorem is proved.
- No timestamp-order hypothesis appears in any SPListArray representation
  lemma.

## Phase 2: Global invariant, rely, guarantee, and stability

### 2.1 Global singleton invariant

Define `source_I` over singleton proof states. At stable boundaries it
should assert:

```text
concrete family state = rows
abstract state = ArrayReady a
represents rows a
scan/snapshot correspondence
counter-scan consistency
linearization-map consistency
```

Linearization-map consistency should connect interval operations to ghost
state:

- `ls_lini (array_getTop owner)` iff that actor has a current scan for the
  corresponding row;
- `ls_lini array_getCounter` iff `as_pending_counters` contains the actor;
- atomic operations normally remain `ls_inv` until their row response,
  because their abstract invocation and response will be performed
  together.

Lift it to the set assertion:

```coq
Definition SI := lift_assert source_I.
```

### 2.2 Rely/guarantee relations

Define `source_G actor` and `source_R observer` with the following minimum
structure:

- both endpoints satisfy `source_I`;
- an actor preserves every other thread's linearization-map entry;
- an actor preserves every other caller's scan entry and row-snapshot
  entries;
- counters never decrease;
- nodes retain values, timestamps evolve only from `TSTop`, and garbage is
  monotone;
- row-order changes are exactly those permitted by insertion and removal,
  or use a weaker evolution relation sufficient for stability;
- `source_R observer` preserves the observer's token and observer-local
  scan/fold facts.

Then lift the relations to the set framework.

### 2.3 Framework obligations

Prove:

- `ValidRGI (R actor) (G actor) SI actor`;
- cross-thread guarantee/rely compatibility;
- stability of active, completed, scan, atomic-call, and counter-fold
  assertions;
- the usual `Ginv` exposure and `Gret` closure lemmas;
- return-token lemmas for every completed assertion;
- error-precondition lemmas using `APError`.

Use broad evolution relations only when they leave the phase assertions
stable. In particular, the rely for `actor` must not arbitrarily rewrite
that actor's scan progress or counter-fold ghost state.

### Phase 2 acceptance

- `valid_rg` and `parallel_compatible` compile.
- Every assertion needed in Phase 3 has an invariant and stability lemma.
- Administrative invocation/return guarantees are included only through
  the existing set-logic soundness theorem.

## Phase 3: Method triples

Prove methods in increasing order of statefulness.

### 3.1 Insert

For `family_call actor (linsert v)`:

- reject actors outside `D` through `APError`;
- keep the array operation at `ls_inv` during the family invocation;
- at the family response, perform the array insert invocation and response
  in the possibility update;
- use freshness and the insert representation lemma;
- finish with the ordinary `Ret loc` rule.

Delaying the atomic abstract pair until the family response prevents the
single `ArrayAtomicPending` control state from serializing overlapping
operations on different rows.

### 3.2 Set timestamp

For `family_call actor (lsetTS loc ts)`:

- map undefined nodes to the array error case;
- perform the abstract atomic invocation/response at the family response;
- preserve `as_orders` exactly;
- update the timestamp only when its previous value is `TSTop`.

No timestamp/list-order invariant is required at this layer.

### 3.3 Try remove

For `family_call owner (ltryRemove loc)`:

- handle actor and owner domain errors;
- map undefined locations to `APError`;
- success removes `loc` from `as_orders` and adds the node to garbage;
- failure preserves the order and requires the node already be garbage;
- linearize the abstract atomic pair at the family response.

### 3.4 Reset iterator

Replace the assumptions of `resetIter_adapter` with concrete proofs:

- valid actor: `PUpdateId` takes the abstract reset invocation and response,
  changes `as_scans actor` to `empty_scan`, and reaches `ls_linr`;
- invalid actor: reach `APError`;
- the concrete program remains exactly `Ret tt`;
- close with `singleton_provable_linstep` followed by the pure return rule.

### 3.5 Get top

At the family invocation:

- prove the reset/repetition/domain preconditions or reach `APError`;
- align `SPListSpec.step_getTop_inv` with
  `SPListArraySpec.step_getTop_inv`;
- establish equality between the row's saved `(order,counter)` and the
  array `CurrentScan`.

At the family response:

- rewrite `actual_snapshot` using the Phase 1 snapshot-order theorem;
- nonempty case uses `step_getTop_nonempty_res` with the same head location,
  value, and timestamp;
- empty case uses `step_getTop_empty_res` with the saved counter;
- clear the row snapshot and call `end_scan`.

No `lp_top` or timestamp comparison should occur in this proof.

### 3.6 Aggregate counter

Prove

```coq
ForEach ThreadDomain.threads D From 0 Using counter_step
```

by applying `SetLogic.provable_foreach`. Do not unfold `foldM` or manually
apply `provable_seq` in this client proof; the list induction and structural
sequencing belong exclusively to the reusable foreach rule. Instantiate its
suffix-indexed `Inv remaining sum` with an accumulator assertion containing:

- the unvisited suffix of `ThreadDomain.threads D`;
- the visited-owner prefix;
- the current sum;
- the abstract counter value saved at array-counter invocation;
- lower and upper bounds relating the sum to sampled/current row counters.

Linearize the abstract counter invocation before the first row read. The
domain is nonempty by construction. After the fold:

```text
saved total <= accumulated result <= current total.
```

Discharge `provable_foreach`'s exit-triple premise with
`singleton_provable_linstep` followed by `singleton_provable_ret_safe`, thereby
performing the abstract counter response at the final `Ret` and establishing
`ls_linr`. This keeps the final abstract response independent of which row
supplied the last concrete response.

Required arithmetic facts include:

- row counters never decrease;
- `ThreadDomain.threads` has no duplicates;
- the fold visits each domain owner exactly once;
- prefix/suffix decomposition of `sum_counters`.

### Phase 3 acceptance

- All six operation triples compile.
- Reset and the final counter response use `provable_linstep`, not Tau.
- `getTop` is proved solely from saved/current list-order correspondence.
- Invalid operations are covered by `APError` rather than unproved safety
  assumptions.

## Phase 4: Soundness packaging and vertical composition

### 4.1 Method packaging

For every array operation, package its active/completed assertions into
`SetLogic.MethodProvable`, discharging:

- `Pinv`;
- invariant closure;
- stability;
- `Gret` closure;
- return-token agreement;
- the Phase 3 triple.

### 4.2 Layer simulation

Construct `MSPListArray` with `SetLogic.soundness` and prove the initial
singleton/set invariant.

Inspect `Print Assumptions MSPListArray`. It may inherit the same standard
extensionality/classical assumptions already used by the framework, but it
must introduce no `Admitted` theorem or new semantic axiom.

### 4.3 Linearizability and composition

Define:

```coq
MSPListArrayLinearizable := LISim2LILin MSPListArray.
```

Then vertically compose it with:

```coq
SPListFamilyImpl.compose_splist_family D
```

to obtain an end-to-end theorem from the tensor of verified SPList
underlays to the SPListArray layer.

### 4.4 Regression build

Compile at least:

```text
models/simlin/RGILogicSetTests.vo
examples/Common/IndexedFamilyProof.vo
examples/TSStack/SPListProof.vo
examples/TSStack/SPListFamily.vo
examples/TSStack/SPListArraySpec.vo
examples/TSStack/SPListArray.vo
examples/TSStack/SPListArrayProof.vo
```

Then compile the complete `_CoqProject`.

### Phase 4 acceptance

- `MSPListArray` and its `CompLin` theorem compile.
- End-to-end vertical composition with the verified SPList family compiles.
- All existing verified examples remain valid.
- The implementation of `resetIter_impl` is still `Ret tt`.
- Tau remains used only for the existing program/loop semantics.
- Timestamp/list-order consistency is absent from this layer and explicitly
  remains an obligation of the future ListPool overlay proof.

## Expected files

The main proof work should be confined to:

- `examples/TSStack/SPListArrayProof.v`
- `docs/plans/SPListArrayVerificationPlan.md`

The specification repair is in:

- `examples/TSStack/SPListArraySpec.v`

Only add helper lemmas to `SPListSpec.v`, `ThreadDomain.v`, or common map/list
libraries when they are genuinely reusable. The set simulation and logic
should not require further semantic changes.

Current verification status: **specification repair complete; full proof not
started**.
