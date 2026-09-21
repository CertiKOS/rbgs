# Verification Plan: TryStackAux over ListPool

## Objective and deliverables

Prove the implementation in `TryStackAux.v` against
`TryStackAuxSpec.v`, following the TryStackAux layer in `main-tr.pdf`.
The production deliverables are:

```coq
MTryStackAux :
  layer_implementation_simulation
    (@TryStackAuxImpl.E A D)
    (@TryStackAuxImpl.F A D).

MTryStackAuxLinearizable :
  layer_implementation_linearizability
    (@TryStackAuxImpl.E A D)
    (@TryStackAuxImpl.F A D).

MListPoolTryStackAux :
  layer_implementation_linearizability
    (@ListPoolProof.E A D)
    (@TryStackAuxImpl.F A D).
```

The proof is implemented in `TryStackAuxProof.v` and registered in
`_CoqProject`.

## Contract decision

`ListPoolSpec` remains unchanged. In particular, its atomic `getTop`
branch may respond with `YFail` even when every vertex is garbage at both
the invocation and response steps.

`TryStackAuxSpec` therefore permits two overlapping choices when the
graph is empty:

1. `step_tsa_trypop_empty_inv` commits to the atomic empty branch and its
   response is `TSuccEmpty`.
2. `step_tsa_trypop_snapshot_inv` records the empty snapshot and permits
   the later `TFail` response.

There is deliberately no nonempty guard on the snapshot invocation rule.
This is the smallest specification change that simulates all legal
ListPool behaviors while retaining successful empty responses.

This does not force a change to the future TryStack overlay algorithm.
That overlay must already handle `TFail` by retrying; the additional
auxiliary trace is therefore hidden by the retry loop rather than exposed
as a final stack result. Its eventual proof must cover the new empty-state
failure trace, but its public successful-empty behavior need not change.

## Proof architecture

Use `RGILogicSet` through the singleton lifting in
`SingletonPossibility`. A speculative two-possibility fork is unnecessary.
The proof delays the abstract `trypop` response until the concrete result
is known:

- A snapshot-style concrete `getTop` invocation takes the abstract
  snapshot invocation.
- A concrete node response clears only the concrete ListPool snapshot.
  The abstract TryStackAux snapshot and `ls_lini tsa_trypop` token remain
  pending.
- The following concrete `tryRemove` response performs the abstract
  success or failure response.
- An atomic concrete `getTop` does not take an abstract step at invocation.
  At its response, the proof takes both the matching abstract invocation
  and response as a two-step trace.

This alignment removes any need to predict `tryRemove`'s boolean result.

## Simulation state

The single-possibility invariant `source_I` contains an abstract ready
state and four components.

### 1. Graph representation

`graph_represents p s` equates:

- vertex maps;
- edge relations;
- pending-push maps; and
- garbage sets.

Snapshots are excluded because a successful node-return path temporarily
has no concrete snapshot while retaining the abstract snapshot.

### 2. Snapshot/token protocol

`snapshot_protocol p s pi` states:

- every concrete snapshot is represented by the same abstract snapshot;
- an abstract snapshot exists exactly when the actor has
  `ls_lini tsa_trypop`;
- an abstract pending push exists exactly when the actor has a matching
  linearizing push token; and
- every member of an abstract snapshot is an abstract vertex.

The first clause is one-way so the intentional concrete-cleared /
abstract-pending phase is representable.

### 3. Node ownership

`vertices_owned p` states that the owner component of every concrete
vertex belongs to `D`. It is established when an in-domain actor pushes
and is preserved by every other state transformer.

This invariant proves that an internally generated
`lpool_tryRemove owner loc` cannot take ListPool's owner-outside error.
Graph representation and the returned value prove that the node is also
defined. Thus no strengthening of `ListPoolSpec` is needed.

### 4. Abstract control

The invariant requires the abstract control to be `TSAReady`. Temporary
abstract atomic states occur only inside a single PUpdate trace and are
not exposed to interference.

## Rely and guarantee

`graph_evol` requires:

- existing vertex values are preserved;
- outgoing edges of existing source vertices are preserved exactly; and
- garbage grows monotonically.

`actor_local_eq` preserves another actor's concrete snapshot, abstract
snapshot, pending-push entry, and token.

`source_G actor` requires the invariant before and after the action,
`graph_evol`, local equality for every other actor, and ownership of any
resulting concrete atomic-control state by `actor`.

`source_R observer` is the guarantee-generated rely. Prove:

- token preservation for the observer;
- local-state preservation;
- graph evolution under rely;
- `ValidRGI`; and
- parallel compatibility.

## Operation proof plan

### Push

1. Convert the outer invocation token to `ls_lini (tsa_push v)` at the
   concrete push invocation.
2. Apply matching concrete and abstract `start_push` transformers.
3. Extend `vertices_owned` using the actor's domain-membership proof.
4. At the concrete response, apply matching `finish_push` transformers
   and produce the abstract return token.
5. Prove the only ListPool invocation error, actor outside `D`, contradicts
   the method precondition.

### TryPop entry and getTop invocation

1. Split an outer active call into an in-domain `TryPopInside` case or an
   abstract error possibility.
2. For concrete snapshot invocation, take
   `step_tsa_trypop_snapshot_inv`, add equal snapshots, and change the
   token from `ls_inv` to `ls_lini`.
3. For concrete atomic invocation, take no abstract step yet, retain
   `ls_inv tsa_trypop`, and record that both snapshots are absent.

### getTop response

For `YSuccNode v owner loc`:

1. Reject the atomic phase using the concrete-snapshot premise and the
   snapshot protocol.
2. Clear the concrete snapshot only.
3. Preserve the abstract snapshot and linearizing token.
4. Record the returned value and either garbage or top-node evidence for
   the internal removal.

For atomic `YFail`:

1. Take `step_tsa_trypop_snapshot_inv`, even if the graph is empty.
2. Immediately take `step_tsa_trypop_fail`.
3. Clear the just-created abstract snapshot and produce `TFail`.

For atomic `YSuccEmpty`:

1. Transfer `all_vertices_garbage` through graph representation.
2. Take `step_tsa_trypop_empty_inv`.
3. Take `step_tsa_trypop_empty_res` and produce `TSuccEmpty`.

### Internal tryRemove

At invocation:

1. Use the returned value and graph representation to prove the concrete
   node exists.
2. Use `vertices_owned` to prove its owner is in `D`.
3. Rule out all ListPool error constructors.
4. Leave the abstract state and token unchanged while concrete control is
   atomic-pending.

At response `true`:

1. Use concrete liveness to eliminate the stored garbage alternative.
2. Apply `step_tsa_trypop_succ` using the saved snapshot, top proof, and
   value proof.
3. Mark the node garbage in both graphs, clear the abstract snapshot, and
   produce `TSuccNode`.

At response `false`:

1. Apply `step_tsa_trypop_fail` to the saved snapshot.
2. Clear the abstract snapshot without changing the graph.
3. Produce `TFail`.

## Packaging

1. Assemble `push_method_triple` and `trypop_method_triple`.
2. Invoke `SetLogic.soundness` with `R`, `G`, and `SI`.
3. Discharge both operation cases and the initial invariant.
4. Derive linearizability with `LISim2LILin`.
5. Vertically compose with `ListPoolProof.MListPoolLinearizable`.

## Verification checklist

- [x] Keep `ListPoolSpec` unchanged.
- [x] Permit the TryStackAux snapshot branch on an empty graph.
- [x] Define the singleton simulation invariant.
- [x] Prove graph and snapshot-protocol transformer lemmas.
- [x] Add and maintain the node-ownership invariant.
- [x] Prove rely/guarantee validity and parallel compatibility.
- [x] Prove `push_method_triple`.
- [x] Prove all `getTop` invocation and response cases.
- [x] Prove internal `tryRemove` safety and both response cases.
- [x] Prove `trypop_method_triple`.
- [x] Package `MTryStackAux` and derived composition theorems.
- [x] Run the full repository build.
- [x] Run whitespace and trust-assumption audits.

## Final validation commands

```text
make examples/TSStack/TryStackAuxProof.vo
make -j2
git diff --check
```

Also inspect:

```coq
Print Assumptions MTryStackAux.
Print Assumptions MTryStackAuxLinearizable.
Print Assumptions MListPoolTryStackAux.
```

No `Admitted`, `admit`, `Axiom`, or new opaque trust assumption is
acceptable.
