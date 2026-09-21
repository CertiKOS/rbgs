# Verification Plan: ListPool over SPListArray and Timestamp

## Objective

Prove the implementation in `ListPool.v` correct with respect to the DAG
specification in `ListPoolSpec.v`.  The immediate underlay must remain the
horizontal composition

```coq
@SPListArrayLayer.L A D ⊗ₗ TimestampLayer.L
```

and the overlay must remain the ListPool interface.  The production theorem
should ultimately have the shape

```coq
MListPool :
  TPSimulationSet.TPSimulation.layer_implementation_simulation
    (@ListPoolImpl.E A D)
    (@ListPoolImpl.F A D).
```

The exact parameters of `F` will change in the prerequisite domain repair
below.  The derived correctness theorem should be

```coq
MListPoolLinearizable := LISim2LILin MListPool.
```

Finally, compose it with the verified SPListArray implementation while
leaving Timestamp as an explicit underlay:

```coq
compose_list_pool :=
  (SPListArrayProof.compose_splist_array D ⊗
   LIId TimestampLayer.L) ▶
  MListPoolLinearizable.
```

An `LICast` may be needed to normalize the two presentations of the tensor.

The intended proof is the ListPool argument from Appendix A.2, especially
Figures 21--25 and the invariants on pp. 35--38 of `main-tr.pdf`.  It must use
the production set-of-possibilities logic.  Unlike `SPListArrayProof.v`, this
proof is inherently non-singleton: it has to retain alternative placements
of a ListPool `getTop` invocation relative to overlapping pushes and later
commit to the alternatives in which the returned candidate is legal.

## Required preliminary decisions

Four issues should be resolved before building the main invariant.

### 1. Repair the thread-domain mismatch

`SPListArraySpec` errors when the calling thread is outside `D`.  The current
ListPool specification is not parameterized by `D` and permits `push` and
`getTop` from every positive thread identifier.  Consequently an out-of-
domain ListPool call can make the implementation's first array operation
error even though no ListPool possibility can reach `ErrorListPool`.  The
usual `Punsafe -> Psafe \/ APError` obligation is therefore unprovable.

Parameterize `StepListPool`, `ErrorListPool`, `VListPool`, and
`ListPoolLayer.L` by `D`, and add at least:

```coq
| error_actor_outside actor op s :
    ~ ThreadDomain.contains D actor ->
    ErrorListPool D
      {| te_tid := actor; te_ev := InvEv op |}
      (LPReady s)
```

An explicit `tryRemove`-owner-outside error is also recommended because it
matches the underlay contract and avoids making that case depend indirectly
on vertex absence.  Update `ListPoolImpl.F` to `@ListPoolLayer.L A D`.

Acceptance condition: for every first underlay call in each method, either
its no-error premise follows from `ThreadDomain.contains D actor` (and owner,
where applicable), or the overlay token can take an `ErrorListPool` step.

### 2. Use the full set logic, not `lift_assert`

The main proof state is

```coq
@SetPossState.ProofStateSet _ _ (li_lts E) (li_lts F)
```

with assertions from `AssertionsSet` and triples from
`RGILogicSet.RGILogic`.  Do not import or use `SingletonPossibility` in
`ListPoolProof.v`.  `lift_assert`, `lift_relation`, and the singleton
proof-state facade are not part of this proof, including for deterministic
helper steps.  Keeping the development in one assertion language avoids
changing views whenever a deterministic phase is adjacent to a speculative
one.

The abstract configuration must contain, at the same time:

- a fallback branch where the overlay `getTop` invocation is still at
  `ls_inv`, used for the atomic `Fail` and `SuccEmpty` paths;
- branches where `step_getTop_snapshot_inv` has run with different saved
  snapshots, used for nonempty results;
- all combinations required by concurrent scans belonging to different
  actors.

Use `SpecUnion`, `ALinExists`, `ac_trylin`, and the mixed finite update chain.
Do not collapse the configuration to one branch after an ordinary underlay
step.  A commit to one compatible subfamily is appropriate only when the
ListPool result has been determined.

### 3. Avoid a hidden finiteness assumption in ignored-node removal

The paper derives its generalized `I_ignore` rule by repeatedly deleting
ignored vertices from a finite graph.  The Coq states currently represent
vertices and garbage as predicates/functions and carry no finite-support
witness for all historical nodes.  A literal induction over the ignored
vertex set is therefore unavailable.

Prefer a stronger, directly maintained witness invariant:

```text
For every active scan and every live candidate that is valid for the
visited portion, there is a nonempty subconfiguration whose ListPool
snapshot makes that candidate an lp_top.
```

This is the only consequence of `I_visit + I_ignore` needed by the final
nonempty case.  Preserve it constructively when possibilities are branched
at push and scan steps.  If this stronger invariant proves awkward, the
fallback is to add a finite allocation-history list to both array and pool
states and prove finite support.  Do not use classical choice to pretend an
infinite predicate is enumerable.

### 4. Account for stale observations of `TSTop`

A scan can read a node with timestamp `TSTop`; its owner can subsequently
replace that timestamp by an interval before the scan finishes.  The
candidate stored by `getTop_impl` retains the observed `TSTop`.  Thus the
naive invariant "the accumulator is a top node under the current
`array_edge` relation" is not stable.

The proof should instead retain an abstract-top witness.  The key causal
fact is that if a node was still pending when a competing push began, the
ListPool `start_push` rule did not create an edge from that competing push to
the pending node.  Later `setTS` changes concrete timestamp order but never
adds an abstract edge.  Formalize this fact before attempting the fold
proof.

Acceptance condition: construct and prove a two-node candidate-selection
lemma covering all four combinations of interval and `TSTop` observations,
including a candidate whose current array timestamp no longer equals its
saved timestamp.

## Proof architecture

Create `examples/TSStack/ListPoolProof.v`.  Use the following module setup:

```coq
Module ListPoolProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSet.
  Import TimestampSpec SPListSpec SPListArraySpec ListPoolSpec ListPoolImpl.
  Module SetLogic := RGILogicSet.RGILogic.
  Import TPSimulationSet.TPSimulation CompLinLayer.
```

The proof should be developed in seven phases.  Each phase is intended to
compile before the next one begins.

### Paper-style assertion notation

Introduce the notation layer before defining the invariant and use it
consistently throughout the proof.  Reuse the production notations already
exported by `AssertionsSet`:

```coq
α ↦∀ ls       (* every possibility agrees on ls *)
α ↦∃ ls       (* a nonempty speculative subconfiguration agrees on ls *)
P ⊕ Q         (* union of speculative possibility families *)
P * Q         (* separating conjunction *)
```

Add thin aliases for the paper's operation-state notation instead of
spelling out `ls_inv`, `ls_lini`, and `ls_linr` in every assertion:

```coq
Notation "α '↦∀◦(' op ')'" := (α ↦∀ (ls_inv op)).
Notation "α '↦∃◦(' op ')'" := (α ↦∃ (ls_inv op)).
Notation "α '↦∀•(' op ')'" := (α ↦∀ (ls_lini op)).
Notation "α '↦∃•(' op ')'" := (α ↦∃ (ls_lini op)).
Notation "α '↦∀•(' op ',' ret ')'" :=
  (α ↦∀ (ls_linr op ret)).
Notation "α '↦∃•(' op ',' ret ')'" :=
  (α ↦∃ (ls_linr op ret)).
```

If Coq's lexer requires slightly different quoting, preserve the displayed
paper form in comments and choose the closest compiling notation.  Also
define readable assertion names or notations for:

```text
gettingT(actor, N, P)
I_vertex, I_edge, I_push, I_garbage
I_iter, I_ignore, I_visit
I_loop^uv, I_loop^vi(owner), I_loop^vd
I_loop^r(candidate), I_loop^bottom(done,count)
```

The underlying definitions should remain ordinary Gallina predicates so
lemmas can unfold them selectively.  Proof scripts and theorem statements
should use these names and `⊕` instead of exposing raw `SpecUnion` witnesses
unless constructing or destructing that connective itself.

## Phase 0: Specification and library preparation

### 0.1 Domain repair

Make the domain change described above and update all constructor calls and
layer aliases.  Add inversion lemmas for the new error constructors so that
method proofs can use `provable_perror` without repeatedly destructing the
entire ListPool LTS.

### 0.2 Payload accessors

Define accessors that expose the state stored in either array control:

```coq
Definition array_payload (c : SPListArrayControl) : SPListArrayState :=
  match c with
  | ArrayReady a => a
  | ArrayAtomicPending a _ _ => a
  end.

Definition underlay_array (s : State (li_lts E)) := array_payload (fst s).
Definition underlay_timestamp (s : State (li_lts E)) := snd s.
```

Define a similar partial accessor for `LPReady`; the global invariant should
exclude `LPAtomicPending` at stable boundaries.  Atomic pool controls only
need to occur inside a finite possibility-update derivation.

### 0.3 Timestamp algebra

Add reusable lemmas, preferably to `TimestampSpec.v` when they are not
ListPool-specific:

- irreflexivity and transitivity of `timestamp_lt`;
- `TSInterval lo hi < TSTop`;
- inversion of `timestamp_lt` for two intervals;
- the existing `timestamp_ltb_spec` in `ListPool.v` in both true and false
  forms;
- `finish_newTS` advances the clock past the returned upper endpoint;
- if an interval was completed before a later `start_newTS`, its upper
  endpoint is strictly below the later lower endpoint;
- timestamp-state validity preservation, reusing `step_timestamp_valid`.

Define and prove preservation of

```coq
Definition stamped_before_clock a ts_state : Prop :=
  forall n lo hi,
    as_timestamps a n = Some (TSInterval lo hi) ->
    S hi <= ts_clock ts_state.
```

The `newTS` response assertion must retain the returned `lower` and `upper`
long enough to prove that stamping the new node preserves all old abstract
edges.

### 0.4 Array scan and counter algebra

Extract from `SPListArraySpec` and `SPListArrayProof` the lemmas needed by the
higher layer:

- status exclusivity for `Unvisited`, `Visiting`, `Visited`, and `Ignored`;
- `reset_scan` makes every existing node unvisited;
- `begin_scan` changes only the selected row from unvisited to visiting;
- `end_scan` changes the saved row nodes to visited and post-snapshot nodes
  to ignored;
- insert into an already visited/current row is ignored, while insert into
  an unvisited row is unvisited;
- removal preserves scan status and only enlarges garbage;
- `actual_scan_order = []` implies every saved location not in the current
  row order;
- `actual_scan_order = loc :: rest` makes `loc` the first live saved row
  node;
- row counters are monotone and increase exactly once per insertion;
- sum monotonicity and the componentwise-equality consequence of equality of
  two finite sums over the NoDup thread domain.

The last item is needed for the empty proof: if every sampled row counter is
at most its later counter and the two totals are equal, every row counter is
unchanged.

### 0.5 ListPool state algebra

Prove elementary facts for `start_push`, `finish_push`, `start_snapshot`,
`clear_snapshot`, and `mark_garbage`:

- vertex lookup at the inserted node and preservation elsewhere;
- pending-map lookup for the actor and preservation for other actors;
- exact description of newly created edges;
- old edges are preserved;
- snapshots are unchanged by push completion and removal;
- garbage is monotone and vertex values never change;
- snapshot membership is unaffected by later pushes;
- `lp_top` is preserved when garbage grows, provided the candidate itself
  remains live;
- the garbage response needs only an existing snapshot and a defined
  garbage vertex, matching the deliberate relaxation in `ListPoolSpec`.

### Phase 0 acceptance

- The repaired specifications and `ListPool.v` compile.
- The full `_CoqProject` still compiles.
- The timestamp and state-algebra lemmas contain no `Admitted`.
- A small Coq lemma demonstrates the stale-`TSTop` case is represented by
  missing abstract edges rather than by current concrete timestamp order.

## Phase 1: Uniform representation across possibilities

### 1.1 Concrete structural invariant

For an array payload `a` and timestamp state `tss`, define
`concrete_wf a tss` containing:

- `timestamp_state_valid tss`;
- `stamped_before_clock a tss`;
- every array node has exactly one timestamp;
- every `TSTop` node corresponds to the unique pending push of its owner;
- every completed push node has an interval timestamp;
- each row's current order is NoDup and contains exactly its live nodes;
- within one owner row, nonoverlapping completed insertions respect timestamp
  order;
- counters agree with insertion history strongly enough for the empty-case
  argument.

Some of these facts may already follow from the SPListArray LTS but must be
restated at this layer because the proof starts from the array abstraction,
not its lower SPList implementation.

### 1.2 Per-possibility representation

Define `represents_branch a tss lp pi`.  For every branch it should assert:

```text
lp_vertices lp n = as_values a n
lp_garbage lp n  <-> as_garbage a n
lp_pending_pushes lp agrees with TSTop/push phase
lp_edges lp contains only causally justified edges
every lp snapshot is a subset of defined vertices and is lp_closed
pi is consistent with pending pushes and active snapshots
```

"Causally justified" should be a named relation, not just
`lp_edges subset array_edge`.  It needs to support stale `TSTop`
observations.  A useful split is:

- if both endpoints were complete before the newer push began, the final
  timestamp intervals are strictly ordered;
- if the older endpoint was pending, no edge to it was created;
- edges never appear during `setTS`, scan, or removal.

Derive the simpler theorem used by completed-node comparisons:

```coq
edge_implies_timestamp_lt_if_observed_complete : ...
```

### 1.3 Uniform fields

The abstract branches may differ in edges and snapshots, but the following
must agree with the concrete state in every branch:

- vertices and values;
- garbage;
- pending pushes;
- the linearization-map entries for methods other than deliberately
  speculative `getTop`.

Define `all_branches_represent sigma Delta` by quantifying over
`Delta lp_control pi`.  Require `lp_control = LPReady lp` at invariant
boundaries.  Derive branch-independent lookup lemmas, such as:

```coq
all_branches_vertex
all_branches_garbage
all_branches_pending
all_branches_value
```

These lemmas should accept a membership proof for a branch and avoid
unfolding the complete invariant in method proofs.

### 1.4 Initial state

Show that the tensor initial state and the initially one-branch ListPool
configuration satisfy `concrete_wf` and `all_branches_represent`:

- array and pool vertices are empty;
- timestamp clock is zero and pending map is empty;
- no edges, snapshots, garbage, or pending pushes exist;
- all scan/counter maps are empty;
- every timestamp/order condition is vacuous.

### Phase 1 acceptance

- Representation is proved for the initial state.
- Array insert, setTS, remove, reset/begin/end scan, and timestamp inv/res
  each have a preservation lemma at the payload level.
- Per-branch lookup facts no longer require destructing `AbstractConfig`.
- The relation explicitly permits different edges/snapshots but not
  different vertex values or garbage sets.

## Phase 2: Speculation invariants for getTop

This phase is the core future-dependent part of the proof.

### 2.1 Branch predicates

Define pointwise predicates over a ListPool possibility:

```text
PoolInvBranch actor:
  token is ls_inv lpool_getTop and actor has no pool snapshot

PoolSnapshotBranch actor N:
  token is ls_lini lpool_getTop and lp_snapshots actor = Some N

PoolTopBranch actor candidate:
  some N exists, PoolSnapshotBranch actor N holds, and candidate is
  lp_top (N minus garbage) lp_edges with the expected value
```

Then define nonempty-subconfiguration assertions using either `SpecUnion`
or an explicit decomposition into an owned subconfiguration plus a frame.
Merely writing `exists lp pi, Delta lp pi /\ ...` is sufficient for a
read-only fact, but use a genuine subconfiguration assertion whenever the
proof later commits to or updates exactly those branches.

### 2.2 Fallback branch

For every active concrete scan, maintain `fallback_inv actor`: a nonempty
subconfiguration in `PoolInvBranch actor`.  This branch is preserved through
all row scans and all interference.  At the final empty-counter decision it
is committed and advanced by:

```text
step_getTop_atomic_inv;
step_getTop_empty_res  or  step_getTop_fail_res.
```

Without this branch, the implementation cannot take the atomic alternatives
after speculative snapshot invocations have already occurred.

### 2.3 Snapshot-started branch

After the first array row invocation, maintain that at least one branch has
taken `step_getTop_snapshot_inv`.  This is enough for a garbage candidate,
because `step_getTop_garbage_res` intentionally does not require the returned
garbage node to belong to the saved snapshot.

The thread domain is nonempty, so completing the `ForEach` guarantees this
branch exists.

### 2.4 Top-witness family

Replace the paper's finite ignored-node elimination with a direct property:

```text
top_witness actor visited candidate:
  if candidate is the accumulator selected from the visited rows and is
  still live, a nonempty subconfiguration satisfies
  PoolTopBranch actor candidate.
```

The snapshot in that subconfiguration must:

- contain the candidate;
- contain every nonignored visited live node whose presence is required by
  real-time/edge closure;
- omit ignored predecessors that would prevent the candidate from being
  top;
- remain closed under the branch's `lp_edges` relation.

Prove that this property implies exactly the premises of
`step_getTop_top_res` after all owners have been visited.

### 2.5 Possibility transformers

Implement small semantic constructors rather than repeating raw
`ac_trylin` scripts:

- advance every branch by one mandatory pool event;
- preserve a selected subconfiguration and its frame;
- branch one source possibility into "getTop invocation before push" and
  "push before getTop invocation" descendants;
- combine independent choices for all scanning actors in
  `ThreadDomain.threads D`;
- commit to a nonempty subconfiguration and advance its selected branches
  to a universal `ls_linr` token.

Each transformer must prove:

- output nonemptiness;
- unchanged `ac_active` domain;
- output is a subset of `ac_steps` of the input;
- foreign linearization-map entries are preserved;
- the relevant representation and witness properties.

Use `PUpdateIdSpec`, `SpecUnion_intro`, `ac_trylin_subset_steps`, and
`provable_linstep`.  Do not add a second semantics or an axiom asserting that
the desired speculative branch exists.

### Phase 2 acceptance

- Fallback, started-snapshot, and top-witness assertions are defined with
  explicit nonemptiness.
- Push insertion can extend the possibility family while preserving all
  other actors' scan witnesses.
- A top-witness subconfiguration can be committed and advanced through the
  ListPool top response.
- No proof step enumerates the predicate-valued vertex set.

## Phase 3: Global invariant, rely, and guarantee

### 3.1 Global invariant

Define `I` directly as an `AssertionsSet` assertion.  At minimum it contains:

```text
the concrete underlay is (array_control, timestamp_state)
concrete_wf (array_payload array_control) timestamp_state
every abstract possibility is LPReady and represents the concrete payload
uniform vertex/value/garbage/pending facts
overlay-token consistency for pending pushes
scan-token/speculation consistency for every actor
fallback/snapshot/top witness facts for active scans
counter-token consistency for active array_getCounter calls
```

Keep method-local accumulators out of `I`; they belong in phase assertions.
Only shared facts that environmental steps must preserve should be global.

### 3.2 Guarantee

Define `G actor` so that both endpoints satisfy `I` and so that it records:

- the concrete transition is one permitted phase of actor's ListPool
  method;
- foreign active-domain/token entries are preserved pointwise across all
  descendant possibilities;
- foreign `as_scans` and `as_pending_counters` entries are unchanged;
- vertices and counters grow monotonically;
- garbage grows monotonically;
- timestamps change only from `TSTop` to a returned interval;
- abstract edges only grow at a push invocation and snapshots only change
  for the acting scan;
- every new possibility descends from a source possibility through valid
  ListPool steps.

It is acceptable for `G actor` to forget the exact branch-to-branch mapping
after a commit, provided it retains enough provenance to prove foreign-token
and witness stability.

### 3.3 Rely

Define `R observer` from guarantees of actors other than `observer`, plus
foreign `GINV`, `GRET`, and identity steps, following the
`GuaranteeGeneratedRely` pattern in `SPListArrayProof.v`.  Since this proof is
not singleton, define a set-native observer-view relation:

- the concrete observer-local scan/counter entries are unchanged;
- every post-branch descends from a pre-branch with the same observer token;
- if the observer owns a fallback or witness subconfiguration, a
  corresponding post-subconfiguration exists unless the candidate became
  garbage, in which case the loop assertion's garbage alternative holds.

Use `ac_active`/`domain_equiv` rather than equality of entire abstract
configurations.

### 3.4 Framework obligations

Prove:

- `ValidRGI (R actor) (G actor) I actor`;
- cross-thread guarantee/rely compatibility;
- stability of active and completed method assertions;
- stability of push phases, timestamp phases, scan-fold phases, and counter
  phases;
- `Ginv` exposure and `Gret` closure;
- completed-result agreement in every possibility;
- error weakening for all domain and undefined-location cases.

### Phase 3 acceptance

- `valid_rg` and `parallel_compatible` compile.
- Every assertion used by a method triple has a named stability theorem.
- Stability explicitly covers candidate removal, concurrent push insertion,
  concurrent timestamp completion, and speculative-family extension.
- The invariant introduces no new axioms or `Admitted` facts.

## Phase 4: Push and tryRemove method triples

Prove the non-looping methods first; they exercise the representation and
speculation-preservation machinery without the fold invariant.

### 4.1 Push

The concrete program is:

```text
array_insert v; newTS; array_setTS loc ts; Ret tt
```

Use the following phase assertions:

```text
PushReady actor v
PushInserted actor v loc
PushTimestampPending actor v loc lower
PushTimestamped actor v loc ts
PushCompleted actor v
```

At the `array_insert` response:

- obtain freshness and the new location from the array transition;
- take `step_push_inv` in every mandatory ListPool branch;
- create both relative-order alternatives needed by every other active
  scan: getTop-before-push omits the node from its snapshot, while
  push-before-getTop may include it;
- preserve the fallback branch and all existing top witnesses;
- establish that the new node is `TSTop` and pool-pending.

At `newTS` invocation/response:

- do not take a ListPool step;
- use `timestamp_state_valid` and `stamped_before_clock`;
- remember the returned endpoints in the continuation assertion;
- prove that every completed push ordered below the new push has a strictly
  smaller interval.

At `array_setTS` response:

- update the node from `TSTop` to the returned interval;
- prove all causally justified edge facts remain true;
- take `step_push_res` in every branch;
- remove the pool-pending entry and reach universal
  `ls_linr (lpool_push v) tt`.

The abstract push response must not occur at `newTS`; it occurs only after
the timestamp is visible through SPListArray.

### 4.2 tryRemove

For `array_tryRemove owner loc`:

- route invalid actor/owner/undefined cases to `APError`;
- at the underlay invocation, take `step_tryRemove_inv` in all branches;
- on `true`, use array liveness/representation and take
  `step_tryRemove_succ`, synchronously adding the node to both garbage sets;
- on `false`, use existing garbage and take `step_tryRemove_fail`;
- prove snapshots and edge sets are unchanged;
- weaken every affected scan candidate from "live top witness" to the
  allowed garbage-candidate alternative;
- preserve fallback and other top-witness branches.

Because tryRemove is atomic in both layers, no new speculative branches are
needed.

### Phase 4 acceptance

- Push and tryRemove method triples compile.
- Push preserves the witness family for every foreign scan.
- The timestamp proof covers overlapping and nonoverlapping allocations.
- Successful removal preserves scan stability through the garbage
alternative.

## Phase 5: getTop fold and final commitment

### 5.1 Method entry and reset

Define `GetTopActive actor` and use `provable_perror` for an actor outside
`D`.  The external overlay token initially agrees universally on
`ls_inv lpool_getTop`.

For `array_resetIter`:

- prove the underlay call is safe;
- leave the ListPool token at `ls_inv`;
- initialize the concrete scan progress to `empty_scan`;
- initialize the fallback branch;
- initialize the candidate to `None` and count to zero;
- establish the empty visited-prefix invariant.

### 5.2 Fold decomposition

Use `SetLogic.provable_foreach` on

```coq
ForEach ThreadDomain.threads D From (None, 0) Using scan_step
```

with a suffix-indexed invariant

```coq
ScanFold actor remaining scan
```

that existentially stores a visited prefix `done` satisfying:

```text
ThreadDomain.threads D = done ++ remaining
NoDup (done ++ remaining)
scan_visited progress = done
scan_current progress = None
```

It must also include the following accumulator facts.

For `fst scan = Some candidate`:

- the candidate value/owner/location matches a defined array vertex;
- its saved timestamp is the timestamp returned when its row was scanned;
- it came from an owner in `done`;
- either it is now garbage, or a live `PoolTopBranch` subconfiguration
  exists;
- no later pure `Ret` step changes this witness.

For `fst scan = None`:

- every row in `done` returned empty;
- every node in each saved row snapshot is now garbage;
- `snd scan` is exactly the sum of the saved row counters;
- that sum is at most the sum of current counters for `done`;
- fallback and snapshot-started alternatives remain available.

### 5.3 One row: invocation

At `array_getTop owner` invocation:

- use the suffix/NoDup facts to prove `owner` has not been visited;
- align the concrete scan with `begin_scan`;
- retain the fallback `ls_inv` branches;
- in the snapshot family, optionally take
  `step_getTop_snapshot_inv` in branches where it has not yet run;
- establish the paper's transition from `I_loop_uv` to
  `I_loop_vi[owner]`.

### 5.4 One row: nonempty response

For a response `inl (v, ts, loc)`:

- use `actual_scan_order` to show this is the first live node in the saved
  row order;
- derive that no other live node from this row has a causally valid incoming
  edge to it;
- apply `choose_candidate` and split on the previous candidate and
  `timestamp_ltb`;
- when the new node replaces the previous candidate, construct/preserve a
  snapshot branch making the new node top;
- when the previous candidate is retained, use the false timestamp
  comparison plus the pending/overlap lemma to rule out a new abstract edge
  into it;
- handle both nodes' possible later transition from `TSTop` to intervals;
- update progress with `end_scan` and extend `done` by `owner`.

Package the hard graph fact as a standalone lemma, for example:

```coq
choose_candidate_preserves_top_witness : ...
```

Do not bury this argument inside the `PUpdate` proof.

### 5.5 One row: empty response

For `inr count`:

- record the row's saved counter;
- prove every location in its saved order is absent from the current live
  order and therefore garbage;
- add `count` to the accumulator;
- preserve an existing candidate and its witness, or extend the all-empty
  prefix fact;
- update progress with `end_scan` and extend `done`.

### 5.6 Fold exit: nonempty candidate

When all owners have been visited and a candidate exists, perform a
possibility update before the outer pure return.

If the candidate is now garbage:

- commit to any snapshot-started branch;
- use exact vertex/value and garbage correspondence;
- take `step_getTop_garbage_res`;
- discard all other branches and establish universal
  `ls_linr lpool_getTop (YSuccNode ...)`.

If the candidate is live:

- commit to its `PoolTopBranch` subconfiguration;
- discharge snapshot lookup, `lp_top`, and vertex-value premises;
- take `step_getTop_top_res`;
- clear the snapshot and establish the same universal completed token.

This is the Coq counterpart of Figure 23.

### 5.7 Fold exit: no candidate and counter call

Leave the ListPool result unresolved and invoke `array_getCounter`.

At its invocation:

- record `saved_total = total_counter a` from `start_counter`;
- prove `snd scan <= saved_total` from the per-row sampled counts;
- preserve the fallback branch.

At its response `current_counter`:

- obtain `saved_total <= current_counter <= total_counter current_a`;
- split on `Nat.eqb current_counter (snd scan)`.

Equal case:

- derive equality throughout the inequalities;
- use componentwise counter monotonicity and the all-empty saved snapshots to
  prove every current row order is empty;
- combine vertex/garbage representation to prove
  `all_vertices_garbage lp` in the fallback branch;
- commit to that branch and take `step_getTop_atomic_inv` followed by
  `step_getTop_empty_res`;
- return `YSuccEmpty`.

Unequal case:

- commit to a fallback branch;
- take `step_getTop_atomic_inv` followed by `step_getTop_fail_res` (which has
  no state guard);
- return `YFail`.

This is the Coq counterpart of the `I_loop_bottom` argument in Figure 22.

### Phase 5 acceptance

- `getTop_method_triple` compiles using `provable_foreach`.
- No unfolding of `foldM` is needed in the client proof.
- All three results (`YSuccNode`, `YSuccEmpty`, and `YFail`) end with a
  universal `ls_linr` token.
- The nonempty proof covers live and garbage candidates separately.
- The empty proof derives `all_vertices_garbage`; it does not assume it.
- The fail proof retains a fallback `ls_inv` possibility until the counter
  comparison.

## Phase 6: Soundness packaging

### 6.1 Method assertions

For each ListPool operation define set-native active/completed assertions:

```coq
Active actor op     := I /\ ALin actor (ls_inv op)
Completed actor op r := I /\ ALin actor (ls_linr op r)
```

If direct conjunction is too strong for method-entry `Ginv`, use the
standard `Ginv` exposure lemma to obtain the universal token after the
framework adds it to every possibility.  Prove:

- active entails invariant;
- completed entails invariant;
- active/completed stability;
- `Ginv` exposes active;
- `Gret` closes completed;
- completed assertions agree on the returned token in every possibility.

### 6.2 Simulation theorem

Construct:

```coq
Program Definition MListPool : layer_implementation_simulation E F :=
  {| li_impl := list_pool_impl D |}.
```

Discharge it with `SetLogic.soundness`, the Phase 3 rely/guarantee facts,
the three method triples, and the initial invariant.

Run:

```coq
Print Assumptions MListPool.
```

Only the framework's existing classical/extensionality assumptions are
acceptable.  There must be no `Admitted`, new `Axiom`, or semantic shortcut.

### 6.3 Linearizability and vertical composition

Define `MListPoolLinearizable`, then compose horizontally and vertically as
shown in the objective.  Add only the smallest `LICast` lemmas needed for
definitional differences between:

- equality normalization between native set-layer tensors; and
- tensoring the SPListArray correctness theorem with Timestamp identity.

### 6.4 Regression build

Compile at least:

```text
examples/TSStack/TimestampSpec.vo
examples/TSStack/ListPoolSpec.vo
examples/TSStack/SPListArraySpec.vo
examples/TSStack/SPListArrayProof.vo
examples/TSStack/ListPool.vo
examples/TSStack/ListPoolProof.vo
models/simlin/RGILogicSetTests.vo
```

Then run the complete `_CoqProject` build and `git diff --check`.

### Phase 6 acceptance

- `MListPool` and `MListPoolLinearizable` compile.
- End-to-end composition from the verified SPList-array underlay plus
  Timestamp compiles.
- All existing examples still build.
- `Print Assumptions` reports no new trust assumptions.

## Recommended implementation order

The following order minimizes time spent inside large `PUpdate` proofs
before the semantic design is known to work:

1. Repair the ListPool thread-domain errors and compile all existing files.
2. Prove timestamp clock/order helpers and the stale-`TSTop` causal lemma.
3. Define per-branch representation and prove initial/transition algebra.
4. Prototype a two-branch `getTop-before-push` / `push-before-getTop`
   possibility transformer.
5. Prototype committing a top-witness subconfiguration to a universal
   nonempty response.
6. Generalize the transformer across all active scans in the finite thread
   domain.
7. Define the global invariant and prove rely/guarantee compatibility.
8. Complete `tryRemove`, then `push`.
9. Prove one-row nonempty/empty scan lemmas and the candidate-selection
   theorem.
10. Assemble the `ForEach` proof and the three final result paths.
11. Package soundness and compose layers.

Steps 2, 4, and 5 are feasibility gates.  If any one fails, revise the
state/speculation representation before proceeding; do not compensate with
larger opaque invariants.

## Expected files

Primary work:

- `examples/TSStack/ListPoolProof.v`
- `docs/plans/ListPoolVerificationPlan.md`

Expected prerequisite edits:

- `examples/TSStack/ListPoolSpec.v` for domain-aware errors;
- `examples/TSStack/ListPool.v` for the updated overlay layer parameter and,
  if useful, reusable candidate/timestamp lemmas;
- `examples/TSStack/TimestampSpec.v` for general timestamp-order lemmas;
- `examples/TSStack/SPListArraySpec.v` only for genuinely reusable scan or
  counter lemmas, not to encode ListPool-specific ghost state;
- `_CoqProject` to register `ListPoolProof.v`.

No change to the executable ListPool algorithm is expected.  If the stale
`TSTop` feasibility gate exposes a real algorithm/specification mismatch,
document the counterexample and repair the smallest incorrect contract
before continuing.

Current verification status: **domain/timestamp prerequisites, set-native
configuration evolution, observer-token rely/guarantee, initial invariant,
and core representation-preservation algebra compile.  The operation triples,
the speculative `getTop` witness invariant, and final soundness packaging
remain to be implemented.**
