# Verification Plan: TryStack over TryStackAux

## Objective and deliverables

Prove that the implementation in `TryStack.v` refines the graph-based,
atomic specification in `TryStackSpec.v`.  Appendix A.4 of `main-tr.pdf`,
especially Figures 30--32 and the definitions of `CanPop`, `PopAttempt`,
`I_pop`, and `I_graph`, is the mathematical reference.

The intended production deliverables are a new
`examples/TSStack/TryStackProof.v`, an `_CoqProject` entry after
`TryStackAuxProof.v`, and these exported results:

```coq
MTryStack :
  layer_implementation_simulation
    (@TryStackImpl.E A D)
    (@TryStackImpl.F A D).

MTryStackLinearizable :
  layer_implementation_linearizability
    (@TryStackImpl.E A D)
    (@TryStackImpl.F A D).

MListPoolTryStack :
  layer_implementation_linearizability
    (@ListPoolProof.E A D)
    (@TryStackImpl.F A D).
```

The final theorem is obtained by vertically composing
`TryStackAuxProof.MListPoolTryStackAux` with
`MTryStackLinearizable`.

No `Admitted`, `admit`, new `Axiom`, or semantic shortcut is acceptable.

## Main proof strategy

Use `RGILogicSet` directly, not the singleton facade used by
`TryStackAuxProof.v`.  A concrete TryStackAux `trypop` takes a snapshot at
its invocation and may return a node that is only top in that snapshot.
The atomic TryStack operation must therefore be speculatively linearized
at one of several possible positions before its concrete result is known.
The invariant must retain all choices that may later be selected by the
TryStackAux response.

At a high level:

1. A concrete `trypop` snapshot invocation records the snapshot and
   expands the abstract configuration with legal serializations of that
   operation and the other pending try-pops.  It also retains a failure
   branch and, where needed, an unlinearized branch.
2. An unfinished concrete push retains both abstract possibilities: the
   push may already be reflected, or it may remain unlinearized with its
   node omitted from that possibility.  This is essential when a pop
   snapshot overlaps the push and must be linearized before it.
3. Interference preserves enough serializations for every outstanding
   snapshot and both choices for every relevant unfinished push.
4. A concrete response filters the abstract configuration to branches
   with the same result.  The central theorem is that this filter is
   nonempty.
5. A concrete push response catches up every surviving deferred branch
   before completing the corresponding abstract push.

The production invariant must remain schedule-indexed and branch
correlated, as in the paper's `I_pop`.  In particular, a permission such as
"beta may precede this pending push" is not stored as a fact that can later
be combined freely with permissions from other possibilities.  It belongs
to the particular member of `Delta` in which beta was linearized before the
push.  All response filters and snapshot images must preserve that
correlation.

Speculation must happen at invocation rather than being delayed until the
response.  A push that starts after the snapshot can make the returned
snapshot node cease to be a global top.  A surviving possibility must
already have placed the try-pop before that later push.

## Diagnosis of the discarded proof path

An abandoned development introduced a shared `SnapshotDeferrals` map and
made the production forest quantify over every `HistoricalPopResponseSequence`
admitted by that map.  This does not faithfully encode the paper's
invariant.  The map records each snapshot's deferral permissions
independently, while the paper stores complete, correlated possibilities in
`Delta`.  Quantifying over arbitrary historical sequences consequently
forms a cross-product of decisions that may have come from different
members of `Delta`.

For example, while a push is pending, one branch may have linearized it and
another branch may have linearized an older pop before it.  Both branches
must be retained.  Once the push responds, each surviving branch has made a
particular commitment.  A global deferral map forgets which commitment
belongs to which branch and can later demand a response history combining
the incompatible halves of the two branches.

This was a problem with the mechanization, not a counterexample to the
paper's reordering argument.  The paper's `PopAttempt` witnesses live inside
individual possibilities and therefore retain the missing correlation.
The discarded path culminated in an unproved
`ready_snapshot_success_normal_forms` premise; that premise was stronger
than `I_pop` and was not derivable from its factorized ghost state.

The following material has therefore been removed from
`TryStackProof.v`:

- `SnapshotDeferrals` and historical response relations;
- historical/latent response forests and their normal-form layer;
- the superseded `future_I`/`saturated_I` closure experiment;
- the incomplete forest-based `R`, `G`, method triples, and exports; and
- the experimental causal-history predicate, which diagnosed the lost
  correlation but did not repair the production invariant.

The retained checkpoint ends with `trypop_success_deferred_nonempty` and
uses `prophecy_I`, `OmittedPopPlan`, and `omission_exhaustive_pop`, which are
the closest direct encodings of the paper's `I_graph`, `CanPop`,
`PopAttempt`, `Fail`, and `Pending` assertions.

## Resolved foundation: garbage-independent edges

The three graph specifications now use the paper's rule: a new push adds
edges to every defined vertex whose push is no longer pending, regardless
of whether that vertex is garbage.  `ListPoolProof.v` and
`TryStackAuxProof.v` have been adapted and compile against this rule; the
full repository build also passes.  These changes are committed in
`7f51a8d`.

When no pending push is deferred, the TryStack proof can use the paper's
graph invariant directly:

```coq
Definition graph_represents p s : Prop :=
  tsa_vertices p = ts_vertices s /\
  tsa_edges p = ts_edges s /\
  tsa_pending_pushes p = ts_pending_pushes s /\
  (forall n, tsa_garbage p n -> ts_garbage s n) /\
  (forall n, ts_garbage s n -> ts_is_vertex s n).
```

The Coq LTS exposes the interval between an underlay push invocation and
its response.  During that interval linearizability requires both choices:
the corresponding atomic push may have linearized already, or may still be
pending.  The latter possibility cannot have exact vertex equality because
the concrete node exists while the abstract node does not.  Use an omitted
set of live, pending concrete push nodes and a partial graph relation:

- a node in the omitted set is absent from the abstract vertex and pending
  maps;
- a visible node agrees with the concrete vertex map;
- edges between visible live nodes agree with the concrete graph; and
- the dependency information needed to reflect an omitted push later is
  retained as a ghost readiness condition.

The ordinary exact relation is the empty-omission special case.  The edge
rule itself remains garbage-independent in all three public specifications;
the live-edge comparison is only an internal proof device for branches
whose earlier pending pushes have deliberately not yet been linearized.

Establish the following representation lemmas before the speculative
schedule development:

- `tsa_start_push` preserves a deferred branch by extending its omission
  set, and preserves a reflected branch by taking `ts_start_push`;
- `tsa_finish_push` catches up an omitted push if necessary and then takes
  `ts_finish_push` in every surviving branch;
- speculative `ts_mark_garbage` preserves it by extending only abstract
  garbage with an existing vertex;
- concrete `tsa_mark_garbage` preserves it after filtering to branches
  that already contain the same node in abstract garbage; and
- exact edge equality transfers `lp_top` facts after accounting for the
  concrete/abstract garbage inclusion.

## Proof-state model

### Payload projections

Define projections that erase the two-event encoding of atomic control:

```coq
concrete_payload : TryStackAuxControl -> TryStackAuxState
abstract_payload : TryStackControl -> TryStackState
```

The global invariant should expose abstract `TSReady` states only.
`TSAtomicPending` is used inside a finite `poss_steps` trace and must not
be visible at an interference boundary.  The concrete invariant must also
describe `TSAAtomicPending`, because the empty TryStackAux branch is split
into an invocation and response by the Coq LTS.

### Finite snapshot domain

Use the finite `ThreadDomain.threads D` list to enumerate snapshot owners:

```coq
Definition snapshot_actors (p : TryStackAuxState) : list tid :=
  filter (fun actor => isSome (TMap.find actor (tsa_snapshots p)))
         (ThreadDomain.threads D).
```

Maintain and prove:

- every snapshot owner belongs to `D`;
- `snapshot_actors` is duplicate-free;
- membership in `snapshot_actors` is equivalent to the existence of a
  concrete snapshot; and
- every snapshot member is a vertex.

These properties make the paper's finite permutations usable in Coq and
also discharge internal-call safety.

### Schedules and pop attempts

Represent a serialization as a duplicate-free list of actors.  Define
Coq versions of the paper predicates, parameterized by the concrete
snapshot map and by one abstract branch:

```text
CanPop accumulated edges snapshots garbage schedule
PopAttempt accumulated edges snapshots garbage schedule rho pi
```

For each actor in a successful schedule, select a node that is:

- top in that actor's saved live snapshot; and
- top in the union of the snapshots accumulated so far.

`PopAttempt` additionally records the corresponding atomic TryStack
invocation/response trace, the `ls_linr ts_trypop (TSuccNode ...)` token,
and the accumulated abstract garbage.  At the end it permits any remaining
pending actors to be resolved to `TFail`, as in the paper's `Fail(B)`
branch.

Prove the following reusable facts by induction on schedules:

- `PopAttempt` produces a valid `poss_steps` trace;
- it preserves the common vertices, edges, and pending-push map;
- abstract garbage is concrete garbage plus the nodes selected by the
  schedule;
- selected nodes are distinct;
- the linearization map changes only at actors named in the schedule or
  failure set; and
- shortening the accumulated snapshot union preserves the suffix of a
  valid `CanPop` schedule.  This is the lemma used when a response removes
  an actor from the outstanding schedule.

### Exhaustive possibility invariant

The paper writes `I_pop` using a separating conjunction over every
permutation.  In Coq, state the semantic content directly over
`AbstractConfig`:

1. Every possibility has an abstract ready state related to the concrete
   graph.
2. For every admissible permutation of outstanding snapshot actors, if
   `CanPop` holds, the configuration contains the corresponding
   `PopAttempt` possibility.
3. For every pending snapshot actor, the configuration contains a branch
   in which it is still unlinearized or has returned `TFail`, as required
   by the invocation update.
4. Possibilities agree on vertices, edges, and pending pushes; only
   garbage and linearization tokens differ by speculative schedule.
5. Every possibility has the same active thread domain, as required by
   `AbstractConfig`.
6. Concrete and abstract garbage contain only defined vertices, ensuring
   fresh locations remain fresh in every possibility.

Call the conjunction of this protocol, the graph relation, snapshot
well-formedness, and concrete-control consistency `I`.

The proof should define a local constructor for the relational image of
an abstract configuration under legal schedule steps.  The generic
`PStep` interface checks reachability and nonemptiness but does not by
itself require the post-configuration to contain every legal image.  The
constructor must therefore include an explicit completeness field (or be
defined directly as a `Program Definition AbstractConfig`) rather than
relying on an arbitrary `PStep` witness.

## Rely and guarantee

Define a branch-wise graph evolution relation that records:

- preservation of existing vertex values;
- preservation of exact concrete/abstract edge correspondence and
  monotone evolution of the common graph;
- monotone concrete and abstract garbage;
- preservation of other actors' snapshots and pending-push entries; and
- preservation of the observing actor's token in every possibility.

`G actor` should require `I` before and after, the graph evolution facts,
local equality for every other actor, ownership of a concrete atomic
control state by `actor`, and the appropriate schedule-image relation on
the abstract configurations.

Define `R observer` as the guarantee-generated rely.  Prove:

- identity and transitivity facts needed by `ValidRGI`;
- stability of `I`, active-call assertions, internal-call assertions, and
  completed-call assertions;
- invocation/return administrative steps preserve the observer view; and
- parallel compatibility for distinct actors.

The pointwise `token_rely` and possibility-rectangularity lemmas in
`ListPoolProof.v` are the closest existing templates.  The simpler
`actor_local_eq` development in `TryStackAuxProof.v` can be reused for
concrete snapshot and pending-push maps, but not for the abstract
configuration as a whole.

## Operation proof plan

### Push

1. Split an external active call into an in-domain case or an abstract
   error possibility, following `TryStackAuxProof.push_method_triple`.
2. At the concrete `tsa_push v` invocation, retain both images of every
   possibility: a deferred image that keeps `ls_inv (ts_push v)` and omits
   the new node, and a reflected image that takes `step_ts_push_inv`.
3. Prove that both images preserve the exhaustive snapshot invariant.
   Garbage-independent edge generation makes reflection independent of
   garbage; the omitted-node readiness witness records the edges needed if
   reflection is postponed.
4. At the concrete response, first reflect any deferred push, then take
   `step_ts_push_res` in every possibility, remove the matching pending-push
   entry, and produce
   `ls_linr (ts_push v) tt`.
5. Rule out the TryStackAux actor-outside error from the method's domain
   precondition.

The push proof should be attempted immediately after the basic graph
representation lemmas.  It is the quickest integration test for exact
graph equality across the speculative family.

### Try-pop invocation: snapshot branch

When `step_tsa_trypop_snapshot_inv` records `S[actor] = dom(V)`:

1. Preserve a branch in which `actor` remains at `ls_inv ts_trypop`.
2. Add a branch that atomically returns `TFail` for `actor`.
3. For every legal placement of `actor` among outstanding snapshot
   actors, add the successful schedule images described by `PopAttempt`.
4. Prove the new abstract configuration is nonempty using either the
   identity or failure branch.
5. Prove the exhaustive schedule invariant.  Follow the paper's split:
   if a target permutation omits `actor`, obtain it through identity or
   failure; if it contains `actor`, split it as
   `prefix ++ actor :: suffix` and use the corresponding speculative
   atomic pop followed by the suffix schedule.

This is the main combinatorial construction in the proof.

### Try-pop invocation: atomic-empty branch

The Coq TryStackAux LTS has a separate
`TSAAtomicPending s actor tsa_trypop` state, unlike the paper's single
atomic transition.  Keep a dedicated internal assertion for this state.
Either:

- speculatively take the abstract empty invocation and response at the
  concrete invocation, recording `ls_linr ts_trypop TSuccEmpty`; or
- leave the abstract call unresolved and take both abstract steps at the
  concrete response.

The first option is preferred because `ts_all_vertices_garbage` is already
known at invocation and the concrete response is forced to be
`TSuccEmpty`.  Prove that no rely step can interleave while the concrete
control is atomic-pending.

### Try-pop response: successful node

For `TSuccNode v owner loc`, let `n = (owner, loc)`.

1. Extract the concrete premise that `n` is top in the saved live
   snapshot and has value `v`.
2. Use the exhaustive schedule invariant to select a nonempty family of
   possibilities in which `actor` atomically popped exactly `n`.  For a
   push that overlaps this pop, select the deferred branch when the pop
   must precede that push, and retain the reflected branch when the push
   may precede it.
3. Filter away unresolved, failed, and differently successful branches.
4. Transfer the concrete garbage update to the surviving branches; those
   branches already contain `n` in abstract garbage.
5. Clear the concrete snapshot, remove `actor` from the schedule protocol,
   and prove the suffix `CanPop` obligations using the schedule-shortening
   lemma.
6. Establish universal agreement on
   `ls_linr ts_trypop (TSuccNode v owner loc)` and return the same result.

The retained lemma `trypop_success_deferred_nonempty` already establishes
nonemptiness for the fixed result.  The remaining work is preservation of
the complete schedule family after filtering.  It must follow the paper's
`Grmv` argument directly:

1. Define the successful-result filter as a subconfiguration of `Delta`
   containing exactly branches whose actor token is
   `ls_linr ts_trypop (TSuccNode v owner loc)` and whose abstract garbage
   already contains the selected node.
2. For an arbitrary post-response schedule `A` and failure set `B`, reason
   about the corresponding pre-response schedules rather than constructing
   an independent historical response order.
3. Decompose a successful pre-schedule as
   `A_prefix ++ (actor,n) :: A_suffix`.  The actor's selected node and token
   identify the branches retained by the filter.
4. Remove `(actor,n)` from that schedule.  The accumulated snapshot seen by
   every member of `A_suffix` only becomes smaller.  Prove once, by induction
   over `A_suffix`, that `lp_top` is preserved when the accumulated snapshot
   shrinks; reuse `can_pop_shrink_accumulated` and its omitted-plan analogue.
5. Remove `actor` from the pending/failure bookkeeping, preserve all other
   tokens with finite-map `gso/gro` lemmas, and rewrite the abstract garbage
   using the plan's exact garbage equation.
6. Show completeness of the filtered configuration for every post schedule
   and failure set.  This is the important branch-correlation obligation:
   the witness must be a member generated for that schedule by `I_pop`, not
   a combination of per-actor permissions.

If the existing `omission_exhaustive_pop` statement does not expose enough
provenance to select the required pre-schedule after filtering, strengthen
its branch witness with the originating schedule decomposition.  Do not
replace it with a shared history map.  The strengthening should remain a
per-schedule existential inside `Delta`, matching the large conjunction in
the paper.

### Try-pop response: failure

1. Select the retained failure branches for `actor`.
2. Show this filter is nonempty even when the saved snapshot was empty.
3. Clear the concrete snapshot without changing concrete garbage.
4. Remove `actor` from the pending/failure schedule bookkeeping and
   establish universal `ls_linr ts_trypop TFail`.

The empty-snapshot case is required by the repository's relaxed
TryStackAux specification; it is absent from the paper's guarded
`trypop-snapshot` rule.

### Try-pop response: empty

This response comes only from the concrete atomic-empty control state.
Use the decision made in its invocation proof, return `TSuccEmpty`, and
restore `TSAReady`.  The snapshot schedule is unchanged because the atomic
branch never installed a snapshot.

## Packaging

1. Define `SActive`, `SCompleted`, and the internal invocation/response
   assertions using `AssertionsSet.ALin`, which requires all surviving
   possibilities to agree on the acting thread's token.
2. Assemble `push_method_triple` and `trypop_method_triple` with
   `RGILogicSet.RGILogic.provable_vis_safe`, `provable_linstep`, and
   `provable_ret_safe`.
3. Apply `SetLogic.soundness` using the established `R`, `G`, and `I`.
4. Package `MTryStack`, derive `MTryStackLinearizable` with `LISim2LILin`,
   and compose `MListPoolTryStack`.

## Differences from the paper outline

| Topic | Paper | Planned Coq proof |
|---|---|---|
| Graph edges | Maintains literal `E = Ep`; push edges ignore garbage. | Matches the paper: all three Coq graph layers now use garbage-independent edges, so the proof maintains literal edge equality. |
| Pending push interval | Treats the abstract placement of an overlapping push implicitly in the possibility family. | Makes the two choices explicit. A deferred possibility omits the live pending node until the concrete push response; a reflected possibility contains it. Exact graph equality is recovered after catch-up. |
| Possibility connective | Uses large separating/speculative conjunctions over permutations and failure sets. | States the semantic closure/completeness property directly on `AbstractConfig`, with explicit finite schedule constructors. |
| Correlation of choices | Each `PopAttempt` is witnessed by one particular possibility in `Delta`. | Preserve the same schedule-indexed witness. Do not factor deferral permissions into a global per-snapshot relation. |
| Underlay operation names | Describes `getT`/removal-style guarantee phases. | Maps them to the invocation and response of the single concrete `tsa_trypop` call. |
| Atomic transitions | Treats atomic try-pop as one transition. | Accounts for `TSAtomicPending` and `TSAAtomicPending`, the Coq two-event encoding, while hiding abstract pending control inside `poss_steps`. |
| Empty snapshot | The paper's TryStackAux snapshot rule is guarded by `dom(V) != g`. | Must also simulate a snapshot invocation followed by `TFail` when all vertices are garbage. |
| Result representation | Writes successful results mostly as `Succ(n)`. | Preserves the Coq result `TSuccNode v owner loc` and proves the vertex lookup supplies `v`. |
| `popAttemptS` recurrence | The displayed recurrence uses `top(N \\ g)` in one place, which conflicts with `CanPop`, the preceding `PopAttempt`, and the successful underlay rule. | Uses the actor's saved set `N' \\ g` together with the accumulated union; records this as an explicit formalization decision. |
| Figure captions | Figures 31 and 32 appear to label the push and try-pop outlines in the opposite order. | Follows the code bodies and surrounding prose, not the captions. |

## Anticipated proof risks

1. **Nonempty response filters.** `AbstractConfig` cannot represent an
   empty possibility set.  Every success/failure/empty filter needs an
   explicit surviving witness.
2. **Completeness, not just soundness, of speculative images.** The generic
   `PStep` relation only constrains retained outputs.  A custom image
   constructor or stronger postcondition is needed to prove that every
   future concrete result remains represented.
3. **Finite-map/list bridge.** The paper quantifies over `dom(S)` as a
   finite set.  Coq uses `PositiveMap` plus function-valued snapshots, so
   enumeration, ownership, `NoDup`, permutation, and map-membership lemmas
   must be made explicit.
4. **Interference during a pending snapshot.** Later pushes and other
   try-pops must preserve the exact schedule branch needed by the eventual
   response.  In particular, an unfinished overlapping push must retain
   both its reflected and deferred possibilities; pointwise reachability
   alone is insufficient.
5. **Two-event atomic encoding.** The invariant and method assertions must
   cover concrete `TSAAtomicPending` states without exposing abstract
   `TSAtomicPending` states to interference.
6. **Freshness across speculative garbage.** Concrete freshness must imply
   abstract freshness in every branch.  This depends on explicitly
   maintaining that every speculative garbage node remains in the common
   vertex domain.
7. **Proof size.** The implementation is tiny, but the exhaustive
   speculation invariant is likely comparable in complexity to the
   possibility-management portions of `ListPoolProof.v`, not to the
   singleton `TryStackAuxProof.v`.
8. **Result-filter completeness.** A witness that merely proves the
   requested successful result exists is insufficient.  After filtering,
   every remaining `CanPop` schedule and failure choice must still have a
   correlated member in the filtered `AbstractConfig`.  Preserve or expose
   schedule provenance if the current existential statement hides it.

## Implementation order and checkpoints

- [x] Align `ListPoolSpec`, `TryStackAuxSpec`, and `TryStackSpec` with the
  paper's garbage-independent push-edge rule.
- [x] Adapt `ListPoolProof.v` and `TryStackAuxProof.v` and run the full
  repository build.
- [ ] Create `TryStackProof.v` with imports, layer aliases, payload
  projections, and theorem signatures.
- [ ] Prove exact, partial, and deferred graph-representation preservation
  and top-transfer lemmas needed by the paper-aligned invariant.
- [ ] Define snapshot enumeration and prove its finite-domain lemmas.
- [ ] Define schedules, `CanPop`, `PopAttempt`, and their `poss_steps`
  soundness lemmas.
- [ ] Define the exhaustive possibility invariant and prove it initially.
- [ ] Define the relational-image `AbstractConfig` constructor and prove
  active-domain, reachability, nonemptiness, and completeness.
- [ ] Define `R` and `G`; prove `ValidRGI`, stability, and parallel
  compatibility.
- [ ] Finish packaging the proved push invocation/response invariant updates
  into `push_method_triple`.
- [ ] Prove snapshot-invocation possibility expansion for `prophecy_I`
  using the paper's schedule split and reflected/deferred push cases.
- [ ] Prove atomic-empty invocation/response invariant handling.
- [ ] Prove successful response filtering and its nonemptiness theorem.
- [ ] Prove failure response filtering, including the empty-snapshot case.
- [ ] Assemble `trypop_method_triple`.
- [ ] Package the simulation and composition theorems.
- [ ] Register the file and run the complete validation suite.

## Validation commands

```text
make examples/TSStack/TryStackProof.vo
make -j2
git diff --check
rg -n "Admitted|admit|Axiom" examples/TSStack/TryStackProof.v
```

Also inspect:

```coq
Print Assumptions MTryStack.
Print Assumptions MTryStackLinearizable.
Print Assumptions MListPoolTryStack.
```

Expected assumptions are only the repository's existing classical and
extensionality principles used to reason about proposition-valued sets and
maps.



# A Misleading Proof Difficulty

Consider the following execution:
1. m is pushed and completes.
2. n starts pushing and remains pending, creating n → m.
3. Pop β snapshots {m,n}.
4. x is pushed and completes. It creates x → m, but no x → n because n is pending.
5. Pop α snapshots {m,n,x} and successfully removes n.
6. β can now return m from its old snapshot, since n is garbage and x is absent from that snapshot.


It might seem that Pop β cannot be linearized. However, since it is concurrent with all operations other than push m, it can be reordered before step 2 in the linearized execution to produce a valid result.
In other word, when constructing the possibility, before the underlay push actually returns, there should have two families where the push has not linearized and it has linearized.