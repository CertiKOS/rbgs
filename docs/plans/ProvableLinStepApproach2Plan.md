# Phased Implementation Plan: Inductive Possibility-Update Steps

## Goal

Implement approach 2 for `provable_linstep`: a possibility update that is
not associated with a concrete program step and is represented by a new
simulation branch at the same semantic level as `Error` and `Continue`.

The completed implementation must satisfy all of the following:

- Possibility-update prefixes are inductive and therefore finite.
- Concrete execution remains coinductive.
- A possibility update changes only the abstract possibility/configuration;
  it does not change the concrete state, concrete program, or trace.
- `Tau` is unchanged and is not used to encode possibility updates. It
  remains the silent concrete-program constructor used by loop rules.
- Existing program-logic rules retain essentially their current statements
  and proof-script interfaces.
- Existing verified examples continue to compile, preferably without source
  changes.
- The new feature is implemented only in the set-based simulation and
  program logic. The older pointwise simulation and logic remain legacy
  compatibility code; they do not receive a second mixed-fixed-point
  implementation.
- Soundness is proved against the existing `CompLin.CompLin` definition of
  linearizability. `CompLin.v`, trace events, and the definition of
  linearizability are not weakened or replaced.

This plan has four phases. Each phase is intended to be one focused working
session and must end at a compilable checkpoint. Do not begin the next phase
until the current phase's acceptance tests pass.

## Fixed design

The intended semantic structure is the mixed fixed point

```text
Simulation = nu X. mu Y. Error + PossibilityUpdate(Y) + Continue(X).
```

In Coq, the initial encoding to test is an inductive head inside a
coinductive wrapper:

```coq
Inductive SimulationHead (X : State -> Prop) : State -> Prop :=
| HeadError ...
| HeadContinue (... continuations returning X ...)
| HeadUpdate s s'
    (Hupdate : ...)
    (Hnext : SimulationHead X s').

CoInductive Simulation (s : State) : Prop :=
| SimulationRoll : SimulationHead Simulation s -> Simulation s.
```

`HeadUpdate` must continue with the inductive `SimulationHead X`, not with
the coinductive `X`. This is what rules out an infinite update-only
cofixpoint, including one made from identity updates.

If Coq's positivity or elimination restrictions make this encoding
unusable, the fallback is an internal natural-number index bounding the
abstract-update prefix. The public simulation should hide that index.

Existing constructors may become internal head constructors plus public
wrapper lemmas. Preserve the names and practical signatures of
`provable_ret`, `provable_vis`, `provable_tau`, and their derived rules so
that existing client proofs using `apply` or `eapply` remain valid.

## Phase overview

| Phase | Session outcome | Main gate |
|---|---|---|
| 1. Semantic kernel | A standalone mixed TPSimulation prototype and trace-soundness proof | Finite updates can be consumed before a return without changing traces |
| 2. Logic vertical slice | Mixed Hoare, method, and sequential RGI prototypes plus an immediate-return test | `provable_linstep`, sequencing, and framing work without Tau |
| 3. Parallel and set promotion | A productive parallel-composition proof and production set-level framework | Abstract-update normalization terminates under interference |
| 4. Compatibility and integration | Singleton facade, legacy build compatibility, soundness audit, and reset-style client test | No regression in examples or the existing linearizability theorem |

## Phase 1: Semantic kernel and trace-soundness prototype

### Scope

Do not replace production definitions in this phase. Add a small prototype
module alongside the current framework so the repository remains fully
buildable even if the mixed encoding needs to change.

### Work

1. Record the clean baseline:

   - `git status --short`;
   - compilation of the core simlin framework;
   - compilation of representative singleton and set examples;
   - the types of `cal_to_CompLin` and `LISim2LILin`.

2. Define a mixed set-level thread-pool simulation using the fixed design.
   Its update payload should reuse the existing condition

   ```coq
   (Delta' ⊆ ac_steps Delta)%AbstractConfig
   ```

   while preserving the concrete state and concrete pool.

3. Prove a normalization lemma: every rolled simulation contains a finite
   update prefix ending in `Error` or `Continue`.

4. Prove the prototype analogue of `TPSimulation_abs_reaches`. Before
   consuming each concrete trace step, induct over the finite head:

   - update: emit the existing `AbsStepSteps` and continue with the same
     concrete trace step;
   - error: use the existing error-prefix argument;
   - continue: use the existing invocation, return, visible-step, Tau, and
     no-error cases.

5. Add a focused semantic test in which the concrete pool can return
   immediately, but the current abstract configuration is not yet in
   `ls_linr`. The mixed simulation must first take an update and then use
   the unchanged return condition.

### Acceptance tests

- The prototype compiles with no `Admitted` or new axioms.
- A finite-prefix/normalization theorem is available.
- An identity update is allowed but cannot form an infinite proof by itself.
- The immediate-return trace is matched as

  ```text
  Delta --AbsStepSteps--> Delta' --AbsStepRet--> ac_res Delta' t.
  ```

- The possibility update contributes no `TEvent`, `TErr`, concrete `ustep`,
  or concrete `taustep`.
- Existing production files and examples still compile unchanged.

### Go/no-go rule

Proceed only if Coq accepts a usable mixed encoding and the trace-soundness
proof needs no fairness, productivity, or trace-definition changes.

## Phase 2: Program logic through sequential RGI simulation

### Scope

Build a complete mixed vertical slice under prototype names. Keep the old
public framework active until parallel composition has been proved in Phase
3. This keeps the repository compilable throughout the session.

### Work

1. Add the mixed form of the set-level `HTripleProvable` to the prototype.
   Add the public rule

   ```coq
   provable_linstep :
     (⊨ P' ==>> I) ->
     Stable R I P' ->
     (G ⊨ P ⭆ P') ->
     HTripleProvable P' p Q ->
     HTripleProvable P p Q.
   ```

   The program `p` is identical on both sides, and the rule must not mention
   or construct `Tau`.

2. Provide compatibility wrappers for the old primitive rules. Existing
   proofs should still be able to write `eapply provable_ret`, `eapply
   provable_vis`, and `apply provable_tau` once the prototype is promoted.

3. Reprove the structural rules by induction through the abstract-update
   head and coinduction through concrete continuations:

   - weak precondition and weak postcondition;
   - combined consequence;
   - `provable_seq`;
   - loop rules;
   - frame and frame-context rules.

4. Pay special attention to `provable_seq`. If the left computation starts
   with an update, the bound computation must retain that update even when
   `bindProg (Ret a) k` reduces to `k a`.

5. Add mixed `MethodSimulation` and sequential `RGISimulation` prototypes.
   Map `provable_linstep` to a simulation update node while keeping the
   concrete state, program, and pending operation unchanged.

6. Prove the mixed analogue of `logic_soundness` through method simulation,
   and the single-thread/sequential RGI construction. Parallel composition
   is deliberately deferred to Phase 3.

7. Add an immediate-return program-logic test:

   - concrete body: `Ret tt`;
   - precondition: the operation is active as `ls_inv`;
   - `PUpdateId` performs the abstract operation and establishes `ls_linr`;
   - ordinary `provable_ret` closes the method;
   - no Tau is inserted into the implementation or proof.

### Acceptance tests

- Zero, one, and two consecutive `provable_linstep` rules compile.
- `provable_linstep` works before `Ret` and `Vis`.
- `provable_seq` preserves updates across definitional reduction of bind.
- Both frame rules use the existing `PUpdateId_frame` infrastructure.
- The immediate-return method reaches a method-simulation return core only
  after the abstract update.
- All existing production examples still compile because the prototype has
  not replaced the public definitions yet.

## Phase 3: Parallel composition and production set-level promotion

### Scope

This is the decisive feasibility phase. First prove productive parallel
composition for the prototype. Only after that proof succeeds, replace the
production set-level definitions in `TPSimulationSet.v`,
`RGISimulationSet.v`, and `RGILogicSet.v`.

### Parallel-composition problem

A global `TPSim_Continue` must be ready for any enabled concrete return. It
therefore cannot leave an active returning thread behind an abstract-update
prefix. Normalizing threads naively can ping-pong: an update by thread A is
rely interference for B, and B's stability proof could reintroduce an
update prefix already removed from B.

The implementation must make this impossible by construction or by a
proved non-growth property. The preferred solution is an internal
update rank:

- taking an update strictly decreases the actor's rank;
- rely stability preserves or decreases every other thread's rank;
- concrete continuations may start with a new finite rank;
- the normalization measure is the sum of ranks for the finite set of
  active threads.

If a rank is unnecessary because the chosen head representation provides
an equivalent structural measure, document and prove that measure instead.

### Work

1. Strengthen or index mixed RGI stability so that rely interference cannot
   increase the remaining abstract-update prefix.

2. Prove finite active-pool normalization:

   ```text
   per-thread mixed simulations
       -> finite global possibility-update prefix
       -> all active threads expose Error or Continue cores.
   ```

3. Test normalization with:

   - one updating active thread;
   - two updating active threads;
   - one updating and one already-normalized thread;
   - an update that is the identity on abstract state;
   - a fresh invocation on a thread absent from the current pool.

4. Reprove mixed `rgisim_parapllel_composition` and connect it to the mixed
   TPSimulation from Phase 1.

5. Promote the successful set-level prototype into the production modules:

   - remove the old conjunctive `msim_linstep`, `rgisim_linstep`, and
     `tpsim_linstep` fields;
   - install the inductive update branch;
   - expose old constructors/rules through compatibility lemmas;
   - expose `provable_linstep` as the new rule;
   - adapt `CompLinSound.v` to the production mixed TPSimulation;
   - adapt the singleton-to-set bridge only where its target set-simulation
     constructors changed.

6. Compile the complete set-level dependency chain and all set-level
   examples, especially `IndexedFamilyProof.v`, `SPListProof.v`,
   `EBStackSepProof.v`, and `FAISet.v`.

### Acceptance tests

- Parallel normalization terminates by an explicit inductive measure.
- An adversarial stability construction that increases update rank
  is rejected or cannot satisfy the simulation interface.
- No fairness assumption is introduced.
- The production set-level `soundness`, `cal_to_CompLin`, and
  `LISim2LILin` theorems compile.
- Their conclusions still use the unchanged `CompLin.CompLin`.
- Existing set-level examples compile with no semantic proof changes.

### Go/no-go rule

If rank-preserving stability cannot be derived from the existing
rely/guarantee discipline or enforced internally while retaining existing
examples, stop here and document the missing assumption. Do not replace
the inductive branch with an ordinary coinductive update constructor; that
would admit infinite identity-update simulations and invalidate the
intended soundness argument.

## Phase 4: Singleton facade, complete regression, and integration

### Scope

Expose the validated set-level rule through the singleton assertion facade,
remove temporary prototype code, and run the complete compatibility and
soundness audit. Do not implement mixed simulation or mixed Hoare logic a
second time in the legacy pointwise modules.

### Work

1. Add `singleton_provable_linstep` (and a tactic-facing wrapper if useful)
   to `SingletonPossibility.v`. It should lift the singleton `PUpdateId`
   premise and construct the new set-level `provable_linstep` rule, just as
   the existing singleton `Vis` and `Ret` facade rules construct set-level
   proofs.

2. Leave `RGISimulation.v` and `RGILogic.v` unchanged. Leave their old
   pointwise simulations, logic, and verified clients intact.

3. Change `TPSimulation.v` only if required to repair its
   `TPSimulation_singleton_lift` compatibility proof after the target
   `TPSimulationSet` constructors change. This is an adapter repair, not a
   pointwise implementation of the new update branch.

4. Preserve the old public rule statements and tactic-facing names. Add
   small API checks for all primitive, safe, sequencing, loop, frame,
   method, and top-level soundness rules.

5. Compile the complete `_CoqProject`, with particular attention to:

   - TicketDispenser and TicketLock;
   - TreiberStack, TryStack, and EBStack;
   - LazyCoin;
   - CCAS and CASTask;
   - Exchanger;
   - FAI and FAISet;
   - IndexedFamilyProof;
   - SPListProof and SPListFamily.

6. Convert the Phase 2 immediate-return example into a permanent regression
   test. Then use the same rule shape for the SPListArray reset adapter:

   ```text
   Ret tt
     with provable_linstep establishing the abstract reset result
     followed by the unchanged pure provable_ret rule.
   ```

7. Audit the final soundness boundary:

   - no changes to `CompLin.v` or the definition of linearizability;
   - abstract updates map only to finite `AbsStepSteps` prefixes;
   - Tau maps only to concrete `taustep` behavior;
   - no new `Admitted`, axioms, or fairness hypotheses;
   - inspect `Print Assumptions` for `cal_to_CompLin` and `LISim2LILin`.

8. Remove obsolete prototype definitions and update this document with the
   final theorem names, test targets, and any mechanical client changes.

### Acceptance tests

- The full repository build succeeds.
- Existing verified examples remain valid; any source edits are limited to
  mechanical name qualification and are documented.
- The permanent regression test proves an abstract update before an
  immediate concrete return without Tau.
- Identity updates are usable as derived rules but are not required by old
  proofs.
- The final implementation proves the same public linearizability theorem
  as before.

## Files expected to change

Production changes should remain concentrated in:

- `models/simlin/TPSimulationSet.v`
- `models/simlin/RGISimulationSet.v`
- `models/simlin/RGILogicSet.v`
- `models/simlin/SingletonPossibility.v`
- `models/simlin/CompLinSound.v`
- `_CoqProject` for any permanent regression module

`models/simlin/TPSimulation.v` may need a small compatibility-only change to
`TPSimulation_singleton_lift`, because it translates a legacy pointwise
simulation into the set simulation whose constructors are changing. It is
not otherwise in scope. `RGISimulation.v` and `RGILogic.v` are explicitly
out of scope.

`Assertion.v` already contains `PUpdateId`, consequence, composition, and
frame lemmas. Extend it only if the implementation exposes a genuinely
missing stability or rank-preservation lemma.

## Explicit non-goals

- Do not encode the new update rule with Tau.
- Do not add an updateful primitive `provable_ret`; the new rule composes
  before the existing pure return rule.
- Do not weaken the return condition in the final simulation.
- Do not change the trace or linearizability definitions.
- Do not treat successful reset verification as a complete SPListArray
  proof. The separate timestamp-order versus row-order specification issue
  must still be resolved independently.

## Session handoff discipline

At the end of each phase:

1. ensure the scoped build target succeeds;
2. ensure no new `Admitted` remains;
3. update the phase status and record exact theorem/test names here;
4. record any changed public signatures;
5. leave the worktree in a state from which the next phase can start without
   reconstructing experimental results.

Current status: **Phases 1 through 4 complete**.

### Phase 1 handoff

- Prototype (retired after production promotion): `TPSimulationMixed.v`.
- The direct inductive-head encoding compiled for the thread-pool kernel.
- Normalization: `head_normalizes`, `simulation_normalizes`.
- Trace soundness: `TPSimulation_abs_reaches`.
- Immediate-return regression: `immediate_return_after_update_test`.
- Production modules and the linearizability definition remain unchanged.

### Phase 2 handoff

- Prototypes (retired after production promotion): `RGILogicMixed.v` and
  `RGISimulationMixed.v`.
- The prototype regression target `RGILogicMixedTests.v` was replaced by
  the permanent production target `RGILogicSetTests.v` in Phase 4.
- Coq's guarded-elimination restriction prevented structural program-logic
  proofs from eliminating an inductive head between a cofixpoint and its
  recursive calls.  The public logic and RGI prototypes therefore use the
  documented fallback: a hidden finite `UpdateChain`/`AbstractUpdateSteps`
  prefix
  packaged with one coinductive concrete core.  This still implements
  `nu X. mu Y` and rules out infinite update-only proofs.
- Public update rule: `provable_linstep`, with the planned signature and no
  `Tau` premise or construction.
- Structural rules: `provable_conseq_weak_pre`,
  `provable_conseq_weak_post`, `provable_conseq_weak`, `provable_seq`,
  `provable_dowhile_unroll`, `provable_dowhile`,
  `provable_doloop_data`, and `provable_doloop`.
- Frame rules: `provable_frame_same_context` uses `PUpdateId_frame`;
  `provable_frame` uses `PUpdateId_frame_context`.
- Simulation normalization: `method_simulation_normalizes` and
  `rgi_simulation_normalizes`.
- Soundness/composition: `logic_soundness` and
  `msim_sequential_composition`.  Parallel composition remains deferred.
- Focused tests: `zero_updates`, `one_update`, `two_updates`,
  `update_before_ret`, `update_before_vis`, `update_survives_bind_ret`,
  `immediate_return_no_tau`, and
  `immediate_method_reaches_mixed_simulation`.

### Phase 3 handoff

- Production promotion: `TPSimulationSet.v`, `RGISimulationSet.v`, and
  `RGILogicSet.v` now use finite abstract-update prefixes; the old
  conjunctive `tpsim_linstep`, `rgisim_linstep`, and `msim_linstep` fields
  are absent.
- Ranked interfaces: `MethodUpdateSteps`, `RGIUpdateSteps`,
  `MethodSimulationRanked`, and `RGISimulationRanked`.  Outer rely
  stability explicitly returns a rank no greater than its source rank, so
  an adversarial rank-increasing stability witness cannot inhabit the
  interface.
- Finite-pool normalization: `normalize_thread_list` is structurally
  recursive on the finite active-thread list and consumes each thread's
  finite update derivation; `normalize_active_threads` packages
  the resulting all-core state.  Absent threads have rank zero, including
  fresh invocations.
- Productive parallel composition: `rgisim_parapllel_composition`, using
  the sole production constructor `TPSimRoll`.  It carries the normalized
  finite `AbstractUpdateSteps` prefix and its terminal error/continue core
  directly,
  so the parallel recursive calls are syntactically guarded.  No fairness
  premise was added.
- Production logic and soundness: `provable_linstep`, `logic_soundness`,
  `soundness`, `TPSimulation_abs_reaches`, `cal_to_CompLin`, and
  `LISim2LILin` compile, and the final conclusion remains
  `CompLin.CompLin`.
- Compatibility: `TPSim_Error`, `TPSim_Continue`, `TPSim_Update`,
  `TPSim_Head`, and `TPSim_to_Head` expose the production thread-pool
  constructors/rules and both directions of the declarative inductive-head
  view; `provable_vis` and
  `provable_tau` remain transparent guarded wrappers for existing cofixed
  client proofs.  `MethodProvable` retains its prior public argument order.
- Terminology cleanup requested during promotion renamed finite-prefix APIs
  from `Admin` to `AbstractUpdateSteps`, `MethodUpdateSteps`,
  `RGIUpdateSteps`, and `UpdateChain`; auxiliary rely names in
  `Assertion.v` were likewise changed from `Admin`/`Administrative` to
  `Auxiliary`/`Linearization`.  The five corresponding edits in
  `SPListProof.v` are mechanical name updates only.
- Acceptance build targets: `PaperTheorems.v`, `CompLinLayer.v`,
  `IndexedFamilyProof.v`, `SPListProof.v`, `EBStackSepProof.v`, and
  `FAISet.v`.  All compile without semantic proof changes and without new
  `Admitted` declarations.
- `immediate_return_no_tau` has the concrete body `Ret tt`; its
  `PUpdateId` premise changes `ALin t (ls_inv f)` to
  `ALin t (ls_linr f ret)` before the ordinary return rule.
- No production public signature changed in Phase 2.  The legacy
  pointwise files and all production set-level modules remain unchanged.

### Phase 4 handoff

- Singleton facade: `singleton_provable_linstep` lifts pointwise
  `PUpdateId` into the production set logic; the tactic-facing entry points
  are `singleton_linstep P'` and `singleton_linstep P' using stableDB`.
- Permanent production regression: `RGILogicSetTests.v`, including
  `zero_updates`, `one_update`, `two_updates`, `update_before_ret`,
  `update_before_vis`, `update_survives_bind_ret`,
  `immediate_return_no_tau`, and
  `immediate_method_reaches_simulation`.  The same module checks the public
  primitive, safe, consequence, sequencing, loop, frame, method-soundness,
  top-level-soundness, and singleton-facade rule names.
- SPListArray reset adapter: `SPListArrayProof.resetIter_adapter` proves the
  literal `resetIter_impl = Ret tt` by first applying
  `singleton_provable_linstep` to establish the abstract reset response and
  then applying the unchanged `singleton_provable_ret_safe`.  This is only
  the reset adapter; it does not discharge the independent timestamp-order
  versus row-order obligation for a complete SPListArray refinement proof.
- Prototype files `TPSimulationMixed.v`, `RGISimulationMixed.v`,
  `RGILogicMixed.v`, and `RGILogicMixedTests.v` were removed from the
  worktree and `_CoqProject`.
- Public additions are `singleton_provable_linstep`, `singleton_linstep`,
  `RGILogicSetTests` regression lemmas, and `resetIter_adapter`.  Existing
  public theorem statements were preserved; `RGISimulation.v`,
  `RGILogic.v`, `CompLin.v`, and the linearizability definition were not
  changed.
- Acceptance audit: the complete `_CoqProject` builds; no new `Admitted`,
  axiom, fairness hypothesis, or semantic client edit was introduced.
  `Print Assumptions` reports both `cal_to_CompLin` and `LISim2LILin` closed
  under the global context.
