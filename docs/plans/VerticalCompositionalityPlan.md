# Proof Plan: Vertical Compositionality of `CompLin` (Lemma 4.3)

Target: `CompLinVComp.v`, module `CompLinVComp.VComp`, lemma `CompLin_vcomp`
(currently `Admitted`):

```coq
Lemma CompLin_vcomp
    {E F G : Op.t}
    {VE : @LTS E} {VF : @LTS F} {VG : @LTS G}
    (M1 : ModuleImpl E F) (M2 : ModuleImpl F G)
    (sigma0 : State VE) (rho0 : State VF) (tau0 : State VG) :
  CompLin M1 sigma0 rho0 ->
  CompLin M2 rho0 tau0 ->
  CompLin (M1 ▶ M2) sigma0 tau0.
```

Scope decision: this proof works **directly on the trace semantics of
`CompLin.v`** (`ImplTraces`/`ImplTracesClosed`/`CompLin`), independent of the
`TPSimulationSet`/`AbstractConfig` machinery in `Compositionality.v`. That
file already contains a complete, ~950-line vertical-compositionality proof
for the older, simulation-based `TPSimulation` notion (`VCompTPSim`), plus an
unfinished port to the Set-based `AbstractConfig` version
(`VCompTPSimSet.vcompSim`, currently `Admitted`). We deliberately do **not**
build on that file: it proves compositionality of a different (stronger,
simulation-witnessed) correctness notion, and bridging it back down to
`CompLin`-level hypotheses would additionally require the unproven
"completeness" direction of Lemma 5.3 (`CompLin ⟹ cal`). The plan below
re-derives everything needed directly against `CompLin`, from scratch.

## Relation to LHL (`ehatti/LHL`)

The user pointed at [LHL](https://github.com/ehatti/LHL), which proves
vertical compositionality of linearizability by first establishing an
*observational refinement* principle and composing it with associativity of
layering. Reading `Core/{Specs,Linearizability,VCompFacts,RefinesFacts,LinFacts}.v`
confirms this and gives a direct template for our proof.

### LHL's decomposition

LHL's `Spec T E` is an arbitrary (thread-locally well-formed) labeled
transition system. `overObj (spec :> impl) : Spec T F` is the object built by
running `impl` over `spec` and hiding underlay events — critically, it has
the *same type* as any hand-written spec, so it can be recursively fed into
another `overObj`. Their vertical-compositionality theorem `vcomp_lin` is a
short proof built from four independent facts:

| LHL lemma | Role |
|---|---|
| `layerRefines_trans` / `specRefines_trans` | trivial transitivity of trace inclusion |
| `mkLayer_monotonic` | `overObj(_ :> impl)` is monotonic in its underlying spec w.r.t. trace refinement |
| `layerRefines_VComp_assoc` / `_inv` | `overObj(spec :> impl\|>impl') ≡ overObj(overObj(spec:>impl) :> impl')` (the hard part — described in their own comments as the trickiest proof in the file, needing explicit `assoc_states`/`assoc_traces` witnesses to realign two independently-generated traces) |
| `eutt_layerRefines` + `idImpl_is_identity_l` | the copy-cat implementation is a `\|>`-identity up to weak bisimulation |

These combine into `lin_obs_ref`: *if the bottom layer linearizes to spec
`VF`, then any client stacked on the concrete bottom layer observationally
refines the same client stacked on the abstract `VF`*. `vcomp_lin` itself is
then: `assoc_inv`, then `lin_obs_ref` (using the first linearizability
hypothesis), then the second hypothesis, chained by transitivity.

### How this maps onto our development, and where it helps

Our `LTS` record (`Step`/`Error` as bare relations, no proof obligation) is
exactly as unconstrained as LHL's `Spec`, so the same trick — packaging a
"composed object" as a first-class value of the same type as a primitive
library — transplants directly. Concretely:

- LHL's `overObj (spec :> impl)` ↦ our new derived object `compLTS VE M1 :
  @LTS F` (defined below). Building this was the one design question left
  open in the earlier planning pass, and LHL's construction (visible event +
  hidden-underlay-closure, packaged as an ordinary transition system) is
  exactly what resolved it.
- LHL's `mkLayer_monotonic` ↦ our `ImplTraces_lib_mono`: a *generic*
  precongruence lemma (holds for **any** `ModuleImpl E F` and any two
  `@LTS E` values related by trace-refinement) — this is the real content of
  "observational refinement" and is the piece our codebase was missing
  entirely; nothing like it exists yet even for horizontal composition.
- LHL's `layerRefines_VComp_assoc[_inv]` ↦ our `vcomp_decompose`: the
  hardest lemma either way, in both developments. LHL needs bespoke
  `assoc_states`/`assoc_traces` realignment witnesses because their traces
  are untyped lists; our `CompLinHComp.v` already had to solve an analogous
  "realign an interleaved trace against two independently-stepping
  components" problem for horizontal composition (see
  `trace_steps_single_growth_split`, `hpools`), so we reuse that
  proof *technique* (not code) via a fresh three-way pool invariant
  `pools_vcomp`/`thread_vcomp`, playing the role of LHL's realignment
  witnesses.
- LHL's `eutt_layerRefines`/`idImpl_is_identity_l` step ↦ **not needed as a
  separate lemma** in our setting. Because our `compLTS` is defined by
  *literally unfolding* `M1`'s own `trace_step` relation (rather than via a
  general coalgebraic `overObj` requiring a separate identity-up-to-weak-
  bisimulation argument), the fact that "the copy-cat over `compLTS` is
  M1's own semantics" is provable as a direct, low-risk unfolding lemma
  (`compLTS_id_correct`) instead of a coinductive bisimulation proof. This
  is a simplification LHL's more general `Spec`/`Prog` setup doesn't get for
  free, but our closer coupling between `ModuleImpl` and `trace_step` does.

So LHL's role in this plan is less "supplies a lemma we import" and more
"supplies the right *shape* of decomposition" — in particular, it told us
(a) that a derived/composed spec object of the same type as a primitive one
is the right abstraction to reach for, (b) that monotonicity-in-the-
underlying-library needs to be proved as its own generic, reusable lemma
rather than inlined into the final proof, and (c) exactly which four facts
compose into the final theorem, which lets us budget effort (the
associativity/decompose lemma is the one genuinely hard piece; everything
else is comparatively mechanical).

## New object: `compLTS` (STATUS: implemented, compiles — `models/simlin/CompLinVComp.v`)

```coq
Definition compLTS {E F} (VE : @LTS E) (M : ModuleImpl E F) : @LTS F :=
  {| State := State VE * ThreadPoolState E F;
     Step  := compStep VE M;
     Error := compError VE M |}.
```

**Correction from the original plan.** The first version of `compStep`
bundled a silent closure *before* the visible event uniformly for both
invocation and return. That is unsound: a trace can legitimately be observed
stopping right after an invocation event, before any of `M`'s internal
computation for it has run — so "silent closure, then the visible event"
cannot be the right shape for invocation. The fix, now implemented:

- `compStep VE M (t, InvEv op) X Y` — **pure bookkeeping**, no closure at
  all: unconditionally available whenever `TMap.find t (snd X) = None`,
  landing at `X` with `t` added running `M op t` fresh (mirrors `invstep`
  directly). This matches how a fresh call is recorded "for free" the
  instant it's issued — the real vertical composite's own `substProg`
  unfolds `Vis m k` to `Tau (bindSubstProg ...)` in exactly one
  unconditional silent step, with no semantic content attached yet.
- `compStep VE M (t, ResEv op r) X Y` — bundles the *entire* internal
  computation: arbitrary `csilent_steps` (silent `VE`-level closure) from
  `X` to some `X'`, then exactly one `trace_step` from `X'` producing
  `TEvent (t, ResEv op r)` (i.e. `M`'s own `TraceStepRet`). This is sound
  because a completed return is only ever exposed once `M` has actually
  finished computing it — there is no "stops early" case to worry about.
- `compError VE M (t, InvEv op) X` — after `csilent_steps` to some `X'` with
  thread `t` idle, immediately invoking `op` leads via **one** further
  `trace_step` straight to `TErr op` — matching the one-shot-oracle shape
  `Error` has everywhere else in this development.

### A second gap found (now resolved): reordering

Attempting `compLTS_id_correct` (below) surfaced a second real issue.
Reconstructing an `M`-level trace from a given `idImpl`-over-`compLTS`
derivation isn't a verbatim replay: `M`'s completion of one thread's
operation can become available, deep inside the derivation, at a
chronological point *earlier* than some other, unrelated thread's
invocation event that nonetheless appears *earlier* in the target trace.
Naively reacting to information as soon as it's available reorders items
relative to the target trace.

The fix is a genuine new piece of infrastructure, now proved and compiling:
bookkeeping-only invocation entries for a thread untouched by a given
`csilent_steps` run commute freely with that run, in either direction. This
is what lets `M`'s internal, per-thread-independent silent computation be
repositioned relative to unrelated threads' invocation bookkeeping when
reconstructing a target order.

- `tmap_add_add` — `TMap.add i x (TMap.add j y m) = TMap.add j y (TMap.add i x m)`
  for `i <> j`. Proved directly by induction on `PositiveMap.add`'s own
  recursive structure (no map-extensionality axiom needed: keys with a
  different leading bit land in different `Node` fields and commute "for
  free" by unfolding; keys sharing a leading bit recurse via the IH).
- `csilent_step_dom_preserved` / `csilent_steps_dom_preserved` — a
  `csilent_step(s)` run never changes whether an untouched thread's key is
  present.
- `csilent_step_add_extra` / `csilent_steps_add_extra` — the reordering
  lemma itself: if `t2` is absent both before and after a `csilent_step(s)`
  run, the *same* run is still valid with `t2`'s entry present (any value)
  throughout, added at either end.

These are the load-bearing tools `compLTS_id_correct`/`vcomp_decompose` will
build on; `csilent_step`'s restriction to `TraceStepU`/`TraceStepTau`
(everything that doesn't grow the trace) is exactly what keeps this lemma
to `TMap.add`/`TMap.add` commutation and avoids also needing an
`add`/`remove` commutation fact (which `TraceStepRet` would otherwise pull
in).

## PIVOT: `compLTS` abandoned for the main proof

Attempting `compLTS_id_correct` traced the reordering gap to its root cause:
it's an artifact of routing through an *independently-generated*
`idImpl`-over-`compLTS` derivation, which imposes its own invocation/return
ordering with no guarantee of matching the real composite's chronological
order. `compLTS`/`compStep`/`compError` and the reordering lemmas
(`tmap_add_add`, `csilent_step(s)_add_extra`) all compile and are correct,
but are **not used by the plan below** — they package "M1 over VE" as an
independently, out-of-order-queryable object, which is exactly the
capability that isn't needed once the proof works directly against the real
derivation. Left in the file as validated-but-currently-unused
infrastructure rather than deleted, in case a later snag makes them useful
again.

## Revised plan: direct two-pass argument (STATUS: in progress)

No `compLTS`. Work directly against a given
`trace_steps (M1 ▶ M2) (mkTraceConfig nil sigma0 ∅) (mkTraceConfig s sigma_f c_f)`.

1. **`pools_vcomp`/`thread_vcomp`** (STATUS: done, compiles) — a three-way
   pool-splitting invariant relating, per thread: the composite's own
   `ThreadState E G` (running `substProg t M1 (M2 g t)`-shaped programs),
   `M2`'s shadow `ThreadState F G` (as if `M2` ran directly over an abstract
   F-level library), and `M1`'s own in-flight `ThreadState E F` bookkeeping.
   Vertical-stacking analogue of `hpools` in `CompLinHComp.v`, rederived
   fresh (not reusing `Compositionality.v`'s `thread_comp`, which
   additionally threads speculative `LinState` bookkeeping this proof
   doesn't need — it works with concretely-completed values, not
   speculative linearization points). Also needed, and now proved: six
   `substProg`/`bindSubstProg` CoFixpoint-unfolding equations
   (`substProgVis`/`Ret`/`Tau`, `bindSubstProgVis`/`Ret`/`Tau`) plus two
   corollaries (`substProg_ret_inv`, `bindSubstProg_not_ret`) — standard
   `PPid`/`PP` boilerplate, needed to recognize exactly when a composite
   thread's step crosses an F-level invocation/return boundary.

2. **Pass 1 — extract `m`** (STATUS: error-free fragment done and `Qed`'d —
   `vcomp_pass1_step` + `vcomp_pass1_clean` in `CompLinVComp.v`): induction
   on the given `trace_steps (M1 ▶ M2)` derivation, maintaining
   `pools_vcomp`, recording into a growing `Trace F` every F-level operation
   `M1` actually completes (a `TVC_Idle -> TVC_Mid -> ... -> TVC_Idle` round
   trip for some thread), in the order it actually completes —
   self-consistent by construction, confirmed no reordering risk in
   practice. All four non-error `trace_step` cases of the composite are
   proved:
   - `TraceStepInv`/`TraceStepRet` (composite's own G-level bookkeeping):
     contribute nothing to `m`; `M1`'s pools are untouched.
   - `TraceStepU` (`M1`'s own underlay calls, embedded via `ts_step`'s
     `ts_inv`/`ts_res` inside `bindSubstProg`): replayed as the
     *analogous* `M1`-level `ts_step`, reusing the same underlying
     `Step VE`/`ts_step` witness with the overlay tag swapped from the
     composite's `g` to `M1`'s own in-flight F-op tag — contributes a
     single silent (trace-preserving) `M1` step, nothing added to `m`.
   - `TraceStepTau` (the `substProg`/`bindSubstProg` Tau-unfold boundary):
     this is where `m` actually grows. Splits into the four semantically
     meaningful sub-cases (`TVC_Idle` with `p = Vis m k` → F-op invocation,
     recorded as `TEvent (InvEv m)`; `TVC_Mid` with `u = Ret r` → F-op
     completion, recorded as `TEvent (ResEv m r)`; plus two "nothing
     happens to `M1`" sub-cases — `TVC_Idle` with `p = Tau _` is pure
     `M2`-level silent progress, `TVC_Mid` with `u = Tau _` is pure
     `M1`-internal silent progress) plus two structurally-impossible
     sub-cases (`TVC_Idle` with `p = Ret _`, `TVC_Mid` with `u = Vis _ _`)
     discharged via `substProg_ret_inv`/`bindSubstProg_not_ret`/
     `substProg_not_vis`/`bindSubstProg_not_ret`.
   - `TraceStepError`: **done**. The composite erroring (an `M1`-internal
     underlay call, embedded in a `TVC_Mid` state, hitting `Error VE`)
     translates directly to an analogous `M1`-level `TraceStepError`,
     reusing the same `Error VE` witness under `M1`'s own in-flight F-op
     tag (same technique as the `TraceStepU`/`ts_inv` case). `vcomp_pass1`
     (renamed from `vcomp_pass1_clean`) now returns the full two-outcome
     disjunction — clean witness, or `m1_reaches_error` — and is `Qed`'d
     with **zero remaining admits**. Pass 1 is complete.

3. **Apply `CompLin M1 sigma0 rho0`** to the now-fixed, fully-known `m`
   (STATUS: trivial once 2 exists): a single hypothesis application,
   producing a witnessing `idImpl`-over-`rho0` run for `m` (or an
   earlier-erroring prefix).

4. **Pass 2 — build M2's shadow run** (STATUS: not started): walk the *same*
   derivation again, in the *same* order, advancing `M2`'s shadow F,G-pool
   (via `pools_vcomp`) in lockstep with peeling items off the fixed witness
   from step 3 (one item per `TVC_Idle -> TVC_Mid` / `TVC_Mid -> TVC_Idle`
   transition pass 1 already located). Concludes `ImplTraces M2 rho0 s`
   (up to the usual closure).

5. **Assembly — `CompLin_vcomp`**: chain step 4's conclusion through
   `CompLin M2 rho0 tau0`. Should be short once 2–4 exist.

Honest scope note: steps 2 and 4 are each comparable in size to
`CompLinHComp.hcomp_decompose` (a large, load-bearing induction) or to the
relevant slice of the `Compositionality.v` `vcompSim_gen` proof this
development is deliberately not reusing. This is a multi-session effort;
treat the status markers above as the source of truth for what's actually
proved versus planned.

## Remaining work (as of this checkpoint) — Pass 1 is fully done; here's Pass 2

**Applying `CompLin M1`** (step 2 of the original 4-item list) turns out to
be entangled with Pass 2's own structure, not a separate step done first:
`CompLin M1 sigma0 rho0` applied to `vcomp_pass1`'s clean-branch `m` (or to
its `m1_reaches_error` witness) itself returns `ImplTracesClosed idImpl
rho0 m` — *itself* a two-outcome disjunction (exact realization, or errors
at some earlier F-prefix `p` of `m`). Both the "errors at `p`" outcome of
*this* disjunction and `vcomp_pass1`'s own `m1_reaches_error` outcome feed
into the *same* downstream argument: "Pass 2, given an `idImpl`-over-`rho0`
witness for some prefix of `m` (complete or not), builds the corresponding
`M2`-level prefix of `s` (complete, or ending in a `M2`-level error)." So
Pass 2 needs its own two-outcome disjunction, symmetric to Pass 1's.

**Pass 2's relational machinery is different from Pass 1's**, and is the
next real design/proof task:

- Pass 1 needed `pools_vcomp M1 (tc_pool X) cFG cEF`, relating the
  composite's *real* pool to `M1`'s bookkeeping (`cEF`) via the fact that
  the composite's own Prog literally *is* `substProg`/`bindSubstProg`
  applied to `M1`. That relationship is unchanged and still needed in Pass
  2 to identify F-level boundary crossings (still `pools_vcomp M1 (tc_pool
  X) cFG cEF` — reuse `thread_vcomp`'s existing case split, not a new
  version of it).
- Pass 2 additionally needs to relate `cFG` (specifically, which threads
  are currently pending on which F-op, from `ts_pend`) to `cabs` — the
  *separate*, independently-evolving pool of the *given, fixed*
  `idImpl`-over-`rho0` witness being consumed. Unlike `cEF` (which tracks
  `M1`'s real `Prog E` continuation), `cabs`'s shape is fully determined by
  `idImpl`'s trivial `Vis m (fun v => Ret v)` body — this is exactly the
  role `CompLinSound.v`'s `LinState`/`linstate_to_ts`/`pool_matches_lin`
  already play (relating a linearization-state abstraction to a concrete
  `idImpl`-driven pool). Reusable directly (`CompLinSound.v`, not
  `Compositionality.v`, so it's in scope) rather than reinventing.
- The witness itself should be threaded as "the *remaining*, not yet
  consumed, portion of a fixed complete run": a hypothesis of shape
  `trace_steps idImpl (mkTraceConfig consumed rho_cur cabs_cur) (mkTraceConfig full rho_final cabs_final)`,
  peeled one item at a time via `trace_steps_single_growth_split`
  (`CompLinHComp.v`, already generic and reusable) exactly when
  `pools_vcomp`'s own case split identifies an F-level boundary crossing —
  the same trigger points already fully enumerated by Pass 1's proof (the
  `TraceStepTau` sub-cases: `TVC_Idle`/`Vis` → consume an `Inv` item,
  `TVC_Mid`/`Ret` → consume a `Ret` item).
- Structurally this should mirror Pass 1's case analysis closely (same
  five `trace_step` constructors, same `TVC_Idle`/`TVC_Mid` split, same
  four `TraceStepTau` sub-cases) but built and proved fresh, since the
  *payload* differs (consuming + building `M2`'s trace_step, rather than
  producing `M1`'s).

Once Pass 2 exists (as a `vcomp_pass2` mirroring `vcomp_pass1`'s two-outcome
shape), assembling `CompLin_vcomp` is: Pass 1 → `CompLin M1` → Pass 2 →
`CompLin M2` → done, chaining the four two-outcome disjunctions via
`CompLinSound.trace_snoc_prefix`-style closure transitivity (small, direct
once the pieces exist).

## Superseded: original `compLTS`-mediated lemma roadmap (kept for reference, not being pursued)

1. **`compLTS_id_correct`** (linchpin, STATUS: not yet proved — this is where
   the reordering gap above was found, and turned out meaningfully harder
   than "definitional unfolding"):
   only the direction actually needed downstream is required —
   `ImplTraces (idImpl : ModuleImpl F F) (VE := compLTS VE M) (sigma0, ∅) s ->
   ImplTraces M sigma0 s` (an idImpl-over-`compLTS` witness for `s` implies
   an `M`-level witness for the *same* `s`). The other direction is not
   needed and should be skipped.

   Proof plan: structural induction on the given `trace_steps idImpl A B`
   derivation. Process it left to right relative to the *target* trace, not
   the raw chronological step order: invocation items are replayed directly
   via `M`'s own bookkeeping-only `TraceStepInv` (always available — the
   same `pool_dom_from_init`/`trace_active` domain fact governs both
   `idImpl`'s own pool and the `M`-witness being built, since both are
   functions of the same prefix); return items require the *real* semantic
   witness, which structurally must already have fired earlier in the given
   derivation (an `idImpl`-level `TraceStepRet` is only enabled once its
   pool entry shows `Ret r`, which only happens via the corresponding
   `compStep` `ResEv` case). `csilent_steps_add_extra` is what lets that
   already-fired witness, extracted from its own local pool context, be
   transplanted into the left-to-right-constructed pool context (which
   generally differs by some set of "other currently active thread" keys) —
   applied once per such extra/missing key. That last step (iterating the
   transplant over a finite but unbounded key set) is the remaining
   engineering; the tool it needs is already proved.

2. **`ImplTraces_lib_mono`** (generic monotonicity / observational
   refinement):
   ```coq
   (forall s, ImplTraces idImpl sigma1 s -> ImplTracesClosed idImpl sigma2 s) ->
   forall s, ImplTraces M sigma1 s -> ImplTracesClosed M sigma2 s.
   ```
   for any `M : ModuleImpl E F`, `sigma1 : State VE1`, `sigma2 : State VE2`
   (same `E`). Says `ImplTraces _` is a precongruence w.r.t. swapping the
   underlying library for a trace-refining one. Proof: replay VE1's own
   `Step`-call sequence (embedded in `ustep` during M's run) as an
   `idImpl`-over-VE1 run, invoke the hypothesis to get a matching
   (or earlier-erroring) `idImpl`-over-VE2 run, and feed VE2's responses
   back into re-running M's fixed thread continuations — the same
   shadow-replay technique `CompLinSound.v` already uses (Layer 1/Layer 2),
   minus any Poss/AbstractConfig speculation, since there is nothing
   nondeterministic to track at this level. Largest self-contained piece.

3. **`pools_vcomp` / `thread_vcomp`** (fresh three-way pool-splitting
   invariant, built directly against `ThreadPoolState`, no reuse of
   `Compositionality.v`): relates a composite `ThreadState E G` entry
   (running `substProg t M1 (M2 g t)`-shaped programs) to its shadow
   `ThreadState F G` entry (as if M2 ran directly over `compLTS`) and M1's
   own bookkeeping `ThreadState E F` entry inside `compLTS`'s pool
   component. Plays the role `hpools`/`ts_left` play in `CompLinHComp.v`,
   for stacking instead of tensor.

4. **`vcomp_decompose`** (the hard associativity theorem):
   ```coq
   ImplTraces (M1 ▶ M2) sigma0 s ->
   ImplTraces (VE := compLTS VE M1) M2 (sigma0, ∅) s   (* up to the usual closure *)
   ```
   By induction on `trace_steps (M1▶M2) ...`, using `pools_vcomp` to track
   the correspondence and `substProgVis`/`bindSubstProgVis`/
   `bindSubstProgRet` unfolding equations to identify exactly when a
   composite micro-step crosses an F-level invocation/return boundary.
   Same difficulty tier as `CompLinHComp.hcomp_decompose`, adapted to
   vertical stacking. This is the proof's centerpiece, and the direct
   counterpart of LHL's `layerRefines_VComp_assoc`.

5. **Assembly — `CompLin_vcomp`**: chain
   `ImplTraces (M1▶M2) sigma0` --(4)--> `ImplTraces M2 (compLTS-initial)`
   --(2, fed by `CompLin M1` rewritten through 1)--> `ImplTracesClosed M2 rho0`
   --(hypothesis `CompLin M2 rho0 tau0`)--> `ImplTracesClosed idImpl tau0`,
   using a small `ImplTracesClosed`-transitivity helper (same shape as
   `CompLinSound.trace_snoc_prefix`, reusable since it lives in
   `CompLinSound.v`, not `Compositionality.v`).

## Suggested order of attack

1. `compLTS` + `compLTS_id_correct` — cheapest, validates the design.
2. `ImplTraces_lib_mono` — self-contained, single signature `E`, no stacking.
3. `pools_vcomp`/`thread_vcomp` + `vcomp_decompose` together (3 only exists
   to serve 4).
4. `CompLin_vcomp` assembly — should be short given 1–4 (mirrors how short
   LHL's own `vcomp_lin` is once its four supporting facts are in place).
