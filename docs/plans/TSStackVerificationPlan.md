# Verification Plan: TSStack over TryStack

## Objective and deliverables

Prove that the TSStack implementation (`push` forwards to the atomic
TryStack push; `pop` retries `trypop`) refines the atomic stack, following
Section 7.2 and the "Stack" part of Appendix A.4 of `main-tr.pdf` as
literally as the Coq framework allows.  Paper references below are to that
appendix: the definitions of `pending`, `perm`, `I_stack`, `I_graph`,
`I_pending`, `push`, `G_push-inv`, `G_push-ret`, `G_pop`, `G_pop-emp`, and
the proof outlines in Fig. 34 (push) and Fig. 35 (pop).

Files:

- `examples/TSStack/TSStackSpec.v`: overlay interface.
- `examples/TSStack/TSStack.v`: implementation (Fig. 12 / Fig. 33).
- `examples/TSStack/TSStackProof.v`: the proof.

Exported results:

```coq
MTSStack :
  layer_implementation_simulation
    (@TSStackImpl.E A D) (@TSStackImpl.F A D).
MTSStackLinearizable :
  layer_implementation_linearizability
    (@TSStackImpl.E A D) (@TSStackImpl.F A D).
MListPoolTSStack :
  layer_implementation_linearizability
    (@ListPoolProof.E A D) (@TSStackImpl.F A D).
```

`MListPoolTSStack` composes the exported `TryStackProof.MListPoolTryStack`
with `MTSStackLinearizable`; the TryStack proof itself is not consulted.

No `Admitted`, `admit`, new `Axiom`, or semantic shortcut is acceptable.

## Agreed departures from the paper text

These are the only intended departures.  Anything else that turns out to
be necessary must be reported before it is implemented.

1. **Overlay error rule.**  `StackSpec.VStack` is error-free.  The
   underlay `TryStackSpec` errors when an actor outside `D` invokes an
   operation, and the framework tolerates an underlay error only through
   an erroneous abstract possibility.  `TSStackSpec.VTSStack D` therefore
   reuses `EStack A` and `StepStack` verbatim and adds
   `error_stack_actor_outside`, as every lower TSStack layer does.

2. **Reading of the `G_pop` filter.**  The paper writes the retained
   possibilities as those with `ρ = v·ρ'` and `V[(β,l)] = v`.  Its proof
   that `G_pop` preserves `I_stack` uses "a permutation with `(β,l)` as the
   head", which is only available if the filter retains the possibilities
   *justified by a permutation headed by `(β,l)`*.  With duplicate values
   the value-based reading does not preserve `I_stack`.  The filter is
   therefore defined as: `(ρ,π) ∈ Δ`, `(P[β] = ⊥ ∨ π[β] = •(push,ok))`,
   and some `N = (β,l)·N'` witnesses `I_stack` for `(ρ,π)`; then
   `ρ = v·ρ'` and `π' = π[α ↦ •(pop, v)]`.  This is a subset of the paper's
   filter, and with it the paper's arguments for all three invariants go
   through unchanged.

3. **Finiteness witness.**  The paper's `perm(V,E)` is implicitly
   nonempty.  Coq needs an explicit witness: the invariant carries a
   duplicate-free, newest-first list of all vertices that is compatible
   with `E`.  It also records the graph well-formedness facts the paper
   takes for granted (garbage and pending entries are vertices, edges
   connect vertices).  These facts are part of the concrete-state half of
   `I` and never interact with the possibility-set arguments.

4. **Two-event encoding of `trypop`.**  The Coq underlay splits the atomic
   `trypop` into an invocation (to `TSAtomicPending`) and a response.  The
   invocation and the `Fail` response take no abstract step (identity
   update).  The `Succ(v,β,l)` response is `G_pop`, the `Succ(⊥)` response
   is `G_pop-emp`.  The guarantee records that a thread's atomic control
   state is owned by that thread, so the assertion between the two events
   is trivially stable.

## Dictionary: paper notation to Coq

| Paper | Coq |
| --- | --- |
| `(V,E,P,g)` | `s : TryStackState` with `ts_vertices`, `ts_edges`, `ts_pending_pushes`, `ts_garbage`; `payload σ` erases `TSAtomicPending` |
| `S_p ∈ Val*` | `ρ = Idle stk`, `stk : list A` |
| `(α,l) ∈ \|P\|` | `ts_is_pending s (α,l)` |
| `dom(V)\g` | `ts_is_live s n` |
| `α ↦ ◦(push(v))`, `α ↦ •(push(v),ok)` | tokens `ls_inv (push v)`, `ls_linr (push v) tt` |
| `α ↦ ◦(pop)`, `α ↦ •(pop, r)` | `ls_inv pop`, `ls_linr pop r` |
| `pending(π,P)` | `omitted s π n := ts_is_pending s n ∧ ∃v, π[fst n] = Some (ls_inv (push v))` |
| `perm(X,E)` | `perm s X N := NoDup N ∧ ecompat E N ∧ ∀n, In n N ↔ X n`, where `ecompat` says no later element has an edge to an earlier one |
| `ρ = map(V,N)` | `values_of s N stk := Forall2 (fun n v => ts_vertices s n = Some v) N stk` |
| `α ↦∀ ls` | `AssertionsSet.ALin α ls` |
| `α ↦ ◦ ⊕ α ↦ • * true` | some possibility has `◦`, some has `•`, every possibility has one of them |
| `Δ' = {…}` | an `AbstractConfig` built from `Δ` as an image or a filter; membership is exactly the paper's set comprehension |

## Invariant (paper's `I`, plus the concrete-state facts)

```text
I_stack s Δ   := ∀(ρ,π)∈Δ. ∃N stk. perm s (live \ omitted π) N ∧ values_of s N stk ∧ ρ = Idle stk
I_graph s Δ   := ∀P' ⊆ pending vertices. ∀N ∈ perm s (live \ P'). ∀stk, values_of s N stk →
                 ∃(ρ,π)∈Δ. ρ = Idle stk ∧
                   (∀(β,l) pending, (β,l) ∉ P' → π[β] = •(push V(β,l), ok)) ∧
                   (∀(β,l) pending live, (β,l) ∈ P' → π[β] = ◦(push V(β,l)))
I_pending s Δ := ∀β l, P[β] = l → ∃v, V(β,l) = v ∧
                   ((β,l) ∈ g → ∀(ρ,π)∈Δ. π[β] = •(push v,ok)) ∧
                   ((β,l) ∉ g → ∀(ρ,π)∈Δ. π[β] = ◦(push v) ∨ π[β] = •(push v,ok))
graph_wf s    := finiteness witness; g ⊆ dom V; pending entries are vertices;
                 edges connect vertices; no edge enters a pending vertex
I w           := graph_wf s ∧ I_stack s Δ ∧ I_graph s Δ ∧ I_pending s Δ   where s = payload (σ w)
```

`I_graph` is stated through lookups, exactly as in the paper, so it is
insensitive to the structural representation of `PositiveMap`s and the
initial singleton `(Idle nil, TMap.empty)` satisfies it directly.

Two presentational differences from the paper's `I_pending`: the two
nonempty halves of `α ↦ ◦ ⊕ α ↦ •` are not stored but derived from
`I_graph` (`pending_live_both_tokens`), and the edge clause
`∀n. (n,(α,l)) ∉ E` is kept with the other concrete-graph facts in
`graph_wf`.  Neither changes any argument.

## Guarantees (paper's four relations, plus administrative ones)

Each relation below is the paper's definition, stated as a Coq `Variant`
whose membership clause for `Δ'` is the paper's set comprehension.  `I`
itself is not part of `G`; the program logic supplies `I` at the post-state
in every stability obligation.

- `G_push-inv α`: `σ ⊨ Graph(V,E,P,g)`, `P[α] = ⊥`, all `π[α] = ◦(push v)`;
  `σ' ⊨ GraphPush(V,E,P,g,α,l,v)` (this is `ts_start_push α l v s`);
  `Δ' = {(ρ',π') | (ρ,π) ∈ Δ ∧ (ρ',π') ∈ push(ρ,π)}`, where `push` is the
  reflexive–transitive closure of "linearize one push `β` with
  `P[β] = l`, `(β,l) ∉ g`, `π[β] = ◦(push v)`: `ρ ↦ v·ρ`,
  `π ↦ π[β ↦ •(push v, ok)]`" (two `poss_step`s).
- `G_push-ret α`: `P[α] = l`; `σ' = ts_finish_push α s`;
  `Δ' = {(ρ,π) ∈ Δ | π[α] = •(push v, ok)}`.
- `G_pop α (β,l)`: `(β,l)` top among live vertices, `V(β,l) = v`;
  `σ' = ts_mark_garbage (β,l) s`; `Δ'` as in departure 2.
- `G_pop-emp α`: all vertices garbage; `σ' = σ`;
  `Δ' = {(ρ, π[α ↦ •(pop,⊥)]) | (ρ,π) ∈ Δ}` (every `ρ` is `Idle nil` by `I_stack`).
- Identity updates for the `trypop` invocation and the `Fail` response.
- `GINV`, `GRET` (framework), `GId`.

`G α` is the union of the above for actor `α`; each relation fixes the
concrete control before and after (`TSReady`, or an atomic state owned by
`α`).  `R α` is the union of `G β`, `GINV β`, `GRET β` for `β ≠ α`, and
`GId`; parallel compatibility is then immediate.

## Proof obligations, in the paper's order

1. **Preliminaries.**  `ecompat` facts (monotone in `E`, suffix closed,
   "elements before `n` have no edge from `n`"); `select_sublist`
   (classical selection from the finiteness witness, giving `perm_exists`);
   `values_exist`; `pending_unique`; token-map lookup lemmas.
2. **`push` closure.**  `lin_step`, `lin_closure`; each step is two
   `poss_step`s; steps preserve `Idle`; `lin_all` linearizes a list of
   pending vertices, last one first, producing `vals ++ stk`.
3. **`I ∘ G_push-inv ⇒ I`.**
   - `I_stack`: by induction on the closure.  The old `N` remains valid in
     the new graph because the new vertex is omitted while `π[α] = ◦`; each
     linearization of a pending vertex `m` prepends `m`, valid because no
     edge enters a pending vertex.
   - `I_graph`: given `P'` and `N`.  If `(α,l) ∈ P'` or `(α,l) ∉ N`, the
     old `I_graph` applies unchanged.  Otherwise `N = N'·(α,l)·N''` with
     `N'` consisting of pending vertices (the only vertices without an edge
     from `(α,l)`); apply the old `I_graph` to `N''` with
     `P' ∪ N' ∪ {(α,l)}`, then linearize `(α,l)` and afterwards the
     elements of `N'` from last to first.
   - `I_pending`: only `α` changed; `Δ'` contains the identity image
     (`◦`) and the image linearizing `α` first (`•`); every image has one of
     the two; no edge enters `(α,l)`.
   - `graph_wf`: prepend `(α,l)` to the finiteness witness.
4. **`I ∘ G_push-ret ⇒ I`.**
   - `I_stack`: subset; the same `N` works because `(α,l)` is not omitted.
   - `I_graph`: `(α,l)` is no longer pending, so any admissible `P'` and `N`
     for the new state is admissible for the old state; the possibility it
     yields has `π[α] = •` and survives the filter.
   - `I_pending`: `α` is cleared; others unchanged.
5. **`I ∘ G_pop ⇒ I`.**
   - `I_stack`: the retained `(ρ,π)` is witnessed by `(β,l)·N'`; `N'`
     witnesses `ρ'` in the new state.
   - `I_graph`: extend `N'` to `(β,l)·N'`, valid since `(β,l)` is a top
     vertex; the old `I_graph` (with `(β,l) ∉ P'`) yields a possibility with
     `π[β] = •` when `(β,l)` is pending, which passes the filter.
   - `I_pending`: if `(β,l)` is pending it is now garbage and every
     retained possibility has `π[β] = •`; other threads unchanged.
6. **`I ∘ G_pop-emp ⇒ I`**, identity updates, `GINV`, `GRET`.  For `GINV t`
   the new token is `◦(f)` for a thread without a pending push (a pending
   push implies a token by `I_pending`), so `I_graph` is unaffected.  For
   `GRET t` similarly, using the `Completed` postcondition's `P[t] = ⊥`.
7. **Stability.**  Every assertion of the outlines (`I`, `I ∧ α↦∀◦(op)`,
   `I ∧ P[α] = l`, `I ∧ α↦∀•(op, r) ∧ P[α] = ⊥`, the atomic-control
   assertion) is stable under `R α`: filters are subsets; the `push`
   closure changes tokens only of threads with a pending live push, and
   `I ∧ α↦∀ls` excludes `α` from those by `I_pending`; other threads'
   guarantees do not touch `P[α]` or `α`'s own atomic control.
8. **`ValidRGI`.**  Whether every possibility lacks a token for `t` is
   preserved because no update changes `None`-ness of another thread's
   token.
9. **Method outlines.**
   - Fig. 34: `Active α (push v)` → in-domain or abstract error
     (`provable_perror`); `provable_vis_safe` on `ts_push v` with
     `G_push-inv` for the invocation and `G_push-ret` for the response;
     `provable_ret_safe`.
   - Fig. 35: `provable_perror`; `provable_doloop` with loop invariant
     `I ∧ α↦∀◦(pop) ∧ α ∈ D`; body `provable_vis_safe` on `ts_trypop`
     (identity at invocation; `G_pop`, `G_pop-emp`, identity at the three
     responses); `provable_ret_safe` on the three results.
10. **Packaging.**  `MethodProvable` records, `SetLogic.soundness`,
    `MTSStack`, `MTSStackLinearizable`, `MListPoolTSStack`.

## Checklist

- [x] `TSStackSpec.v`, `TSStack.v`, `_CoqProject` entries.
- [x] Preliminaries (1) and `push` closure (2).
- [x] Invariant, guarantees, rely (definitions).
- [x] Preservation lemmas (3)–(6).
- [x] Stability, `ValidRGI`, parallel compatibility (7)–(8).
- [x] Method outlines (9) and packaging (10).
- [x] Full build, `git diff --check`, `Print Assumptions`.

## Outcome

`MTSStack` and `MTSStackLinearizable` depend only on `classic` and
`Eqdep.Eq_rect_eq.eq_rect_eq` (the latter from dependent elimination on
the underlay step, as in the other layers).  `MListPoolTSStack` adds the
propositional and functional extensionality principles used by the lower
layers.  The mechanized argument follows Appendix A.4 with exactly the
four departures listed above.

## Validation commands

```text
make examples/TSStack/TSStackProof.vo
make -j2
git diff --check
rg -n "Admitted|admit|Axiom" examples/TSStack/TSStack*.v
```

Expected assumptions are only the classical and extensionality principles
already used by the framework.
