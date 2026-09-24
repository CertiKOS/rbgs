# Coq pitfalls in this development

A running list of things that repeatedly cost time when writing proofs here.
Each entry says how the problem shows up, why it happens, and what to do.
Add an entry whenever a proof session loses more than a few minutes to
something that is not a real proof obstacle.

Maintained by hand. Keep entries short; put long explanations in the plan
of the layer where the problem arose.

## Parsing and notation

| Symptom | Cause | Fix |
| --- | --- | --- |
| `Syntax error: ',' or ')' expected` right before a `]` | `)]` lexes as one token: `TPSimulation` defines the notation `[( ρ , π )]` for abstract configurations. | Write `) ]` with a space, in tactic lists (`[tac (H) \| tac]`) and everywhere else. The same holds for `[(` in intro patterns: write `[ (a & b) H ]`. |
| `Unknown interpretation for notation "( _ , _ )"` | Files that import `AssertionsSingle`/`AssertionsSet` get the notations `( σ , ρ , π )` and `( σ , Δ )` for proof states, which replace the standard tuple notation. | Write pairs as `pair a b`. Nested tuples in patterns (`(v, ts, taken, next)`) still work as intro patterns. |
| `lia` fails with `Cannot find witness` on a trivial goal such as `1 <= 2` | `<=`, `<` and numerals are re-bound by imported scopes (positives from `PArith`, orders from `coqrel`). The goal is not Peano arithmetic. | State facts with `Peano.le`/`Peano.lt` and constructor numerals (`S O`), or annotate with `%nat`; reduce definitions with `unfold ...; simpl` before `lia`. |
| A `t` in scope has type `Type` | `Import Reg` (and similar) brings a module type field named `t` into scope; `inversion` then renames a constructor binder `t` to `t0`. | Do not refer to binder names introduced by `inversion`. Use `match goal with H : ... ?tt ... \|- _ => ... end` to capture them. |

## Unification and rewriting

| Symptom | Cause | Fix |
| --- | --- | --- |
| `rewrite H` reports `Found no subterm matching ...` although the printed goal contains the term | The implicit argument differs up to unfolding, typically `@LinState (@ESPList A)` versus `@LinState (li_sig F)`, or `@fst mem_control cas_control` versus `@fst (State ...) (State ...)`. `rewrite` matches syntactically. | Avoid `rewrite`: use `exact (eq_trans H1 H2)`, `refine (eq_trans _ _)`, `pose proof (eq_trans (eq_sym H) H') as Habs; discriminate Habs`. Or state the lemma on the concrete shapes (`pair mc cc`) so both sides print and elaborate identically. |
| `congruence` fails on two chained equalities | Same cause as above: the equalities' types differ up to conversion. | `exact (eq_trans H1 H2)`. |
| `simpl` makes a later `rewrite` fail | `simpl` unfolds `live_at`, `live_order`, projections of `mk`/`mks`, and sometimes `mem_heap`, changing the syntactic shape. | Use targeted reduction: `cbn [mk SinglePossState.σ fst snd]`, or prove small equations (`live_order_cons_live`) and rewrite with those instead of calling `simpl`. |
| `exact (lemma _ _ H)` fails with `Cannot infer this placeholder of type concrete_state` | Arguments are elaborated before the goal is unified, so a hole that only the goal determines stays open. | Give the argument explicitly (`(pair (Idle s3) s2)`), or use `apply lemma with (σ := ...)`. |
| `Unable to find an instance for the variable t` on `apply lemma` | A lemma parameter appears only in hypotheses, not in the conclusion. | `apply (lemma q t0)`. |
| `The term "K" has type "... -> Type"` with a universe inconsistency in an `assert (forall K, ...)` | The binder was inferred as `Type`-valued. | Annotate: `forall K : tid -> single_state -> Prop`. |

## Tactics on this framework

| Symptom | Cause | Fix |
| --- | --- | --- |
| `No matching clauses for match` from `match goal` | The pattern matched but the *body* failed; Ltac backtracks over all clauses and then reports no match. | Debug the body with explicit names first (`all: exact I.` prints the context), then restore the `match`. |
| `repeat split; auto` leaves goals or splits too far | `split` also splits definitions that unfold to conjunctions (`source_G`, `represents`), and fails on `linked`/`HLinked` conjuncts. | Split explicitly: `split; [exact H1\|]. split; [exact H2\|]. ...` |
| `Hstep is already used` | `pupdate_intros_atomic` introduces `Hstep`, `Hpre`, `σ1`/`Δ1`, `s2`, `s3`, `t0`, `l0`, `H0`. | Do not reuse those names. Rename `H0` with `match goal with H : s3 l0 = Some _ \|- _ => rename H into Hconcrete end`. |
| The event's return variable disappears after `pupdate_intros_atomic` | `inversion` substitutes the lemma's variable that appears in the event (`t`, `l`, `ts`) by the constructor's. | Bind the surviving term from the goal: `match goal with \|- context [GetTopWindow _ _ _ _ _ ?tss] => pose (TS := tss) end`. Get field values from a member's `NodeCell` and `injection`, not from the constructor's names. |
| `Error: The reference End was not found` when compiling a truncated file | The truncation point is inside a `Definition`/`Lemma`. | Truncate one line before the header, or after the previous `Qed`. |

## Proof engineering that worked

- **Iterate on a truncated copy.** `SPListProof.v` compiles in seconds up to
  any point. A script that copies the first `N` lines, appends
  `End Proof. End SPListProof.`, and runs `coqc` with the `_CoqProject`
  flags (`-R examples examples -R models models ...`, see `Makefile.conf`)
  gives one error per iteration.
- **Print the goal by failing.** `exact I.` (or `all: exact I.`) shows the
  full context and goal in the error message; `Set Printing All.` before it
  exposes implicit-argument mismatches.
- **Plan the set-of-possibilities structure before proving.** Twins,
  filters and forks (`SPListProof.v`, section "Pointwise possibility
  facade") need their invariants fixed first; the individual update lemmas
  are then mechanical.
