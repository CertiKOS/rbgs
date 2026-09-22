# Verification Plan: Timestamp over CAS

## Objective

Prove the implementation in `Timestamp.v` (Fig. 15 of `main-tr.pdf`) correct
with respect to the `(t, p)` specification of Appendix A.1 in
`TimestampSpec.v`.  The underlay is a single `ECASReg nat` register; the
paper's hardware `CAS` interface has only `cas` and `get`, so `set` is simply
never called.  The production theorem is

```coq
TimestampProof.MTimestamp :
  layer_implementation_simulation TimestampImpl.E TimestampImpl.F
```

with `MTimestampLinearizable := LISim2LILin MTimestamp`.

## Proof shape

Singleton-possibility proof in the style of `FAISet.v`.

* **Invariant** `I`: the abstract clock `t` equals the register value.
* **Thread-local assertions**: `Stamped t t1` (the actor's pending entry is
  `t1`) and `Observed n` (`n` is at most the register value; the register is
  monotone, so this is stable).
* **Guarantee** `G t`: register non-decreasing; other threads' pending
  entries and linearization tokens unchanged.  **Rely** `R t` is the
  corresponding view from the actor's side.
* **Linearization points**:
  * the abstract invocation linearizes at the response of the first `get`,
    so the pending entry records exactly `t1`;
  * a successful `cas t1 (t1+1)` linearizes the response `[t1, t1]`
    (register and clock both become `t1 + 1`);
  * in the two branches returning `[t1, n - 1]` for a later read `n`, the
    response is an abstract-only `singleton_linstep`: `n <= t`, so
    `max t n = t` keeps the invariant, and `t1 < n` gives `t1 <= n - 1`.

## Structure of `TimestampProof.v`

The method triple is one proof whose skeleton is the sequence of
`singleton_vis_safe` / `singleton_linstep` / `singleton_ret_safe` steps, with
the possibility updates inline.  Only non-logical facts are separate lemmas:
stability of each assertion, rely/guarantee compatibility, absence of
underlay errors, and the shapes of the four CAS register steps
(`step_*_shape`).  Thread events carry dependent result arguments that
`injection` drops, so `cas_result` reads the boolean back explicitly.
