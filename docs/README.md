# Documentation

All prose documentation for this development lives here. Coq sources stay
under `examples/`, `models/`, `structures/`, `lattices/` and `interfaces/`.

## `CoqPitfalls.md`

A maintained list of Coq pitfalls specific to this development (notation
clashes, rewriting failures, tactic conventions) and the workarounds that
proved reliable. Read it before starting a proof session; add an entry
whenever a session loses time to something that is not a real proof
obstacle.

## `plans/`

Verification plans: the design notes written before (and maintained during)
each layer proof. Tracked in git.

| File | Subject |
| --- | --- |
| `TimestampVerificationPlan.md` | Timestamp layer proof |
| `NodeMemVerificationPlan.md` | NodeMem layer proof; owner-map ghost memory and its proof from the plain memory |
| `SPListArrayVerificationPlan.md` | SPListArray layer proof |
| `ListPoolVerificationPlan.md` | ListPool layer proof |
| `TryStackAuxVerificationPlan.md` | TryStackAux layer proof |
| `TryStackVerificationPlan.md` | TryStack layer proof |
| `TSStackVerificationPlan.md` | TSStack layer proof |
| `VerticalCompositionalityPlan.md` | Vertical composition in `models/simlin` |
| `ProvableLinStepApproach2Plan.md` | Provable linearization step, approach 2 |

## `proof-details/`

LaTeX write-ups of the finished proofs. The `.tex` sources are tracked; the
`.pdf` files are build products and are ignored by git. Rebuild with:

```sh
cd docs/proof-details && pdflatex <name>.tex
```

## `paper/`

The RGSimLin paper PDFs, kept locally for reference. This directory is
ignored by git because the paper sources live outside this repository.
