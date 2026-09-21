# Documentation

All prose documentation for this development lives here. Coq sources stay
under `examples/`, `models/`, `structures/`, `lattices/` and `interfaces/`.

## `plans/`

Verification plans: the design notes written before (and maintained during)
each layer proof. Tracked in git.

| File | Subject |
| --- | --- |
| `SPListArrayVerificationPlan.md` | SPListArray layer proof |
| `ListPoolVerificationPlan.md` | ListPool layer proof |
| `TryStackAuxVerificationPlan.md` | TryStackAux layer proof |
| `TryStackVerificationPlan.md` | TryStack layer proof |
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
