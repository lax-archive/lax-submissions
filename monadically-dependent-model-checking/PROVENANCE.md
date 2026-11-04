# Provenance

Parts of the proof package are adapted from earlier work. Each adapted file
says so in its header.

## Formal Learning Theory Kernel

The nine modules in `proofs/Lax185574Proofs/Lib/EpsilonSource/` are adapted from
Dhruv Gupta's
[Formal Learning Theory Kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/tree/7511199db276505a464fb8548e9369fc6cbc2209),
commit `7511199db276505a464fb8548e9369fc6cbc2209`, under the Apache License 2.0.
Its copyright and author notices remain in every module.

| Module | Upstream path under `FLT_Proofs/` |
| --- | --- |
| `Basic` | `Basic.lean` |
| `VCDimension` | `Complexity/VCDimension.lean` |
| `FinitePMF` | `PureMath/KLDivergence.lean` |
| `EmpiricalPMF` | `PureMath/ApproxMinimax.lean` |
| `FiniteVCApprox` | `PureMath/FiniteVCApprox.lean` |
| `Generalization` | `Complexity/Generalization.lean` |
| `Rademacher` | `Complexity/Rademacher.lean` |
| `Symmetrization` | `Complexity/Symmetrization.lean` |
| `FiniteSupportUC` | `Complexity/FiniteSupportUC.lean` |

The changes are: extraction of the dependencies of the epsilon-net theorem,
renamed namespaces, removal of unused declarations, a port to Lean 4.33.0,
replacement of two ambiguous `zero_le _` arguments by `by positivity`, and
removal of working comments and proof sketches. No hypotheses were removed and
no axioms were added.

## Earlier formalization by Szymon Toruńczyk

The modules whose header reads "Adapted from an earlier formalization by Szymon
Toruńczyk" come from an earlier, unpublished Lean development of parts of this
paper, written by Szymon Toruńczyk with GPT-6 under the same license.

## Archive submissions

- `proofs/Lax185574Proofs/Gaifman/`: lax-512892, *Gaifman's Theorem*, by Fatemeh
  Ghasemi.
- `Clustering.lean` and `WalkDistance.lean`: lax-3.
- `Lib/TupleRamsey.lean` and `Lib/ExplicitRamsey.lean`: lax-345067.
- `Lib/TransductionCalculus.lean`: lax-710763.
