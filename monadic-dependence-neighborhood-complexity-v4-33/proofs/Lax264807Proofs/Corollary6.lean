import Lax264807.WeaklySparseDependent
import Lax12.NowhereDenseNC

/-!
Corollary 6 of DMMPT26, composed from the *statements* of its two halves:
6a (weakly sparse + monadically dependent ⇒ nowhere dense,
`Lax264807.WeaklySparseDependent`), discharged by its own proof in this
package, and 6b (nowhere dense ⇒ almost linear neighborhood complexity,
`Lax12.NowhereDenseNC`), assumed from the `sparsity-lectures` submission,
which owns the neighborhood-complexity concepts.  Consumed by the
terminal-sparsification step (Lemma 24) of the Appendix-A machinery;
composing the statements rather than importing the proofs is what makes
the dependency visible in the archive's proof network.
-/

namespace Lax264807Proofs.Corollary6

open Lax12.GraphClasses Lax12.NeighborhoodComplexity
open Lax264807.GraphClasses Lax264807.MonadicDependence

/-- Corollary 6: weakly sparse monadically dependent classes have
almost linear neighborhood complexity. -/
theorem hasAlmostLinearNC_of_weaklySparse_of_monadicallyDependent
    (C : GraphClass) (hs : WeaklySparse C) (hd : MonadicallyDependent C) :
    HasAlmostLinearNC C :=
  Lax12.NowhereDenseNC.hasAlmostLinearNC_of_nowhereDense C
    (Lax264807.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent C hs hd)

end Lax264807Proofs.Corollary6
