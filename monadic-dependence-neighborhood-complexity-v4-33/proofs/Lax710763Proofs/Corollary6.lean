import Lax710763.WeaklySparseDependent
import Lax199508.NowhereDenseNC

/-!
Corollary 6 of DMMPT26, composed from the *statements* of its two halves:
6a (weakly sparse + monadically dependent ⇒ nowhere dense,
`Lax710763.WeaklySparseDependent`), discharged by its own proof in this
package, and 6b (nowhere dense ⇒ almost linear neighborhood complexity,
`Lax199508.NowhereDenseNC`), assumed from the `sparsity-lectures` submission,
which owns the neighborhood-complexity concepts.  Consumed by the
terminal-sparsification step (Lemma 24) of the Appendix-A machinery;
composing the statements rather than importing the proofs is what makes
the dependency visible in the archive's proof network.
-/

namespace Lax710763Proofs.Corollary6

open Lax199508.GraphClasses Lax199508.NeighborhoodComplexity
open Lax710763.GraphClasses Lax710763.MonadicDependence

/-- Corollary 6: weakly sparse monadically dependent classes have
almost linear neighborhood complexity. -/
theorem hasAlmostLinearNC_of_weaklySparse_of_monadicallyDependent
    (C : GraphClass) (hs : WeaklySparse C) (hd : MonadicallyDependent C) :
    HasAlmostLinearNC C :=
  Lax199508.NowhereDenseNC.hasAlmostLinearNC_of_nowhereDense C
    (Lax710763.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent C hs hd)

end Lax710763Proofs.Corollary6
