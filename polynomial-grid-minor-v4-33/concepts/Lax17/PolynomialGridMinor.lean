import Mathlib.Analysis.SpecialFunctions.Log.Base
import Lax17.GridMinor
import Lax17.Treewidth

/-!
---
title: Exponent 8 ($\times$ Polylogarithmic) Bound for the Grid-Minor Theorem
type: theorem
---
There are positive integers $K$ and $b$ such that every finite simple graph
of treewidth at least
$$
K g^8 (\log_2 g)^b
$$
contains the $g \times g$ square grid as a minor.

Treewidth is defined through finite tree decompositions, and minor
containment uses branch sets.
-/

namespace Lax17.PolynomialGridMinor

universe u

/-- Exponent-eight grid-minor bound with a natural-number polylogarithmic
factor. -/
axiom polynomial_grid_minor_eight_polylog :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {g : ℕ},
          2 ≤ g →
            K * g ^ 8 * (Nat.log 2 g) ^ b ≤
                Lax17.Treewidth.treewidth G →
              Lax17.GridMinor.ContainsGridMinor G g

end Lax17.PolynomialGridMinor
