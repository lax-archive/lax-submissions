import Lax17.GridMinor
import Lax17.PathOfSets

/-!
---
title: A grid minor from a strong path-of-sets system
type: theorem
---
A sufficiently long and wide strong path-of-sets system contains a
prescribed square grid minor.
-/

namespace Lax17.StrongPathOfSetsContainsGrid

universe u

/-- A strong path-of-sets system of length at least `2g(g-1)` and width at
least `16g² + 10g` contains the `g × g` grid as a minor. -/
axiom strongPathOfSetsContainsGrid :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {ℓ w g : ℕ},
      Nonempty (Lax17.PathOfSets.StrongSystem G ℓ w) →
        2 ≤ g →
          2 * g * (g - 1) ≤ ℓ →
            16 * g ^ 2 + 10 * g ≤ w →
              Lax17.GridMinor.ContainsGridMinor G g

end Lax17.StrongPathOfSetsContainsGrid
