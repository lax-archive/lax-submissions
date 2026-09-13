import Mathlib.Data.Nat.Log
import Lax17.PathOfSets
import Lax17.Treewidth

/-!
---
title: A strong path-of-sets system from treewidth
type: theorem
---
Sufficiently large treewidth produces a strong path-of-sets system of
prescribed length and width.
-/

namespace Lax17.StrongPathOfSetsFromTreewidth

universe u

/-- Sufficiently large treewidth produces a strong path-of-sets system of
prescribed length and width. -/
axiom strongPathOfSetsFromTreewidth :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {ℓ w k : ℕ},
        1 < ℓ →
          1 < w →
            1 < k →
              k ≤ Lax17.Treewidth.treewidth G →
                c * w * ℓ ^ 50 * (Nat.log 2 k) ^ d < k →
                  Nonempty (Lax17.PathOfSets.StrongSystem G ℓ w)

end Lax17.StrongPathOfSetsFromTreewidth
