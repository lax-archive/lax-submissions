import Mathlib.Data.Nat.Log
import Lax17.Degree
import Lax17.PathOfSets
import Lax17.Treewidth

/-!
---
title: A hairy path-of-sets system from treewidth
type: theorem
---
Sufficiently large treewidth produces a hairy strong path-of-sets system.
-/

namespace Lax17.HairyPathOfSetsFromTreewidth

universe u

/-- Sufficiently large treewidth produces a hairy strong path-of-sets
system. -/
axiom hairyPathOfSetsFromTreewidth :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {ℓ w k : ℕ},
        1 < ℓ →
          1 < w →
            1 < k →
              k ≤ Lax17.Treewidth.treewidth G →
                c * w * ℓ ^ 50 * (Nat.log 2 k) ^ d < k →
                  ∃ H : SimpleGraph V,
                    H ≤ G ∧
                      Lax17.Degree.MaximumAtMost H 3 ∧
                        Nonempty (Lax17.PathOfSets.HairySystem H ℓ w)

end Lax17.HairyPathOfSetsFromTreewidth
