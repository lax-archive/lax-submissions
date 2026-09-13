import Mathlib.Data.Nat.Log
import Lax17.Degree
import Lax17.Treewidth

/-!
---
title: Degree-three treewidth sparsifier
type: theorem
---
Large treewidth contains a degree-three spanning subgraph that preserves
treewidth up to a polylogarithmic factor.
-/

namespace Lax17.TreewidthSparsifier

universe u

/-- If `G` has treewidth at least `k > 1`, it has a spanning subgraph `H` of
maximum degree three for which
`k ≤ c · treewidth(H) · (log₂ k)^d`. -/
axiom degreeThreeTreewidthSparsifier :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {k : ℕ},
        1 < k →
          k ≤ Lax17.Treewidth.treewidth G →
            ∃ H : SimpleGraph V,
              H ≤ G ∧
                Lax17.Degree.MaximumAtMost H 3 ∧
                  k ≤ c * Lax17.Treewidth.treewidth H *
                    (Nat.log 2 k) ^ d

end Lax17.TreewidthSparsifier
