import Lax17.PathOfSets

/-!
---
title: Crossbar stitching
type: theorem
---
Compatible local routed row families in the designated clusters of a strong
path-of-sets system can be stitched into global rows.  The pairwise local
bridges survive in every designated even cluster.
-/

namespace Lax17.CrossbarStitching

universe u

/-- The row-stitching conclusion used before sparse-grid assembly. -/
axiom crossbarStitching :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {g : ℕ}
    (P : Lax17.PathOfSets.StrongSystem G
      (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g)),
      2 ≤ g →
        (∀ i : Fin (2 * g * (g - 1)),
          ∃ localRows :
              Lax17.Paths.VertexLinkage G
                (P.left i) (P.right i) g,
            (∀ row : Fin g,
              (localRows.path row).StaysIn (P.cluster i)) ∧
                localRows.HasPairwiseBridgesIn (P.cluster i)) →
          ∃ rows :
              Lax17.Paths.VertexLinkage G
                (P.left P.toSystem.firstIndex)
                (P.right P.toSystem.lastIndex) g,
            ∀ i : Fin (g * (g - 1)),
              ∃ clusterIndex : Fin (2 * g * (g - 1)),
                clusterIndex.1 = 2 * i.1 + 1 ∧
                  rows.HasPairwiseBridgesIn
                    (P.cluster clusterIndex)

end Lax17.CrossbarStitching
