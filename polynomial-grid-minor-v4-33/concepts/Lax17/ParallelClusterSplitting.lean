import Lax17.PathOfSets
import Lax17.Degree

/-!
---
title: Parallel cluster splitting
type: theorem
---
Three large linked terminal sets in one cluster can be retained in three
pairwise disjoint connected subclusters.
-/

namespace Lax17.ParallelClusterSplitting

universe u

/-- The degree-three cluster-splitting theorem used to create one base/hair
pair while retaining linked interfaces of width `w`. -/
axiom parallelClusterSplitting :
  ∃ c : ℕ, 0 < c ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {C A B : Finset V} {w : ℕ},
        0 < w →
          Lax17.Degree.MaximumAtMost G 3 →
            Lax17.PathOfSets.IsCluster G C →
              A ⊆ C →
                B ⊆ C →
                  A.card = c * w →
                    B.card = c * w →
                      Disjoint A B →
                        Lax17.Linkedness.NodeWellLinkedIn G C A →
                          Lax17.Linkedness.NodeWellLinkedIn G C B →
                            Lax17.Linkedness.NodeLinkedIn G C A B →
                              Nonempty
                                (Lax17.PathOfSets.HairyClusterSplit
                                  G C A B w)

end Lax17.ParallelClusterSplitting
