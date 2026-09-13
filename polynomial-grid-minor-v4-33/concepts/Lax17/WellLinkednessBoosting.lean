import Lax17.Degree
import Lax17.Linkedness
import Lax17.PathOfSets

/-!
---
title: Well-linkedness boosting
type: theorem
---
In bounded degree, edge well-linkedness can be boosted to node
well-linkedness after losing only a constant-factor number of terminals.
-/

namespace Lax17.WellLinkednessBoosting

universe u

/-- In a connected cluster of a graph of maximum degree `Δ ≥ 3`, an
edge-well-linked terminal set of size `κ` contains a node-well-linked subset
of size at least `⌊κ / (4Δ)⌋`. -/
axiom wellLinkednessBoosting :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C T : Finset V) (Δ κ : ℕ),
      Lax17.PathOfSets.IsCluster G C →
        Lax17.Degree.MaximumAtMost G Δ →
          3 ≤ Δ →
            T.card = κ →
              Lax17.Linkedness.EdgeWellLinkedIn G C T →
                ∃ T' : Finset V,
                  T' ⊆ T ∧ κ / (4 * Δ) ≤ T'.card ∧
                    Lax17.Linkedness.NodeWellLinkedIn G C T'

end Lax17.WellLinkednessBoosting
