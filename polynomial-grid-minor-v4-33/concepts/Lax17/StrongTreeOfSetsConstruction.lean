import Mathlib.Data.Nat.Log
import Lax17.TreeOfSets

/-!
---
title: Strong tree-of-sets construction
type: theorem
---
A sufficiently large node-well-linked set supports a strong subcubic
tree-of-sets system.
-/

namespace Lax17.StrongTreeOfSetsConstruction

universe u

/-- A sufficiently large node-well-linked set supports a strong subcubic
tree-of-sets system. -/
axiom strongTreeOfSetsConstruction :
  ∃ c d p : ℕ, 0 < c ∧ 0 < d ∧ 0 < p ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (X : Finset V) {m w x Δ : ℕ},
        1 < m →
          1 < w →
            1 < x →
              Lax17.Degree.MaximumAtMost G Δ →
                X.card = x →
                  Lax17.Linkedness.NodeWellLinkedIn G Finset.univ X →
                    c * w * m ^ 24 * Δ ^ p *
                        (Nat.log 2 x) ^ d < x →
                      Nonempty (Lax17.TreeOfSets.StrongSystem G m w)

end Lax17.StrongTreeOfSetsConstruction
