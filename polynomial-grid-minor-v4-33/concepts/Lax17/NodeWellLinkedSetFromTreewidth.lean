import Lax17.Linkedness
import Lax17.Treewidth

/-!
---
title: A well-linked set from treewidth
type: theorem
---
Large treewidth yields a proportionally large node-well-linked set.
-/

namespace Lax17.NodeWellLinkedSetFromTreewidth

universe u

/-- Large treewidth yields a large node-well-linked vertex set. -/
axiom nodeWellLinkedSetFromTreewidth :
  ∃ c : ℕ, 0 < c ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {k : ℕ},
        c * k ≤ Lax17.Treewidth.treewidth G →
          ∃ X : Finset V,
            k ≤ X.card ∧
              Lax17.Linkedness.NodeWellLinkedIn G Finset.univ X

end Lax17.NodeWellLinkedSetFromTreewidth
