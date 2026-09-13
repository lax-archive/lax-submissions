import Lax17.Linkedness

/-!
---
title: Linking small terminal subsets
type: theorem
---
Disjoint equally large subsets of a node-well-linked set can be linked
inside the same cluster.
-/

namespace Lax17.SmallLinkedSubsets

universe u

/-- Disjoint equally large subsets of a node-well-linked set are linked
inside the same cluster. -/
axiom smallLinkedSubsets :
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    (C X A B : Finset V),
      Lax17.Linkedness.NodeWellLinkedIn G C X →
        A ⊆ X → B ⊆ X → Disjoint A B → A.card = B.card →
          Lax17.Linkedness.NodeLinkedIn G C A B

end Lax17.SmallLinkedSubsets
