import Lax17.Crossbar
import Lax17.Degree

/-!
---
title: Crossbar-or-pseudo-grid dichotomy
type: theorem
---
Theorem 4.1: two full disjoint linkage families yield either a crossbar or a
pseudo-grid.
-/

namespace Lax17.CrossbarOrPseudoGrid

universe u

/-- The self-contained crossbar-or-pseudo-grid form of Theorem 4.1. -/
axiom crossbarOrPseudoGrid :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {A B X : Finset V} {g κ D : ℕ},
      2 ≤ g →
        Lax17.Crossbar.IsPowerOfTwo g →
          A.card = κ → B.card = κ → X.card = κ →
            Disjoint A B → Disjoint A X → Disjoint B X →
              (∀ x ∈ X, Lax17.Degree.Exactly G x 1) →
                Lax17.Paths.VertexLinkage G A B κ →
                  Lax17.Paths.VertexLinkage G A X κ →
                    1 ≤ D → D ≤ κ / (2 * g ^ 2) →
                      Nonempty
                          (Lax17.Crossbar.System G A B X (g ^ 2)) ∨
                        Nonempty
                          (Lax17.Crossbar.PseudoGrid
                            G A B X g D κ)

end Lax17.CrossbarOrPseudoGrid
