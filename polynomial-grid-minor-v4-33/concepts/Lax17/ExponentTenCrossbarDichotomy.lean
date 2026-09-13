import Mathlib.Data.Nat.Log
import Lax17.Crossbar
import Lax17.Degree

/-!
---
title: Exponent-ten crossbar dichotomy
type: theorem
---
The exponent-ten crossbar theorem: three equal terminal sets and two full
linkages yield either a width-\(g^2\) crossbar or a minor carrying a large
strong path-of-sets system.
-/

namespace Lax17.ExponentTenCrossbarDichotomy

universe u

/-- The axiom-free exponent-ten crossbar dichotomy. -/
axiom exponentTenCrossbarDichotomy :
  ∃ c : ℕ, 0 < c ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {A B X : Finset V} {g κ : ℕ},
        2 ≤ g →
          Lax17.Crossbar.IsPowerOfTwo g →
            A.card = κ → B.card = κ → X.card = κ →
              Disjoint A B → Disjoint A X → Disjoint B X →
                2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ κ →
                  (∀ x ∈ X, Lax17.Degree.Exactly G x 1) →
                    Lax17.Paths.VertexLinkage G A B κ →
                      Lax17.Paths.VertexLinkage G A X κ →
                        Nonempty
                            (Lax17.Crossbar.System
                              G A B X (g ^ 2)) ∨
                          ∃ length width : ℕ,
                            g ^ 2 ≤ c * length ∧
                              g ^ 2 ≤ c * width ∧
                                Lax17.Crossbar.HasStrongPathOfSetsMinor
                                  G length width

end Lax17.ExponentTenCrossbarDichotomy
