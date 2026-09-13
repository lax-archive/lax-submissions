import Mathlib.Data.Nat.Log
import Lax17.Degree
import Lax17.Expansion
import Lax17.GridMinor

/-!
---
title: Grid minors from separator expansion
type: theorem
---
A graph with no small balanced separator contains every square grid whose
vertices-plus-edges complexity fits the explicit Theorem 8.1 budget.
-/

namespace Lax17.ExpanderGrid

universe u

/-- The expander-to-grid handoff in the no-small-balanced-separator form. -/
axiom expanderContainsGrid :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d g : ℕ),
      2 ≤ Fintype.card V →
        Lax17.Expansion.NoSmallBalancedSeparator G d →
          ((3 * (d + 1) * (15 * (d + 1))) * 8) *
              (5 * g ^ 2) * Nat.log 2 (Fintype.card V) ≤
                Fintype.card V →
            Lax17.GridMinor.ContainsGridMinor G g

end Lax17.ExpanderGrid
