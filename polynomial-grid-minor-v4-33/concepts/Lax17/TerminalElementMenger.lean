import Lax17.TerminalConnectivity

/-!
---
title: Terminal element-Menger theorem
type: theorem
---
For a named-edge multigraph, the canonical available-boundary formulation of
terminal element-connectivity is equivalent to the usual formulation by
arbitrary terminal element cuts.
-/

namespace Lax17.TerminalElementMenger

universe u

/-- Terminal element-connectivity in arbitrary-cut form. -/
axiom terminalElementMenger :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V)
    (terminals : Finset V) (k : ℕ),
      H.TerminalElementConnectedAtLeast terminals k ↔
        ∀ ⦃a : V⦄, a ∈ terminals →
          ∀ ⦃b : V⦄, b ∈ terminals → a ≠ b →
            ∀ C : H.ElementCut terminals a b, k ≤ C.order

end Lax17.TerminalElementMenger
