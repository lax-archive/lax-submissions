import Lax17.TerminalConnectivity

/-!
---
title: Hind--Oellermann deletion--contraction theorem
type: theorem
---
Deleting or contracting a nonterminal edge preserves terminal
element-connectivity.
-/

namespace Lax17.HindOellermann

universe u

/-- Hind--Oellermann deletion--contraction for terminal element
connectivity. -/
axiom hindOellermannDeletionContraction :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V)
    (terminals : Finset V) (k : ℕ) (e₀ : H.Edge),
      H.left e₀ ∉ terminals → H.right e₀ ∉ terminals →
        H.TerminalElementConnectedAtLeast terminals k →
          (H.deleteEdge e₀).TerminalElementConnectedAtLeast terminals k ∨
            ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
              (K : Lax17.TerminalConnectivity.EdgeIndexedGraph W)
              (mapVertex : V → W),
                Nonempty (H.IsContraction e₀ K mapVertex) ∧
                  K.TerminalElementConnectedAtLeast
                    (Lax17.TerminalConnectivity.EdgeIndexedGraph.terminalImage
                      mapVertex terminals) k

end Lax17.HindOellermann
