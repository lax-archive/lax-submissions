import Lax17.TerminalConnectivity

/-!
---
title: Mader's admissible split-off theorem
type: theorem
---
Every eligible splitting centre has a pair of incident edges whose split-off
preserves the relevant local edge-connectivities.
-/

namespace Lax17.Mader

universe u

/-- Mader's admissible split-off theorem, including the exceptional
degree-three exclusion. -/
axiom maderAdmissibleSplitOff :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V) (s : V),
      2 ≤ H.degree s → H.degree s ≠ 3 → H.NoIncidentCutEdge s →
        ∃ p : H.SplitPair s, H.IsMaderAdmissible p

end Lax17.Mader
