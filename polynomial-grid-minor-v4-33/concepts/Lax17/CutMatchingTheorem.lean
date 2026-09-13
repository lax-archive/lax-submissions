import Mathlib.Data.Nat.Log
import Lax17.Expansion

/-!
---
title: Cut-matching expansion theorem
type: theorem
---
On every finite even vertex set, a logarithmic number of perfect
matching rounds can be chosen across successive bisections so that the union
of the matching-edge instances has constant expansion.  This is the
existential form of the cut-matching game used in the grid-minor proof;
algorithmic running-time claims are intentionally omitted.
-/

namespace Lax17.CutMatchingTheorem

universe u

/-- A cut-matching transcript of \(O(\log n)\) rounds with half-expansion. -/
axiom logarithmicCutMatchingExpansion :
  ∃ c : ℕ, 0 < c ∧
    ∀ (V : Type u) [Fintype V] [DecidableEq V],
      2 ≤ Fintype.card V →
        (∃ half : ℕ, Fintype.card V = 2 * half) →
        ∃ T : Lax17.Expansion.CutMatchingTranscript V,
          T.length ≤ c * Nat.log 2 (Fintype.card V) ∧
            T.IsHalfEdgeExpander

end Lax17.CutMatchingTheorem
