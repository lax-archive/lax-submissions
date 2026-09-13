import Lax17.Degree
import Lax17.Linkedness
import Lax17.PathOfSets
import Mathlib.Data.Nat.Log

/-!
---
title: A low-degree well-linked core
type: theorem
---
A sufficiently long strong path-of-sets system has a same-vertex subgraph of
maximum degree three in which its first left interface remains
polylogarithmically edge-well-linked.
-/

namespace Lax17.LowDegreeWellLinkedCore

universe u

/-- The local strong-path form of the degree-three sparsifier theorem. -/
axiom lowDegreeWellLinkedCore :
  ∃ cLength logLength cWellLinked logWellLinked : ℕ,
    0 < cLength ∧ 0 < logLength ∧
      0 < cWellLinked ∧ 0 < logWellLinked ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} {length width : ℕ}
      (P : Lax17.PathOfSets.StrongSystem G length width),
        1 < width →
          (∃ half : ℕ, width = 2 * half) →
            cLength * (Nat.log 2 width) ^ logLength ≤ length →
              ∃ H : SimpleGraph V,
                H ≤ G ∧
                  Lax17.Degree.MaximumAtMost H 3 ∧
                    Lax17.Linkedness.ScaledEdgeWellLinked H
                      (P.left ⟨0, P.length_pos⟩) 1
                        (cWellLinked *
                          (Nat.log 2 width) ^ logWellLinked)

end Lax17.LowDegreeWellLinkedCore
