import Lax17.Paths

/-!
---
title: Vertex-Menger theorem
type: theorem
---
The vertex form of Menger's theorem gives an exact alternative between
\(k\) vertex-disjoint terminal-to-terminal paths and a separator of size
less than \(k\).
-/

namespace Lax17.VertexMenger

universe u

/-- Finite vertex-Menger in packing-or-separator form. -/
axiom vertexMenger :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ),
      Nonempty (Lax17.Paths.VertexLinkage G A B k) ∨
        ∃ X : Finset V,
          X.card < k ∧ Lax17.Paths.IsVertexSeparator G A B X

end Lax17.VertexMenger
