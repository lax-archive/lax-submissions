import Lax17.Paths

/-!
---
title: Edge-Menger theorem
type: theorem
---
The edge form of Menger's theorem gives an exact alternative between
\(k\) edge-disjoint paths inside a cluster and a cut partition with boundary
of size less than \(k\).
-/

namespace Lax17.EdgeMenger

universe u

/-- Finite edge-Menger in packing-or-cut form. -/
axiom edgeMenger :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C A B : Finset V) (k : ℕ),
      A ⊆ C →
        B ⊆ C →
          Disjoint A B →
            (∃ P : Lax17.Paths.EdgeLinkage G A B k,
              ∀ i : Fin k, (P.path i).StaysIn C) ∨
              Nonempty (Lax17.Paths.EdgeCutPartition G C A B k)

end Lax17.EdgeMenger
