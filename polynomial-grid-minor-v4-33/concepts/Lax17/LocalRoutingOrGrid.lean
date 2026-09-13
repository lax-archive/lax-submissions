import Lax17.GridMinor
import Lax17.PathOfSets

/-!
---
title: Local routing-or-grid alternative
type: theorem
---
In one strong cluster, large equal terminal sets either admit the desired
local routing or force the target grid minor.
-/

namespace Lax17.LocalRoutingOrGrid

universe u

/-- In one connected cluster, large linked terminal sets either force an
`h × h` grid minor or admit `q` disjoint routes with pairwise bridges. -/
axiom localRoutingOrGrid :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C A B : Finset V} {h q w : ℕ},
      1 < h →
        1 < q →
          Lax17.PathOfSets.IsCluster G C →
            Lax17.Linkedness.NodeLinkedIn G C A B →
              A.card = w →
                B.card = w →
                  (16 * h + 10) * q ≤ w →
                    Lax17.GridMinor.ContainsGridMinor G h ∨
                      ∃ Q : Lax17.Paths.VertexLinkage G A B q,
                        (∀ i : Fin q, (Q.path i).StaysIn C) ∧
                          Q.HasPairwiseBridgesIn C

end Lax17.LocalRoutingOrGrid
