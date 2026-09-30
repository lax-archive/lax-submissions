import Mathlib.Data.Set.Card
import Lax68.Planar

/-!
---
title: Planar graphs have a vertex of degree at most 5
type: theorem
---
Every finite planar graph with at least one vertex has a vertex of degree at
most $5$.
-/

set_option autoImplicit false

namespace Lax909950.LowDegree

/-- Every nonempty finite planar graph has a vertex with at most five
neighbors. -/
axiom exists_degree_le_five {V : Type*} [Finite V] [Nonempty V] {G : SimpleGraph V}
    (hG : Lax68.Planar.IsPlanar G) :
  ∃ x : V, (G.neighborSet x).ncard ≤ 5

end Lax909950.LowDegree
