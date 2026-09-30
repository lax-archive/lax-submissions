import Mathlib.Data.Set.Card
import Lax68.Planar

/-!
---
title: Planar graphs have at most 3v − 6 edges
type: theorem
---
Every finite planar graph with $v \geq 3$ vertices has at most $3v - 6$ edges.
-/

set_option autoImplicit false

namespace Lax909950.EdgeDensity

/-- A finite planar graph with $v \geq 3$ vertices has at most $3v - 6$ edges.
(Since $v \geq 3$, the natural-number subtraction does not truncate.) -/
axiom edge_density {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : Lax68.Planar.IsPlanar G) (hV : 3 ≤ Nat.card V) :
  G.edgeSet.ncard ≤ 3 * Nat.card V - 6

end Lax909950.EdgeDensity
