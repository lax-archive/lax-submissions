import Lax68.Planar

/-!
---
title: Planar triangulations
type: definition
---

![A planar triangulation (K₄)](https://raw.githubusercontent.com/lax-archive/lax-submissions/5f143bf55b530fd7057d45e9b1c7c9d24869ebad/planar-graph-classes-v4-33/assets/triangulation.svg "A planar triangulation (K₄)")

A planar triangulation of a graph G is a planar supergraph T on the same vertex set,
with at least three vertices, to which no edge can be added while preserving
planarity. For finite graphs, this is equivalent to a plane embedding in which
every face of T, including the outer face, is bounded by a triangle.
-/

set_option autoImplicit false

namespace Lax68.Triangulations

/-- A maximal planar supergraph on the same vertex set, with at least three vertices. -/
def IsPlanarTriangulationOf {V : Type*}
    (G T : SimpleGraph V) : Prop :=
  (∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
    G ≤ T ∧
    Planar.IsPlanar T ∧
    ∀ H : SimpleGraph V,
      T < H →
      ¬ Planar.IsPlanar H

end Lax68.Triangulations
