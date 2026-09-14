import Lax68.Planar

/-!
---
title: Triangulations
type: definition
---

![Triangulation illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/4dd917c8b9a1e181ec951b7f6fa384262af31fa9/planar-graph-classes-v4-33/assets/triangulation.svg "Triangulation illustration")

A triangulation of a graph G is a planar supergraph T on the same vertex set,
with at least three vertices, to which no edge can be added while preserving
planarity. For a plane embedding this is equivalent to every face of T being
bounded by a triangle.
-/

set_option autoImplicit false

namespace Lax68.Triangulations

def IsTriangulationOf {V : Type*}
    (G T : SimpleGraph V) : Prop :=
  (∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
    G ≤ T ∧
    Planar.IsPlanar T ∧
    ∀ H : SimpleGraph V,
      T < H →
      ¬ Planar.IsPlanar H

end Lax68.Triangulations
