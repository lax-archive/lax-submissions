import Lax68.Planar

/-!
---
title: Triangulations
type: definition
---
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

/-- If T is a triangulation of a planar graph G, then T is planar. -/
axiom triangulationOf_planar {V : Type*}
    {G T : SimpleGraph V} :
  Lax68.Planar.IsPlanar G →
  Lax68.Triangulations.IsTriangulationOf G T →
  Lax68.Planar.IsPlanar T

end Lax68.Triangulations
