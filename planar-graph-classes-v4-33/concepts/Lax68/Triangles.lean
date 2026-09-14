import Mathlib.Combinatorics.SimpleGraph.Maps
import Lax68.MaximalOuterplanar
import Lax68.Outerplanar
import Lax68.Planar

/-!
---
title: Triangles
type: definition
---
A triangle is a finite complete graph on exactly three vertices.
-/

set_option autoImplicit false

namespace Lax68.Triangles

def IsTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g SimpleGraph.completeGraph (Fin 3))

/-- Every triangle is maximal outerplanar. -/
axiom triangle_maximalOuterplanar
    {V : Type*} {G : SimpleGraph V} :
  Lax68.Triangles.IsTriangle G →
  Lax68.MaximalOuterplanar.IsMaximalOuterplanar G

/-- Every triangle is outerplanar. -/
axiom triangle_outerplanar
    {V : Type*} {G : SimpleGraph V} :
  Lax68.Triangles.IsTriangle G →
  Lax68.Outerplanar.IsOuterplanar G

/-- Every triangle is planar. -/
axiom triangle_planar
    {V : Type*} {G : SimpleGraph V} :
  Lax68.Triangles.IsTriangle G →
  Lax68.Planar.IsPlanar G

end Lax68.Triangles
