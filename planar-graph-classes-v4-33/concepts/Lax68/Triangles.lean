import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
---
title: Triangles
type: definition
---

![Triangle graph illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/4dd917c8b9a1e181ec951b7f6fa384262af31fa9/planar-graph-classes-v4-33/assets/triangle.svg "Triangle graph illustration")

A triangle is a finite complete graph on exactly three vertices.
-/

set_option autoImplicit false

namespace Lax68.Triangles

def IsTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g SimpleGraph.completeGraph (Fin 3))

end Lax68.Triangles
