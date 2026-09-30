import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Lax68.Planar

/-!
---
title: Six color theorem
type: theorem
---
Every finite planar graph admits a proper coloring of its vertices with six
colors, i.e. an assignment of one of six colors to each vertex such that
adjacent vertices receive different colors.
-/

set_option autoImplicit false

namespace Lax909950.SixColoring

/-- Every finite planar graph is $6$-colorable. -/
axiom six_colorable {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : Lax68.Planar.IsPlanar G) :
  G.Colorable 6

end Lax909950.SixColoring
