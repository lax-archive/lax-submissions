import Lax68.Triangulations
import Lax68.Planar

/-!
---
title: Planar triangulations are planar
type: theorem
---
Every planar triangulation T of a graph G is planar, directly by definition.
-/

set_option autoImplicit false

namespace Lax68.TriangulationPlanar

/-- Every planar triangulation is planar. -/
axiom planarTriangulationOf_planar {V : Type*}
    {G T : SimpleGraph V} :
  Lax68.Triangulations.IsPlanarTriangulationOf G T →
  Lax68.Planar.IsPlanar T

end Lax68.TriangulationPlanar
