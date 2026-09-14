import Lax68.GridsAndWalls
import Lax68.Planar

/-!
---
title: Grids are planar
type: theorem
---
Every grid graph is planar.

Open in this formalization: no proof is supplied yet.
-/

set_option autoImplicit false

namespace Lax68.GridPlanar

/-- Every grid graph is planar.

Open in this formalization: no proof is supplied yet. -/
axiom grid_planar {V : Type*} {G : SimpleGraph V} :
  Lax68.GridsAndWalls.IsGrid G →
  Lax68.Planar.IsPlanar G

end Lax68.GridPlanar
