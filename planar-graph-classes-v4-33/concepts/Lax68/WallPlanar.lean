import Lax68.GridsAndWalls
import Lax68.Planar

/-!
---
title: Walls are planar
type: theorem
---
Every wall graph is planar.

Open in this formalization: no proof is supplied yet.
-/

set_option autoImplicit false

namespace Lax68.WallPlanar

/-- Every wall graph is planar.

Open in this formalization: no proof is supplied yet. -/
axiom wall_planar {V : Type*} {G : SimpleGraph V} :
  Lax68.GridsAndWalls.IsWall G →
  Lax68.Planar.IsPlanar G

end Lax68.WallPlanar
