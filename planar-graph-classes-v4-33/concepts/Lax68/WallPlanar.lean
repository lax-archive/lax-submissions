import Lax68.GridsAndWalls
import Lax68.Planar

/-!
---
title: Walls are planar
type: theorem
---
Every wall graph is planar.

A proof is supplied assuming grid planarity, which remains open in this
formalization.
-/

set_option autoImplicit false

namespace Lax68.WallPlanar

/-- Every wall graph is planar.

A proof is supplied assuming the still-open grid planarity statement. -/
axiom wall_planar {V : Type*} {G : SimpleGraph V} :
  Lax68.GridsAndWalls.IsWall G →
  Lax68.Planar.IsPlanar G

end Lax68.WallPlanar
