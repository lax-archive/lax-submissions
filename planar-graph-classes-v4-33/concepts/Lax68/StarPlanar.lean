import Lax68.Stars
import Lax68.Planar

/-!
---
title: Stars are planar
type: opn
---
Every star graph is planar.
-/

set_option autoImplicit false

namespace Lax68.StarPlanar

/-- Every finite star graph is planar. -/
axiom star_planar {V : Type*} [Finite V] {G : SimpleGraph V} :
  Lax68.Stars.IsStar G →
  Lax68.Planar.IsPlanar G

end Lax68.StarPlanar
