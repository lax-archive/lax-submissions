import Lax68.Wheels
import Lax68.Planar

/-!
---
title: Wheels are planar
type: opn
---
Every wheel graph is planar.
-/

set_option autoImplicit false

namespace Lax68.WheelPlanar

/-- Every wheel graph is planar. -/
axiom wheel_planar
    {V : Type*} {G : SimpleGraph V} :
  Lax68.Wheels.IsWheel G →
  Lax68.Planar.IsPlanar G

end Lax68.WheelPlanar
