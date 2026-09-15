import Lax68.Wheels
import Lax68.HalinGraphs

/-!
---
title: Wheels are Halin graphs
type: opn
---
Every wheel graph is a Halin graph.

Open in this formalization: no proof is supplied yet.
-/

set_option autoImplicit false

namespace Lax68.WheelHalin

/-- Every wheel graph is a Halin graph.

Open in this formalization: no proof is supplied yet. -/
axiom wheel_halin
    {V : Type*} {G : SimpleGraph V} :
  Lax68.Wheels.IsWheel G →
  Lax68.HalinGraphs.IsHalin G

end Lax68.WheelHalin
