import Lax68.Ladders
import Lax68.Outerplanar

/-!
---
title: Ladders are outerplanar
type: theorem
---
Every ladder graph is outerplanar.

Open in this formalization: no proof is supplied yet.
-/

set_option autoImplicit false

namespace Lax68.LadderOuterplanar

/-- Every ladder graph is outerplanar.

Open in this formalization: no proof is supplied yet. -/
axiom ladder_outerplanar {V : Type*} {G : SimpleGraph V} :
  Lax68.Ladders.IsLadder G →
  Lax68.Outerplanar.IsOuterplanar G

end Lax68.LadderOuterplanar
