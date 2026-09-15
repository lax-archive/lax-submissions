import Lax68.Stars
import Lax68.Outerplanar

/-!
---
title: Stars are outerplanar
type: theorem
---
Every star graph is outerplanar.
-/

set_option autoImplicit false

namespace Lax68.StarOuterplanar

/-- Every finite star graph is outerplanar. -/
axiom star_outerplanar {V : Type*} [Finite V] {G : SimpleGraph V} :
  Lax68.Stars.IsStar G →
  Lax68.Outerplanar.IsOuterplanar G

end Lax68.StarOuterplanar
