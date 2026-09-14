import Lax68.MaximalOuterplanar
import Lax68.Outerplanar

/-!
---
title: Maximal outerplanar graphs are outerplanar
type: theorem
---
Every maximal outerplanar graph is outerplanar.
-/

set_option autoImplicit false

namespace Lax68.MaximalOuterplanarOuterplanar

/-- Every maximal outerplanar graph is outerplanar. -/
axiom maximalOuterplanar_outerplanar {V : Type*} {G : SimpleGraph V} :
  Lax68.MaximalOuterplanar.IsMaximalOuterplanar G →
  Lax68.Outerplanar.IsOuterplanar G

end Lax68.MaximalOuterplanarOuterplanar
