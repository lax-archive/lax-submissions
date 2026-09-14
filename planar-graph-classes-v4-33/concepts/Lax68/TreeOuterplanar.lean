import Lax68.Trees
import Lax68.Outerplanar

/-!
---
title: Trees are outerplanar
type: theorem
---
Every finite tree is outerplanar.

Open in this formalization: no proof is supplied yet.
-/

set_option autoImplicit false

namespace Lax68.TreeOuterplanar

/-- Every finite tree is outerplanar.

Open in this formalization: no proof is supplied yet. -/
axiom tree_outerplanar {V : Type*} [Finite V] {G : SimpleGraph V} :
  Lax68.Trees.IsTree G →
  Lax68.Outerplanar.IsOuterplanar G

end Lax68.TreeOuterplanar
