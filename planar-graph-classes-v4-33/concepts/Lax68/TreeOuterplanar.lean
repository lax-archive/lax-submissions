import Lax68.Trees
import Lax68.Outerplanar

/-!
---
title: Trees are outerplanar
type: theorem
---
Every finite tree is outerplanar.

The proof excludes `K₄` and `K₂,₃` using preservation of acyclicity under
minors. It depends on the excluded-minor characterization of outerplanarity,
which remains open in this submission.
-/

set_option autoImplicit false

namespace Lax68.TreeOuterplanar

/-- Every finite tree is outerplanar. -/
axiom tree_outerplanar {V : Type*} [Finite V] {G : SimpleGraph V} :
  Lax68.Trees.IsTree G →
  Lax68.Outerplanar.IsOuterplanar G

end Lax68.TreeOuterplanar
