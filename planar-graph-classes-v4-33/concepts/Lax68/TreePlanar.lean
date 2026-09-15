import Lax68.Trees
import Lax68.Planar

/-!
---
title: Trees are planar
type: theorem
---
Every finite tree is planar.
-/

set_option autoImplicit false

namespace Lax68.TreePlanar

/-- Every finite tree is planar. -/
axiom tree_planar {V : Type*} [Finite V] {G : SimpleGraph V} :
  Lax68.Trees.IsTree G →
  Lax68.Planar.IsPlanar G

end Lax68.TreePlanar
