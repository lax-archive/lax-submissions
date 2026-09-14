import Lax68.Triangles
import Lax68.MaximalOuterplanar

/-!
---
title: Triangles are maximal outerplanar
type: theorem
---
Every triangle is maximal outerplanar.

Open in this formalization: no proof is supplied yet.
-/

set_option autoImplicit false

namespace Lax68.TriangleMaximalOuterplanar

/-- Every triangle is maximal outerplanar.

Open in this formalization: no proof is supplied yet. -/
axiom triangle_maximalOuterplanar
    {V : Type*} {G : SimpleGraph V} :
  Lax68.Triangles.IsTriangle G →
  Lax68.MaximalOuterplanar.IsMaximalOuterplanar G

end Lax68.TriangleMaximalOuterplanar
