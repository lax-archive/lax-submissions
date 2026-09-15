import Lax68.Triangles
import Lax68.MaximalOuterplanar

/-!
---
title: Triangles are maximal outerplanar
type: theorem
---
Every triangle is maximal outerplanar.

A triangle is drawn using three explicit points on a circle. Since the
triangle is complete, no further edge can be added on its existing vertices.
-/

set_option autoImplicit false

namespace Lax68.TriangleMaximalOuterplanar

/-- Every triangle is maximal outerplanar. -/
axiom triangle_maximalOuterplanar
    {V : Type*} {G : SimpleGraph V} :
  Lax68.Triangles.IsTriangle G →
  Lax68.MaximalOuterplanar.IsMaximalOuterplanar G

end Lax68.TriangleMaximalOuterplanar
