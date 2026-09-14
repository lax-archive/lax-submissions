import Lax68.Outerplanar

/-!
---
title: The excluded-minor characterization of outerplanarity
type: theorem
---
For every finite simple graph, having an outerplane drawing is equivalent to
containing neither *K₄* nor *K₂,₃* as a minor.

This is the standard excluded-minor characterization of outerplanar graphs.
It is an open theorem in this submission.
-/

set_option autoImplicit false

namespace Lax68.OuterplanarExcludedMinors

/-- A finite graph is outerplanar exactly when it has neither `K₄` nor `K₂,₃`
as a minor. This remains open in the present formalization. -/
axiom outerplanar_iff_excludedMinors
    {V : Type*} {G : SimpleGraph V} :
  Finite V →
  (Lax68.Outerplanar.IsOuterplanar G ↔
    Lax68.Outerplanar.IsOuterplanarByExcludedMinors G)

end Lax68.OuterplanarExcludedMinors
