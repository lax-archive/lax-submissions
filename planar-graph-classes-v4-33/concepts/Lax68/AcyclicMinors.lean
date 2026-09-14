import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Lax68.GraphMinors

/-!
---
title: Minors of acyclic graphs are acyclic
type: theorem
---
Every minor of an acyclic graph is acyclic. Consequently, a graph containing
a cycle cannot be a minor of a tree.
-/

set_option autoImplicit false

namespace Lax68.AcyclicMinors

/-- Taking a graph minor preserves acyclicity. -/
axiom acyclic_minor {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} :
  G.IsAcyclic → Lax68.GraphMinors.IsMinor H G → H.IsAcyclic

end Lax68.AcyclicMinors
