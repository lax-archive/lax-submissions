import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
---
title: Square grid graphs
type: definition
---
The square grid of order \(g\) has vertex set
\(\{0,\ldots,g-1\}\times\{0,\ldots,g-1\}\). Two vertices are adjacent when
they agree in one coordinate and are consecutive in the other.

The definition is the Cartesian box product of two copies of mathlib's
finite path graph. Thus order zero gives the empty graph and order one gives
a single isolated vertex.
-/

namespace Lax17.Grid

/-- The canonical `g × g` square grid. -/
def squareGrid (g : ℕ) : SimpleGraph (Fin g × Fin g) :=
  SimpleGraph.pathGraph g □ SimpleGraph.pathGraph g

end Lax17.Grid
