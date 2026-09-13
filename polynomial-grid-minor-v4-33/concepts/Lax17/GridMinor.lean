import Lax17.Grid
import Lax17.Minor

/-!
---
title: Square grid minors
type: definition
---
A graph contains a square grid minor of order \(g\) when the canonical
\(g\times g\) square grid is a minor of it.

Because graph-minor containment is invariant under relabelling, choosing the
canonical coordinate grid loses no generality.
-/

namespace Lax17.GridMinor

universe u

/-- `G` contains the `g × g` square grid as a minor. -/
def ContainsGridMinor {V : Type u} (G : SimpleGraph V) (g : ℕ) : Prop :=
  Lax17.Minor.IsMinor (Lax17.Grid.squareGrid g) G

end Lax17.GridMinor
