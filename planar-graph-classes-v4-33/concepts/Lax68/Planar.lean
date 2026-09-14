import Lax68.GraphMinors
import Lax68.StraightLineDrawings

/-!
---
title: Planar graphs
type: definition
---
A graph is planar here when it has a crossing-free straight-line drawing in
the real plane. For finite simple graphs, this agrees with the usual notion
of planarity. The drawing certificate is supplied by a separate concept.
-/

set_option autoImplicit false

namespace Lax68.Planar

/-- Existence of a crossing-free straight-line drawing in the real plane. -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  StraightLineDrawings.HasStraightLineDrawing G

def IsPlanarByExcludedMinors {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬GraphMinors.IsMinor GraphMinors.K5 G ∧
  ¬GraphMinors.IsMinor GraphMinors.K33 G

end Lax68.Planar
