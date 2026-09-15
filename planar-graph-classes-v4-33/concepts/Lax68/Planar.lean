import Lax68.GraphMinors
import Lax68.StraightLineDrawings

/-!
---
title: Planar graphs
type: definition
---

![Planar graph illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/1d7f2bc99763b554a5d59824c6c0d682f8241254/planar-graph-classes-v4-33/assets/planar.svg "Planar graph illustration")

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
