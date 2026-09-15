import Lax68.GraphMinors
import Lax68.StraightLineDrawings

/-!
---
title: Outerplanar graphs
type: definition
---

![Outerplanar graph illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/d475531e6ec14f564ed7488033e83d43ae8bd5e6/planar-graph-classes-v4-33/assets/outerplanar.svg "Outerplanar graph illustration")

A graph is outerplanar here when it has a crossing-free straight-line drawing
with every vertex on one circle, a compact certificate for having every
vertex on the boundary of the outer face.
-/

set_option autoImplicit false

namespace Lax68.Outerplanar

structure OuterplaneDrawing {V : Type*} (G : SimpleGraph V)
    extends StraightLineDrawings.StraightLineDrawing G where
  radius : ℝ
  radius_pos : 0 < radius
  onBoundary :
    ∀ v : V,
      let p := toStraightLineDrawing.point v
      p.1 ^ 2 + p.2 ^ 2 = radius ^ 2

def IsOuterplanar {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (OuterplaneDrawing G)

/-- The usual forbidden-minor characterization of outerplanarity. -/
def IsOuterplanarByExcludedMinors {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ GraphMinors.IsMinor GraphMinors.K4 G ∧
  ¬ GraphMinors.IsMinor GraphMinors.K23 G

end Lax68.Outerplanar
