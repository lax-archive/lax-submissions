import Mathlib.Combinatorics.SimpleGraph.Hasse
import Lax68.GridsAndWalls
import Lax68.Outerplanar
import Lax68.Planar
import Lax68.SeriesParallel

/-!
---
title: Ladders
type: definition
---
A finite ladder is a nonempty two-row grid: two paths joined by corresponding
rungs.
-/

set_option autoImplicit false

namespace Lax68.Ladders

def HasLadderShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ,
    0 < n ∧
    Nonempty
      (G ≃g (SimpleGraph.pathGraph n □ SimpleGraph.pathGraph 2))

def IsLadder {V : Type*} (G : SimpleGraph V) : Prop :=
  HasLadderShape G

/-- Every ladder graph is a two-row grid. -/
axiom ladder_grid {V : Type*} {G : SimpleGraph V} :
  Lax68.Ladders.IsLadder G →
  Lax68.GridsAndWalls.IsGrid G

/-- Every ladder graph is outerplanar.

Open in this formalization: no proof is supplied yet. -/
axiom ladder_outerplanar {V : Type*} {G : SimpleGraph V} :
  Lax68.Ladders.IsLadder G →
  Lax68.Outerplanar.IsOuterplanar G

/-- Every ladder graph is series-parallel.

Open in this formalization: no proof is supplied yet. -/
axiom ladder_seriesParallel {V : Type*} {G : SimpleGraph V} :
  Lax68.Ladders.IsLadder G →
  Lax68.SeriesParallel.IsSeriesParallel G

/-- Every ladder graph is planar. -/
axiom ladder_planar {V : Type*} {G : SimpleGraph V} :
  Lax68.Ladders.IsLadder G →
  Lax68.Planar.IsPlanar G

end Lax68.Ladders
