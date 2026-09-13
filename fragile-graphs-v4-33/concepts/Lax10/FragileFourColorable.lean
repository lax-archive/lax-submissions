import Lax10.Fragile

/-!
---
title: Graphs without a 3-connected subgraph are 4-colorable
type: theorem
---
Every finite simple graph with no $3$-connected subgraph is $4$-colorable.
-/

namespace Lax10.FragileFourColorable

universe u

open Lax10.ThreeConnectedAndColorable
open Lax10.Fragile

/-- Every finite simple graph with no $3$-connected subgraph is $4$-colorable. -/
axiom fragile_four_colorable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hfragile : HasNoThreeConnectedSubgraph G) :
    KColorable 4 G

end Lax10.FragileFourColorable
