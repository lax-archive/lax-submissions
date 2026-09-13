import Lax10.ThreeConnectedAndColorable

/-!
---
title: Fragile and m-fragile graphs
type: definition
---
An $m$-fragile graph is a graph whose $3$-connected subgraphs are all
$(m - 1)$-colorable. A fragile graph is a graph with no $3$-connected
subgraph.
-/

namespace Lax10.Fragile

universe u

variable {V : Type u}

open Lax10.ThreeConnectedAndColorable

/--
An $m$-fragile graph is one whose $3$-connected subgraphs are all
$(m - 1)$-colorable.
-/
def MFragile (m : Nat) (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, ThreeConnected H.coe → KColorable (m - 1) H.coe

/-- A graph is fragile when none of its subgraphs is $3$-connected. -/
def HasNoThreeConnectedSubgraph (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, ¬ ThreeConnected H.coe

end Lax10.Fragile
