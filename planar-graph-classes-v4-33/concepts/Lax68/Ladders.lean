import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
---
title: Ladders
type: definition
---

![Ladder graph illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/4dd917c8b9a1e181ec951b7f6fa384262af31fa9/planar-graph-classes-v4-33/assets/ladder.svg "Ladder graph illustration")

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

end Lax68.Ladders
