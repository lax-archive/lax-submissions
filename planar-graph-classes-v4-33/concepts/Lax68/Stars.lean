import Mathlib.Combinatorics.SimpleGraph.UniversalVerts

/-!
---
title: Stars
type: definition
---

![Star graph illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/4dd917c8b9a1e181ec951b7f6fa384262af31fa9/planar-graph-classes-v4-33/assets/star.svg "Star graph illustration")

A star has a centre adjacent to every other vertex and has no edges between
two non-central vertices.
-/

set_option autoImplicit false

namespace Lax68.Stars

def HasStarShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ centre : V,
    centre ∈ G.universalVerts ∧
    ∀ ⦃u v⦄, G.Adj u v → u = centre ∨ v = centre

def IsStar {V : Type*} (G : SimpleGraph V) : Prop :=
  HasStarShape G

end Lax68.Stars
