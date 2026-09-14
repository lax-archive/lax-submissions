import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
---
title: Paths
type: definition
---

![Path graph illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/4dd917c8b9a1e181ec951b7f6fa384262af31fa9/planar-graph-classes-v4-33/assets/path.svg "Path graph illustration")

A finite path graph is a graph isomorphic to the standard path graph on a
positive number of vertices.
-/

set_option autoImplicit false

namespace Lax68.Paths

def HasPathShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ,
    0 < n ∧
    Nonempty (G ≃g SimpleGraph.pathGraph n)

def IsPath {V : Type*} (G : SimpleGraph V) : Prop :=
  HasPathShape G

end Lax68.Paths
