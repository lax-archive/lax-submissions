import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
---
title: Trees
type: definition
---

![Tree illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/4dd917c8b9a1e181ec951b7f6fa384262af31fa9/planar-graph-classes-v4-33/assets/tree.svg "Tree illustration")

A tree is a connected acyclic simple graph, using mathlib's native
`SimpleGraph.IsTree` predicate.
-/

set_option autoImplicit false

namespace Lax68.Trees

def IsTree {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsTree

end Lax68.Trees
