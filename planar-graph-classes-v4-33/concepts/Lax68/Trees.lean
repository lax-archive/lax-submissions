import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Lax68.Outerplanar
import Lax68.Planar

/-!
---
title: Trees
type: definition
---
A tree is a connected acyclic simple graph, using mathlib's native
`SimpleGraph.IsTree` predicate.
-/

set_option autoImplicit false

namespace Lax68.Trees

def IsTree {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsTree

/-- Every finite tree is outerplanar. -/
axiom tree_outerplanar {V : Type*} [Finite V] {G : SimpleGraph V} :
  Lax68.Trees.IsTree G →
  Lax68.Outerplanar.IsOuterplanar G

/-- Every finite tree is planar. -/
axiom tree_planar {V : Type*} [Finite V] {G : SimpleGraph V} :
  Lax68.Trees.IsTree G →
  Lax68.Planar.IsPlanar G

end Lax68.Trees
