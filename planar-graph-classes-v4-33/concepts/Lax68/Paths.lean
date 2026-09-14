import Mathlib.Combinatorics.SimpleGraph.Hasse
import Lax68.Outerplanar
import Lax68.Planar
import Lax68.Trees

/-!
---
title: Paths
type: definition
---
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

/-- Every path graph is a tree. -/
axiom path_tree {V : Type*} {G : SimpleGraph V} :
  Lax68.Paths.IsPath G →
  Lax68.Trees.IsTree G

/-- Every path graph is outerplanar. -/
axiom path_outerplanar {V : Type*} {G : SimpleGraph V} :
  Lax68.Paths.IsPath G →
  Lax68.Outerplanar.IsOuterplanar G

/-- Every path graph is planar. -/
axiom path_planar {V : Type*} {G : SimpleGraph V} :
  Lax68.Paths.IsPath G →
  Lax68.Planar.IsPlanar G

end Lax68.Paths
