import Mathlib.Combinatorics.SimpleGraph.UniversalVerts
import Lax68.Outerplanar
import Lax68.Planar
import Lax68.Trees

/-!
---
title: Stars
type: definition
---
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

/-- Every star graph is a tree. -/
axiom star_tree {V : Type*} {G : SimpleGraph V} :
  Lax68.Stars.IsStar G →
  Lax68.Trees.IsTree G

/-- Every finite star graph is outerplanar. -/
axiom star_outerplanar {V : Type*} [Finite V] {G : SimpleGraph V} :
  Lax68.Stars.IsStar G →
  Lax68.Outerplanar.IsOuterplanar G

/-- Every finite star graph is planar. -/
axiom star_planar {V : Type*} [Finite V] {G : SimpleGraph V} :
  Lax68.Stars.IsStar G →
  Lax68.Planar.IsPlanar G

end Lax68.Stars
