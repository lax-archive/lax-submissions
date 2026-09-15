import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Thin symmetric loopless quiver
type: definition
---
A thin symmetric loopless quiver has at most one arrow between each ordered
pair of vertices, arrows exist symmetrically in both directions, and there
are no arrows from a vertex to itself. Two such quivers on the same vertices
are isomorphic here when their arrow types are equivalent for every ordered
pair.

# Formalization notes

The structure bundles mathlib's `Quiver V`, which is normally used as a
typeclass instance. Symmetry concerns existence of arrows; thinness then
makes that existence all the edge data there is. Hom-wise equivalence is the
appropriate isomorphism notion because a quiver has no composition or
additional structure to preserve.
-/

namespace Lax683916.ThinSymmetricLooplessQuivers

universe u v w

/-- A quiver has no parallel arrows. -/
def IsThin {V : Type u} (Q : Quiver.{v} V) : Prop :=
  ∀ u v : V, Subsingleton (Q.Hom u v)

/-- A quiver has an arrow in one direction exactly when it has one in the reverse direction. -/
def IsSymmetric {V : Type u} (Q : Quiver.{v} V) : Prop :=
  ∀ u v : V, Nonempty (Q.Hom u v) ↔ Nonempty (Q.Hom v u)

/-- A quiver has no arrows from a vertex to itself. -/
def IsLoopless {V : Type u} (Q : Quiver.{v} V) : Prop :=
  ∀ u : V, IsEmpty (Q.Hom u u)

/-- A bundled quiver that is thin, symmetric, and loopless. -/
structure ThinSymmetricLooplessQuiver (V : Type u) : Type max (u + 1) (v + 1) where
  /-- The underlying quiver. -/
  quiver : Quiver.{v} V
  /-- There is at most one arrow with each fixed source and target. -/
  thin : IsThin quiver
  /-- Arrows exist symmetrically in the two directions. -/
  symmetric : IsSymmetric quiver
  /-- No arrow has equal source and target. -/
  loopless : IsLoopless quiver

/-- Two quivers on the same vertices are isomorphic when all corresponding arrow types are equivalent. -/
structure Isomorphic {V : Type u} (Q : ThinSymmetricLooplessQuiver.{u, v} V)
    (R : ThinSymmetricLooplessQuiver.{u, w} V) where
  /-- The equivalence between arrows with each fixed source and target. -/
  homEquiv : ∀ u v : V, Q.quiver.Hom u v ≃ R.quiver.Hom u v

/-- The quiver whose arrow types are lifts of a simple graph's adjacency propositions. -/
def ofSimpleGraph {V : Type u} (G : SimpleGraph V) :
    ThinSymmetricLooplessQuiver.{u, 0} V where
  quiver := ⟨fun u v ↦ PLift (G.Adj u v)⟩
  thin _ _ := ⟨fun a b ↦ by
    cases a
    cases b
    rfl⟩
  symmetric u v := by
    constructor
    · rintro ⟨h⟩
      exact ⟨⟨h.down.symm⟩⟩
    · rintro ⟨h⟩
      exact ⟨⟨h.down.symm⟩⟩
  loopless u := ⟨fun h ↦ G.loopless.irrefl u h.down⟩

end Lax683916.ThinSymmetricLooplessQuivers
