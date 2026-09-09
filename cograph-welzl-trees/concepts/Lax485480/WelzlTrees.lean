import Lax195003.WelzlOrders
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice

/-!
---
title: Welzl trees
type: definition
---
Let `𝒜` be a set system on a finite ground set and let *T* be a spanning
tree of that ground set.  A member *X* of `𝒜` crosses an edge of *T* when
exactly one endpoint of the edge belongs to *X*.  Its tree crossing count is
the number of crossed edges, and the crossing number of *T* is the largest
such count over all members of `𝒜`.  A Welzl tree of crossing number at
most *k* is a spanning tree whose crossing number is at most *k*.

# Formalization notes

An edge is represented by its unordered pair of endpoints.  The cut of *X*
is defined with `Sym2.fromRel` from the symmetric relation saying that the
endpoints lie on opposite sides of *X*; intersecting this cut with the edge
set of *T* therefore counts every crossed edge exactly once.

A spanning tree is a `SimpleGraph.IsTree` on the entire ground type, so no
separate spanning field is needed.  The crossing number is a natural
supremum, following the Welzl-order definition.  It is bounded by the finite
number of pairs of ground elements, and `sSup ∅ = 0` supplies the expected
value for an empty set system.  `IsWelzlTree` is a proposition rather than a
structure carrying data already determined by the tree and set system.
-/

namespace Lax485480.WelzlTrees

open Lax195003.WelzlOrders

/-- The symmetric cut relation determined by `X`: its two arguments lie on
opposite sides of `X`. -/
def SeparatedBy {V : Type*} (X : Set V) (u v : V) : Prop :=
  u ∈ X ↔ v ∉ X

/-- The unordered pairs whose endpoints lie on opposite sides of `X`. -/
def cutEdges {V : Type*} (X : Set V) : Set (Sym2 V) :=
  Sym2.fromRel (r := SeparatedBy X) (by
    intro u v
    simp only [SeparatedBy]
    tauto)

/-- The number of edges of `T` crossed by `X`. -/
noncomputable def treeCrossingCount {n : ℕ} (T : SimpleGraph (Fin n))
    (X : Set (Fin n)) : ℕ :=
  (T.edgeSet ∩ cutEdges X).ncard

/-- The largest tree crossing count of a member of `𝒜`. -/
noncomputable def treeCrossingNumber {n : ℕ} (𝓕 : SetSystem (Fin n))
    (T : SimpleGraph (Fin n)) : ℕ :=
  sSup {k : ℕ | ∃ X ∈ 𝓕, k = treeCrossingCount T X}

/-- `T` is a spanning Welzl tree of crossing number at most `k` for `𝒜`. -/
def IsWelzlTree {n : ℕ} (𝓕 : SetSystem (Fin n))
    (T : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  T.IsTree ∧ treeCrossingNumber 𝓕 T ≤ k

end Lax485480.WelzlTrees
