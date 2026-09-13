import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
---
title: Graph minors
type: definition
---
A graph \(H\) is a minor of a graph \(G\) when every vertex of \(H\) can be
represented by a nonempty connected branch set of vertices of \(G\), distinct
branch sets are disjoint, and every edge of \(H\) is represented by an edge of
\(G\) between the corresponding branch sets.

This is the standard branch-set definition. It applies to arbitrary simple
graphs; the polynomial grid-minor theorem later specializes the host graph to
a finite vertex type.
-/

namespace Lax17.Minor

universe u v

/-- Branch-set data witnessing that `H` is a minor of `G`. -/
structure Model {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set representing each vertex of `H`. -/
  branchSet : W → Set V
  /-- Every branch set is nonempty. -/
  branch_nonempty : ∀ w : W, (branchSet w).Nonempty
  /-- Every branch set induces a connected graph in `G`. -/
  branch_connected :
    ∀ w : W, (G.induce (branchSet w)).Connected
  /-- Branch sets representing distinct vertices are disjoint. -/
  branch_disjoint :
    ∀ ⦃x y : W⦄, x ≠ y → Disjoint (branchSet x) (branchSet y)
  /-- Every edge of `H` is represented by an edge between branch sets. -/
  adjacent :
    ∀ ⦃x y : W⦄, H.Adj x y →
      ∃ a ∈ branchSet x, ∃ b ∈ branchSet y, G.Adj a b

/-- `H` is a graph minor of `G`. -/
def IsMinor {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (Model H G)

end Lax17.Minor
