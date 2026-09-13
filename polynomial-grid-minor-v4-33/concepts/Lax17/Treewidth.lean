import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
---
title: Treewidth
type: definition
---
A tree decomposition of a finite simple graph consists of a finite tree and
a bag of graph vertices at every tree node. Every graph vertex occurs in a
bag, the endpoints of every graph edge occur together in a bag, and the tree
nodes whose bags contain any fixed graph vertex induce a connected subtree.

The width of a decomposition is its largest bag cardinality minus one, using
natural-number subtraction. The treewidth of a graph is the least width of
any of its tree decompositions. The natural-number convention gives the empty
graph treewidth zero.
-/

namespace Lax17.Treewidth

universe u

/-- A finite tree decomposition of a simple graph. -/
structure TreeDecomposition {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) where
  /-- The node type of the decomposition tree. -/
  Node : Type
  /-- The decomposition tree has finitely many nodes. -/
  [nodeFintype : Fintype Node]
  /-- Decomposition-tree nodes have decidable equality. -/
  [nodeDecidableEq : DecidableEq Node]
  /-- The tree on decomposition nodes. -/
  tree : SimpleGraph Node
  /-- The node graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag assigned to each decomposition node. -/
  bag : Node → Finset V
  /-- Every graph vertex occurs in a bag. -/
  vertex_mem_bag : ∀ v : V, ∃ i : Node, v ∈ bag i
  /-- The endpoints of every graph edge occur together in a bag. -/
  edge_mem_bag :
    ∀ ⦃x y : V⦄, G.Adj x y → ∃ i : Node, x ∈ bag i ∧ y ∈ bag i
  /-- Bags containing a fixed graph vertex induce a connected subtree. -/
  bag_indices_connected :
    ∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected

namespace TreeDecomposition

/-- The maximum bag cardinality minus one. -/
noncomputable def width {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} (D : TreeDecomposition G) : ℕ :=
  letI : Fintype D.Node := D.nodeFintype
  (Finset.univ.sup fun i : D.Node => (D.bag i).card) - 1

end TreeDecomposition

/-- `G` has a tree decomposition of width at most `k`. -/
def HasTreewidthAtMost {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : TreeDecomposition G, D.width ≤ k

/-- The least width of a tree decomposition of `G`.

The fallback makes the definition total. For a finite graph it is unreachable,
because the decomposition with one bag containing every vertex always exists.
-/
noncomputable def treewidth {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  letI := Classical.decPred (HasTreewidthAtMost G)
  letI := Classical.propDecidable (∃ k, HasTreewidthAtMost G k)
  if h : ∃ k, HasTreewidthAtMost G k then Nat.find h else 0

end Lax17.Treewidth
