import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Bipartite graphs and bipartite complements
type: definition
---
A *bipartite graph* B = (X, Y, E) has parts X and Y and an edge set E
of pairs xy with x ∈ X and y ∈ Y. Its *bipartite complement*, denoted
B̄, is the bipartite graph with parts X, Y and edge set XY ∖ E.

For a graph G and disjoint vertex sets X, Y ⊆ V(G), G[X, Y] is the
bipartite graph with parts X and Y whose edges connect pairs of vertices
that are adjacent in G. Furthermore, G[X, X] denotes the bipartite
graph whose parts are two copies of X, and whose edges connect two
vertices in opposite parts if the corresponding vertices of G are
either adjacent or equal. The edges of G[X, X] connecting the two copies
of a vertex are its *diagonal edges*. Finally, Ḡ[X, X] is the bipartite
complement of G[X, X], extended with the diagonal edges.

# Formalization notes

A bipartite graph with parts α and β is given by a relation
E : α → β → Prop, and `bipartiteGraph E` is the simple graph on α ⊕ β
that it defines. The bipartite complement is `bipartiteGraph` of the
negated relation.

The graphs G[X, Y] and Ḡ[X, Y] are built uniformly on two copies of the
vertex set, V ⊕ V, as `pairGraph` and `coPairGraph`. The left copy of
X is one part and the right copy of Y is the other. A left vertex u ∈ X
and a right vertex v ∈ Y are adjacent if u = v or u and v are adjacent
in G, respectively non-adjacent in G. For X = Y this is G[X, X], with
its diagonal edges, and Ḡ[X, X]. For disjoint X and Y the case u = v
never occurs, so this is G[X, Y], and Ḡ[X, Y] is its bipartite
complement, the bipartite graph of the non-adjacent pairs. The other
vertices of V ⊕ V are isolated. So the distance from the left copy of u
to the right copy of v in `pairGraph G X Y` is the distance between u
and v in G[X, Y], and likewise for Ḡ[X, Y].
-/

namespace Lax185574.BipartiteGraphs

universe u w z

/-- The bipartite graph on `α ⊕ β` with an edge between `inl a` and
`inr b` exactly when `E a b`. -/
def bipartiteGraph {α : Type u} {β : Type w} (E : α → β → Prop) : SimpleGraph (α ⊕ β) :=
  SimpleGraph.fromRel fun s t => ∃ a b, s = .inl a ∧ t = .inr b ∧ E a b

variable {V : Type z}

/-- `G[X, Y]`, on two copies of `V`: the left copy of `u ∈ X` and the
right copy of `v ∈ Y` are adjacent if `u = v` or `u` and `v` are
adjacent in `G`. -/
def pairGraph (G : SimpleGraph V) (X Y : Set V) : SimpleGraph (V ⊕ V) :=
  bipartiteGraph fun u v => u ∈ X ∧ v ∈ Y ∧ (u = v ∨ G.Adj u v)

/-- `Ḡ[X, Y]`, on two copies of `V`: the left copy of `u ∈ X` and the
right copy of `v ∈ Y` are adjacent if `u = v` or `u` and `v` are
non-adjacent in `G`. -/
def coPairGraph (G : SimpleGraph V) (X Y : Set V) : SimpleGraph (V ⊕ V) :=
  bipartiteGraph fun u v => u ∈ X ∧ v ∈ Y ∧ (u = v ∨ ¬ G.Adj u v)

end Lax185574.BipartiteGraphs
