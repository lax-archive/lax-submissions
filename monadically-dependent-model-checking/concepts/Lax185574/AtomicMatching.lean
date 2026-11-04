import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Fin.Basic

/-!
---
title: Atomically matched tuples
type: definition
---
For a graph G and tuples ā, b̄ ∈ V(G)^t, the tuples ā = a₁ … a_t and
b̄ = b₁ … b_t are *atomically matched* if there is a relation
∼ ∈ {=, ≠, ≥} such that G ⊨ E(aᵢ, bⱼ) if and only if i ∼ j, for all
i, j ∈ [t]. In particular, the bipartite graph semi-induced between the
tuples ā and b̄ is a matching, a co-matching, or a half-graph.

# Formalization notes

Positions are `Fin t`, which is [t] shifted by one and carries the same
order. The relation i ≥ j is written j ≤ i. Only the adjacency between
the entries of ā and the entries of b̄ is constrained. The entries need
not be distinct, although the conditions force some distinctness, for
instance aᵢ ≠ bᵢ in the case of =.
-/

namespace Lax185574.AtomicMatching

universe u

variable {V : Type u}

/-- The tuples `a` and `b` are atomically matched in `G`: adjacency of
`a i` and `b j` is described by `i = j`, by `i ≠ j`, or by `i ≥ j`. -/
def AtomicallyMatched (G : SimpleGraph V) {t : ℕ} (a b : Fin t → V) : Prop :=
  (∀ i j, G.Adj (a i) (b j) ↔ i = j) ∨
  (∀ i j, G.Adj (a i) (b j) ↔ i ≠ j) ∨
  (∀ i j, G.Adj (a i) (b j) ↔ j ≤ i)

end Lax185574.AtomicMatching
