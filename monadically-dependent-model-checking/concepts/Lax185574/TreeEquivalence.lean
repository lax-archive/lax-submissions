import Lax185574.TypeTrees

/-!
---
title: Type trees are distance types
type: corollary
---
Fix ℓ ≤ k and q, a partial graph G and ā, b̄ ∈ V(G)^ℓ. Then
tree_{k,q}(ā) = tree_{k,q}(b̄) if and only if G ⊨ φ(ā) ⇔ φ(b̄) for every
distFO formula φ(x̄) of distance rank (k, q) with |x̄| = ℓ.

# Formalization notes

The vertex type is finite, as everywhere in the paper. Equality of type
trees is equality of the objects of `Lax185574.TypeTrees`.
-/

namespace Lax185574.TreeEquivalence

open Lax185574.PartialGraphs Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO
open Lax185574.TypeTrees

/-- **Type trees are distance types.** Two tuples have the same type
tree of rank `(k, q)` exactly when they satisfy the same formulas of
distance rank `(k, q)`. -/
axiom tree_eq_iff {V : Type*} [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ}
    (hℓ : ℓ ≤ k) (a b : Fin ℓ → V) :
    tree G k q a = tree G k q b ↔
      ∀ φ : DistFO ℓ, DRank k q φ → (Sat G a φ ↔ Sat G b φ)

end Lax185574.TreeEquivalence
