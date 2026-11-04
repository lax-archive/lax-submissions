import Lax185574.PairRelation

/-!
---
title: The pair relation grows under coarsening
type: lemma
---
Fix a graph G and partitions 𝒫 and 𝒫′ of V(G) such that 𝒫 refines 𝒫′.
Then R(G, 𝒫) ⊆ R(G, 𝒫′).

# Formalization notes

The relation R(G, 𝒫) is `PairRelation.pairRelation`, a simple graph,
and inclusion is the subgraph order. On two copies of V(G), the graph
G[X, Y] is a subgraph of G[X′, Y′] whenever X ⊆ X′ and Y ⊆ Y′, also
when X ≠ Y and X′ = Y′, and likewise for Ḡ[X, Y]. The proof in the
paper says more, that G[X, Y] is an induced subgraph of G[X′, Y′].
Distances only need the subgraph relation.
-/

namespace Lax185574.PairRelationMonotone

open Lax185574.PairRelation

universe z

/-- **Monotonicity of the pair relation.** Coarsening the partition can
only add pairs. -/
axiom pairRelation_mono {V : Type z} (G : SimpleGraph V) (P P' : Setoid V)
    (h : P ≤ P') : pairRelation G P ≤ pairRelation G P'

end Lax185574.PairRelationMonotone
