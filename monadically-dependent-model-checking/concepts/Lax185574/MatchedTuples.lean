import Lax185574.AtomicMatching
import Lax185574.AtomicTypes
import Lax185574.BipartiteGraphs
import Mathlib.Computability.Partrec

/-!
---
title: Many atomic types force atomically matched tuples
type: theorem
---
There exists a computable function Q : ℕ → ℕ such that for every ℓ ∈ ℕ
and for every bipartite graph G = (L, R, E) with |ATypes(L/R)| > Q(ℓ),
there are two tuples ā ∈ L^ℓ and b̄ ∈ R^ℓ that are atomically matched
in G.

This is Corollary 2.4 of Ding, Oporowski, Oxley and Vertigan (1996), see
also Theorem 2 of Gravier, Maffray, Renault and Trotignon (2004).

# Formalization notes

A bipartite graph (L, R, E) is given by two finite types L and R and a
relation E between them. Its graph is the simple graph on L ⊕ R whose
edges are the pairs related by E, `BipartiteGraphs.bipartiteGraph E`. The number
|ATypes(L/R)| is `AtomicTypes.atomicTypeCount` of this graph, for the
vertices of L over the vertices of R. Since L and R are disjoint, it is
the number of distinct neighborhoods of vertices of L. Computability of
Q is mathlib's `Computable`. The two sides are finite, which covers the
use in the paper inside the proof of the ball-types lemma.
-/

namespace Lax185574.MatchedTuples

open Lax185574.AtomicMatching Lax185574.AtomicTypes Lax185574.BipartiteGraphs

universe u v

/-- **Matchings, co-matchings and half-graphs.** A computable `Q` such
that a bipartite graph whose left side realizes more than `Q(ℓ)` atomic
types over the right side contains atomically matched `ℓ`-tuples, one
from each side. -/
axiom exists_atomicallyMatched :
    ∃ Q : ℕ → ℕ, Computable Q ∧
      ∀ (ℓ : ℕ) (L : Type u) (R : Type v) [Finite L] [Finite R] (E : L → R → Prop),
        Q ℓ < atomicTypeCount (bipartiteGraph E) (Set.range Sum.inl)
            (Set.range Sum.inr) →
          ∃ (a : Fin ℓ → L) (b : Fin ℓ → R),
            AtomicallyMatched (bipartiteGraph E) (Sum.inl ∘ a) (Sum.inr ∘ b)

end Lax185574.MatchedTuples
