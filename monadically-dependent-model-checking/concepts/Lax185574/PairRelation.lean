import Lax185574.BipartiteGraphs
import Lax185574.Partitions
import Lax185574.GaifmanGraph

/-!
---
title: Pairs at distance at most 5 in both polarities
type: definition
---
Let G be a graph and 𝒫 a partition of V = V(G). Define
R = R(G, 𝒫) ⊆ (V choose 2) so that for all parts X, Y ∈ 𝒫 (possibly
X = Y) and pairs uv with u ∈ X, v ∈ Y and u ≠ v, we have uv ∈ R if and
only if

dist^{G[X,Y]}(u, v) ≤ 5  and  dist^{Ḡ[X,Y]}(u, v) ≤ 5.

# Formalization notes

The relation is a simple graph on V. For a pair uv the parts are
X = 𝒫(u) and Y = 𝒫(v), and the distances are those from the left copy of
u to the right copy of v in the graphs `pairGraph G X Y` and
`coPairGraph G X Y` of `Lax185574.BipartiteGraphs`, measured by walks.
When X = Y the vertices u and v lie in opposite copies of X, as in the
paper. `SimpleGraph.fromRel` removes the pairs with u = v and
symmetrizes. The condition is already symmetric in u and v, since
exchanging the two copies of V maps G[X, Y] to G[Y, X].
-/

namespace Lax185574.PairRelation

open Lax185574.BipartiteGraphs Lax185574.Partitions Lax185574.GaifmanGraph

universe z

variable {V : Type z}

/-- The relation `R(G, 𝒫)`: distinct `u` and `v` are related if they
are within distance `5` both in `G[𝒫(u), 𝒫(v)]` and in
`Ḡ[𝒫(u), 𝒫(v)]`. -/
def pairRelation (G : SimpleGraph V) (P : Setoid V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v =>
    WithinDist (pairGraph G (part P u) (part P v)) 5 (.inl u) (.inr v) ∧
      WithinDist (coPairGraph G (part P u) (part P v)) 5 (.inl u) (.inr v)

end Lax185574.PairRelation
