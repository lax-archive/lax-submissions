import Lax185574.BipartiteGraphs
import Lax185574.GaifmanGraph

/-!
---
title: A four-part flip of a bipartite graph with short edges in both polarities
type: lemma
---
Let B = (X, Y, E) be a bipartite graph with bipartite complement B̄, and
pick arbitrary vertices x ∈ X and y ∈ Y. Partition X according to
adjacency to y, that is, X = X₊ ⊎ X₋ with X₊ = N(y) and X₋ = X ∖ N(y),
and similarly Y = Y₊ ⊎ Y₋ according to x. Then there is a bipartite
graph B′ = (X, Y, E′), obtained from B by some {X₊, X₋, Y₊, Y₋}-flip,
satisfying

for all uv ∈ E′,  dist^B(u, v) ≤ 5  and  dist^{B̄}(u, v) ≤ 5.

This is Lemma A.3 of Drabik, Dumas, Geniet, Nowakowski, Pilipczuk and
Toruńczyk, *Variants of merge-width and applications* (2026).

# Formalization notes

The parts X and Y are types, and the bipartite graphs B and B̄ are
`bipartiteGraph E` and `bipartiteGraph` of the negated relation, from
`Lax185574.BipartiteGraphs`. Distances are measured by walks from the
copy of u in X to the copy of v in Y.

B′ is again bipartite with parts X and Y, so the flip changes adjacency
only between X and Y, and it is given by its edge relation E′. That B′
is obtained by a {X₊, X₋, Y₊, Y₋}-flip says that for each of the four
pairs of a part of X and a part of Y, either E′ agrees with E on all of
its pairs, or with the negation of E on all of them. The statement
expresses this as: whether E′ agrees with E on a pair uv depends only on
whether u ∈ X₊ and whether v ∈ Y₊.

The cited lemma bounds the distances by 6, and the paper states 5,
noting that the two statements are equivalent. Every walk in a
bipartite graph between a vertex of X and a vertex of Y has odd
length, so a distance at most 6 is at most 5. The statement uses the
bound 5 of the paper.
-/

namespace Lax185574.BipartiteFlip

open Lax185574.BipartiteGraphs Lax185574.GaifmanGraph

universe u w

/-- **Four-part flip of a bipartite graph.** For representatives `x`
and `y`, some flip of `E` on the four parts given by adjacency to `y`
and to `x` keeps only edges `uv` with `dist^B(u, v) ≤ 5` and
`dist^{B̄}(u, v) ≤ 5`. -/
axiom exists_flip_close {X : Type u} {Y : Type w} (E : X → Y → Prop) (x : X) (y : Y) :
    ∃ E' : X → Y → Prop,
      (∀ (u u' : X) (v v' : Y), (E u y ↔ E u' y) → (E x v ↔ E x v') →
        ((E' u v ↔ E u v) ↔ (E' u' v' ↔ E u' v'))) ∧
      ∀ (u : X) (v : Y), E' u v →
        WithinDist (bipartiteGraph E) 5 (.inl u) (.inr v) ∧
          WithinDist (bipartiteGraph fun a b => ¬ E a b) 5 (.inl u) (.inr v)

end Lax185574.BipartiteFlip
