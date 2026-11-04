import Lax185574.Partitions
import Lax185574.GraphBalls
import Mathlib.Order.Lattice.Nat

/-!
---
title: Merge sequences and their radius-r width
type: definition
---
A *merge sequence* of a graph G is a sequence (𝒫₁, R₁), …, (𝒫_m, R_m)
such that:

1. 𝒫₁ is the partition into singletons and 𝒫_m = {V(G)},
2. 𝒫₁ ≼ ⋯ ≼ 𝒫_m,
3. R₁ ⊆ ⋯ ⊆ R_m ⊆ (V(G) choose 2), and
4. for every i ∈ [m] and X, Y ∈ 𝒫_i, the set XY ∖ R_i is contained
   either in E(G) or in E(Ḡ), that is, the pair X, Y is homogeneous once
   pairs in R_i are ignored.

Here XY is the set of pairs xy with x ∈ X, y ∈ Y and x ≠ y. Condition 4
says that 𝒫_i is *homogeneous modulo R_i*. The *radius-r width* of the
merge sequence is

max_{2 ≤ i ≤ m} max_{v ∈ V(G)} |Ball^{R_i}_r(v)/𝒫_{i−1}|.

The offset in the indices of R_i and 𝒫_{i−1} is intentional.

# Formalization notes

A merge sequence is a nonempty list of pairs of a partition, as in
`Lax185574.Partitions`, and a simple graph on the vertex type, whose
edges are the pairs of R_i. So R_i ⊆ (V(G) choose 2) holds by
construction, and R_i ⊆ R_{i+1} is the subgraph order. The partition
into singletons is `⊥` and the partition with one part is `⊤`.

Homogeneity modulo R names the parts X and Y by vertices a and b with
X = 𝒫(a) and Y = 𝒫(b), as for flips in `Lax185574.Flips`. The ball
Ball^{R_i}_r(v) is the ball in the graph R_i, `GraphBalls.graphBall`.
The width is the supremum of a set of natural numbers, finite on a
finite vertex type, and the empty maximum (a sequence of length one) is
0. Algorithms exchange merge sequences as lists of pairs of a partition
and a graph, in the encodings of `Lax185574.Encodings` and
`Lax185574.Partitions`.
-/

namespace Lax185574.MergeSequences

open Lax185574.Partitions Lax185574.GraphBalls

universe z

variable {V : Type z}

/-- `P` is homogeneous modulo `R`: for every pair of parts `𝒫(a)`,
`𝒫(b)`, the pairs of distinct vertices between them that are not in
`R` are all edges of `G`, or all non-edges of `G`. -/
def HomogeneousModulo (G : SimpleGraph V) (P : Setoid V) (R : SimpleGraph V) : Prop :=
  ∀ a b : V,
    (∀ x y : V, P x a → P y b → x ≠ y → ¬ R.Adj x y → G.Adj x y) ∨
      (∀ x y : V, P x a → P y b → x ≠ y → ¬ R.Adj x y → ¬ G.Adj x y)

/-- `ms` is a merge sequence of `G`: it starts with the partition into
singletons and ends with the partition with one part, the partitions
get coarser and the relations grow, and every partition is homogeneous
modulo its relation. -/
def IsMergeSequence (G : SimpleGraph V) (ms : List (Setoid V × SimpleGraph V)) : Prop :=
  ∃ h : ms ≠ [],
    (ms.head h).1 = ⊥ ∧ (ms.getLast h).1 = ⊤ ∧
    (∀ (t : ℕ) (ht : t + 1 < ms.length), ms[t].1 ≤ ms[t + 1].1 ∧ ms[t].2 ≤ ms[t + 1].2) ∧
    ∀ (t : ℕ) (ht : t < ms.length), HomogeneousModulo G ms[t].1 ms[t].2

/-- The radius-`r` width of the merge sequence `ms`: the largest number
of parts of `𝒫_t` that meet a ball of radius `r` in `R_{t+1}`. -/
noncomputable def mergeWidth (r : ℕ) (ms : List (Setoid V × SimpleGraph V)) : ℕ :=
  sSup {K | ∃ (t : ℕ) (ht : t + 1 < ms.length) (v : V),
    K = partCount ms[t].1 (graphBall ms[t + 1].2 r {v})}

end Lax185574.MergeSequences
