import Lax185574.Flips
import Lax185574.Algorithms
import Lax185574.MonadicDependence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Chains of vertex sets with few atomic types in flip-metric balls
type: theorem
---
Let r ∈ ℕ and 𝒞 be a monadically dependent graph class. Then for any
rational ε > 0 and an n-vertex graph G ∈ 𝒞, there is a sequence of
vertex subsets

∅ = B_m ⊆ B_{m−1} ⊆ ⋯ ⊆ B₁ ⊆ B₀ = V(G)

with m ≤ O(r/ε) that satisfies the following condition: for every
i ∈ [m] and u ∈ V(G), Ball^r_{𝒯₁(G,B_i)}[u] intersects at most
O_{𝒞,r,ε}(n^ε) parts of 𝒯₁(G, B_{i−1}). Moreover, given ε, r and G, such
a sequence B₀, B₁, …, B_m can be computed in Õ_{𝒞,r}(n³) time.

This is Theorem 4.4 of Dreier, Mählmann, Pilipczuk and Toruńczyk,
*Monadically dependent graph classes have almost bounded merge-width*
(2026), the companion paper. Here 𝒯₁(G, B) is the
partition of V(G) into 1-types over B, that is, into atomic types, and Ball^r_𝒫[u] is the radius-r ball of the
𝒫-flip metric.

# Formalization notes

In the companion paper ℕ is the set of positive integers, so r ≥ 1. Its
1-types over B are the atomic types over B, `Partitions.atomicTypes`,
and its flips and flip-metric balls are those of `Lax185574.Flips`,
with distances measured by shortest paths. A sequence B₀, …, B_m is the
list [B₀, …, B_m], in the order of the companion paper, which is the
reverse of the order of chains in `Lax185574.Chains`. The bound m ≤
O(r/ε) on the number of steps becomes a bound K · r/ε + K on the length
m + 1 of the list.

The algorithm `A` is chosen before the class, and the sequence is a
function `chain` of r, ε and the graph that `A` computes, in the sense
of `Lax185574.Algorithms`. The companion paper notes that the algorithm
of its Damping Theorem does not depend on the class, and the algorithm
of this theorem iterates it. The bound on the length in its proof uses only the Damping Theorem for
the graph at hand, which holds for every graph with that graph's own
constants (every graph lies in the monadically dependent class {G}).
The proof gives m ≤ 1 + 2r/ε on every graph with at least two vertices,
and graphs with at most one vertex are handled directly. So the length
bound is stated for every graph. The input is the triple (r, ε, G) and
the output is the list of sets.

The time bound Õ_{𝒞,r}(n³) hides a subpolynomial factor that depends on
𝒞 and r. It is spelled out as O(n^{3+δ}) for every real δ > 0, with a
constant c chosen after 𝒞, r, ε and δ. In the companion paper the time
bound does not depend on ε, so this is weaker. The width bound is
c · (n+1)^ε with the same constant.

The algorithm of the companion paper uses integers of n^{o(1)} bits.
Stored in several words, they cost a subpolynomial factor, which the
bound O(n^{3+δ}) absorbs, so the word lengths are those of
`Lax185574.Algorithms`, with the word-length exponent of the algorithm,
which is chosen before the class.
-/

namespace Lax185574.ChainTheorem

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.Algorithms
open Lax185574.Partitions Lax185574.Flips

universe z

variable {V : Type z}

/-- `B` is a decreasing sequence of vertex sets `V = B₀ ⊇ B₁ ⊇ ⋯ ⊇ B_m = ∅`. -/
def IsDecreasingChain [Fintype V] (B : List (Finset V)) : Prop :=
  ∃ h : B ≠ [], B.head h = Finset.univ ∧ B.getLast h = ∅ ∧
    ∀ (t : ℕ) (ht : t + 1 < B.length), B[t + 1] ⊆ B[t]

/-- For every `i ∈ [m]` and vertex `u`, the radius-`r` ball around `u`
in the metric of `B_i`-flips meets at most `K` parts of the partition
into atomic types over `B_{i−1}`. -/
def BallsMeetFewTypes (G : SimpleGraph V) (r : ℕ) (K : ℝ) (B : List (Finset V)) : Prop :=
  ∀ (t : ℕ) (ht : t + 1 < B.length) (u : V),
    (partCount (atomicTypes G (B[t] : Set V))
      (flipBall G (atomicTypes G (B[t + 1] : Set V)) r u) : ℝ) ≤ K

/-- **Chain theorem of the companion paper.** One algorithm computes,
from `r ≥ 1`, a rational `ε > 0` and a graph, a decreasing sequence
`V = B₀ ⊇ ⋯ ⊇ B_m = ∅` of length at most `K · r/ε + K`. On members of a
monadically dependent class, every radius-`r` ball of the `B_i`-flip
metric meets at most `c · (n+1)^ε` atomic types over `B_{i−1}`, and the
algorithm takes time `O(n^(3+δ))` for every `δ > 0`. -/
axiom exists_program_decreasingChain :
    ∃ (A : Algorithm) (K : ℕ) (chain : ℕ → ℚ → (G : Graph) → List (Finset (Fin G.n))),
      (∀ (r : ℕ) (ε : ℚ) (G : Graph), 1 ≤ r → 0 < ε →
        IsDecreasingChain (chain r ε G) ∧ ((chain r ε G).length : ℚ) ≤ K * r / ε + K) ∧
      ∀ C : GraphClass, MonadicallyDependent C → ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε →
        ∀ δ : ℝ, 0 < δ → ∃ c : ℕ, ∀ G ∈ C,
          BallsMeetFewTypes G.toSimpleGraph r (c * ((G.n : ℝ) + 1) ^ (ε : ℝ)) (chain r ε G) ∧
          A.Computes c (r, ε, G) (chain r ε G) ((G.n : ℝ) ^ (3 + δ))

end Lax185574.ChainTheorem
