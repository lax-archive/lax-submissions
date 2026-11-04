import Lax185574.Flips
import Lax185574.GraphBalls

/-!
---
title: Converting the flip metric of a partition into a single flip
type: lemma
---
Let G be a graph and let 𝒫 be a partition of V(G). There is a refinement
𝒬 of 𝒫 with |𝒬| ≤ |𝒫| · 2^|𝒫| and a 𝒬-flip H of G such that, for every
v ∈ V(G) and r ∈ ℕ,

Ball^H_r(v) ⊆ Ball^𝒫_{6r}(v).

This is Lemma 8 of the cited work on separability properties of
monadically dependent graph classes.

# Formalization notes

The graph is finite, so the numbers of parts are natural numbers, the
cardinalities of the quotients. The refinement 𝒬 and the flip H are
chosen once, before the vertex v and the radius r. The ball Ball^H_r(v)
is `GraphBalls.graphBall H r {v}`, and Ball^𝒫_{6r}(v) is the flip-metric
ball `Flips.flipBall`.
-/

namespace Lax185574.PartitionMetricConversion

open Lax185574.Flips Lax185574.GraphBalls

universe u

/-- **Partition-metric conversion.** A refinement `𝒬` of `𝒫` with at
most `|𝒫| · 2^|𝒫|` parts carries a single flip whose radius-`r` balls lie
in the radius-`6r` balls of the flip metric of `𝒫`. -/
axiom exists_refinement_flip {V : Type u} [Finite V] (G : SimpleGraph V)
    (P : Setoid V) :
    ∃ Q : Setoid V, Q ≤ P ∧
      Nat.card (Quotient Q) ≤ Nat.card (Quotient P) * 2 ^ Nat.card (Quotient P) ∧
      ∃ H : SimpleGraph V, IsFlip G Q H ∧
        ∀ (v : V) (r : ℕ), graphBall H r {v} ⊆ flipBall G P (6 * r) v

end Lax185574.PartitionMetricConversion
