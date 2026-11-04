import Lax185574.TypeSplitting
import Lax185574.Flips
import Lax185574.VCDimension

/-!
---
title: Splitting by a transversal keeps few parts in flip-metric balls
type: lemma
---
Let G be a graph, 𝒫 ≼ 𝒬 partitions of V(G), and T a transversal of 𝒫.
Suppose |Ball^𝒬_{r+1}(v)/𝒫| ≤ k for every v ∈ V(G). Then for every
v ∈ V(G),

|Ball^𝒬_r(v)/(𝒫 ∧ T)| ≤ k · π_G(k).

This is Corollary 5.4 of Drabik, Dumas, Geniet, Nowakowski, Pilipczuk and
Toruńczyk, *Variants of merge-width and applications* (2026).

# Formalization notes

The balls are those of the 𝒬-flip metric, `Flips.flipBall`, and 𝒫 ∧ T
is `TypeSplitting.split`. The neighborhood complexity π_G is
`VCDimension.neighborhoodComplexity`. The graph is finite, so that the
counts of parts are exact. The radius r and the bound k are arbitrary
natural numbers.
-/

namespace Lax185574.SplitBalls

open Lax185574.Partitions Lax185574.Flips Lax185574.TypeSplitting Lax185574.VCDimension

universe z

/-- **Splitting along a transversal.** If every radius-`(r+1)` ball of
the `𝒬`-flip metric meets at most `k` parts of `𝒫 ≼ 𝒬`, then every
radius-`r` ball meets at most `k · π_G(k)` parts of `𝒫 ∧ T`. -/
axiom partCount_split_le {V : Type z} [Finite V] (G : SimpleGraph V) (P Q : Setoid V)
    (T : Set V) (r k : ℕ) (hPQ : P ≤ Q) (hT : IsTransversal P T)
    (hk : ∀ v : V, partCount P (flipBall G Q (r + 1) v) ≤ k) (v : V) :
    partCount (split G P T) (flipBall G Q r v) ≤ k * neighborhoodComplexity G k

end Lax185574.SplitBalls
