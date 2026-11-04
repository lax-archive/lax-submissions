import Lax185574.VCDimension

/-!
---
title: Polynomial neighborhood complexity from bounded VC-dimension
type: lemma
---
If G has VC-dimension d then

π_G(k) ≤ (k + 1)^d  for all k ∈ ℕ.

This follows from the Sauer–Shelah lemma.

# Formalization notes

The hypothesis is VC-dimension at most d, which is equivalent: a graph
of VC-dimension d' ≤ d satisfies the bound for d', hence for d. The
graph may be infinite. Its VC-dimension is then an extended natural
number, and the hypothesis excludes the value ⊤.
-/

namespace Lax185574.NeighborhoodComplexityBound

open Lax185574.VCDimension

universe u

/-- **Neighborhood complexity bound.** A graph of VC-dimension at most `d` has
neighborhood complexity `π_G(k) ≤ (k + 1)^d`. -/
axiom neighborhoodComplexity_le {V : Type u} (G : SimpleGraph V) (d : ℕ)
    (hG : vcDim G ≤ d) (k : ℕ) : neighborhoodComplexity G k ≤ (k + 1) ^ d

end Lax185574.NeighborhoodComplexityBound
