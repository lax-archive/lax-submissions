import Lax185574.VCDimension
import Lax185574.MonadicDependence

/-!
---
title: Bounded VC-dimension of monadically dependent classes
type: observation
---
For every monadically dependent graph class 𝒞 there is some d ∈ ℕ such
that every graph G ∈ 𝒞 has VC-dimension at most d.

The paper notes that this is easy to see from the definition of monadic
dependence, and refers to the companion paper for a proof.

# Formalization notes

The VC-dimension is that of `Lax185574.VCDimension`, an extended natural
number, and "VC-dimension at most d" is `vcDim G.toSimpleGraph ≤ d`. The
paper allows infinite graphs in this part. Here the graphs are those of
a `GraphClass`, which are finite, as in every use.

The constant d is chosen after 𝒞 and before the graph. Monadic
dependence is that of `Lax185574.MonadicDependence`, by transductions.
By `Lax185574.IndependenceProperty` no formula has the independence
property on a monadically dependent class, from which the observation
is immediate: a class whose graphs have unbounded VC-dimension gives the
edge formula the independence property.
-/

namespace Lax185574.BoundedVCClasses

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.VCDimension

/-- **Bounded VC-dimension.** Some `d` bounds the VC-dimension of every
graph of a monadically dependent class. -/
axiom exists_vcDim_le (C : GraphClass) (hC : MonadicallyDependent C) :
    ∃ d : ℕ, ∀ G ∈ C, vcDim G.toSimpleGraph ≤ d

end Lax185574.BoundedVCClasses
