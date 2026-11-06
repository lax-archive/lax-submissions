import Lax185574.DpMinimality
import Lax185574.VCDimension

/-!
---
title: Bounded VC-dimension of dp-minimal classes
type: observation
---
Every dp-minimal graph class has bounded VC-dimension: there is some
d ∈ ℕ such that every graph G ∈ 𝒞 has VC-dimension at most d.

# Formalization notes

The VC-dimension is that of `Lax185574.VCDimension`, the VC-dimension of
the neighborhoods of G. The constant d is chosen after 𝒞 and before the
graph.
-/

namespace Lax185574.DpMinimalVC

open Lax185574.Graphs Lax185574.DpMinimality Lax185574.VCDimension

/-- **Bounded VC-dimension.** Some `d` bounds the VC-dimension of every
graph of a dp-minimal class. -/
axiom exists_vcDim_le (C : GraphClass) (hC : DpMinimal C) :
    ∃ d : ℕ, ∀ G ∈ C, vcDim G.toSimpleGraph ≤ d

end Lax185574.DpMinimalVC
