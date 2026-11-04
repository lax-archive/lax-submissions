import Lax185574.GaifmanGraph

/-!
---
title: A graph or its complement has diameter at most 3
type: lemma
---
For every graph G, at least one of G and Ḡ has diameter at most 3.

This is folklore.

# Formalization notes

"Diameter at most 3" says that any two vertices are joined by a walk of
length at most 3, `WithinDist` of `Lax185574.GaifmanGraph`. The
complement Ḡ is the complement `Gᶜ`, whose edges are the pairs of
distinct non-adjacent vertices. The graph may be infinite.
-/

namespace Lax185574.ComplementDiameter

open Lax185574.GaifmanGraph

universe z

/-- **A graph or its complement has diameter at most 3.** -/
axiom diameter_le_three_or_compl {V : Type z} (G : SimpleGraph V) :
    (∀ u v : V, WithinDist G 3 u v) ∨ (∀ u v : V, WithinDist Gᶜ 3 u v)

end Lax185574.ComplementDiameter
