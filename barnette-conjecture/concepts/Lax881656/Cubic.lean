import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card

/-!
---
title: Cubic graphs
type: definition
---
A finite simple graph is cubic, or 3-regular, when every vertex has exactly
three neighbors.

# Formalization notes

The degree of a vertex is expressed as the cardinality of its neighbor set.
The ambient vertex type is finite, so these cardinalities are ordinary natural
numbers. No regularity data is carried beyond the pointwise condition.
-/

set_option autoImplicit false

namespace Lax881656.Cubic

/-- A finite simple graph is cubic when every vertex has degree three. -/
def IsCubic {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v : V, (G.neighborSet v).ncard = 3

end Lax881656.Cubic
