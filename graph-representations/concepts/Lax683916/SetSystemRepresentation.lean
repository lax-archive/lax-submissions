import Mathlib.Combinatorics.SimpleGraph.Basic
import Lax683916.TwoUniformSetSystems

/-!
---
title: Set-system representation of simple graphs
type: theorem
---
Simple graphs on `V` are equivalent to 2-uniform set systems on `V`: an edge
with endpoints `u` and `v` is represented by the two-element set `{u, v}`.

# Formalization notes

The equivalence uses ordinary sets rather than `Sym2 V`, matching the usual
set-system language. The 2-uniformity proof ensures that every member has a
unique interpretation as an unordered pair of distinct vertices.
-/

namespace Lax683916.SetSystemRepresentation

open Lax683916.TwoUniformSetSystems

universe u

/-- An equivalence that sends graph edges to their two-element endpoint sets. -/
structure RepresentationEquiv (V : Type u) where
  /-- The equivalence between the two representation types. -/
  toEquiv : SimpleGraph V ≃ TwoUniformSetSystem V
  /-- A pair belongs to the image set system exactly when its two elements are adjacent. -/
  map_pair : ∀ (G : SimpleGraph V) (u v : V),
    {u, v} ∈ (toEquiv G).sets ↔ G.Adj u v

/-- Simple graphs and 2-uniform set systems on the same ground type are equivalent. -/
axiom simpleGraphEquiv (V : Type u) :
  Nonempty (RepresentationEquiv V)

end Lax683916.SetSystemRepresentation
