import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic

/-!
---
title: 6-colourability
type: definition
---
A graph is 6-colourable when its vertices can be assigned six colours so
that the endpoints of every edge receive different colours.

# Formalization notes

The six colours form the canonical type `Fin 6`, and a colouring is a plain
function from vertices to colours. Properness is expressed directly by
requiring adjacent vertices to have unequal images. This keeps the definition
independent of decidability assumptions and equivalent to the usual assertion
that the chromatic number is at most six, without introducing a separate
chromatic-number parameter that no statement in this submission needs.

The definition applies to arbitrary vertex types because colourability is a
pointwise graph property. The conjecture itself is stated on the canonical
finite carriers `Fin n`.
-/

namespace Lax332265.SixColorable

/-- A graph admits a proper vertex colouring with the six colours in `Fin 6`. -/
def IsSixColorable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ colour : V → Fin 6,
    ∀ ⦃u v : V⦄, G.Adj u v → colour u ≠ colour v

end Lax332265.SixColorable
