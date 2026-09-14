import Lax195003.WelzlOrdersNeighborhoodSetSystem

/-!
---
title: Welzl orders in graphs
type: definition
---
For a graph and a radius *k*, a graph Welzl order of crossing number at most
*ℓ* is a Welzl order for the graph's open *k*-neighborhood set system. It is
therefore crossed at most *ℓ* times by every open *k*-neighborhood.

# Formalization notes

The neighborhood set system and its bounded-walk definition are provided by
the separate `Lax195003.WelzlOrdersNeighborhoodSetSystem` concept. Its
radius-one instance is the ordinary open neighborhood system used by the graph
theorem.

An algorithmic output is a list of vertices in increasing order. Rather than
introducing a separate generic encoding predicate, `EncodesGraphWelzlOrder`
states directly that the list represents some permutation which is a Welzl
order for the graph's `radius`-neighborhood system. It does not prescribe
which of the potentially many good orders an algorithm must choose.
-/

namespace Lax195003.WelzlOrdersInGraphs

open Lax195003.WelzlOrders
open Lax195003.WelzlOrdersNeighborhoodSetSystem

/-- The word `y` encodes a Welzl order of crossing number at most
`crossingBound` for the `radius`-neighborhood set system of `G`. -/
def EncodesGraphWelzlOrder {n : ℕ} (G : SimpleGraph (Fin n))
    (radius crossingBound : ℕ) (y : List ℕ) : Prop :=
  ∃ π : Equiv.Perm (Fin n),
    y = List.ofFn (fun i : Fin n => (π.symm i).val) ∧
      IsWelzlOrder (neighborhoodSetSystem G radius) π crossingBound

end Lax195003.WelzlOrdersInGraphs
