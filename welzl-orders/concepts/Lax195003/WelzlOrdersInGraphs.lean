import Lax195003.WelzlOrders
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
---
title: Welzl orders in graphs
type: definition
---
For a graph and a radius *k*, the relevant set system consists of the open
*k*-neighborhoods of its vertices: all vertices other than the center that
can be reached from it by a walk of length at most *k*. A graph Welzl order
of radius *k* and crossing number at most *ℓ* is a Welzl order for this set
system, and is therefore crossed at most *ℓ* times by every *k*-neighborhood.

# Formalization notes

The neighborhood set system expands the bounded-walk definition directly so
that the graph specialization has only its two mathematical interface
definitions. Removing the center makes radius one the ordinary open
neighborhood used by the graph theorem.

An algorithmic output is a list of vertices in increasing order. Rather than
introducing a separate generic encoding predicate, `EncodesGraphWelzlOrder`
states directly that the list represents some permutation which is a Welzl
order for the graph's `radius`-neighborhood system. It does not prescribe
which of the potentially many good orders an algorithm must choose.
-/

namespace Lax195003.WelzlOrdersInGraphs

open Lax195003.WelzlOrders

/-- The neighborhood set system of a graph at radius `k`: the open
`k`-neighborhood of every vertex. -/
def neighborhoodSetSystem {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    SetSystem (Fin n) :=
  {X | ∃ v : Fin n, X =
    {u : Fin n | u ≠ v ∧ ∃ w : G.Walk v u, w.length ≤ k}}

/-- The word `y` encodes a Welzl order of crossing number at most
`crossingBound` for the `radius`-neighborhood set system of `G`. -/
def EncodesGraphWelzlOrder {n : ℕ} (G : SimpleGraph (Fin n))
    (radius crossingBound : ℕ) (y : List ℕ) : Prop :=
  ∃ π : Equiv.Perm (Fin n),
    y = List.ofFn (fun i : Fin n => (π.symm i).val) ∧
      IsWelzlOrder (neighborhoodSetSystem G radius) π crossingBound

end Lax195003.WelzlOrdersInGraphs
