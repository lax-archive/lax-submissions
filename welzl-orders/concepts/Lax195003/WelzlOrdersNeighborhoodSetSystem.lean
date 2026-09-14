import Lax195003.WelzlOrders
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
---
title: Neighborhood set systems of graphs
type: definition
---
For a graph and a radius *k*, its neighborhood set system consists of the
open *k*-neighborhood of every vertex. The open *k*-neighborhood of a vertex
contains every other vertex reachable from it by a walk of length at most
*k*.

# Formalization notes

The center vertex is excluded explicitly, so the radius-one instance is the
ordinary open neighborhood set system of a simple graph.
-/

namespace Lax195003.WelzlOrdersNeighborhoodSetSystem

open Lax195003.WelzlOrders

/-- The neighborhood set system of a graph at radius `k`: the open
`k`-neighborhood of every vertex. -/
def neighborhoodSetSystem {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    SetSystem (Fin n) :=
  {X | ∃ v : Fin n, X =
    {u : Fin n | u ≠ v ∧ ∃ w : G.Walk v u, w.length ≤ k}}

end Lax195003.WelzlOrdersNeighborhoodSetSystem
