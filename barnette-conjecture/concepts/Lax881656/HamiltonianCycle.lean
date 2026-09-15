import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
---
title: Hamiltonian cycles
type: definition
---
A Hamiltonian cycle in a graph is a cycle that visits every vertex. A graph
has a Hamiltonian cycle when such a closed walk exists.

# Formalization notes

A cycle is represented by mathlib's closed-walk predicate, which ensures that
no vertex is repeated except for the common start and end. The separate
spanning condition says that every graph vertex belongs to its support.
-/

set_option autoImplicit false

namespace Lax881656.HamiltonianCycle

/-- A closed walk is a Hamiltonian cycle when it is a cycle and visits every
vertex of the graph. -/
def IsHamiltonianCycle {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {v : V} (cycle : G.Walk v v) : Prop :=
  cycle.IsCycle ∧ ∀ w : V, w ∈ cycle.support

/-- A graph has a Hamiltonian cycle when it contains a spanning cycle. -/
def HasHamiltonianCycle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∃ cycle : G.Walk v v, IsHamiltonianCycle cycle

end Lax881656.HamiltonianCycle
