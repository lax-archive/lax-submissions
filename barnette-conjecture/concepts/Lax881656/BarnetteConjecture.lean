import Lax68.Planar
import Lax881656.ThreeConnected
import Lax881656.Cubic
import Lax881656.Bipartite
import Lax881656.HamiltonianCycle

/-!
---
title: Barnette's conjecture
type: theorem
---
Every finite, simple, 3-connected, cubic, bipartite planar graph has a
Hamiltonian cycle.

This is an open problem. The conjecture is known when every face has size at
most 8; maximum face size 10 is the next natural restricted case.

# Formalization notes

Finite simple graphs are stated on the canonical vertex type `Fin n`.
Planarity is the straight-line-drawing predicate imported from the Planar
Graph Classes submission; the other four hypotheses and conclusion use the
dedicated definition concepts in this submission.
-/

set_option autoImplicit false

namespace Lax881656.BarnetteConjecture

/-- Barnette's conjecture: every 3-connected cubic bipartite planar graph has
a Hamiltonian cycle. -/
axiom barnette_conjecture {n : ℕ} (G : SimpleGraph (Fin n)) :
  (Lax881656.ThreeConnected.IsThreeConnected G ∧
    Lax881656.Cubic.IsCubic G ∧
    Lax881656.Bipartite.IsBipartite G ∧
    Lax68.Planar.IsPlanar G) →
  Lax881656.HamiltonianCycle.HasHamiltonianCycle G

end Lax881656.BarnetteConjecture
