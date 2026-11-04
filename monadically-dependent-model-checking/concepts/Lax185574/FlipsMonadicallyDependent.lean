import Lax185574.DefinableFlips
import Lax185574.MonadicDependence

/-!
---
title: Definable flips preserve monadic dependence
type: observation
---
Let 𝒞 be a monadically dependent graph class and s ∈ ℕ. The class
consisting of all s-definable flips of graphs from 𝒞 is monadically
dependent.

# Formalization notes

The paper allows infinite graphs in this part. Here the graphs are
those of a `GraphClass`, which are finite, as in every use.

A flip H of a graph G ∈ 𝒞 is a `SimpleGraph` on the vertices of G, as
are all flips in this submission. The class contains it as a graph,
`Graph.ofSimpleGraph H`, which has the same vertices and adjacency.
Monadic dependence is that of `Lax185574.MonadicDependence`, by
transductions.
-/

namespace Lax185574.FlipsMonadicallyDependent

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.DefinableFlips

/-- The class of all `s`-definable flips of graphs from `C`. -/
def definableFlipClass (C : GraphClass) (s : ℕ) : GraphClass :=
  {H | ∃ G ∈ C, ∃ F : SimpleGraph (Fin G.n),
    IsDefinableFlip G.toSimpleGraph s F ∧ H = Graph.ofSimpleGraph F}

/-- **Definable flips preserve monadic dependence.** The `s`-definable
flips of the graphs of a monadically dependent class form a monadically
dependent class. -/
axiom monadicallyDependent_definableFlipClass (C : GraphClass)
    (hC : MonadicallyDependent C) (s : ℕ) :
    MonadicallyDependent (definableFlipClass C s)

end Lax185574.FlipsMonadicallyDependent
