import Lax185574.PartialGraphs
import Mathlib.Order.Lattice.Nat

/-!
---
title: Radius-r width of a construction sequence
type: definition
---
Partial graphs, construction sequences and their radius-r width are
defined in the technical overview of the paper. A construction sequence
of a graph G with vertex set V is a sequence G₁, …, G_λ of partial
graphs with vertex set V. Its *radius-r width* is the maximum, over all
t ∈ [λ] and v ∈ V, of the number of parts of G_t that intersect
Ball^{G_t}_r(v). The ball is taken in the Gaifman graph (V, R(G_t)) of
G_t, whose edges are the resolved pairs E(G_t) ∪ N(G_t). The radius-r
merge-width of G is the minimum radius-r width over all construction
sequences of G.

For a partial graph H with partition 𝒫 and a set W ⊆ V(H), the induced
partial graph H[W] has vertex set W, edges E(H) ∩ (W choose 2),
non-edges N(H) ∩ (W choose 2), and partition { P ∩ W : P ∈ 𝒫 } ∖ {∅}.

# Formalization notes

A construction sequence is a list of partial graphs, as in
`Lax185574.ConstructionSequences`. The Gaifman graph (V, R(G_t)) is the
graph of resolved pairs, so the ball is `PartialGraph.ball`. The
parts of a partial graph are its nonempty color classes, so the parts
meeting a set B correspond to the colors of the vertices of B, and their
number is the number of these colors. The maximum is the supremum of a
set of natural numbers, which is finite when the vertex type is finite.
The empty maximum is 0.

This width counts parts. It is not the radius-r depth-q width of
`Lax185574.Width`, which counts types. The merge-width of a graph is not
needed and is not defined here.

The induced partial graph H[W] is the induced substructure of
`Lax185574.GaifmanGraph` on the structure of H, see
`Lax185574.PartialGraphs`. Its colors are those of H restricted to W, so
its parts are the nonempty sets P ∩ W.
-/

namespace Lax185574.ConstructionWidth

open Lax185574.PartialGraphs

universe z

variable {V : Type z}

/-- The radius-`r` width of the sequence `s`: the largest number of
parts of `s[t]` that meet a ball of radius `r` in the resolved pairs of
`s[t]`. -/
noncomputable def constructionWidth (r : ℕ) (s : List (PartialGraph V)) : ℕ :=
  sSup {K | ∃ (t : ℕ) (ht : t < s.length) (v : V),
    K = ((s[t]).color '' (s[t]).ball r v).ncard}

end Lax185574.ConstructionWidth
