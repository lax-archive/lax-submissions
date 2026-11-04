import Lax185574.ConstructionSequences
import Lax185574.FirstOrderTypes
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice

/-!
---
title: Radius-r depth-q width of a construction sequence
type: definition
---
For r, q ∈ ℕ, the *radius-r depth-q width* of a construction sequence
G₁, …, G_λ is

max_{t ∈ [λ−1]} max_{v ∈ V(G)} |Types^{G_t}_{q,q}(Ball^{G_{t+1}}_r(v))|.

It measures a construction sequence by the number of types of q-tuples
realized near each vertex. Types are taken in G_t, and balls in G_{t+1}.

# Formalization notes

The partial graph `G_t` is the relational structure of
`Lax185574.PartialGraphs`, with edges, non-edges and one unary relation
per color. The types are those of `Lax185574.FirstOrderTypes`, without
parameters, `typeCount`. The maximum is the supremum of a set of natural numbers.
That set is finite when the vertex type is finite, which is the case in
every statement that uses the width. The empty maximum, for a sequence
of length one, is 0.
-/

namespace Lax185574.Width

open Lax185574.PartialGraphs Lax185574.FirstOrderTypes

universe z

variable {V : Type z}

/-- The number of types of `q`-tuples of quantifier rank `q`, in the
partial graph `G`, realized by tuples from the set `X`. -/
noncomputable def partialTypeCount (G : PartialGraph V) (k q : ℕ) (X : Set V) : ℕ :=
  @typeCount language V G.structure k q X

/-- The radius-`r` depth-`q` width of the sequence `s`: the largest
number of types of `q`-tuples of quantifier rank `q` in `s[t]` realized
by tuples from a ball of radius `r` in `s[t+1]`. -/
noncomputable def width (r q : ℕ) (s : List (PartialGraph V)) : ℕ :=
  sSup {K | ∃ (t : ℕ) (ht : t + 1 < s.length) (v : V),
    K = partialTypeCount s[t] q q (s[t + 1].ball r v)}

end Lax185574.Width
