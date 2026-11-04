import Lax185574.PartialGraphs
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
---
title: The distance matrix of a partial graph
type: definition
---
The *distance matrix* of a partial graph G is the |G| × |G| matrix D_G
with entries D_G(u, v) = dist^G(u, v) ∈ ℕ ∪ {∞}.

# Formalization notes

The distance is the extended distance `SimpleGraph.edist` of mathlib in
the graph of resolved pairs, a value in `ℕ∞`. So D_G is 0 on the
diagonal, and ∞ for vertices in different components of the graph of
resolved pairs. The matrix of a partial graph on `Fin n` is a function
of two vertices.

Algorithms receive the matrix in the encoding of `Lax185574.Encodings`.
A distance in ℕ ∪ {∞} is encoded as one entry, 0 for ∞ and d + 1 for a
finite distance d. The matrix is the family of its rows, and each row is
the family of its entries. So the word of D_G is n, followed by every
row in order as n and the n entries of the row. Every row has n + 1
entries, the word has length 1 + n(n + 1), and the entry at (u, v) is at
position 2 + u(n + 1) + v, counting from 0. The paper does not say how
∞ is represented. Its bounds O(|G|²) for reading the matrix need entries
of constant size, which this encoding provides.
-/

namespace Lax185574.DistanceMatrix

open Lax185574.PartialGraphs

/-- The distance matrix `D_G`: `D_G(u, v) = dist^G(u, v)`, the distance
in the graph of resolved pairs, and `∞` if there is no path. -/
noncomputable def distMatrix {n : ℕ} (G : PartialGraph (Fin n)) : Fin n → Fin n → ℕ∞ :=
  fun u v => G.resolved.edist u v

end Lax185574.DistanceMatrix
