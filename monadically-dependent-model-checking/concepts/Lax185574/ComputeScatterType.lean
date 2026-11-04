import Lax185574.ScatterTypes
import Lax185574.DistanceMatrix
import Lax185574.Algorithms

/-!
---
title: Computing the scatter type
type: lemma
---
There is an algorithm which, given a nonempty partial graph G, numbers
k ≥ 1 and q ∈ ℕ, its distance matrix D_G, and the family
(tree_{k,q}(a) : a ∈ V(G)), computes stp^G_{k,q} in time

  |G|² · poly_{k,q}(max_{a ∈ V(G)} ‖tree_{k,q}(a)‖).

# Formalization notes

The algorithm is an algorithm in the sense of `Lax185574.Algorithms`,
one for all k and q. Its input is the tuple of G, k, q, the distance
matrix and the family of type trees, with the encodings of
`Lax185574.Encodings`. The partial graph is on `Fin n`, so |G| = n, and
it is nonempty when 1 ≤ n. The output is the scatter type, a finite set
as in `Lax185574.ScatterTypes`. The largest size of a tree of the
family is `maxTreeSize G k q`, and the time is
`O(n² · (maxTreeSize G k q + 1)^a)`, where the degree `a` and the
constant `c` may depend on k and q. The second factor is increased by
one, so that it is positive.
-/

namespace Lax185574.ComputeScatterType

open Lax185574.Encoding Lax185574.Algorithms
open Lax185574.PartialGraphs Lax185574.ScatterTypes Lax185574.TypeTrees
open Lax185574.DistanceMatrix

/-- **Computing the scatter type.** One algorithm computes `stp^G_{k,q}`
from `G`, `k`, `q`, the distance matrix `D_G` and the type trees of all
vertices, in time quadratic in `n` and polynomial in the largest size of
a tree. -/
axiom exists_program_stp :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)), 1 ≤ k → 1 ≤ n →
        A.Computes c (G, k, q, distMatrix G, family G k q) (stp G k q)
          (n ^ 2 * (maxTreeSize G k q + 1) ^ a)

end Lax185574.ComputeScatterType
