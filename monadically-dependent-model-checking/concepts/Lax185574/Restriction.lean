import Lax185574.TypeTrees
import Lax185574.Algorithms

/-!
---
title: Ordered coordinate restriction of type trees
type: lemma
---
There is an operation ↾ on type trees such that for all k, q ∈ ℕ,
partial graphs G, tuples w̄ ∈ V(G)^ℓ with ℓ ≤ k and ordered lists J of
distinct positions in [ℓ],

  tree_{k,q}(w̄) ↾ J = tree_{k,q}(w̄ ↾ J).

Given τ and J one can compute τ ↾ J in time polynomial in ‖τ‖.

# Formalization notes

The operation is given by one algorithm in the sense of
`Lax185574.Algorithms`, for all k and q. Its input is the pair of the
tree and J, a list of positions. Positions are counted from 0. The tuple
w̄ ↾ J has the entries w_{j₁}, …, w_{j_p}. The size ‖τ‖ is the length of
the encoding of τ, and the time is `O((‖τ‖ + 1)^a)`, where the degree
`a` and the constant `c` may depend on k and q. The paper says
polynomial time, with no subscript, so this is weaker than a degree
independent of k and q. It suffices, since k and q are fixed in every
use.
-/

namespace Lax185574.Restriction

open Lax185574.Encoding Lax185574.Algorithms
open Lax185574.PartialGraphs Lax185574.TypeTrees

/-- **Ordered coordinate restriction.** One algorithm computes
`tree_{k,q}(u ↾ J)` from `tree_{k,q}(u)` and `J`, in time polynomial in
the size of the tree. -/
axiom exists_program_restrict :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n) (J : List (Fin ℓ)),
        ℓ ≤ k → J.Nodup →
          A.Computes c (tree G k q u, J) (tree G k q (fun i => u (J.get i)))
            (((encode (tree G k q u)).length + 1) ^ a)

end Lax185574.Restriction
