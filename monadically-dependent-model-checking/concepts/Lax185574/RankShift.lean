import Lax185574.TypeTrees
import Lax185574.Algorithms

/-!
---
title: Rank shift of type trees
type: lemma
---
There is a polynomial-time algorithm which maps tree_{k,q}(ā) to
tree_{k+1,q−1}(ā) for all k ∈ ℕ, q ≥ 1, partial graphs G and nonempty
ā ∈ V(G)^{≤k}.

# Formalization notes

The algorithm is an algorithm in the sense of `Lax185574.Algorithms`,
one for all k and q. Polynomial time means time `O((N + 1)^a)` on an
input of length `N`, where the degree `a` and the constant `c` may
depend on k and q. The paper says polynomial time, with no subscript,
so this is weaker than a degree independent of k and q. It suffices,
since k and q are fixed in every use. q ≥ 1 is written as q + 1.
-/

namespace Lax185574.RankShift

open Lax185574.Encoding Lax185574.Algorithms
open Lax185574.PartialGraphs Lax185574.TypeTrees

/-- **Rank shift.** One algorithm computes `tree_{k+1,q}(u)` from
`tree_{k,q+1}(u)` in polynomial time. -/
axiom exists_program_shift :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k →
        A.Computes c (tree G k (q + 1) u) (tree G (k + 1) q u)
          (((encode (tree G k (q + 1) u)).length + 1) ^ a)

end Lax185574.RankShift
