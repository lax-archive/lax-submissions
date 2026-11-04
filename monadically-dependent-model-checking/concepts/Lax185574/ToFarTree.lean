import Lax185574.ScatterTypes
import Lax185574.FarTrees
import Lax185574.Algorithms

/-!
---
title: Computing the far tree
type: lemma
---
Fix k ∈ ℕ and q ≥ 1, let G be a partial graph, and let ā ∈ V(G)^{≤k} be
nonempty. Then ftree_{k,q}(ā) is computable from tree_{k,q}(ā) and
stp_{k,q} in time

  ‖stp_{k,q}‖ · poly_{k,q}(‖tree_{k,q}(ā)‖).

# Formalization notes

The algorithm is an algorithm in the sense of `Lax185574.Algorithms`,
one for all k and q. q ≥ 1 is written as q + 1. The input is the pair of
the type tree and the scatter type. Sizes are lengths of encodings. The
time is `O((‖stp‖ + 1) · (‖τ‖ + 1)^a)`, where the degree `a` and the
constant `c` may depend on k and q. The factors are increased by one, so
that the bound is positive.
-/

namespace Lax185574.ToFarTree

open Lax185574.Encoding Lax185574.Algorithms
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes Lax185574.FarTrees

/-- **Computing the far tree.** One algorithm computes `ftree_{k,q}(u)`
from `tree_{k,q}(u)` and `stp_{k,q}`, in time linear in the size of the
scatter type and polynomial in the size of the tree. -/
axiom exists_program_ftree :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k →
        A.Computes c (tree G k (q + 1) u, stp G k (q + 1)) (ftree G k (q + 1) u)
          (((encode (stp G k (q + 1))).length + 1) *
            ((encode (tree G k (q + 1) u)).length + 1) ^ a)

end Lax185574.ToFarTree
