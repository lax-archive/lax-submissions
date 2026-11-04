import Lax185574.TypeTrees
import Lax185574.ConstructionSequences
import Lax185574.Algorithms

/-!
---
title: Lifting type trees through a merge
type: lemma
---
Fix ℓ ≤ k and q ∈ ℕ. Let G be a partial graph and ā ∈ V(G)^ℓ. Given
tree^G_{k,q}(ā) and two distinct colors P, Q, one can compute
tree^H_{k,q}(ā), where H = merge_{P,Q}(G), in time
poly_{k,q}(‖tree^G_{k,q}(ā)‖).

# Formalization notes

The merge is `Lax185574.ConstructionSequences.merge`, which recolors Q
to P. The algorithm is an algorithm in the sense of
`Lax185574.Algorithms`, one for all k and q. Its input is the triple of
the type tree, P and Q. The size ‖τ‖ is the length of the encoding of
τ, and the time is `O((‖τ‖ + 1)^a)`, where the degree `a` and the
constant `c` may depend on k and q.
-/

namespace Lax185574.MergeLift

open Lax185574.Encoding Lax185574.Algorithms
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ConstructionSequences

/-- **Merge lift.** One algorithm computes the type tree of a tuple
after a merge from its type tree before, in time polynomial in the size
of the tree. -/
axiom exists_program_mergeLift :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n) (P Q : ℕ),
        ℓ ≤ k → P ≠ Q →
          A.Computes c (tree G k q u, P, Q) (tree (merge G P Q) k q u)
            (((encode (tree G k q u)).length + 1) ^ a)

end Lax185574.MergeLift
