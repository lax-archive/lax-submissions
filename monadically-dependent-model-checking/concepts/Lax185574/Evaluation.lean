import Lax185574.TypeTrees
import Lax185574.Algorithms

/-!
---
title: Evaluation of distance formulas on type trees
type: lemma
---
Let φ(x̄) be a distFO formula of distance rank (k, q), G a partial graph
and ā ∈ V(G)^ℓ with ℓ = |x̄| ≤ k. Then whether G ⊨ φ(ā) holds is
decidable in polynomial time, given tree^G_{k,q}(ā) and φ.

For a type tree τ = tree^G_{k,q}(ā) one writes τ ⊨ φ if G ⊨ φ(ā). The
lemma shows that this depends on τ only.

# Formalization notes

The algorithm is an algorithm in the sense of `Lax185574.Algorithms`,
one for all k and q. Its input is the pair of the type tree and the
formula. It decides whether `u` satisfies `φ` in time polynomial in the
size of the input, `O((N + 1)^a)` for an input of length `N`. The
degree `a` and the constant `c` may depend on k and q. The paper says
polynomial time, with no subscript, so this is weaker than a degree
independent of k and q. It suffices, since k and q are fixed in every
use. Running times of the paper of the form poly_{k,q} are formalized
in the same way. That the answer depends on τ alone is part of the
statement, because the output of the algorithm depends on its input
only.
-/

namespace Lax185574.Evaluation

open Lax185574.Encoding Lax185574.Algorithms
open Lax185574.PartialGraphs Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO
open Lax185574.TypeTrees

/-- **Evaluation.** One algorithm decides, given `tree_{k,q}(u)` and a
formula `φ` of distance rank `(k, q)`, whether `u` satisfies `φ`, in
time polynomial in the size of the input. -/
axiom exists_program_eval :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n) (φ : DistFO ℓ),
        ℓ ≤ k → DRank k q φ →
          A.Decides c (tree G k q u, φ) (Sat G u φ)
            (((encode (tree G k q u)).length + (encode φ).length + 1) ^ a)

end Lax185574.Evaluation
