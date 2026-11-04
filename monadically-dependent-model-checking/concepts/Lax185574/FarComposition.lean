import Lax185574.TypeTrees
import Lax185574.Algorithms

/-!
---
title: Far composition of type trees
type: lemma
---
There is an operation ∗ on type trees such that for all k, q ∈ ℕ,
partial graphs G and nonempty tuples ā₁, ā₂ with |ā₁ ā₂| ≤ k and
dist(ā₁, ā₂) > ρ⁻(k, q),

  tree_{k,q}(ā₁) ∗ tree_{k,q}(ā₂) = tree_{k,q}(ā₁ ā₂).

Given τ₁ and τ₂ one can compute τ₁ ∗ τ₂ in time poly_{k,q}(‖τ₁‖ + ‖τ₂‖).

# Formalization notes

The paper adapts Lemma 3.1 of its locality note. The operation is given
by one algorithm in the sense of `Lax185574.Algorithms`, for all k and
q, whose input is the pair of the two trees. The size ‖τ‖ is the length
of the encoding of τ, and the time is `O((‖τ₁‖ + ‖τ₂‖ + 1)^a)`, where the
degree `a` and the constant `c` may depend on k and q.
dist(ā₁, ā₂) > r means that no entry of ā₁ is within distance r of an
entry of ā₂.
-/

namespace Lax185574.FarComposition

open Lax185574.Encoding Lax185574.Algorithms
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax3.DistFO (rhoMinus rhoPlus)

/-- **Far composition.** One algorithm computes the type tree of the
concatenation of two far tuples from their type trees, in time
polynomial in their sizes. -/
axiom exists_program_compose :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ₁ ℓ₂ : ℕ) (u₁ : Fin ℓ₁ → Fin n)
        (u₂ : Fin ℓ₂ → Fin n), 1 ≤ ℓ₁ → 1 ≤ ℓ₂ → ℓ₁ + ℓ₂ ≤ k →
        (∀ i j, ¬ WithinDist G.resolved (rhoMinus k q) (u₁ i) (u₂ j)) →
          A.Computes c (tree G k q u₁, tree G k q u₂) (tree G k q (Fin.append u₁ u₂))
            (((encode (tree G k q u₁)).length + (encode (tree G k q u₂)).length + 1) ^ a)

end Lax185574.FarComposition
