import Lax185574.TypeTrees
import Lax185574.Width

/-!
---
title: Type tree sizes
type: lemma
---
Let k ≥ 1 and q ∈ ℕ, and put r = ρ⁺(k, q) and d = r + k + q. The
following holds for every partial graph G.

1. |{tree^G_{k+i,q−i}(v̄) | v̄ ∈ X^ℓ}| ≤ |Types^G_{d,d}(X)| for all
   i ∈ {0, …, q}, ℓ ∈ [k+i] and X ⊆ V(G).
2. ‖tree^G_{k,q}(a)‖ ≤ poly_{k,q}(|Types^G_{d,d}(Ball^G_r(a))|) for every
   a ∈ V(G).

# Formalization notes

Types^G_{d,d}(X) is counted by `Lax185574.Width.partialTypeCount`, the
number of first-order types of quantifier rank d of d-tuples from X in
the partial graph G. The vertices are `Fin n`. The polynomial of the
second part has a constant and a degree depending on k and q.
-/

namespace Lax185574.TypeTreeSizes

open Lax185574.PartialGraphs Lax185574.Encoding Lax185574.TypeTrees Lax185574.Width
open Lax3.DistFO (rhoMinus rhoPlus)

/-- **Type tree sizes, counting.** The number of type trees of tuples
from `X` is at most the number of `d`-types of `d`-tuples from `X`. -/
axiom treeCount_le {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) (hk : 1 ≤ k)
    (i ℓ : ℕ) (hi : i ≤ q) (hℓ : 1 ≤ ℓ) (hℓk : ℓ ≤ k + i) (X : Set (Fin n)) :
    Set.ncard {τ : TypeTree | ∃ v : Fin ℓ → Fin n, (∀ j, v j ∈ X) ∧ τ = tree G (k + i) (q - i) v} ≤
      partialTypeCount G (rhoPlus k q + k + q) (rhoPlus k q + k + q) X

/-- **Type tree sizes, size.** The size of the type tree of a vertex is
polynomial in the number of `d`-types of `d`-tuples from its ball. -/
axiom tree_length_le (k q : ℕ) (hk : 1 ≤ k) :
    ∃ c a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (v : Fin n),
      wordLength (tree G k q ![v]) ≤
        c * (partialTypeCount G (rhoPlus k q + k + q) (rhoPlus k q + k + q)
          (G.ball (rhoPlus k q) v) + 1) ^ a

end Lax185574.TypeTreeSizes
