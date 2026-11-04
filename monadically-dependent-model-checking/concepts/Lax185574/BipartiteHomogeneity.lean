import Mathlib.Data.Fintype.Card
import Mathlib.Order.Monotone.Basic

/-!
---
title: Homogeneous rectangles for colorings of pairs of tuples
type: lemma
---
For a tuple ā = (a₁, …, a_ℓ) ∈ [n]^ℓ, the *order type* otp(ā) of ā is
the atomic type of ā in the ordered set ([n], ≤). It stores, for each
i, j ∈ [ℓ], whether aᵢ < aⱼ, aᵢ = aⱼ or aᵢ > aⱼ.

For every k, ℓ ∈ ℕ there is an unbounded, non-decreasing function
U_{k,ℓ} : ℕ → ℕ with the following property. For every t ∈ ℕ and
coloring

c : [t]^ℓ × [t]^ℓ → [k]

there are subsets I, J ⊆ [t] of size U_{k,ℓ}(t) such that c(ā, b̄) only
depends on otp(ā) and otp(b̄), for all ā ∈ I^ℓ and b̄ ∈ J^ℓ.

This is a version of Ramsey's theorem, see Lemma 4.4 of the cited work
on flip-breakability.

# Formalization notes

The set [t] is `Fin t`, with the same order, and the colors [k] are
`Fin k`. The order type of a tuple records `compare` for every pair of
positions. "c(ā, b̄) only depends on otp(ā) and otp(b̄)" says that any
two pairs of tuples from I^ℓ × J^ℓ with the same order types get the
same color. Unboundedness says that every value is reached. The sets
I and J have exactly U_{k,ℓ}(t) elements.
-/

namespace Lax185574.BipartiteHomogeneity

/-- The order type `otp(ā)` of a tuple of elements of `[t]`: the
comparison of every pair of its entries. -/
def orderType {ℓ t : ℕ} (a : Fin ℓ → Fin t) : Fin ℓ → Fin ℓ → Ordering :=
  fun i j => compare (a i) (a j)

/-- **Homogeneous rectangles.** Every coloring of pairs of
`ℓ`-tuples from `[t]` with `k` colors is determined by the order types
on `I^ℓ × J^ℓ`, for some sets `I` and `J` of size `U_{k,ℓ}(t)`, where
`U_{k,ℓ}` is unbounded and non-decreasing. -/
axiom exists_orderType_homogeneous (k ℓ : ℕ) :
    ∃ U : ℕ → ℕ, Monotone U ∧ (∀ m : ℕ, ∃ t : ℕ, m ≤ U t) ∧
      ∀ (t : ℕ) (c : (Fin ℓ → Fin t) → (Fin ℓ → Fin t) → Fin k),
        ∃ I J : Finset (Fin t), I.card = U t ∧ J.card = U t ∧
          ∀ a a' b b' : Fin ℓ → Fin t,
            (∀ i, a i ∈ I) → (∀ i, a' i ∈ I) → (∀ i, b i ∈ J) → (∀ i, b' i ∈ J) →
            orderType a = orderType a' → orderType b = orderType b' →
            c a b = c a' b'

end Lax185574.BipartiteHomogeneity
