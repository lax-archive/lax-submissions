import Lax185574.GaifmanGraph
import Mathlib.Data.Set.Card

/-!
---
title: Clustering of a tuple
type: lemma
---
Let r ∈ ℕ, ℓ ≥ 1, G a graph and ā = (a₁, …, a_ℓ) ∈ V(G)^ℓ. There exist a
radius ρ with r ≤ ρ ≤ 9^{ℓ−1} r and a partition 𝓑 of {a₁, …, a_ℓ} with
the following property. For every X ⊆ V(G), every inclusion-wise
maximal 4ρ-scattered subset S ⊆ X, and every H ≥ 4ρ + r,

  ∃x ∈ X: dist(x, ā) > r
  ⟺ ∃x ∈ X: r < dist(x, ā) ≤ H,
     or |{B ∈ 𝓑 | ∃x ∈ X: dist(x, B) ≤ r}| < |S|.

Moreover, ρ and 𝓑 can be determined by tests of the form
dist(aᵢ, aⱼ) ≤ s, where i, j ∈ [ℓ] and s ≤ 8 · 9^{ℓ−1} r.

# Formalization notes

The paper cites Corollary 3.4 and Lemma 3.5 of its locality note. The
statement here makes "can be determined by tests" explicit by naming a
criterion that the tests decide. A radius ρ and a partition are
*admissible* if entries in the same block are within distance 4ρ − 2r
of each other, and entries in different blocks are not within distance
4ρ + 2r. The statement says that an admissible pair with
r ≤ ρ ≤ 9^{ℓ−1} r exists, and that every admissible pair with r ≤ ρ has
the property above. Admissibility of a pair involves only tests
dist(aᵢ, aⱼ) ≤ s with s ≤ 4 · 9^{ℓ−1} r + 2r ≤ 8 · 9^{ℓ−1} r. So an
algorithm that knows these tests finds a suitable pair by trying all
candidates. A statement that only asserts that the pair is some
function of the tests would not let an algorithm compute it.

The graph is finite. The partition is given on the positions: a function
β : [ℓ] → [ℓ] puts the positions i and j in the same block when
β(i) = β(j). dist(x, ā) > r means that x is within distance r of no
entry, and r < dist(x, ā) ≤ H means that x is within distance r of no
entry and within distance H of some entry.
-/

namespace Lax185574.Clustering

open Lax185574.GaifmanGraph

variable {V : Type*}

/-- The radius `ρ` and the partition `β` of the positions are
admissible for `a` at radius `r`: entries in one block are within
distance `4ρ − 2r`, and entries in different blocks are not within
distance `4ρ + 2r`. -/
def Admissible (G : SimpleGraph V) (r : ℕ) {ℓ : ℕ} (a : Fin ℓ → V) (ρ : ℕ)
    (β : Fin ℓ → Fin ℓ) : Prop :=
  ∀ i j, (β i = β j → WithinDist G (4 * ρ - 2 * r) (a i) (a j)) ∧
    (β i ≠ β j → ¬ WithinDist G (4 * ρ + 2 * r) (a i) (a j))

/-- **Clustering.** Some admissible radius lies between `r` and
`9^(ℓ−1) r`, and every admissible pair detects the vertices of a set `X`
far from `a`: by vertices at bounded distance, or by counting a maximal
scattered subset of `X`. -/
axiom clustering [Finite V] (G : SimpleGraph V) (r ℓ : ℕ) (hℓ : 1 ≤ ℓ) (a : Fin ℓ → V) :
    (∃ ρ β, r ≤ ρ ∧ ρ ≤ 9 ^ (ℓ - 1) * r ∧ Admissible G r a ρ β) ∧
    ∀ ρ β, r ≤ ρ → Admissible G r a ρ β →
      ∀ (X S : Set V) (H : ℕ), S ⊆ X →
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ WithinDist G (4 * ρ) x y) →
        (∀ x ∈ X, ∃ y ∈ S, WithinDist G (4 * ρ) x y) →
        4 * ρ + r ≤ H →
        ((∃ x ∈ X, ∀ i, ¬ WithinDist G r (a i) x) ↔
          (∃ x ∈ X, (∀ i, ¬ WithinDist G r (a i) x) ∧ ∃ i, WithinDist G H (a i) x) ∨
          (β '' {i | ∃ x ∈ X, WithinDist G r (a i) x}).ncard < S.ncard)

end Lax185574.Clustering
