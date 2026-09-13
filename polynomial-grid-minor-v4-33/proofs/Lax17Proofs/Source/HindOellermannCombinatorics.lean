import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Lax17Proofs

universe u v w

/-!
# Finite counting lemmas for Hind--Oellermann

This module isolates the finite-set counting used in the Hind--Oellermann
argument.  No graph structure is needed: a finite set cannot cheaply meet too
many pairwise disjoint parts, and meeting one part twice forces it to miss
another part when its cardinality is at most the number of parts.
-/

namespace HindOellermannCombinatorics

open Finset

variable {ι α : Type*} [DecidableEq α]

/-- The intersections of pairwise disjoint finite sets with a common finite
set have total cardinality at most the cardinality of the common set. -/
theorem sum_card_inter_le_card (indices : Finset ι) (family : ι → Finset α)
    (hitting : Finset α)
    (hpair : (↑indices : Set ι).PairwiseDisjoint family) :
    ∑ i ∈ indices, (family i ∩ hitting).card ≤ hitting.card := by
  classical
  have hpairInter :
      (↑indices : Set ι).PairwiseDisjoint (fun i => family i ∩ hitting) := by
    intro i hi j hj hij
    exact (hpair hi hj hij).mono inter_subset_left inter_subset_left
  have hunionSubset :
      indices.biUnion (fun i => family i ∩ hitting) ⊆ hitting := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, _hi, hxi⟩
    exact (Finset.mem_inter.mp hxi).2
  rw [← Finset.card_biUnion hpairInter]
  exact Finset.card_le_card hunionSubset

/-- A finite set meeting every member of a pairwise disjoint finite family has
cardinality at least the number of indexed family members. -/
theorem card_indices_le_card_of_pairwiseDisjoint_of_hits
    (indices : Finset ι) (family : ι → Finset α) (hitting : Finset α)
    (hpair : (↑indices : Set ι).PairwiseDisjoint family)
    (hhits : ∀ i ∈ indices, (family i ∩ hitting).Nonempty) :
    indices.card ≤ hitting.card := by
  calc
    indices.card = ∑ _i ∈ indices, 1 := Finset.card_eq_sum_ones indices
    _ ≤ ∑ i ∈ indices, (family i ∩ hitting).card := by
      exact Finset.sum_le_sum fun i hi => (hhits i hi).card_pos
    _ ≤ hitting.card := sum_card_inter_le_card indices family hitting hpair

/-- If a finite set has cardinality at most the number of pairwise disjoint
family members and meets one member in at least two elements, then it is
disjoint from another member. -/
theorem exists_disjoint_of_card_le_of_two_le_card_inter
    (indices : Finset ι) (family : ι → Finset α) (hitting : Finset α)
    (hpair : (↑indices : Set ι).PairwiseDisjoint family)
    (hcard : hitting.card ≤ indices.card) {i : ι} (hi : i ∈ indices)
    (htwo : 2 ≤ (family i ∩ hitting).card) :
    ∃ j ∈ indices, Disjoint (family j) hitting := by
  by_contra hnone
  push Not at hnone
  have hone : ∀ j ∈ indices, 1 ≤ (family j ∩ hitting).card := by
    intro j hj
    exact (Finset.not_disjoint_iff_nonempty_inter.mp (hnone j hj)).card_pos
  have hstrict :
      indices.card < ∑ j ∈ indices, (family j ∩ hitting).card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_lt_sum
      (fun j hj => hone j hj)
      ⟨i, hi, by omega⟩
  have hsum := sum_card_inter_le_card indices family hitting hpair
  omega

section Fintype

variable [Fintype ι]

/-- Fintype-indexed form of
`card_indices_le_card_of_pairwiseDisjoint_of_hits`. -/
theorem fintype_card_le_card_of_pairwiseDisjoint_of_hits
    (family : ι → Finset α) (hitting : Finset α)
    (hpair : Pairwise fun i j => Disjoint (family i) (family j))
    (hhits : ∀ i, (family i ∩ hitting).Nonempty) :
    Fintype.card ι ≤ hitting.card := by
  classical
  simpa using card_indices_le_card_of_pairwiseDisjoint_of_hits
    (Finset.univ : Finset ι) family hitting
    (fun i _hi j _hj hij => hpair hij) (fun i _hi => hhits i)

/-- Fintype-indexed form of
`exists_disjoint_of_card_le_of_two_le_card_inter`. -/
theorem exists_disjoint_of_card_le_fintype_card_of_two_le_card_inter
    (family : ι → Finset α) (hitting : Finset α)
    (hpair : Pairwise fun i j => Disjoint (family i) (family j))
    (hcard : hitting.card ≤ Fintype.card ι) (i : ι)
    (htwo : 2 ≤ (family i ∩ hitting).card) :
    ∃ j, Disjoint (family j) hitting := by
  classical
  simpa using exists_disjoint_of_card_le_of_two_le_card_inter
    (Finset.univ : Finset ι) family hitting
    (fun a _ha b _hb hab => hpair hab) (by simpa using hcard)
    (Finset.mem_univ i) htwo

end Fintype

/-- Numeric form for a family indexed by `Fin k`: every hitting set has at
least `k` elements. -/
theorem card_le_card_of_fin_pairwiseDisjoint_of_hits {k : ℕ}
    (family : Fin k → Finset α) (hitting : Finset α)
    (hpair : Pairwise fun i j => Disjoint (family i) (family j))
    (hhits : ∀ i, (family i ∩ hitting).Nonempty) :
    k ≤ hitting.card := by
  simpa using fintype_card_le_card_of_pairwiseDisjoint_of_hits
    family hitting hpair hhits

/-- Numeric form for a family indexed by `Fin k`: meeting one member twice
forces a set of cardinality at most `k` to miss another member. -/
theorem exists_fin_disjoint_of_card_le_of_two_le_card_inter {k : ℕ}
    (family : Fin k → Finset α) (hitting : Finset α)
    (hpair : Pairwise fun i j => Disjoint (family i) (family j))
    (hcard : hitting.card ≤ k) (i : Fin k)
    (htwo : 2 ≤ (family i ∩ hitting).card) :
    ∃ j, Disjoint (family j) hitting := by
  exact exists_disjoint_of_card_le_fintype_card_of_two_le_card_inter
    family hitting hpair (by simpa using hcard) i htwo

end HindOellermannCombinatorics

end Lax17Proofs
