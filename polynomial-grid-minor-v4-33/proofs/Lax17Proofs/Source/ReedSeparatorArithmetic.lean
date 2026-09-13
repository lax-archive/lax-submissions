import Lax17Proofs.Source.BalancedSeparation

namespace Lax17Proofs

universe u v w

/-!
# Cardinality bounds for Reed's recursive separator step

This file isolates the finite-set arithmetic used when a balanced separation
splits a recursive Reed decomposition.  A separator of cardinality at most
`k` and a terminal set of cardinality in `(4 * k, 8 * k]` give two strictly
smaller regions.  The separator augmented by either child's terminals still
has cardinality at most `8 * k`.
-/

namespace SimpleGraph
namespace ReedSeparatorArithmetic


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {C T Y Z : Finset V} {k : ℕ}

private theorem overlap_card_lt_right_terminals
    (hlarge : 4 * k < T.card)
    (hYZ : BalancedSeparation G C T T.card Y Z)
    (hoverlap : (Y ∩ Z).card ≤ k) :
    (Y ∩ Z).card < (Z ∩ T).card := by
  have hbalanced := hYZ.right_balanced
  omega

/-- The left side of the balanced separation is strictly smaller than the
ambient region. -/
theorem left_card_lt_ambient
    (hlarge : 4 * k < T.card)
    (hYZ : BalancedSeparation G C T T.card Y Z)
    (hoverlap : (Y ∩ Z).card ≤ k) :
    Y.card < C.card := by
  have hright := overlap_card_lt_right_terminals hlarge hYZ hoverlap
  have hright_le : (Z ∩ T).card ≤ Z.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hcard := Finset.card_union_add_card_inter Y Z
  rw [hYZ.toVertexSeparation.cover] at hcard
  omega

/-- The right side of the balanced separation is strictly smaller than the
ambient region. -/
theorem right_card_lt_ambient
    (hlarge : 4 * k < T.card)
    (hYZ : BalancedSeparation G C T T.card Y Z)
    (hoverlap : (Y ∩ Z).card ≤ k) :
    Z.card < C.card := by
  have hleft := left_card_lt_ambient
    (G := G) (C := C) (T := T) (Y := Z) (Z := Y)
    hlarge hYZ.symm (by simpa [Finset.inter_comm] using hoverlap)
  simpa using hleft

/-- Both recursive regions are strictly smaller than their parent region. -/
theorem side_cards_lt_ambient
    (hlarge : 4 * k < T.card)
    (hYZ : BalancedSeparation G C T T.card Y Z)
    (hoverlap : (Y ∩ Z).card ≤ k) :
    Y.card < C.card ∧ Z.card < C.card :=
  ⟨left_card_lt_ambient hlarge hYZ hoverlap,
    right_card_lt_ambient hlarge hYZ hoverlap⟩

private theorem terminal_cover
    (hT : T ⊆ C)
    (hYZ : BalancedSeparation G C T T.card Y Z) :
    (Y ∩ T) ∪ (Z ∩ T) = T := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_inter.mp hv).2
    · exact (Finset.mem_inter.mp hv).2
  · intro hvT
    have hvC : v ∈ C := hT hvT
    have hvYZ : v ∈ Y ∪ Z := by
      rw [hYZ.toVertexSeparation.cover]
      exact hvC
    rcases Finset.mem_union.mp hvYZ with hvY | hvZ
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvY, hvT⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvZ, hvT⟩)

/-- The root set inherited by the left child has cardinality at most `8 * k`.
It consists of the separator together with the terminals lying on the left
side. -/
theorem left_child_root_card_le
    (hT : T ⊆ C)
    (hlarge : 4 * k < T.card)
    (hupper : T.card ≤ 8 * k)
    (hYZ : BalancedSeparation G C T T.card Y Z)
    (hoverlap : (Y ∩ Z).card ≤ k) :
    ((Y ∩ Z) ∪ (Y ∩ T)).card ≤ 8 * k := by
  have hright := overlap_card_lt_right_terminals hlarge hYZ hoverlap
  have hinter :
      (Y ∩ Z) ∩ (Y ∩ T) = (Y ∩ T) ∩ (Z ∩ T) := by
    ext v
    simp [and_assoc, and_left_comm, and_comm]
  have hchild := Finset.card_union_add_card_inter (Y ∩ Z) (Y ∩ T)
  rw [hinter] at hchild
  have hterminals := Finset.card_union_add_card_inter (Y ∩ T) (Z ∩ T)
  rw [terminal_cover hT hYZ] at hterminals
  omega

/-- The root set inherited by the right child has cardinality at most
`8 * k`. -/
theorem right_child_root_card_le
    (hT : T ⊆ C)
    (hlarge : 4 * k < T.card)
    (hupper : T.card ≤ 8 * k)
    (hYZ : BalancedSeparation G C T T.card Y Z)
    (hoverlap : (Y ∩ Z).card ≤ k) :
    ((Y ∩ Z) ∪ (Z ∩ T)).card ≤ 8 * k := by
  have hright := left_child_root_card_le
    (G := G) (C := C) (T := T) (Y := Z) (Z := Y)
    hT hlarge hupper hYZ.symm
    (by simpa [Finset.inter_comm] using hoverlap)
  simpa [Finset.inter_comm] using hright

/-- Both child root sets satisfy the recursive `8 * k` cardinality budget. -/
theorem child_root_cards_le
    (hT : T ⊆ C)
    (hlarge : 4 * k < T.card)
    (hupper : T.card ≤ 8 * k)
    (hYZ : BalancedSeparation G C T T.card Y Z)
    (hoverlap : (Y ∩ Z).card ≤ k) :
    ((Y ∩ Z) ∪ (Y ∩ T)).card ≤ 8 * k ∧
      ((Y ∩ Z) ∪ (Z ∩ T)).card ≤ 8 * k :=
  ⟨left_child_root_card_le hT hlarge hupper hYZ hoverlap,
    right_child_root_card_le hT hlarge hupper hYZ hoverlap⟩

/-- The complete cardinality package for one recursive Reed decomposition
step. -/
theorem recursive_step_cardinality_bounds
    (hT : T ⊆ C)
    (hlarge : 4 * k < T.card)
    (hupper : T.card ≤ 8 * k)
    (hYZ : BalancedSeparation G C T T.card Y Z)
    (hoverlap : (Y ∩ Z).card ≤ k) :
    Y.card < C.card ∧ Z.card < C.card ∧
      ((Y ∩ Z) ∪ (Y ∩ T)).card ≤ 8 * k ∧
      ((Y ∩ Z) ∪ (Z ∩ T)).card ≤ 8 * k := by
  exact ⟨left_card_lt_ambient hlarge hYZ hoverlap,
    right_card_lt_ambient hlarge hYZ hoverlap,
    left_child_root_card_le hT hlarge hupper hYZ hoverlap,
    right_child_root_card_le hT hlarge hupper hYZ hoverlap⟩

end ReedSeparatorArithmetic
end SimpleGraph

end Lax17Proofs
