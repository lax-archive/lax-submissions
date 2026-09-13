import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Balanced vertex separations

This file contains the separation language used in the nonconstructive proof
of Chekuri--Chuzhoy Theorem 2.14.  A separation is represented by two finite
vertex sets `Y` and `Z` covering an ambient finite set `C`, with no graph edge
between the two exclusive sides `Y \ Z` and `Z \ Y`.  Its order is
`|(Y ∩ Z)|`.

Balancedness is stated in the arithmetic form used by the formal proof:
`κ ≤ 4 * |Y ∩ T|` and `κ ≤ 4 * |Z ∩ T|`, where `κ = |T|`.
-/

namespace SimpleGraph


open Finset

variable {V : Type u} [DecidableEq V]

/-- A vertex separation of an ambient finite vertex set `C`.

The two sides `Y` and `Z` cover `C`; vertices outside `C` are irrelevant.  The
separation condition forbids edges between the two exclusive sides. -/
structure VertexSeparation (G : _root_.SimpleGraph V)
    (C Y Z : Finset V) : Prop where
  /-- The left side lies in the ambient set. -/
  left_subset : Y ⊆ C
  /-- The right side lies in the ambient set. -/
  right_subset : Z ⊆ C
  /-- The two sides cover the ambient set. -/
  cover : Y ∪ Z = C
  /-- There are no graph edges from `Y \ Z` to `Z \ Y`. -/
  no_cross :
    ∀ ⦃u v : V⦄, u ∈ Y → u ∉ Z → v ∈ Z → v ∉ Y → ¬ G.Adj u v

namespace VertexSeparation

variable {G : _root_.SimpleGraph V} {C Y Z : Finset V}

/-- The order of a vertex separation is the size of the overlap. -/
def order (_h : VertexSeparation G C Y Z) : ℕ :=
  (Y ∩ Z).card

@[simp] theorem order_eq (h : VertexSeparation G C Y Z) :
    h.order = (Y ∩ Z).card := rfl

/-- The trivial separation `(C,C)`. -/
theorem trivial (G : _root_.SimpleGraph V) (C : Finset V) :
    VertexSeparation G C C C := by
  refine ⟨subset_rfl, subset_rfl, by simp, ?_⟩
  intro u v _hu hu_not _hv _hv_not
  exact False.elim (hu_not ‹u ∈ C›)

/-- Swapping the two sides preserves being a separation. -/
theorem symm (h : VertexSeparation G C Y Z) :
    VertexSeparation G C Z Y := by
  refine ⟨h.right_subset, h.left_subset, ?_, ?_⟩
  · simpa [union_comm] using h.cover
  · intro u v huZ huY vY vZ huv
    exact h.no_cross vY vZ huZ huY (G.symm huv)

/-- No edge crosses from the right exclusive side to the left exclusive side
either. -/
theorem no_cross_symm (h : VertexSeparation G C Y Z)
    {u v : V} (huZ : u ∈ Z) (huY : u ∉ Y)
    (hvY : v ∈ Y) (hvZ : v ∉ Z) :
    ¬ G.Adj u v := by
  intro huv
  exact h.no_cross hvY hvZ huZ huY (G.symm huv)

/-- Both sides of a separation are subsets of `C`. -/
theorem inter_subset_left (_h : VertexSeparation G C Y Z) :
    Y ∩ Z ⊆ Y := Finset.inter_subset_left

/-- Both sides of a separation are subsets of `C`. -/
theorem inter_subset_right (_h : VertexSeparation G C Y Z) :
    Y ∩ Z ⊆ Z := Finset.inter_subset_right

end VertexSeparation

/-- A balanced separation with respect to a terminal set `T` of cardinality
`κ`.  The paper writes this as each side containing at least `κ / 4`
terminals; this file avoids floor/ceiling conventions by multiplying through. -/
structure BalancedSeparation [Fintype V] (G : _root_.SimpleGraph V)
    (C T : Finset V) (κ : ℕ) (Y Z : Finset V) : Prop extends
      VertexSeparation G C Y Z where
  /-- The left side contains at least a quarter of the terminals. -/
  left_balanced : κ ≤ 4 * (Y ∩ T).card
  /-- The right side contains at least a quarter of the terminals. -/
  right_balanced : κ ≤ 4 * (Z ∩ T).card

namespace BalancedSeparation

variable [Fintype V]
variable {G : _root_.SimpleGraph V} {C T Y Z : Finset V} {κ : ℕ}

/-- The order of a balanced separation is the size of its overlap. -/
def order (h : BalancedSeparation G C T κ Y Z) : ℕ :=
  h.toVertexSeparation.order

@[simp] theorem order_eq (h : BalancedSeparation G C T κ Y Z) :
    h.order = (Y ∩ Z).card := rfl

/-- The trivial balanced separation `(C,C)`, assuming `κ = |T|` and
`T ⊆ C`. -/
theorem trivial (G : _root_.SimpleGraph V) {C T : Finset V} {κ : ℕ}
    (hT : T ⊆ C) (hcard : T.card = κ) :
    BalancedSeparation G C T κ C C := by
  refine
    { toVertexSeparation := VertexSeparation.trivial G C
      left_balanced := ?_
      right_balanced := ?_ }
  · have hCT : C ∩ T = T := by
      ext v
      constructor
      · intro hv
        exact (mem_inter.mp hv).2
      · intro hv
        exact mem_inter.mpr ⟨hT hv, hv⟩
    rw [hCT, ← hcard]
    omega
  · have hCT : C ∩ T = T := by
      ext v
      constructor
      · intro hv
        exact (mem_inter.mp hv).2
      · intro hv
        exact mem_inter.mpr ⟨hT hv, hv⟩
    rw [hCT, ← hcard]
    omega

/-- Swapping the two sides preserves balancedness. -/
theorem symm (h : BalancedSeparation G C T κ Y Z) :
    BalancedSeparation G C T κ Z Y where
  toVertexSeparation := h.toVertexSeparation.symm
  left_balanced := h.right_balanced
  right_balanced := h.left_balanced

/-- There exists at least one balanced separation under the usual terminal
cardinality hypotheses. -/
theorem exists_of_terminals_subset {C T : Finset V} {κ : ℕ}
    (hT : T ⊆ C) (hcard : T.card = κ) :
    ∃ Y Z : Finset V, BalancedSeparation G C T κ Y Z :=
  ⟨C, C, trivial G hT hcard⟩

/-- Possible orders of balanced separations. -/
def OrderPredicate (G : _root_.SimpleGraph V) (C T : Finset V) (κ n : ℕ) :
    Prop :=
  ∃ Y Z : Finset V, BalancedSeparation G C T κ Y Z ∧ (Y ∩ Z).card = n

/-- The set of possible balanced-separation orders is nonempty. -/
theorem exists_order {C T : Finset V} {κ : ℕ}
    (hT : T ⊆ C) (hcard : T.card = κ) :
    ∃ n : ℕ, OrderPredicate G C T κ n := by
  rcases exists_of_terminals_subset (G := G) hT hcard with ⟨Y, Z, hYZ⟩
  exact ⟨(Y ∩ Z).card, Y, Z, hYZ, rfl⟩

/-- The minimum order among all balanced separations. -/
noncomputable def minOrder (G : _root_.SimpleGraph V)
    (C T : Finset V) (κ : ℕ) (hT : T ⊆ C) (hcard : T.card = κ) : ℕ := by
  classical
  exact Nat.find (exists_order (G := G) hT hcard)

/-- A balanced separation attaining `minOrder` exists. -/
theorem minOrder_spec {C T : Finset V} {κ : ℕ}
    (hT : T ⊆ C) (hcard : T.card = κ) :
    OrderPredicate G C T κ (minOrder G C T κ hT hcard) := by
  classical
  dsimp [minOrder]
  exact Nat.find_spec (exists_order (G := G) hT hcard)

/-- The minimum order is at most the order of any balanced separation. -/
theorem minOrder_le {C T Y Z : Finset V} {κ : ℕ}
    (hT : T ⊆ C) (hcard : T.card = κ)
    (hYZ : BalancedSeparation G C T κ Y Z) :
    minOrder G C T κ hT hcard ≤ (Y ∩ Z).card := by
  classical
  dsimp [minOrder]
  exact Nat.find_min' (p := OrderPredicate G C T κ)
    (exists_order (G := G) hT hcard)
    ⟨Y, Z, hYZ, rfl⟩

/-- A balanced separation is minimum if no balanced separation has smaller
order. -/
def IsMinimum (_h : BalancedSeparation G C T κ Y Z) : Prop :=
  ∀ ⦃Y' Z' : Finset V⦄,
    BalancedSeparation G C T κ Y' Z' → (Y ∩ Z).card ≤ (Y' ∩ Z').card

/-- Any balanced separation whose order is `minOrder` is minimum. -/
theorem isMinimum_of_order_eq_minOrder {C T Y Z : Finset V} {κ : ℕ}
    (hT : T ⊆ C) (hcard : T.card = κ)
    (hYZ : BalancedSeparation G C T κ Y Z)
    (horder : (Y ∩ Z).card = minOrder G C T κ hT hcard) :
    IsMinimum hYZ := by
  intro Y' Z' hY'Z'
  rw [horder]
  exact minOrder_le (G := G) hT hcard hY'Z'

/-- A minimum balanced separation rules out strictly smaller balanced
separations. -/
theorem not_order_lt_of_isMinimum {C T Y Z Y' Z' : Finset V} {κ : ℕ}
    {hYZ : BalancedSeparation G C T κ Y Z}
    (hmin : IsMinimum hYZ)
    (hY'Z' : BalancedSeparation G C T κ Y' Z') :
    ¬ (Y' ∩ Z').card < (Y ∩ Z).card := by
  intro hlt
  exact (not_lt_of_ge (hmin hY'Z')) hlt

end BalancedSeparation

end SimpleGraph

end Lax17Proofs
