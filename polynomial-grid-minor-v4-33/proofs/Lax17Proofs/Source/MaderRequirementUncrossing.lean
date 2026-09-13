import Lax17Proofs.Source.MaderConnectivity

namespace Lax17Proofs

universe u v w

/-!
# Skew-supermodularity of the Mader requirement

This module proves the exact skew-supermodularity disjunction for the
center-avoiding requirement.  The proof records all four possible regions of
a pair realizing each requirement; the resulting four-by-four case analysis
also covers requirements whose eligible pair set is empty.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

private theorem exists_centerAvoidingRequirement_pair_of_ne_zero
    (H : FiniteEdgeIndexedGraph W) {s : W} {X : Finset W}
    (hX : X ⊆ Finset.univ.erase s)
    (hne : H.centerAvoidingRequirement s X ≠ 0) :
    ∃ x ∈ X, ∃ y, y ∉ X ∧ y ≠ s ∧
      H.localEdgeConnectivity x y = H.centerAvoidingRequirement s X := by
  classical
  have hnonempty : X.Nonempty := by
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    intro hXempty
    subst X
    exact hne (H.centerAvoidingRequirement_empty s)
  have hproper : X ⊂ Finset.univ.erase s := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hX, ?_⟩
    intro hXground
    apply hne
    apply H.centerAvoidingRequirement_eq_zero_of_ground_subset
    simp [hXground]
  exact H.exists_centerAvoidingRequirement_pair hnonempty hproper

private theorem localEdgeConnectivity_le_centerAvoidingRequirement_of_separated
    (H : FiniteEdgeIndexedGraph W) {s x y : W} {Z : Finset W}
    (hxs : x ≠ s) (hys : y ≠ s)
    (hsep : (x ∈ Z ∧ y ∉ Z) ∨ (y ∈ Z ∧ x ∉ Z)) :
    H.localEdgeConnectivity x y ≤ H.centerAvoidingRequirement s Z := by
  rcases hsep with hsep | hsep
  · exact H.localEdgeConnectivity_le_centerAvoidingRequirement
      hsep.1 hsep.2 hys
  · rw [H.localEdgeConnectivity_comm x y]
    exact H.localEdgeConnectivity_le_centerAvoidingRequirement
      hsep.1 hsep.2 hxs

private theorem centerAvoidingRequirement_crossing_profile
    (H : FiniteEdgeIndexedGraph W) {s : W} (X Y : Finset W)
    (hX : X ⊆ Finset.univ.erase s) :
    (H.centerAvoidingRequirement s X ≤
          H.centerAvoidingRequirement s (X ∩ Y) ∧
        H.centerAvoidingRequirement s X ≤
          H.centerAvoidingRequirement s (Y \ X)) ∨
    (H.centerAvoidingRequirement s X ≤
          H.centerAvoidingRequirement s (X ∩ Y) ∧
        H.centerAvoidingRequirement s X ≤
          H.centerAvoidingRequirement s (X ∪ Y)) ∨
    (H.centerAvoidingRequirement s X ≤
          H.centerAvoidingRequirement s (X \ Y) ∧
        H.centerAvoidingRequirement s X ≤
          H.centerAvoidingRequirement s (Y \ X)) ∨
    (H.centerAvoidingRequirement s X ≤
          H.centerAvoidingRequirement s (X \ Y) ∧
        H.centerAvoidingRequirement s X ≤
          H.centerAvoidingRequirement s (X ∪ Y)) := by
  classical
  by_cases hzero : H.centerAvoidingRequirement s X = 0
  · left
    omega
  rcases H.exists_centerAvoidingRequirement_pair_of_ne_zero hX hzero with
    ⟨x, hx, y, hy, hys, heq⟩
  have hxs : x ≠ s := (Finset.mem_erase.mp (hX hx)).1
  have le_of_sep (Z : Finset W)
      (hsep : (x ∈ Z ∧ y ∉ Z) ∨ (y ∈ Z ∧ x ∉ Z)) :
      H.centerAvoidingRequirement s X ≤
        H.centerAvoidingRequirement s Z := by
    rw [← heq]
    exact H.localEdgeConnectivity_le_centerAvoidingRequirement_of_separated
      hxs hys hsep
  by_cases hxY : x ∈ Y
  · by_cases hyY : y ∈ Y
    · exact Or.inl ⟨
        le_of_sep (X ∩ Y) (by simp [hx, hy, hxY, hyY]),
        le_of_sep (Y \ X) (by simp [hx, hy, hxY, hyY])⟩
    · exact Or.inr (Or.inl ⟨
        le_of_sep (X ∩ Y) (by simp [hx, hy, hxY, hyY]),
        le_of_sep (X ∪ Y) (by simp [hx, hy, hxY, hyY])⟩)
  · by_cases hyY : y ∈ Y
    · exact Or.inr (Or.inr (Or.inl ⟨
        le_of_sep (X \ Y) (by simp [hx, hy, hxY, hyY]),
        le_of_sep (Y \ X) (by simp [hx, hy, hxY, hyY])⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨
        le_of_sep (X \ Y) (by simp [hx, hy, hxY, hyY]),
        le_of_sep (X ∪ Y) (by simp [hx, hy, hxY, hyY])⟩))

/-- The center-avoiding requirement is skew-supermodular on subsets of the
center-deleted ground set.  This is the exact disjunction: no positivity or
properness assumption is imposed on either set. -/
theorem centerAvoidingRequirement_skew_supermodular
    (H : FiniteEdgeIndexedGraph W) {s : W} {X Y : Finset W}
    (hX : X ⊆ Finset.univ.erase s)
    (hY : Y ⊆ Finset.univ.erase s) :
    H.centerAvoidingRequirement s X +
          H.centerAvoidingRequirement s Y ≤
        H.centerAvoidingRequirement s (X ∩ Y) +
          H.centerAvoidingRequirement s (X ∪ Y) ∨
    H.centerAvoidingRequirement s X +
          H.centerAvoidingRequirement s Y ≤
        H.centerAvoidingRequirement s (X \ Y) +
          H.centerAvoidingRequirement s (Y \ X) := by
  have hXprofile := H.centerAvoidingRequirement_crossing_profile X Y hX
  have hYprofile := H.centerAvoidingRequirement_crossing_profile Y X hY
  rw [Finset.inter_comm Y X, Finset.union_comm Y X] at hYprofile
  rcases hXprofile with hXI | hXIU | hXBC | hXBU
  · rcases hYprofile with hYIB | hYIU | hYCB | hYCU <;> omega
  · rcases hYprofile with hYIB | hYIU | hYCB | hYCU <;> omega
  · rcases hYprofile with hYIB | hYIU | hYCB | hYCU <;> omega
  · rcases hYprofile with hYIB | hYIU | hYCB | hYCU <;> omega

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
