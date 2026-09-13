import Lax17Proofs.Source.MaderDangerous
import Lax17Proofs.Source.MaderRequirementUncrossing

namespace Lax17Proofs

universe u v w

/-!
# Surplus uncrossing for Mader's theorem

Integer surplus avoids truncated natural subtraction.  The two alternatives
below are Frank's surplus form of cut submodularity and posimodularity.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Boundary cardinality minus the maximum center-avoiding requirement. -/
noncomputable def maderSurplus (H : FiniteEdgeIndexedGraph W) (s : W)
    (X : Finset W) : Int :=
  (H.boundary X).card - H.centerAvoidingRequirement s X

theorem maderSurplus_nonneg (H : FiniteEdgeIndexedGraph W)
    (s : W) (X : Finset W) : 0 ≤ H.maderSurplus s X := by
  have h := H.centerAvoidingRequirement_le_boundary s X
  simp only [maderSurplus]
  omega

theorem MaderDangerous.surplus_le_one
    {H : FiniteEdgeIndexedGraph W} {s : W} {X : Finset W}
    (h : H.MaderDangerous s X) : H.maderSurplus s X ≤ 1 := by
  have hb := h.boundary_le
  simp only [maderSurplus]
  omega

theorem MaderTight.surplus_eq_zero
    {H : FiniteEdgeIndexedGraph W} {s : W} {X : Finset W}
    (h : H.MaderTight s X) : H.maderSurplus s X = 0 := by
  simp [maderSurplus, h.2.2]

theorem maderTight_iff_surplus_eq_zero
    (H : FiniteEdgeIndexedGraph W) (s : W) (X : Finset W)
    (hX : X.Nonempty) (hground : X ⊆ Finset.univ.erase s) :
    H.MaderTight s X ↔ H.maderSurplus s X = 0 := by
  constructor
  · exact MaderTight.surplus_eq_zero
  · intro hzero
    refine ⟨hX, hground, ?_⟩
    have hreq := H.centerAvoidingRequirement_le_boundary s X
    simp only [maderSurplus] at hzero
    omega

/-- Surplus uncrossing with the exact named-edge correction terms. -/
theorem maderSurplus_uncrossing
    (H : FiniteEdgeIndexedGraph W) {s : W} {X Y : Finset W}
    (hX : X ⊆ Finset.univ.erase s)
    (hY : Y ⊆ Finset.univ.erase s) :
    H.maderSurplus s (X ∩ Y) + H.maderSurplus s (X ∪ Y) +
          2 * (H.unionInterCorrectionEdges X Y).card ≤
        H.maderSurplus s X + H.maderSurplus s Y ∨
      H.maderSurplus s (X \ Y) + H.maderSurplus s (Y \ X) +
          2 * (H.sdiffCorrectionEdges X Y).card ≤
        H.maderSurplus s X + H.maderSurplus s Y := by
  have hcutUnionNat := H.boundary_union_inter_card_identity X Y
  have hcutDiffNat := H.boundary_sdiff_card_identity X Y
  have hreq := H.centerAvoidingRequirement_skew_supermodular hX hY
  have hcutUnion :
      (H.boundary X).card + (H.boundary Y).card =
        (H.boundary (X ∩ Y)).card + (H.boundary (X ∪ Y)).card +
          2 * (H.unionInterCorrectionEdges X Y).card := by
    exact_mod_cast hcutUnionNat
  have hcutDiff :
      (H.boundary X).card + (H.boundary Y).card =
        (H.boundary (X \ Y)).card + (H.boundary (Y \ X)).card +
          2 * (H.sdiffCorrectionEdges X Y).card := by
    exact_mod_cast hcutDiffNat
  rcases hreq with hreq | hreq
  · left
    simp only [maderSurplus]
    omega
  · right
    simp only [maderSurplus]
    omega

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
