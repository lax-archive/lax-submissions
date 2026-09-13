import Lax17Proofs.Source.MaderDangerousCover

namespace Lax17Proofs

universe u v w

/-!
# The final three-set cut-edge contradiction

This is the purely finite-set and named-edge conclusion of Frank's even-case
proof.  It is kept separate from the dangerous-cover arithmetic so that the
last incidence argument can be checked independently.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

private theorem outside_two_of_three_petals
    {M X1 X2 X3 : Finset W} {x1 x2 x3 z : W}
    (hX1 : X1 = M ∪ {x1}) (hX2 : X2 = M ∪ {x2})
    (hX3 : X3 = M ∪ {x3})
    (hx1M : x1 ∉ M) (hx2M : x2 ∉ M) (hx3M : x3 ∉ M)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hzM : z ∉ M) :
    (z ∉ X1 ∪ X2) ∨ (z ∉ X1 ∪ X3) ∨ (z ∉ X2 ∪ X3) := by
  by_cases hz1 : z = x1
  · right; right
    subst z
    simp [hX2, hX3, hx1M, h12, h13]
  by_cases hz2 : z = x2
  · right; left
    subst z
    have h21 : x2 ≠ x1 := fun h => h12 h.symm
    simp [hX1, hX3, hx2M, h21, h23]
  · left
    simp [hX1, hX2, hzM, hz1, hz2]

/-- Three one-petal extensions of a common core, with one common named
correction edge for every pair, have singleton boundary at the core. -/
theorem boundary_eq_singleton_of_three_pair_corrections
    (H : FiniteEdgeIndexedGraph W) {s t : W} (e0 : H.Edge)
    {M X1 X2 X3 : Finset W} {x1 x2 x3 : W}
    (he0 : e0 ∈ H.incidentEdges s)
    (he0other : H.otherEndpointAt s e0 = t)
    (htM : t ∈ M) (hsM : s ∉ M)
    (hX1 : X1 = M ∪ {x1}) (hX2 : X2 = M ∪ {x2})
    (hX3 : X3 = M ∪ {x3})
    (hx1M : x1 ∉ M) (hx2M : x2 ∉ M) (hx3M : x3 ∉ M)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hInter12 : X1 ∩ X2 = M) (hInter13 : X1 ∩ X3 = M)
    (hInter23 : X2 ∩ X3 = M)
    (hCorrection12 : H.sdiffCorrectionEdges X1 X2 = {e0})
    (hCorrection13 : H.sdiffCorrectionEdges X1 X3 = {e0})
    (hCorrection23 : H.sdiffCorrectionEdges X2 X3 = {e0}) :
    H.boundary M = {e0} := by
  apply Finset.Subset.antisymm
  · intro e he
    have hcross := (H.mem_boundary M e).mp he
    have force (A B : Finset W) (hInter : A ∩ B = M)
        (hOutside :
          (if H.left e ∈ M then H.right e else H.left e) ∉ A ∪ B)
        (hCorrection : H.sdiffCorrectionEdges A B = {e0}) : e = e0 := by
      have hedge : e ∈ H.sdiffCorrectionEdges A B := by
        rw [sdiffCorrectionEdges, H.mem_edgesBetween]
        rcases hcross with h | h
        · have hleftInter : H.left e ∈ A ∩ B := by simpa [hInter] using h.1
          have hrightOutside : H.right e ∈ (A ∪ B)ᶜ := by
            simp only [Finset.mem_compl]
            simpa [h.1] using hOutside
          exact Or.inl ⟨hleftInter, hrightOutside⟩
        · have hrightInter : H.right e ∈ A ∩ B := by simpa [hInter] using h.1
          have hleftOutside : H.left e ∈ (A ∪ B)ᶜ := by
            simp only [Finset.mem_compl]
            have hleftNotM : H.left e ∉ M := h.2
            simpa [hleftNotM] using hOutside
          exact Or.inr ⟨hrightInter, hleftOutside⟩
      rw [hCorrection] at hedge
      simpa using hedge
    let z := if H.left e ∈ M then H.right e else H.left e
    have hzM : z ∉ M := by
      dsimp [z]
      rcases hcross with h | h
      · simp [h.1, h.2]
      · simp [h.2, h.1]
    rcases outside_two_of_three_petals hX1 hX2 hX3 hx1M hx2M hx3M
        h12 h13 h23 hzM with hout | hout | hout
    · simpa [force X1 X2 hInter12 hout hCorrection12]
    · simpa [force X1 X3 hInter13 hout hCorrection13]
    · simpa [force X2 X3 hInter23 hout hCorrection23]
  · intro e he
    have heq : e = e0 := by simpa using he
    subst e
    rw [H.mem_boundary]
    have hends := H.otherEndpointAt_ends he0
    rcases hends with h | h
    · exact Or.inr ⟨by simpa [he0other, h.2] using htM,
        by simpa [h.1] using hsM⟩
    · exact Or.inl ⟨by simpa [he0other, h.2] using htM,
        by simpa [h.1] using hsM⟩

private theorem eq_inter_union_sdiff (A B : Finset W) :
    A = (A ∩ B) ∪ (A \ B) := by
  ext z
  simp
  tauto

/-- The form consumed by the dangerous-cover proof: pairwise singleton
differences force a common core and three distinct one-vertex petals. -/
theorem boundary_eq_singleton_of_three_singleton_differences
    (H : FiniteEdgeIndexedGraph W) {s t : W} (e0 : H.Edge)
    {X1 X2 X3 : Finset W} {x1 x2 x3 : W}
    (he0 : e0 ∈ H.incidentEdges s)
    (he0other : H.otherEndpointAt s e0 = t)
    (ht1 : t ∈ X1) (ht2 : t ∈ X2) (ht3 : t ∈ X3)
    (hs1 : s ∉ X1) (hs2 : s ∉ X2) (hs3 : s ∉ X3)
    (h12 : X1 \ X2 = {x1}) (h21 : X2 \ X1 = {x2})
    (h13 : X1 \ X3 = {x1}) (h31 : X3 \ X1 = {x3})
    (h23 : X2 \ X3 = {x2}) (h32 : X3 \ X2 = {x3})
    (hCorrection12 : H.sdiffCorrectionEdges X1 X2 = {e0})
    (hCorrection13 : H.sdiffCorrectionEdges X1 X3 = {e0})
    (hCorrection23 : H.sdiffCorrectionEdges X2 X3 = {e0}) :
    H.boundary (X1 ∩ X2 ∩ X3) = {e0} := by
  let M := X1 ∩ X2 ∩ X3
  have hx1diff : x1 ∈ X1 \ X2 := by simp [h12]
  have hx2diff : x2 ∈ X2 \ X1 := by simp [h21]
  have hx3diff : x3 ∈ X3 \ X1 := by simp [h31]
  have hx1 := Finset.mem_sdiff.mp hx1diff
  have hx2 := Finset.mem_sdiff.mp hx2diff
  have hx3 := Finset.mem_sdiff.mp hx3diff
  have h12ne : x1 ≠ x2 := by
    intro h
    exact hx1.2 (h ▸ hx2.1)
  have h13ne : x1 ≠ x3 := by
    intro h
    exact hx3.2 (h ▸ hx1.1)
  have h23ne : x2 ≠ x3 := by
    intro h
    have hx3X2not := (Finset.mem_sdiff.mp
      (by simp [h32] : x3 ∈ X3 \ X2)).2
    exact hx3X2not (h ▸ hx2.1)
  have hInter12 : X1 ∩ X2 = M := by
    apply Finset.Subset.antisymm
    · intro z hz
      have hzData := Finset.mem_inter.mp hz
      refine Finset.mem_inter.mpr ⟨hz, ?_⟩
      by_contra hz3
      have hzDiff : z ∈ X1 \ X3 := Finset.mem_sdiff.mpr ⟨hzData.1, hz3⟩
      have hzx1 : z = x1 := by simpa [h13] using hzDiff
      exact hx1.2 (hzx1 ▸ hzData.2)
    · exact Finset.inter_subset_left
  have hInter13 : X1 ∩ X3 = M := by
    apply Finset.Subset.antisymm
    · intro z hz
      have hzData := Finset.mem_inter.mp hz
      have hz2 : z ∈ X2 := by
        by_contra hz2
        have hzDiff : z ∈ X1 \ X2 := Finset.mem_sdiff.mpr ⟨hzData.1, hz2⟩
        have hzx1 : z = x1 := by simpa [h12] using hzDiff
        have hx1X3not := (Finset.mem_sdiff.mp
          (by simp [h13] : x1 ∈ X1 \ X3)).2
        exact hx1X3not (hzx1 ▸ hzData.2)
      change z ∈ X1 ∩ X2 ∩ X3
      simp only [Finset.mem_inter]
      exact ⟨⟨hzData.1, hz2⟩, hzData.2⟩
    · intro z hz
      simp only [M, Finset.mem_inter] at hz
      exact Finset.mem_inter.mpr ⟨hz.1.1, hz.2⟩
  have hInter23 : X2 ∩ X3 = M := by
    apply Finset.Subset.antisymm
    · intro z hz
      have hzData := Finset.mem_inter.mp hz
      have hz1 : z ∈ X1 := by
        by_contra hz1
        have hzDiff : z ∈ X2 \ X1 := Finset.mem_sdiff.mpr ⟨hzData.1, hz1⟩
        have hzx2 : z = x2 := by simpa [h21] using hzDiff
        have hx2X3not := (Finset.mem_sdiff.mp
          (by simp [h23] : x2 ∈ X2 \ X3)).2
        exact hx2X3not (hzx2 ▸ hzData.2)
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hz1, hzData.1⟩,
        hzData.2⟩
    · intro z hz
      simp only [M, Finset.mem_inter] at hz
      exact Finset.mem_inter.mpr ⟨hz.1.2, hz.2⟩
  have hX1 : X1 = M ∪ {x1} := by
    calc
      X1 = (X1 ∩ X2) ∪ (X1 \ X2) := eq_inter_union_sdiff X1 X2
      _ = M ∪ {x1} := by rw [hInter12, h12]
  have hX2 : X2 = M ∪ {x2} := by
    calc
      X2 = (X2 ∩ X1) ∪ (X2 \ X1) := eq_inter_union_sdiff X2 X1
      _ = M ∪ {x2} := by rw [Finset.inter_comm, hInter12, h21]
  have hX3 : X3 = M ∪ {x3} := by
    calc
      X3 = (X3 ∩ X1) ∪ (X3 \ X1) := eq_inter_union_sdiff X3 X1
      _ = M ∪ {x3} := by rw [Finset.inter_comm, hInter13, h31]
  have hx1M : x1 ∉ M := by
    intro h
    simp only [M, Finset.mem_inter] at h
    exact hx1.2 h.1.2
  have hx2M : x2 ∉ M := by
    intro h
    simp only [M, Finset.mem_inter] at h
    exact hx2.2 h.1.1
  have hx3M : x3 ∉ M := by
    intro h
    simp only [M, Finset.mem_inter] at h
    exact hx3.2 h.1.1
  have htM : t ∈ M := by simp [M, ht1, ht2, ht3]
  have hsM : s ∉ M := by
    intro h
    simp only [M, Finset.mem_inter] at h
    exact hs1 h.1.1
  exact H.boundary_eq_singleton_of_three_pair_corrections e0 he0 he0other
    htM hsM hX1 hX2 hX3 hx1M hx2M hx3M h12ne h13ne h23ne
    hInter12 hInter13 hInter23 hCorrection12 hCorrection13 hCorrection23

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
