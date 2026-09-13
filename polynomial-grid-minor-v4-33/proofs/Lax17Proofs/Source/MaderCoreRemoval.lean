import Lax17Proofs.Source.MaderEvenCore

namespace Lax17Proofs

universe u v w

/-!
# Removing the minimum-degree anchor in the irreducible Mader case

This is equation (15) in Frank's proof.  Once every proper tight set is a
singleton, local connectivity is the minimum of the endpoint degrees.  Thus
an anchor of minimum degree among the center neighbors can be replaced by any
other center neighbor which remains in the cut.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Removing a minimum-degree anchor does not decrease the center-avoiding
requirement if another noncenter vertex of at least that degree remains. -/
theorem centerAvoidingRequirement_le_erase_of_min_degree
    (H : FiniteEdgeIndexedGraph W) {s t u : W} {Z : Finset W}
    (htight : H.MaderTightSingletons s)
    (htZ : t ∈ Z) (huZ : u ∈ Z) (hut : u ≠ t)
    (hts : t ≠ s) (hus : u ≠ s) (hdegree : H.degree t ≤ H.degree u) :
    H.centerAvoidingRequirement s Z ≤
      H.centerAvoidingRequirement s (Z.erase t) := by
  apply H.centerAvoidingRequirement_le
  intro x hx y hy hys
  by_cases hxt : x = t
  · subst x
    have huy : u ≠ y := by
      intro h
      exact hy (h ▸ huZ)
    have hty : t ≠ y := by
      intro h
      exact hy (h ▸ htZ)
    have huErase : u ∈ Z.erase t := Finset.mem_erase.mpr ⟨hut, huZ⟩
    have hyErase : y ∉ Z.erase t := fun h => hy (Finset.mem_of_mem_erase h)
    have htu := H.localEdgeConnectivity_eq_min_degree_of_tightSingletons
      htight hts hys hty
    have huyEq := H.localEdgeConnectivity_eq_min_degree_of_tightSingletons
      htight hus hys huy
    calc
      H.localEdgeConnectivity t y = min (H.degree t) (H.degree y) := htu
      _ ≤ min (H.degree u) (H.degree y) := min_le_min_right _ hdegree
      _ = H.localEdgeConnectivity u y := huyEq.symm
      _ ≤ H.centerAvoidingRequirement s (Z.erase t) :=
        H.localEdgeConnectivity_le_centerAvoidingRequirement huErase hyErase hys
  · exact H.localEdgeConnectivity_le_centerAvoidingRequirement
      (Finset.mem_erase.mpr ⟨hxt, hx⟩)
      (fun h => hy (Finset.mem_of_mem_erase h)) hys

private theorem sdiff_eq_erase_of_inter_eq_singleton
    {X Y : Finset W} {t : W} (hinter : X ∩ Y = {t}) :
    X \ Y = X.erase t := by
  ext z
  constructor
  · intro hz
    have hne : z ≠ t := by
      intro hzt
      subst z
      have htInter : t ∈ X ∩ Y := by simp [hinter]
      exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_inter.mp htInter).2
    exact Finset.mem_erase.mpr ⟨hne, (Finset.mem_sdiff.mp hz).1⟩
  · intro hz
    have hzData := Finset.mem_erase.mp hz
    refine Finset.mem_sdiff.mpr ⟨hzData.2, ?_⟩
    intro hzY
    have hzInter : z ∈ X ∩ Y := Finset.mem_inter.mpr ⟨hzData.2, hzY⟩
    have : z = t := by simpa [hinter] using hzInter
    exact hzData.1 this

/-- If two center-avoiding sets meet exactly in the minimum-degree anchor and
each difference retains a suitable replacement, the difference alternative
of surplus uncrossing holds outright. -/
theorem maderSurplus_sdiff_of_inter_eq_singleton_min_degree
    (H : FiniteEdgeIndexedGraph W) {s t u v : W} {X Y : Finset W}
    (htight : H.MaderTightSingletons s)
    (hinter : X ∩ Y = {t})
    (htX : t ∈ X) (htY : t ∈ Y)
    (huX : u ∈ X) (huY : u ∉ Y) (hut : u ≠ t)
    (hvY : v ∈ Y) (hvX : v ∉ X) (hvt : v ≠ t)
    (hts : t ≠ s) (hus : u ≠ s) (hvs : v ≠ s)
    (hdegreeU : H.degree t ≤ H.degree u)
    (hdegreeV : H.degree t ≤ H.degree v) :
    H.maderSurplus s (X \ Y) + H.maderSurplus s (Y \ X) +
          2 * (H.sdiffCorrectionEdges X Y).card ≤
        H.maderSurplus s X + H.maderSurplus s Y := by
  have hXY : X \ Y = X.erase t :=
    sdiff_eq_erase_of_inter_eq_singleton hinter
  have hYXinter : Y ∩ X = {t} := by simpa [Finset.inter_comm] using hinter
  have hYX : Y \ X = Y.erase t :=
    sdiff_eq_erase_of_inter_eq_singleton hYXinter
  have hreqX : H.centerAvoidingRequirement s X ≤
      H.centerAvoidingRequirement s (X \ Y) := by
    rw [hXY]
    exact H.centerAvoidingRequirement_le_erase_of_min_degree htight htX huX
      hut hts hus hdegreeU
  have hreqY : H.centerAvoidingRequirement s Y ≤
      H.centerAvoidingRequirement s (Y \ X) := by
    rw [hYX]
    exact H.centerAvoidingRequirement_le_erase_of_min_degree htight htY hvY
      hvt hts hvs hdegreeV
  have hcut := H.boundary_sdiff_card_identity X Y
  simp only [maderSurplus]
  omega

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
