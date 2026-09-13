import Lax17Proofs.Source.MaderCoreConfiguration
import Lax17Proofs.Source.MaderTightContraction

namespace Lax17Proofs

universe u v w

/-!
# Pair structure in the minimum dangerous cover

This module formalizes Frank's Section 4.4.  Surplus uncrossing, the
minimum-cover replacement argument, and the minimum-degree anchor removal
lemma force each ordered difference of two selected cover members to be one
private center neighbor.  The correction cut contains exactly the anchor edge.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Exact output of the two-member structure argument. -/
structure MaderCoverPairData (H : FiniteEdgeIndexedGraph W) (s : W)
    (e0 : H.Edge) (X Y : Finset W) where
  firstPrivate : W
  secondPrivate : W
  firstPrivate_neighbor : firstPrivate ∈ H.centerNeighbors s
  secondPrivate_neighbor : secondPrivate ∈ H.centerNeighbors s
  first_sdiff : X \ Y = {firstPrivate}
  second_sdiff : Y \ X = {secondPrivate}
  correction_eq : H.sdiffCorrectionEdges X Y = {e0}

private theorem ssubset_ground_of_subset_dangerous
    {H : FiniteEdgeIndexedGraph W} {s : W} {A X : Finset W}
    (hA : A.Nonempty) (hAX : A ⊆ X) (hX : H.MaderDangerous s X) :
    A ⊂ Finset.univ.erase s := by
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨hAX.trans hX.subset_ground, ?_⟩
  intro heq
  have hgroundX : Finset.univ.erase s ⊆ X := by simpa [← heq] using hAX
  exact hX.ssubset_ground.not_subset hgroundX

/-- The union of two distinct members of a minimum dangerous cover has
surplus at least two. -/
theorem minimumDangerousCover_union_surplus_two
    (H : FiniteEdgeIndexedGraph W) {s t : W}
    {family : Finset (Finset W)} {X Y : Finset W}
    (hdegree : 2 ≤ H.degree s)
    (hminimum : FinsetFamilyIsMinimumCover family
      (H.dangerousAnchorFamily s t) (H.centerNeighbors s))
    (hX : X ∈ family) (hY : Y ∈ family) (hXY : X ≠ Y) :
    2 ≤ H.maderSurplus s (X ∪ Y) := by
  have hXdata := H.mem_dangerousAnchorFamily.mp (hminimum.1 hX)
  have hYdata := H.mem_dangerousAnchorFamily.mp (hminimum.1 hY)
  have hUnionNotAmbient := hminimum.union_not_mem_ambient hX hY hXY
  have hUnionNotDangerous : ¬ H.MaderDangerous s (X ∪ Y) := by
    intro hUnion
    exact hUnionNotAmbient (H.mem_dangerousAnchorFamily.mpr
      ⟨hUnion, Finset.mem_union_left Y hXdata.2⟩)
  have hnonempty : (X ∪ Y).Nonempty :=
    hXdata.1.nonempty.mono Finset.subset_union_left
  have hsubset : X ∪ Y ⊆ Finset.univ.erase s :=
    Finset.union_subset hXdata.1.subset_ground hYdata.1.subset_ground
  by_cases hproper : X ∪ Y ⊂ Finset.univ.erase s
  · have hreq := H.centerAvoidingRequirement_le_boundary s (X ∪ Y)
    simp only [MaderDangerous, hnonempty, hproper, true_and] at hUnionNotDangerous
    simp only [maderSurplus]
    omega
  · have heq : X ∪ Y = Finset.univ.erase s :=
      Finset.Subset.antisymm hsubset (by
        by_contra hnotSubset
        exact hproper (Finset.ssubset_iff_subset_ne.mpr
          ⟨hsubset, fun h => hnotSubset (by simpa [h])⟩))
    rw [heq, H.maderSurplus_ground s]
    exact_mod_cast hdegree

/-- Pairwise structure of distinct members of the selected cover. -/
theorem exists_maderCoverPairData
    (H : FiniteEdgeIndexedGraph W) {s t : W} (e0 : H.Edge)
    {family : Finset (Finset W)} {X Y : Finset W}
    (hdegree : 2 ≤ H.degree s)
    (htight : H.MaderTightSingletons s)
    (htmin : ∀ u ∈ H.centerNeighbors s, H.degree t ≤ H.degree u)
    (he0 : e0 ∈ H.incidentEdges s)
    (he0other : H.otherEndpointAt s e0 = t)
    (hminimum : FinsetFamilyIsMinimumCover family
      (H.dangerousAnchorFamily s t) (H.centerNeighbors s))
    (hX : X ∈ family) (hY : Y ∈ family) (hXY : X ≠ Y) :
    Nonempty (MaderCoverPairData H s e0 X Y) := by
  classical
  have hXdata := H.mem_dangerousAnchorFamily.mp (hminimum.1 hX)
  have hYdata := H.mem_dangerousAnchorFamily.mp (hminimum.1 hY)
  rcases hminimum.isMinimalCover.exists_private hX with
    ⟨u, huN, huX, huPrivate⟩
  rcases hminimum.isMinimalCover.exists_private hY with
    ⟨v, hvN, hvY, hvPrivate⟩
  have huY : u ∉ Y := huPrivate Y hY hXY.symm
  have hvX : v ∉ X := hvPrivate X hX hXY
  have hut : u ≠ t := by
    intro h
    exact huY (h ▸ hYdata.2)
  have hvt : v ≠ t := by
    intro h
    exact hvX (h ▸ hXdata.2)
  have hts : t ≠ s := by
    intro h
    exact hXdata.1.center_not_mem (h ▸ hXdata.2)
  have hus : u ≠ s := (Finset.mem_erase.mp
    (H.centerNeighbors_subset_ground s huN)).1
  have hvs : v ≠ s := (Finset.mem_erase.mp
    (H.centerNeighbors_subset_ground s hvN)).1
  have hUnionSurplus := H.minimumDangerousCover_union_surplus_two hdegree
    hminimum hX hY hXY
  have hDiff :
      H.maderSurplus s (X \ Y) + H.maderSurplus s (Y \ X) +
            2 * (H.sdiffCorrectionEdges X Y).card ≤
          H.maderSurplus s X + H.maderSurplus s Y := by
    rcases H.maderSurplus_uncrossing hXdata.1.subset_ground
        hYdata.1.subset_ground with hUnion | hDiff
    · have hInterNonneg := H.maderSurplus_nonneg s (X ∩ Y)
      have hXone := hXdata.1.surplus_le_one
      have hYone := hYdata.1.surplus_le_one
      have hInterZero : H.maderSurplus s (X ∩ Y) = 0 := by omega
      have hInterNonempty : (X ∩ Y).Nonempty :=
        ⟨t, Finset.mem_inter.mpr ⟨hXdata.2, hYdata.2⟩⟩
      have hInterSubset : X ∩ Y ⊆ Finset.univ.erase s :=
        Finset.Subset.trans Finset.inter_subset_left hXdata.1.subset_ground
      have hInterTight : H.MaderTight s (X ∩ Y) :=
        (H.maderTight_iff_surplus_eq_zero s (X ∩ Y)
          hInterNonempty hInterSubset).mpr hInterZero
      have hInterProper : X ∩ Y ⊂ Finset.univ.erase s :=
        ssubset_ground_of_subset_dangerous hInterNonempty
          Finset.inter_subset_left hXdata.1
      have hInterCard := htight (X ∩ Y) hInterTight hInterProper
      have hInterEq : X ∩ Y = {t} := by
        rcases Finset.card_eq_one.mp hInterCard with ⟨z, hz⟩
        have htz : t = z := by simpa [hz] using
          (Finset.mem_inter.mpr ⟨hXdata.2, hYdata.2⟩)
        simpa [htz] using hz
      exact H.maderSurplus_sdiff_of_inter_eq_singleton_min_degree htight
        hInterEq hXdata.2 hYdata.2 huX huY hut hvY hvX hvt hts hus hvs
        (htmin u huN) (htmin v hvN)
    · exact hDiff
  have heCorrection : e0 ∈ H.sdiffCorrectionEdges X Y := by
    rw [sdiffCorrectionEdges, H.mem_edgesBetween]
    have hends := H.otherEndpointAt_ends he0
    have htInter : t ∈ X ∩ Y :=
      Finset.mem_inter.mpr ⟨hXdata.2, hYdata.2⟩
    have hsOutside : s ∈ (X ∪ Y)ᶜ := by
      simp [hXdata.1.center_not_mem, hYdata.1.center_not_mem]
    rcases hends with h | h
    · exact Or.inr ⟨by simpa [he0other, h.2] using htInter,
        by simpa [h.1] using hsOutside⟩
    · exact Or.inl ⟨by simpa [he0other, h.2] using htInter,
        by simpa [h.1] using hsOutside⟩
  have hCorrectionPositive : 1 ≤ (H.sdiffCorrectionEdges X Y).card :=
    Finset.one_le_card.mpr ⟨e0, heCorrection⟩
  have hXone := hXdata.1.surplus_le_one
  have hYone := hYdata.1.surplus_le_one
  have hFirstNonneg := H.maderSurplus_nonneg s (X \ Y)
  have hSecondNonneg := H.maderSurplus_nonneg s (Y \ X)
  have hFirstZero : H.maderSurplus s (X \ Y) = 0 := by omega
  have hSecondZero : H.maderSurplus s (Y \ X) = 0 := by omega
  have hCorrectionCard : (H.sdiffCorrectionEdges X Y).card = 1 := by omega
  have hFirstNonempty : (X \ Y).Nonempty :=
    ⟨u, Finset.mem_sdiff.mpr ⟨huX, huY⟩⟩
  have hSecondNonempty : (Y \ X).Nonempty :=
    ⟨v, Finset.mem_sdiff.mpr ⟨hvY, hvX⟩⟩
  have hFirstSubset : X \ Y ⊆ Finset.univ.erase s :=
    Finset.Subset.trans Finset.sdiff_subset hXdata.1.subset_ground
  have hSecondSubset : Y \ X ⊆ Finset.univ.erase s :=
    Finset.Subset.trans Finset.sdiff_subset hYdata.1.subset_ground
  have hFirstTight : H.MaderTight s (X \ Y) :=
    (H.maderTight_iff_surplus_eq_zero s (X \ Y)
      hFirstNonempty hFirstSubset).mpr hFirstZero
  have hSecondTight : H.MaderTight s (Y \ X) :=
    (H.maderTight_iff_surplus_eq_zero s (Y \ X)
      hSecondNonempty hSecondSubset).mpr hSecondZero
  have hFirstProper : X \ Y ⊂ Finset.univ.erase s :=
    ssubset_ground_of_subset_dangerous hFirstNonempty Finset.sdiff_subset hXdata.1
  have hSecondProper : Y \ X ⊂ Finset.univ.erase s :=
    ssubset_ground_of_subset_dangerous hSecondNonempty Finset.sdiff_subset hYdata.1
  have hFirstCard := htight (X \ Y) hFirstTight hFirstProper
  have hSecondCard := htight (Y \ X) hSecondTight hSecondProper
  have hFirstEq : X \ Y = {u} := by
    rcases Finset.card_eq_one.mp hFirstCard with ⟨z, hz⟩
    have huz : u = z := by simpa [hz] using Finset.mem_sdiff.mpr ⟨huX, huY⟩
    simpa [huz] using hz
  have hSecondEq : Y \ X = {v} := by
    rcases Finset.card_eq_one.mp hSecondCard with ⟨z, hz⟩
    have hvz : v = z := by simpa [hz] using Finset.mem_sdiff.mpr ⟨hvY, hvX⟩
    simpa [hvz] using hz
  have hCorrectionEq : H.sdiffCorrectionEdges X Y = {e0} := by
    rcases Finset.card_eq_one.mp hCorrectionCard with ⟨e, heq⟩
    have he0e : e0 = e := by simpa [heq] using heCorrection
    simpa [he0e] using heq
  exact ⟨{
    firstPrivate := u
    secondPrivate := v
    firstPrivate_neighbor := huN
    secondPrivate_neighbor := hvN
    first_sdiff := hFirstEq
    second_sdiff := hSecondEq
    correction_eq := hCorrectionEq }⟩

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
