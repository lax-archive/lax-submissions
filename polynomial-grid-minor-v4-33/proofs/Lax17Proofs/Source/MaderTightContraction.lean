import Lax17Proofs.Source.MaderSetContraction
import Lax17Proofs.Source.MaderSurplus

namespace Lax17Proofs

universe u v w

/-!
# Tight-set contraction for Mader splitting

This module formalizes the contraction step in the finite surplus proof of
Mader's admissible-pair theorem.  A nonempty tight set is contracted away from
the split center.  Cuts in the contracted graph pull back to saturated cuts,
and surplus uncrossing turns every dangerous old witness into a saturated one.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-! ## Connectivity and cut transport -/

/-- Contracting a nonempty set cannot decrease local edge connectivity
between two old vertices that remain distinct after projection. -/
theorem localEdgeConnectivity_le_contractSet
    (H : FiniteEdgeIndexedGraph W) (T : Finset W) (_hT : T.Nonempty)
    {x y : W}
    (hproj : SetContractVertex.projection (T := T) x ≠
      SetContractVertex.projection (T := T) y) :
    H.localEdgeConnectivity x y ≤
      (H.contractSet T).localEdgeConnectivity
        (SetContractVertex.projection (T := T) x)
        (SetContractVertex.projection (T := T) y) := by
  have hxy : x ≠ y := fun h => hproj (congrArg _ h)
  apply ((H.contractSet T).pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
    hproj _).mp
  intro Y hx hy
  rw [contractSet_boundary_card]
  apply (H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity hxy _).mpr
    le_rfl
  · exact SetContractVertex.mem_preimageFinset.mpr hx
  · exact fun h => hy (SetContractVertex.mem_preimageFinset.mp h)

/-- The requirement of a saturated old cut can only increase after
contraction. -/
theorem centerAvoidingRequirement_le_contractSet_of_saturated
    (H : FiniteEdgeIndexedGraph W) {s : W} (T X : Finset W)
    (hT : T.Nonempty) (hs : s ∉ T)
    (hX : SetContractVertex.Saturated T X) :
    H.centerAvoidingRequirement s X ≤
      (H.contractSet T).centerAvoidingRequirement
        (SetContractVertex.projection (T := T) s)
        (SetContractVertex.imageFinset (T := T) X) := by
  apply H.centerAvoidingRequirement_le
  intro x hx y hy hys
  have hpx : SetContractVertex.projection (T := T) x ∈
      SetContractVertex.imageFinset (T := T) X :=
    SetContractVertex.mem_imageFinset.mpr ⟨x, hx, rfl⟩
  have hpy : SetContractVertex.projection (T := T) y ∉
      SetContractVertex.imageFinset (T := T) X := by
    intro hyImage
    have hyPre : y ∈ SetContractVertex.preimageFinset
        (SetContractVertex.imageFinset (T := T) X) :=
      SetContractVertex.mem_preimageFinset.mpr hyImage
    rw [SetContractVertex.preimage_imageFinset_eq hT hX] at hyPre
    exact hy hyPre
  have hpys : SetContractVertex.projection (T := T) y ≠
      SetContractVertex.projection (T := T) s := by
    intro h
    exact hys (SetContractVertex.eq_of_projection_eq_of_right_not_mem h hs)
  exact (H.localEdgeConnectivity_le_contractSet T hT
      (fun h => hpy (h ▸ hpx))).trans
    ((H.contractSet T).localEdgeConnectivity_le_centerAvoidingRequirement
      hpx hpy hpys)

/-- A saturated cut keeps its boundary exactly and its Mader requirement does
not decrease under contraction. -/
theorem contractSet_boundary_card_and_requirement_of_saturated
    (H : FiniteEdgeIndexedGraph W) {s : W} (T X : Finset W)
    (hT : T.Nonempty) (hs : s ∉ T)
    (hX : SetContractVertex.Saturated T X) :
    ((H.contractSet T).boundary
        (SetContractVertex.imageFinset (T := T) X)).card =
        (H.boundary X).card ∧
      H.centerAvoidingRequirement s X ≤
        (H.contractSet T).centerAvoidingRequirement
          (SetContractVertex.projection (T := T) s)
          (SetContractVertex.imageFinset (T := T) X) :=
  ⟨H.contractSet_boundary_card_of_saturated T X hT hX,
    H.centerAvoidingRequirement_le_contractSet_of_saturated T X hT hs hX⟩

/-- A saturated dangerous old cut remains dangerous after contraction. -/
theorem MaderDangerous.contractSet_image
    {H : FiniteEdgeIndexedGraph W} {s : W} {T X : Finset W}
    (hX : H.MaderDangerous s X) (hT : T.Nonempty) (hs : s ∉ T)
    (hsat : SetContractVertex.Saturated T X) :
    (H.contractSet T).MaderDangerous
      (SetContractVertex.projection (T := T) s)
      (SetContractVertex.imageFinset (T := T) X) := by
  have hpre := SetContractVertex.preimage_imageFinset_eq hT hsat
  have himageNonempty :
      (SetContractVertex.imageFinset (T := T) X).Nonempty := by
    rcases hX.nonempty with ⟨x, hx⟩
    exact ⟨SetContractVertex.projection (T := T) x,
      SetContractVertex.mem_imageFinset.mpr ⟨x, hx, rfl⟩⟩
  have himageSubset : SetContractVertex.imageFinset (T := T) X ⊆
      Finset.univ.erase (SetContractVertex.projection (T := T) s) := by
    intro z hz
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    have hsPre : s ∈ SetContractVertex.preimageFinset
        (SetContractVertex.imageFinset (T := T) X) :=
      SetContractVertex.mem_preimageFinset.mpr hz
    rw [hpre] at hsPre
    exact hX.center_not_mem hsPre
  have himageNe : SetContractVertex.imageFinset (T := T) X ≠
      Finset.univ.erase (SetContractVertex.projection (T := T) s) := by
    intro heq
    rcases Finset.exists_of_ssubset hX.ssubset_ground with
      ⟨y, hyGround, hyX⟩
    have hpyGround : SetContractVertex.projection (T := T) y ∈
        Finset.univ.erase (SetContractVertex.projection (T := T) s) := by
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      have hys := SetContractVertex.eq_of_projection_eq_of_right_not_mem h hs
      exact (Finset.mem_erase.mp hyGround).1 hys
    have hpyImage : SetContractVertex.projection (T := T) y ∈
        SetContractVertex.imageFinset (T := T) X := heq ▸ hpyGround
    have hyPre : y ∈ SetContractVertex.preimageFinset
        (SetContractVertex.imageFinset (T := T) X) :=
      SetContractVertex.mem_preimageFinset.mpr hpyImage
    rw [hpre] at hyPre
    exact hyX hyPre
  refine ⟨himageNonempty,
    Finset.ssubset_iff_subset_ne.mpr ⟨himageSubset, himageNe⟩, ?_⟩
  have hboundary := H.contractSet_boundary_card_of_saturated T X hT hsat
  have hreq := H.centerAvoidingRequirement_le_contractSet_of_saturated
    T X hT hs hsat
  rw [hboundary]
  exact hX.boundary_le.trans (Nat.add_le_add_right hreq 1)

/-! ## Incidence and split-pair lifting -/

/-- Contracting a nonempty set disjoint from the center preserves the absence
of incident named cut edges at that center. -/
theorem NoIncidentCutEdge.contractSet
    {H : FiniteEdgeIndexedGraph W} {s : W} (h : H.NoIncidentCutEdge s)
    (T : Finset W) (_hT : T.Nonempty) (hs : s ∉ T) :
    (H.contractSet T).NoIncidentCutEdge
      (SetContractVertex.projection (T := T) s) := by
  intro e heIncident heCut
  rcases ((H.contractSet T).isNamedCutEdge_iff_boundary_card_one_mem e).mp heCut with
    ⟨Y, hcard, heBoundary⟩
  have heOldIncident : e.1 ∈ H.incidentEdges s := by
    exact (contractSetIncidentEquiv H T s hs ⟨e, heIncident⟩).2
  have heOldBoundary : e.1 ∈
      H.boundary (SetContractVertex.preimageFinset Y) := by
    rw [H.mem_boundary]
    exact (contractSet_crosses_iff H T Y e).mp
      (((H.contractSet T).mem_boundary Y e).mp heBoundary)
  have hne := h.boundary_card_ne_one heOldIncident heOldBoundary
  exact hne (by simpa [contractSet_boundary_card H T Y] using hcard)

private noncomputable def oldOtherEndpoint
    (H : FiniteEdgeIndexedGraph W) (s : W) (e : H.Edge) : W :=
  if H.left e = s then H.right e else H.left e

omit [Fintype W] in
private theorem oldOtherEndpoint_data
    (H : FiniteEdgeIndexedGraph W) {s : W} (T : Finset W) (hs : s ∉ T)
    (e : (H.contractSet T).Edge) {z : SetContractVertex W T}
    (hends :
      ((H.contractSet T).left e = SetContractVertex.projection (T := T) s ∧
          (H.contractSet T).right e = z) ∨
        ((H.contractSet T).right e = SetContractVertex.projection (T := T) s ∧
          (H.contractSet T).left e = z)) :
    ((H.left e.1 = s ∧ H.right e.1 = H.oldOtherEndpoint s e.1) ∨
        (H.right e.1 = s ∧ H.left e.1 = H.oldOtherEndpoint s e.1)) ∧
      SetContractVertex.projection (T := T) (H.oldOtherEndpoint s e.1) = z := by
  rcases hends with hends | hends
  · have hleft : H.left e.1 = s :=
      SetContractVertex.eq_of_projection_eq_of_right_not_mem hends.1 hs
    refine ⟨Or.inl ⟨hleft, by simp [oldOtherEndpoint, hleft]⟩, ?_⟩
    rw [oldOtherEndpoint, if_pos hleft]
    simpa only [contractSet_right] using hends.2
  · have hright : H.right e.1 = s :=
      SetContractVertex.eq_of_projection_eq_of_right_not_mem hends.1 hs
    have hleft : H.left e.1 ≠ s := fun h => H.end_ne e.1 (h.trans hright.symm)
    refine ⟨Or.inr ⟨hright, by simp [oldOtherEndpoint, hleft]⟩, ?_⟩
    rw [oldOtherEndpoint, if_neg hleft]
    simpa only [contractSet_left] using hends.2

/-- Every split pair at the projected center is the image of an old split
pair.  Equality is equality of the full `MaderSplitPair` structures. -/
theorem MaderSplitPair.exists_preimage_contractSet
    (H : FiniteEdgeIndexedGraph W) {s : W} (T : Finset W) (hs : s ∉ T)
    (q : (H.contractSet T).MaderSplitPair
      (SetContractVertex.projection (T := T) s)) :
    ∃ p : H.MaderSplitPair s, p.mapContractSet T hs = q := by
  have hfirst := H.oldOtherEndpoint_data T hs q.first q.first_ends
  have hsecond := H.oldOtherEndpoint_data T hs q.second q.second_ends
  let p : H.MaderSplitPair s :=
    { first := q.first.1
      second := q.second.1
      edge_ne := fun h => q.edge_ne (Subtype.ext h)
      firstOther := H.oldOtherEndpoint s q.first.1
      secondOther := H.oldOtherEndpoint s q.second.1
      first_ends := hfirst.1
      second_ends := hsecond.1 }
  refine ⟨p, ?_⟩
  cases q
  rw [MaderSplitPair.mk.injEq]
  exact ⟨Subtype.ext rfl, Subtype.ext rfl, hfirst.2, hsecond.2⟩

/-! ## Saturating a dangerous witness by surplus uncrossing -/

/-- The center-deleted whole ground has boundary equal to the degree of the
center. -/
theorem boundary_ground_card (H : FiniteEdgeIndexedGraph W) (s : W) :
    (H.boundary (Finset.univ.erase s)).card = H.degree s := by
  rw [show Finset.univ.erase s = ({s} : Finset W)ᶜ by ext; simp]
  rw [H.boundary_compl, H.boundary_singleton]
  rfl

/-- The surplus of the center-deleted whole ground is the center degree. -/
theorem maderSurplus_ground (H : FiniteEdgeIndexedGraph W) (s : W) :
    H.maderSurplus s (Finset.univ.erase s) = H.degree s := by
  have hreq := H.centerAvoidingRequirement_eq_zero_of_ground_subset
    (s := s) (X := Finset.univ.erase s) (by rfl)
  simp [maderSurplus, H.boundary_ground_card s, hreq]

/-- Nonempty proper center-avoiding sets of surplus at most one are exactly
the dangerous witnesses needed below. -/
theorem maderDangerous_of_surplus_le_one
    (H : FiniteEdgeIndexedGraph W) {s : W} {X : Finset W}
    (hX : X.Nonempty) (hproper : X ⊂ Finset.univ.erase s)
    (hsurplus : H.maderSurplus s X ≤ 1) :
    H.MaderDangerous s X := by
  refine ⟨hX, hproper, ?_⟩
  have hreq := H.centerAvoidingRequirement_le_boundary s X
  simp only [maderSurplus] at hsurplus
  omega

private theorem MaderSplitPair.first_mem_sdiffCorrectionEdges
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s)
    {T X : Finset W} (hT : T ⊆ Finset.univ.erase s)
    (hX : X ⊆ Finset.univ.erase s)
    (hfirstT : p.firstOther ∈ T) (hfirstX : p.firstOther ∈ X) :
    p.first ∈ H.sdiffCorrectionEdges T X := by
  rw [sdiffCorrectionEdges, H.mem_edgesBetween]
  have hsT : s ∉ T := fun hs => (Finset.mem_erase.mp (hT hs)).1 rfl
  have hsX : s ∉ X := fun hs => (Finset.mem_erase.mp (hX hs)).1 rfl
  rcases p.first_ends with h | h
  · right
    exact ⟨by simpa [h.2] using And.intro hfirstT hfirstX,
      by simp [h.1, hsT, hsX]⟩
  · left
    exact ⟨by simpa [h.2] using And.intro hfirstT hfirstX,
      by simp [h.1, hsT, hsX]⟩

private theorem MaderSplitPair.second_mem_sdiffCorrectionEdges
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s)
    {T X : Finset W} (hT : T ⊆ Finset.univ.erase s)
    (hX : X ⊆ Finset.univ.erase s)
    (hsecondT : p.secondOther ∈ T) (hsecondX : p.secondOther ∈ X) :
    p.second ∈ H.sdiffCorrectionEdges T X := by
  rw [sdiffCorrectionEdges, H.mem_edgesBetween]
  have hsT : s ∉ T := fun hs => (Finset.mem_erase.mp (hT hs)).1 rfl
  have hsX : s ∉ X := fun hs => (Finset.mem_erase.mp (hX hs)).1 rfl
  rcases p.second_ends with h | h
  · right
    exact ⟨by simpa [h.2] using And.intro hsecondT hsecondX,
      by simp [h.1, hsT, hsX]⟩
  · left
    exact ⟨by simpa [h.2] using And.intro hsecondT hsecondX,
      by simp [h.1, hsT, hsX]⟩

/-- Uncrossing a dangerous witness with a nonempty tight set produces a
saturated dangerous witness containing both other endpoints of the split
pair.  The degree hypothesis is used only when `T ∪ X` is the whole
center-deleted ground. -/
theorem exists_saturated_maderDangerous_of_tight
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    {T X : Finset W} (hT : H.MaderTight s T)
    (hTproper : T ⊂ Finset.univ.erase s) (hdegree : 2 ≤ H.degree s)
    (hX : H.MaderDangerous s X)
    (hfirstX : p.firstOther ∈ X) (hsecondX : p.secondOther ∈ X) :
    ∃ Z : Finset W, H.MaderDangerous s Z ∧
      SetContractVertex.Saturated T Z ∧
      p.firstOther ∈ Z ∧ p.secondOther ∈ Z := by
  have hTsubset := hTproper.subset
  have hTsurplus := hT.surplus_eq_zero
  have hXsurplus := hX.surplus_le_one
  have huncross := H.maderSurplus_uncrossing hTsubset hX.subset_ground
  rcases huncross with hunion | hdiff
  · have hinterNonneg := H.maderSurplus_nonneg s (T ∩ X)
    have hunionSurplus : H.maderSurplus s (T ∪ X) ≤ 1 := by
      rw [hTsurplus] at hunion
      norm_num at hunion
      omega
    have hunionSubset : T ∪ X ⊆ Finset.univ.erase s :=
      Finset.union_subset hTsubset hX.subset_ground
    have hunionProper : T ∪ X ⊂ Finset.univ.erase s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hunionSubset, ?_⟩
      intro heq
      have hgroundSurplus := H.maderSurplus_ground s
      rw [heq, hgroundSurplus] at hunionSurplus
      exact (by omega)
    refine ⟨T ∪ X,
      H.maderDangerous_of_surplus_le_one
        (hX.nonempty.mono Finset.subset_union_right) hunionProper hunionSurplus,
      Or.inl Finset.subset_union_left,
      Finset.mem_union_right T hfirstX,
      Finset.mem_union_right T hsecondX⟩
  · have hTXNonneg := H.maderSurplus_nonneg s (T \ X)
    have hXTNonneg := H.maderSurplus_nonneg s (X \ T)
    have hfirstNotT : p.firstOther ∉ T := by
      intro hfirstT
      have hmem := p.first_mem_sdiffCorrectionEdges hTsubset
        hX.subset_ground hfirstT hfirstX
      have hcard : 1 ≤ (H.sdiffCorrectionEdges T X).card :=
        Finset.one_le_card.mpr ⟨p.first, hmem⟩
      rw [hTsurplus] at hdiff
      norm_num at hdiff
      omega
    have hsecondNotT : p.secondOther ∉ T := by
      intro hsecondT
      have hmem := p.second_mem_sdiffCorrectionEdges hTsubset
        hX.subset_ground hsecondT hsecondX
      have hcard : 1 ≤ (H.sdiffCorrectionEdges T X).card :=
        Finset.one_le_card.mpr ⟨p.second, hmem⟩
      rw [hTsurplus] at hdiff
      norm_num at hdiff
      omega
    have hdiffSurplus : H.maderSurplus s (X \ T) ≤ 1 := by
      rw [hTsurplus] at hdiff
      norm_num at hdiff
      omega
    have hdiffSubset : X \ T ⊆ Finset.univ.erase s :=
      Finset.Subset.trans Finset.sdiff_subset hX.subset_ground
    have hdiffProper : X \ T ⊂ Finset.univ.erase s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hdiffSubset, ?_⟩
      intro heq
      rcases hT.1 with ⟨t, ht⟩
      have htGround := hTsubset ht
      have htDiff : t ∈ X \ T := heq ▸ htGround
      exact (Finset.mem_sdiff.mp htDiff).2 ht
    refine ⟨X \ T,
      H.maderDangerous_of_surplus_le_one
        ⟨p.firstOther, Finset.mem_sdiff.mpr ⟨hfirstX, hfirstNotT⟩⟩
        hdiffProper hdiffSurplus,
      Or.inr (Finset.disjoint_left.mpr fun t htT htDiff =>
        (Finset.mem_sdiff.mp htDiff).2 htT),
      Finset.mem_sdiff.mpr ⟨hfirstX, hfirstNotT⟩,
      Finset.mem_sdiff.mpr ⟨hsecondX, hsecondNotT⟩⟩

/-! ## Admissibility lifting -/

/-- Admissibility of a split pair after contracting a nonempty tight proper
set lifts to admissibility before contraction.  The lower degree bound is
needed for the whole-ground union case in surplus uncrossing. -/
theorem tight_contraction_lifts_admissible
    (H : FiniteEdgeIndexedGraph W) {s : W} (T : Finset W)
    (hTnonempty : T.Nonempty) (hT : H.MaderTight s T)
    (hTproper : T ⊂ Finset.univ.erase s) (hdegree : 2 ≤ H.degree s)
    (p : H.MaderSplitPair s)
    (hadmissible : (H.contractSet T).MaderAdmissible
      (p.mapContractSet T
        (fun hs => (Finset.mem_erase.mp (hT.2.1 hs)).1 rfl))) :
    H.MaderAdmissible p := by
  have hs : s ∉ T := fun hs => (Finset.mem_erase.mp (hT.2.1 hs)).1 rfl
  by_contra hnot
  rcases (H.not_maderAdmissible_iff_exists_dangerous p).mp hnot with
    ⟨X, hX, hfirstX, hsecondX⟩
  rcases H.exists_saturated_maderDangerous_of_tight p hT hTproper hdegree
      hX hfirstX hsecondX with
    ⟨Z, hZ, hZsat, hfirstZ, hsecondZ⟩
  have hZcontract := hZ.contractSet_image hTnonempty hs hZsat
  have hfirstImage : (p.mapContractSet T hs).firstOther ∈
      SetContractVertex.imageFinset (T := T) Z := by
    rw [MaderSplitPair.mapContractSet_firstOther]
    exact SetContractVertex.mem_imageFinset.mpr
      ⟨p.firstOther, hfirstZ, rfl⟩
  have hsecondImage : (p.mapContractSet T hs).secondOther ∈
      SetContractVertex.imageFinset (T := T) Z := by
    rw [MaderSplitPair.mapContractSet_secondOther]
    exact SetContractVertex.mem_imageFinset.mpr
      ⟨p.secondOther, hsecondZ, rfl⟩
  exact ((H.contractSet T).not_maderAdmissible_of_exists_dangerous
    (p.mapContractSet T hs)
    ⟨SetContractVertex.imageFinset (T := T) Z,
      hZcontract, hfirstImage, hsecondImage⟩) hadmissible

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
