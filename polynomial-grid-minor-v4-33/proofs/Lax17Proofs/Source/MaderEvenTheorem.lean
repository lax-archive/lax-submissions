import Lax17Proofs.Source.MaderCoverPairStructure
import Lax17Proofs.Source.MaderThreeSetFinal
import Lax17Proofs.Source.MaderEvenInduction

namespace Lax17Proofs

universe u v w

/-!
# The even-degree Mader theorem

This module closes Frank's irreducible minimum-dangerous-cover argument and
feeds it to the tight-contraction induction.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

private theorem singleton_sdiff_eq_private
    {X Y : Finset W} {u x : W}
    (heq : X \ Y = {u}) (hxX : x ∈ X) (hxY : x ∉ Y) :
    X \ Y = {x} := by
  have hxu : x = u := by
    have : x ∈ ({u} : Finset W) := heq ▸ Finset.mem_sdiff.mpr ⟨hxX, hxY⟩
    simpa using this
  simpa [hxu] using heq

/-- The irreducible dangerous-cover argument required by the strong
induction layer. -/
theorem maderEvenCoreStatement : MaderEvenCoreStatement.{u} := by
  classical
  intro W _ _ H s hdegree heven hno hsingle
  let htight : H.MaderTightSingletons s := fun X hX _ => hsingle X hX
  by_contra hnone
  simp only [not_exists] at hnone
  rcases H.exists_maderCoreConfiguration s hdegree heven hnone with ⟨C⟩
  have hFirstData := H.mem_dangerousAnchorFamily.mp
    (C.family_minimum.1 C.first_mem)
  have hSecondData := H.mem_dangerousAnchorFamily.mp
    (C.family_minimum.1 C.second_mem)
  have hThirdData := H.mem_dangerousAnchorFamily.mp
    (C.family_minimum.1 C.third_mem)
  rcases C.family_minimum.isMinimalCover.exists_private C.first_mem with
    ⟨x1, hx1N, hx1First, hx1Private⟩
  rcases C.family_minimum.isMinimalCover.exists_private C.second_mem with
    ⟨x2, hx2N, hx2Second, hx2Private⟩
  rcases C.family_minimum.isMinimalCover.exists_private C.third_mem with
    ⟨x3, hx3N, hx3Third, hx3Private⟩
  have hx1Second : x1 ∉ C.second :=
    hx1Private C.second C.second_mem C.first_ne_second.symm
  have hx1Third : x1 ∉ C.third :=
    hx1Private C.third C.third_mem C.first_ne_third.symm
  have hx2First : x2 ∉ C.first :=
    hx2Private C.first C.first_mem C.first_ne_second
  have hx2Third : x2 ∉ C.third :=
    hx2Private C.third C.third_mem C.second_ne_third.symm
  have hx3First : x3 ∉ C.first :=
    hx3Private C.first C.first_mem C.first_ne_third
  have hx3Second : x3 ∉ C.second :=
    hx3Private C.second C.second_mem C.second_ne_third
  rcases H.exists_maderCoverPairData C.anchorEdge hdegree htight
      C.anchor_min_degree C.anchorEdge_incident C.anchorEdge_other
      C.family_minimum C.first_mem C.second_mem C.first_ne_second with ⟨D12⟩
  rcases H.exists_maderCoverPairData C.anchorEdge hdegree htight
      C.anchor_min_degree C.anchorEdge_incident C.anchorEdge_other
      C.family_minimum C.first_mem C.third_mem C.first_ne_third with ⟨D13⟩
  rcases H.exists_maderCoverPairData C.anchorEdge hdegree htight
      C.anchor_min_degree C.anchorEdge_incident C.anchorEdge_other
      C.family_minimum C.second_mem C.third_mem C.second_ne_third with ⟨D23⟩
  have h12 : C.first \ C.second = {x1} :=
    singleton_sdiff_eq_private D12.first_sdiff hx1First hx1Second
  have h21 : C.second \ C.first = {x2} :=
    singleton_sdiff_eq_private D12.second_sdiff hx2Second hx2First
  have h13 : C.first \ C.third = {x1} :=
    singleton_sdiff_eq_private D13.first_sdiff hx1First hx1Third
  have h31 : C.third \ C.first = {x3} :=
    singleton_sdiff_eq_private D13.second_sdiff hx3Third hx3First
  have h23 : C.second \ C.third = {x2} :=
    singleton_sdiff_eq_private D23.first_sdiff hx2Second hx2Third
  have h32 : C.third \ C.second = {x3} :=
    singleton_sdiff_eq_private D23.second_sdiff hx3Third hx3Second
  have hboundary := H.boundary_eq_singleton_of_three_singleton_differences
    C.anchorEdge C.anchorEdge_incident C.anchorEdge_other
    hFirstData.2 hSecondData.2 hThirdData.2
    hFirstData.1.center_not_mem hSecondData.1.center_not_mem
    hThirdData.1.center_not_mem h12 h21 h13 h31 h23 h32
    D12.correction_eq D13.correction_eq D23.correction_eq
  exact hno C.anchorEdge C.anchorEdge_incident
    ⟨C.first ∩ C.second ∩ C.third, hboundary⟩

/-- Mader's admissible-pair theorem at a positive even-degree center. -/
theorem exists_maderAdmissible_of_even
    (H : FiniteEdgeIndexedGraph W) (s : W)
    (hdegree : 2 ≤ H.degree s) (heven : Even (H.degree s))
    (hno : H.NoIncidentCutEdge s) :
    ∃ p : H.MaderSplitPair s, H.MaderAdmissible p :=
  exists_maderAdmissible_of_even_of_core maderEvenCoreStatement
    H s hdegree heven hno

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
