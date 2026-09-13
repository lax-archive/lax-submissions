import Lax17Proofs.Source.MaderDangerousCover

namespace Lax17Proofs

universe u v w

/-!
# Finite choice data for the irreducible even Mader proof

From a hypothetical graph with no admissible pair, this module chooses the
minimum-degree anchor, a named edge to it, a minimum dangerous cover through
that anchor, and three distinct cover members.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The finite choices used by Sections 4.3--4.5 of Frank's proof. -/
structure MaderCoreConfiguration (H : FiniteEdgeIndexedGraph W) (s : W) where
  anchor : W
  anchor_mem_neighbors : anchor ∈ H.centerNeighbors s
  anchor_min_degree : ∀ u ∈ H.centerNeighbors s,
    H.degree anchor ≤ H.degree u
  anchorEdge : H.Edge
  anchorEdge_incident : anchorEdge ∈ H.incidentEdges s
  anchorEdge_other : H.otherEndpointAt s anchorEdge = anchor
  family : Finset (Finset W)
  family_minimum : FinsetFamilyIsMinimumCover family
    (H.dangerousAnchorFamily s anchor) (H.centerNeighbors s)
  first : Finset W
  second : Finset W
  third : Finset W
  first_mem : first ∈ family
  second_mem : second ∈ family
  third_mem : third ∈ family
  first_ne_second : first ≠ second
  first_ne_third : first ≠ third
  second_ne_third : second ≠ third

/-- Every hypothetical irreducible even counterexample supplies the complete
minimum-cover configuration.  Tight-singleton irreducibility is not needed
until the pair-structure argument. -/
theorem exists_maderCoreConfiguration
    (H : FiniteEdgeIndexedGraph W) (s : W)
    (hdegree : 2 ≤ H.degree s) (heven : Even (H.degree s))
    (hcounter : ∀ p : H.MaderSplitPair s, ¬ H.MaderAdmissible p) :
    Nonempty (MaderCoreConfiguration H s) := by
  classical
  have hincNonempty : (H.incidentEdges s).Nonempty := by
    apply Finset.card_pos.mp
    simpa [degree] using (show 0 < H.degree s by omega)
  rcases hincNonempty with ⟨someEdge, hsomeEdge⟩
  have hneighborsNonempty : (H.centerNeighbors s).Nonempty :=
    ⟨H.otherEndpointAt s someEdge,
      H.mem_centerNeighbors.mpr ⟨someEdge, hsomeEdge, rfl⟩⟩
  rcases Finset.exists_min_image (H.centerNeighbors s) H.degree
      hneighborsNonempty with ⟨t, ht, htmin⟩
  rcases H.mem_centerNeighbors.mp ht with ⟨e0, he0, he0other⟩
  have hcover := H.dangerousAnchorFamily_covers_centerNeighbors
    hdegree hcounter e0 he0
  rw [he0other] at hcover
  rcases exists_minimum_finsetFamilyCover hcover with ⟨family, hminimum⟩
  have hthree : 3 ≤ family.card :=
    H.minimal_dangerousAnchorCover_three_le_card heven hdegree ht hminimum.1
      hminimum.isMinimalCover
  have htwoLt : 2 < family.card := by omega
  rcases Finset.two_lt_card.mp htwoLt with
    ⟨X1, hX1, X2, hX2, X3, hX3, h12, h13, h23⟩
  exact ⟨{
    anchor := t
    anchor_mem_neighbors := ht
    anchor_min_degree := htmin
    anchorEdge := e0
    anchorEdge_incident := he0
    anchorEdge_other := he0other
    family := family
    family_minimum := hminimum
    first := X1
    second := X2
    third := X3
    first_mem := hX1
    second_mem := hX2
    third_mem := hX3
    first_ne_second := h12
    first_ne_third := h13
    second_ne_third := h23 }⟩

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
