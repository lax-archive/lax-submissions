import Lax17Proofs.Source.ChekuriChuzhoySection5Separate

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy PARTITION action

This file completes journal Claim 5.6.  A large cluster without the required
bandwidth is split along a violating partition, both sides are normalized to
their connected components, and Theorem 5.5 completes the small components.
The resulting acceptable clustering is a strict refinement and does not
increase the source potential.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5PartitionAction


open ChekuriChuzhoySection5BandwidthDecomposition
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5Partition
open ChekuriChuzhoySection5Rho
open ChekuriChuzhoySection5Separate
open ChekuriChuzhoySection5SourcePotential

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Claim 5.6 in the form used inside one phase of Theorem 5.8.  The final
field records the hereditary localization invariant used independently for
each dense block from Claim 5.10. -/
theorem exists_partition_acceptable_strict_refinement
    (P : VertexClustering V) (C terminals initial : Finset V)
    (w0 cap D : Nat) (hD : 4 ≤ D)
    (hupper : ∀ z, rho w0 D z ≤ (1 : Rat) / 20)
    (hacceptable : IsAcceptable G terminals w0 cap 1 D P)
    (hCpart : C ∈ P.parts)
    (hClarge : IsLargeCluster G w0 C)
    (hCinitial : C ⊆ initial)
    (hterminal : Disjoint initial terminals)
    (hlargeInside :
      ∀ R ∈ P.parts, IsLargeCluster G w0 R → R ⊆ initial)
    (hnotBandwidth :
      ¬ TruncatedScaledBandwidth G C (w0 / 2) 1 D) :
    ∃ Q : VertexClustering V,
      IsAcceptable G terminals w0 cap 1 D Q ∧
      clusteringPotential G Q
          (boundedContributionOfUpper w0 D (by omega) hupper) ≤
        clusteringPotential G P
          (boundedContributionOfUpper w0 D (by omega) hupper) ∧
      Q < P ∧
      (∀ R ∈ Q.parts, IsLargeCluster G w0 R → R ⊆ initial) := by
  classical
  let schedule :=
    boundedContributionOfUpper w0 D (by omega) hupper
  let cut : ScaledViolatingPartition G C (w0 / 2) 1 D :=
    Nonempty.some <|
      (not_truncatedScaledBandwidth_iff_exists_violating
        (G := G) (C := C) (cap := w0 / 2)
        (by decide) (by omega)).mp hnotBandwidth
  let S := splitClustering P cut
  have hXpart : cut.X ∈ S.parts := by
    rcases ScaledViolatingPartition.left_nonempty cut with ⟨x, hx⟩
    have hblock : S.block x = cut.X := by
      simpa [S] using splitClustering_block_eq_left P cut hx
    rw [← hblock]
    exact S.block_mem_parts x
  let Q0 := componentClustering G S cut.X
  have hterminalX : Disjoint cut.X terminals :=
    (hterminal.mono_left (cut.left_subset.trans hCinitial))
  have hterminalSingleton :
      ∀ t ∈ terminals, ({t} : Finset V) ∈ S.parts := by
    intro t ht
    have htNotC : t ∉ C := by
      intro htC
      exact Finset.disjoint_left.mp hterminal (hCinitial htC) ht
    have hPblock : P.block t = ({t} : Finset V) :=
      P.block_eq_of_mem (hacceptable.terminal_singleton t ht) (by simp)
    have hSblock : S.block t = ({t} : Finset V) := by
      rw [show S.block t = P.block t by
        simpa [S] using
          splitClustering_block_eq_old_of_not_mem P hCpart cut htNotC,
        hPblock]
    rw [← hSblock]
    exact S.block_mem_parts t
  have hpre : PreAcceptable G terminals w0 Q0 :=
    componentClustering_preAcceptable
      (G := G) S cut.X terminals w0 hterminalSingleton hterminalX
  have hsplitPotential :
      clusteringPotential G S schedule ≤
        clusteringPotential G P schedule := by
    simpa [S, schedule] using
      splitClustering_potential_le_large
        (G := G) P hCpart hD hupper cut hClarge
  have hcomponentPotential :
      clusteringPotential G Q0 schedule ≤
        clusteringPotential G S schedule := by
    simpa [Q0] using
      componentClustering_potential_le_of_mem_parts
        (G := G) S cut.X hXpart schedule
  obtain ⟨Q, hQacceptable, hQpotential, hQlargeQ0, hQleQ0⟩ :=
    exists_acceptableCompletion
      (G := G) Q0 terminals hD hupper hpre
  have hQ0leS : Q0 ≤ S := by
    simpa [Q0] using
      componentClustering_le_of_mem_parts
        (G := G) S cut.X hXpart
  have hSleP : S ≤ P := by
    simpa [S] using splitClustering_le (G := G) P hCpart cut
  have hQleP : Q ≤ P := hQleQ0.trans (hQ0leS.trans hSleP)
  have hQneP : Q ≠ P := by
    rcases ScaledViolatingPartition.left_nonempty cut with ⟨x, hx⟩
    rcases ScaledViolatingPartition.right_nonempty cut with ⟨y, hy⟩
    intro hQP
    have hPxy : P.block x = P.block y := by
      rw [P.block_eq_of_mem hCpart (cut.left_subset hx),
        P.block_eq_of_mem hCpart (cut.right_subset hy)]
    have hQxy : Q.block x = Q.block y := by
      simpa [hQP] using hPxy
    have hyQx : y ∈ Q.block x := by
      rw [hQxy]
      exact Q.mem_block y
    have hyQ0 :
        y ∈ Q0.block x :=
      Q.block_subset_of_refines hQleQ0 x hyQx
    have hQ0blocks : Q0.block y = Q0.block x :=
      Q0.block_eq_of_mem (Q0.block_mem_parts x) hyQ0
    have hyX :
        y ∈ cut.X :=
      (mem_A_iff_of_same_componentBlock
        S cut.X hQ0blocks).mpr hx
    exact Finset.disjoint_left.mp cut.disjoint hyX hy
  have hlargeQ0Inside :
      ∀ R ∈ Q0.parts, IsLargeCluster G w0 R → R ⊆ initial := by
    intro R hRQ0 hRlarge
    rcases Q0.nonempty_of_mem_parts hRQ0 with ⟨v, hvR⟩
    have hQ0block : Q0.block v = R :=
      Q0.block_eq_of_mem hRQ0 hvR
    by_cases hvX : v ∈ cut.X
    · intro x hx
      have hxBlock :
          Q0.block x = Q0.block v :=
        (Q0.block_eq_of_mem hRQ0 hx).trans hQ0block.symm
      have hxX :
          x ∈ cut.X :=
        (mem_A_iff_of_same_componentBlock S cut.X hxBlock).mpr hvX
      exact hCinitial (cut.left_subset hxX)
    · have hsubsetS :
          R ⊆ S.block v := by
        rw [← hQ0block]
        exact
          (componentBlock_subset_oldBlock_sdiff
            (G := G) S cut.X hvX).trans Finset.sdiff_subset
      by_cases hvC : v ∈ C
      · have hvY : v ∈ cut.Y := by
          have hvSides : v ∈ cut.X ∨ v ∈ cut.Y := by
            have : v ∈ cut.X ∪ cut.Y := cut.cover.symm ▸ hvC
            exact Finset.mem_union.mp this
          exact hvSides.resolve_left hvX
        have hSblock : S.block v = cut.Y := by
          simpa [S] using splitClustering_block_eq_right P cut hvY
        exact hsubsetS.trans (hSblock ▸ cut.right_subset.trans hCinitial)
      · have hSblock : S.block v = P.block v := by
          simpa [S] using
            splitClustering_block_eq_old_of_not_mem P hCpart cut hvC
        have hboundary :
            (originalBoundary G R).card ≤
              (originalBoundary G (P.block v)).card := by
          have h0 :=
            componentClustering_boundary_le_of_mem_parts
              (G := G) S cut.X hXpart v
          rw [hQ0block, hSblock] at h0
          exact h0
        have hPlarge : IsLargeCluster G w0 (P.block v) :=
          hRlarge.trans hboundary
        exact hsubsetS.trans <| by
          rw [hSblock]
          exact hlargeInside
            (P.block v) (P.block_mem_parts v) hPlarge
  refine ⟨Q, hQacceptable, ?_,
    ⟨hQleP, fun hPleQ => hQneP (le_antisymm hQleP hPleQ)⟩, ?_⟩
  · have hQpotential' :
        clusteringPotential G Q schedule ≤
          clusteringPotential G Q0 schedule := by
      simpa [schedule] using hQpotential
    exact hQpotential'.trans
      (hcomponentPotential.trans hsplitPotential)
  · intro R hRQ hRlarge
    exact hlargeQ0Inside R
      (hQlargeQ0 R hRQ hRlarge) hRlarge

end ChekuriChuzhoySection5PartitionAction
end SimpleGraph

end Lax17Proofs
