import Lax17Proofs.Source.AppendixA3Claim73
import Lax17Proofs.Source.AppendixA3Claim73Boundary
import Lax17Proofs.Source.AppendixA3Claim73Minimality

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Claim 7.3

This file composes the bad-cut certificate, cut submodularity, minimum-set
argument, and ratio-cleared `Gamma` arithmetic into Claim 7.3 itself.
-/

namespace SimpleGraph
namespace AppendixA3Claim73


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

private theorem terminal_card_eq_of_partition
    {A B T : Finset V}
    (hcover : A ∪ B = (Finset.univ : Finset V))
    (hdisjoint : Disjoint A B) :
    (A ∩ T).card + (B ∩ T).card = T.card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).2
      · exact (Finset.mem_inter.mp hv).2
    · intro hvT
      have hvAB : v ∈ A ∪ B := by rw [hcover]; simp
      rcases Finset.mem_union.mp hvAB with hvA | hvB
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvA, hvT⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvB, hvT⟩)
  · exact hdisjoint.mono Finset.inter_subset_left Finset.inter_subset_left

private theorem inter_union_sdiff_partition (A M : Finset V) :
    (A ∩ M) ∪ (M \ A) = M ∧ Disjoint (A ∩ M) (M \ A) := by
  classical
  constructor
  · ext v
    by_cases hvA : v ∈ A <;> simp [hvA]
  · rw [Finset.disjoint_left]
    intro v hvInter hvDiff
    exact (Finset.mem_sdiff.mp hvDiff).2 (Finset.mem_inter.mp hvInter).1

/-- Chuzhoy Claim 7.3 in ratio-cleared form.

For every edge internal to the minimum set `M`, deleting that edge preserves
scaled well-linkedness of the original terminal set `T`.  The strict threshold
is exactly the inequality used at the end of the source proof.
-/
theorem delete_internal_edge_preserves_scaledEdgeWellLinkedIn
    {T Gamma M : Finset V}
    {gamma terminalNum terminalDen gammaNum gammaDen : ℕ} {a b : V}
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn
        G (Finset.univ : Finset V) T terminalNum terminalDen)
    (hGamma :
      Section46.ScaledEdgeWellLinkedIn
        G (Finset.univ : Finset V) Gamma gammaNum gammaDen)
    (hM :
      AppendixA3DeletableEdge.IsMinimumLemma72Set G T Gamma gamma M)
    (hab : G.Adj a b) (haM : a ∈ M) (hbM : b ∈ M)
    (hthreshold : 3 * gammaDen * gamma < gammaNum * Gamma.card) :
    Section46.ScaledEdgeWellLinkedIn
      (G.deleteEdges ({s(a, b)} : Set (Sym2 V)))
      (Finset.univ : Finset V) T terminalNum terminalDen := by
  classical
  by_contra hfail
  rcases exists_deleteEdgeFailureCut_of_not_scaledEdgeWellLinkedIn_deleteEdges
      G T terminalNum terminalDen hTwell hab hfail with ⟨cut⟩
  let Z : Finset V := cut.A ∩ M
  let Z' : Finset V := M \ cut.A
  have hterminalCard := terminal_card_eq_of_partition
    (T := T) cut.cover cut.disjoint
  have hsmall : 2 * (cut.A ∩ T).card ≤ T.card := by
    have hle := cut.terminal_card_le
    omega
  have hboundaries := cut_parts_boundary_le_gamma
    hTwell hM.disjoint_terminals hsmall
      cut.clusterBoundary_source_inequality hM.boundary_card_le
  have hZboundary : (Section44.clusterBoundary G Z).card ≤ gamma := by
    simpa [Z] using hboundaries.1
  have hZ'boundary : (Section44.clusterBoundary G Z').card ≤ gamma := by
    simpa [Z'] using hboundaries.2
  have hpartition := inter_union_sdiff_partition cut.A M
  have hcover : Z ∪ Z' = M := by simpa [Z, Z'] using hpartition.1
  have hdisjoint : Disjoint Z Z' := by simpa [Z, Z'] using hpartition.2
  rcases ((Section44.mem_edgeBoundary (G := G) cut.A cut.B s(a, b)).1
      cut.deleted_edge_mem_boundary) with
    ⟨_hedge, x, hxA, y, hyB, hxy⟩
  have hends : (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
    rw [Sym2.eq_iff] at hxy
    exact hxy
  have hxM : x ∈ M := by
    rcases hends with hends | hends
    · simpa [← hends.1] using haM
    · simpa [← hends.2] using hbM
  have hyM : y ∈ M := by
    rcases hends with hends | hends
    · simpa [← hends.2] using hbM
    · simpa [← hends.1] using haM
  have hyNotA : y ∉ cut.A := by
    intro hyA
    exact Finset.disjoint_left.mp cut.disjoint hyA hyB
  have hZnonempty : Z.Nonempty :=
    ⟨x, by exact Finset.mem_inter.mpr ⟨hxA, hxM⟩⟩
  have hZ'nonempty : Z'.Nonempty :=
    ⟨y, by exact Finset.mem_sdiff.mpr ⟨hyM, hyNotA⟩⟩
  have hhalves := minimumSet_partition_parts_two_mul_inter_gamma_lt
    hM hcover hdisjoint hZnonempty hZ'nonempty hZboundary hZ'boundary
  exact claim_7_3_gamma_arithmetic_false
    hGamma hM.toLemma72SetConditions hcover hdisjoint
      hhalves.1 hhalves.2 hZboundary hZ'boundary hthreshold

end AppendixA3Claim73
end SimpleGraph

end Lax17Proofs
