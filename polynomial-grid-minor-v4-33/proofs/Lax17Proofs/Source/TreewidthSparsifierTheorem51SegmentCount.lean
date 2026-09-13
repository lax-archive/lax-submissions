import Lax17Proofs.Source.TreewidthSparsifierTheorem51Claim54

namespace Lax17Proofs

universe u v w

/-!
# Counting the physical segment quotient

This is the size estimate used in Step 2 of Chekuri--Chuzhoy,
*Degree-3 Treewidth Sparsifiers*, Theorem 5.1.  If one rail is split into more
than one segment, every segment is heavy in a recorded local layer.  Choosing
one branch vertex from that heavy colour injects the segments into the
recorded branch events.  Theorem 1.3 bounds every layer by `8h^4+8h` branch
vertices.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame
open HeavySegments


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- A recorded layer together with one of its branch vertices. -/
abbrev RecordedBranchSlot (E : ExpanderBlocks P count) :=
  Σ j : Fin E.finalState.records.length,
    {v : V //
      v ∈ branchVertexFinset (E.recordAt j).layer.localGraph}

theorem recordedBranchSlot_card_le
    (E : ExpanderBlocks P count) :
    Fintype.card E.RecordedBranchSlot ≤
      E.finalState.records.length * (8 * h ^ 4 + 8 * h) := by
  classical
  change
    Fintype.card
        (Σ j : Fin E.finalState.records.length,
          {v : V //
            v ∈ branchVertexFinset (E.recordAt j).layer.localGraph}) ≤
      E.finalState.records.length * (8 * h ^ 4 + 8 * h)
  rw [Fintype.card_sigma]
  calc
    (∑ j : Fin E.finalState.records.length,
        Fintype.card
          {v : V //
            v ∈ branchVertexFinset (E.recordAt j).layer.localGraph}) ≤
        ∑ _j : Fin E.finalState.records.length,
          (8 * h ^ 4 + 8 * h) := by
      apply Finset.sum_le_sum
      intro j _hj
      have hbranch := (E.recordAt j).layer.branch_bound
      rw [Fintype.card_coe]
      rw [(E.recordAt j).layer.support_eq]
      simpa [branchVertexCount] using hbranch
    _ = E.finalState.records.length * (8 * h ^ 4 + 8 * h) := by
      simp

/-- Under a genuine split, every physical segment contains a recorded branch
vertex. -/
theorem exists_segmentBranchSlot
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 1 < B)
    (hmany :
      1 <
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments.length)
    (i :
      Fin
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments.length) :
    ∃ z : E.RecordedBranchSlot,
      z.2.1 ∈
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments.get i := by
  classical
  let s :=
    (E.exactRailSegmentation hbudget hrecords x B
      (by omega)).segments.get i
  have hs :
      s ∈
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments :=
    List.get_mem _ _
  obtain ⟨j, hj⟩ :=
    E.exactRailSegment_heavy_record_of_split
      hbudget hrecords x B hB hmany s hs
  have hpos :
      0 <
        colourCount E.exactRailColour (Sum.inl j) s := by
    omega
  have hmem :
      Sum.inl j ∈ s.map E.exactRailColour := by
    simpa [colourCount] using hpos
  rcases List.mem_map.mp hmem with ⟨v, hv, hvcolour⟩
  exact
    ⟨⟨j, v,
      E.branch_of_exactRailColour_eq_record j hvcolour⟩, hv⟩

/-- Canonical recorded branch slot charged by one segment. -/
noncomputable def segmentBranchSlot
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 1 < B)
    (hmany :
      1 <
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments.length)
    (i :
      Fin
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments.length) :
    E.RecordedBranchSlot :=
  Classical.choose
    (E.exists_segmentBranchSlot
      hbudget hrecords x B hB hmany i)

theorem segmentBranchSlot_vertex_mem
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 1 < B)
    (hmany :
      1 <
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments.length)
    (i :
      Fin
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments.length) :
    (E.segmentBranchSlot hbudget hrecords x B hB hmany i).2.1 ∈
      (E.exactRailSegmentation hbudget hrecords x B
        (by omega)).segments.get i := by
  exact
    Classical.choose_spec
      (E.exists_segmentBranchSlot
        hbudget hrecords x B hB hmany i)

theorem segmentBranchSlot_injective
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 1 < B)
    (hmany :
      1 <
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments.length) :
    Function.Injective
      (E.segmentBranchSlot hbudget hrecords x B hB hmany) := by
  intro i k hik
  by_contra hne
  have hdisjoint :=
    E.exactRailSegmentLists_disjoint
      hbudget hrecords x B (by omega) hne
  have hi :=
    E.segmentBranchSlot_vertex_mem
      hbudget hrecords x B hB hmany i
  have hk :=
    E.segmentBranchSlot_vertex_mem
      hbudget hrecords x B hB hmany k
  have hv :
      (E.segmentBranchSlot hbudget hrecords x B hB hmany i).2.1 =
        (E.segmentBranchSlot hbudget hrecords x B hB hmany k).2.1 :=
    congrArg (fun z : E.RecordedBranchSlot => z.2.1) hik
  exact List.disjoint_left.mp hdisjoint hi (by simpa [hv] using hk)

/-- One rail has at most one uncharged segment plus all recorded branch
slots. -/
theorem exactRailSegmentation_length_le
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 1 < B) :
    (E.exactRailSegmentation hbudget hrecords x B
        (by omega)).segments.length ≤
      1 + E.finalState.records.length * (8 * h ^ 4 + 8 * h) := by
  by_cases hmany :
      1 <
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments.length
  · have hinj :=
      E.segmentBranchSlot_injective
        hbudget hrecords x B hB hmany
    have hcard :=
      Fintype.card_le_of_injective
        (E.segmentBranchSlot hbudget hrecords x B hB hmany) hinj
    have hslots := E.recordedBranchSlot_card_le
    simpa using hcard.trans (hslots.trans (Nat.le_add_left _ 1))
  · omega

/-- The total number of segment-quotient vertices is polynomial in the rail
height and transcript length. -/
theorem exactRailSegmentIndex_card_le
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 1 < B) :
    Fintype.card
        (ExactRailSegmentIndex E hbudget hrecords B (by omega)) ≤
      h * (1 +
        E.finalState.records.length * (8 * h ^ 4 + 8 * h)) := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ x : Fin h,
        Fintype.card
          (Fin
            (E.exactRailSegmentation hbudget hrecords x B
              (by omega)).segments.length)) ≤
        ∑ _x : Fin h,
          (1 +
            E.finalState.records.length * (8 * h ^ 4 + 8 * h)) := by
      apply Finset.sum_le_sum
      intro x _hx
      simpa using
        E.exactRailSegmentation_length_le
          hbudget hrecords x B hB
    _ = h * (1 +
          E.finalState.records.length * (8 * h ^ 4 + 8 * h)) := by
      simp

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
