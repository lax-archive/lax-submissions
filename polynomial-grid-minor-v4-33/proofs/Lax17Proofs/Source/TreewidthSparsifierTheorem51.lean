import Lax17Proofs.Source.TreewidthSparsifierTheorem51SegmentExpansion

namespace Lax17Proofs

universe u v w

/-!
# Degree-three treewidth sparsifier: Theorem 5.1

This module completes the semantic, cost-free specialization of Theorem 5.1
from Chekuri--Chuzhoy, *Degree-3 Treewidth Sparsifiers*.  Starting with the
repository's proof-facing `StrongPathOfSetsSystem`, it builds the physical
cut-matching transcript, chooses the simultaneous thinning outcome, and uses
the segment-expansion theorem to obtain a degree-three subgraph in which the
first left nail set is polylogarithmically edge-well-linked.

The constants below are deliberately coarse.  The physical construction uses
`O(log h)` restart blocks, records `O(log² h)` local layers, and has exact
well-linkedness denominator bounded here by a universal constant times
`log⁸ h`.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame
open BuildState


set_option maxHeartbeats 2000000

/-- Fixed constants and exponents for the local strong-path formulation of
Theorem 5.1.  The output graph is a same-vertex subgraph of the host, which is
stronger than the topological-minor conclusion needed in Theorem 1.1. -/
theorem theorem51_degree3_wellLinked_subgraph_from_localStrongPathOfSets :
    ∃ cWidth cWidthLog cAlpha cAlphaLog : ℕ,
      0 < cWidth ∧ 0 < cWidthLog ∧ 0 < cAlpha ∧ 0 < cAlphaLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {height width : ℕ}
          (P : StrongPathOfSetsSystem G width height),
            1 < height →
              Even height →
                cWidth * (Nat.log 2 height) ^ cWidthLog ≤ width →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧
                      MaxDegreeAtMost H 3 ∧
                        ScaledWellLinked H (P.left P.firstIndex) 1
                          (cAlpha *
                            (Nat.log 2 height) ^ cAlphaLog) := by
  let C := 2 * segmentRestartMultiplier
  let D := C * realizedRoundConstant
  let CA := 400 * D * C ^ 4 + 2 * D + 2
  let CD := 512 * (4 * D + 2)
  let cAlpha := CD * (6 * CA + 1) + 1
  refine ⟨D, 2, cAlpha, 8, ?_, by decide, ?_, by decide, ?_⟩
  · dsimp [D, C]
    exact Nat.mul_pos
      (Nat.mul_pos (by decide) segmentRestartMultiplier_pos)
      realizedRoundConstant_pos
  · dsimp [cAlpha, CD]
    positivity
  intro V _ _ G height width P hheight heven hwidth
  classical
  let L := Nat.log 2 height
  let N := segmentRestartCount height
  let R := realizedRoundConstant
  have hheightTwo : 2 ≤ height := by omega
  have hLpos : 0 < L := by
    simpa [L] using
      Nat.log_pos (by decide : 1 < 2) hheightTwo
  have hLone : 1 ≤ L := Nat.succ_le_of_lt hLpos
  have hLplus : L + 1 ≤ 2 * L := by omega
  have hN :
      N ≤ C * L := by
    calc
      N = segmentRestartMultiplier * (L + 1) := by
        rfl
      _ ≤ segmentRestartMultiplier * (2 * L) :=
        Nat.mul_le_mul_left segmentRestartMultiplier hLplus
      _ = C * L := by
        dsimp [C]
        ring
  have hbudget :
      N * (R * L) ≤ width := by
    calc
      N * (R * L) ≤ (C * L) * (R * L) :=
        Nat.mul_le_mul_right (R * L) hN
      _ = D * L ^ 2 := by
        dsimp [D]
        ring
      _ ≤ width := by
        simpa [L, D] using hwidth
  rcases
      BuildState.ExpanderBlocks.nonempty
        (P := P) hheight heven N with
    ⟨E⟩
  have hrecords : 0 < E.finalState.records.length :=
    E.records_nonempty hheightTwo (segmentRestartCount_pos height)
  let B := 200 * N ^ 4
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by decide) (Nat.pow_pos (segmentRestartCount_pos height))
  let fallback :=
    E.firstExactRailSegment hheightTwo hbudget hrecords B hB
  obtain ⟨outcome, hsurviving⟩ :=
    E.exists_outcome_survivingSegmentWellLinked
      hheightTwo hbudget hrecords
  let H :=
    (E.blueThinningInput hbudget).thinnedGraph outcome
  refine ⟨H, E.thinnedGraph_le_ambient hbudget outcome,
    E.thinnedGraph_maxDegreeAtMost_three hbudget outcome, ?_⟩
  have hphysical :
      ScaledWellLinked H (P.left P.firstIndex) 1
        ((512 * (2 * (2 * E.finalState.records.length + 1))) *
          (6 * (E.finalState.records.length * (2 * B) +
            2 * E.finalState.records.length + 2) + 1) + 1) := by
    simpa [H, B, fallback] using
      E.thinnedGraph_initialTerminals_scaledWellLinked_of_surviving
        hbudget hrecords B hB fallback outcome
        (512 * (2 * (2 * E.finalState.records.length + 1)))
        (by simpa [B, fallback] using hsurviving)
  let r := E.finalState.records.length
  have hr :
      r ≤ D * L ^ 2 := by
    calc
      r ≤ N * (R * L) := by
        simpa [r, N, R, L] using
          records_length_le_segmentRestartCount E
      _ ≤ (C * L) * (R * L) :=
        Nat.mul_le_mul_right (R * L) hN
      _ = D * L ^ 2 := by
        dsimp [D]
        ring
  have hBbound :
      B ≤ 200 * C ^ 4 * L ^ 4 := by
    calc
      B = 200 * N ^ 4 := rfl
      _ ≤ 200 * (C * L) ^ 4 :=
        Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hN 4)
      _ = 200 * C ^ 4 * L ^ 4 := by
        rw [Nat.mul_pow]
        ring
  have hL2L6 : L ^ 2 ≤ L ^ 6 :=
    Nat.pow_le_pow_right hLpos (by decide)
  have hL6pos : 0 < L ^ 6 := Nat.pow_pos hLpos
  have hL6one : 1 ≤ L ^ 6 := Nat.succ_le_of_lt hL6pos
  have hmain :
      r * (2 * B) ≤
        (400 * D * C ^ 4) * L ^ 6 := by
    calc
      r * (2 * B) ≤
          (D * L ^ 2) * (2 * (200 * C ^ 4 * L ^ 4)) :=
        Nat.mul_le_mul hr (Nat.mul_le_mul_left 2 hBbound)
      _ = (400 * D * C ^ 4) * L ^ 6 := by ring
  have hlinear :
      2 * r ≤ (2 * D) * L ^ 6 := by
    calc
      2 * r ≤ 2 * (D * L ^ 2) := Nat.mul_le_mul_left 2 hr
      _ ≤ 2 * (D * L ^ 6) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left D hL2L6)
      _ = (2 * D) * L ^ 6 := by ring
  have htwo :
      2 ≤ 2 * L ^ 6 := by omega
  have hAbound :
      r * (2 * B) + 2 * r + 2 ≤ CA * L ^ 6 := by
    calc
      r * (2 * B) + 2 * r + 2 ≤
          (400 * D * C ^ 4) * L ^ 6 +
            (2 * D) * L ^ 6 + 2 * L ^ 6 :=
        Nat.add_le_add (Nat.add_le_add hmain hlinear) htwo
      _ = CA * L ^ 6 := by
        dsimp [CA]
        ring
  have hL2pos : 0 < L ^ 2 := Nat.pow_pos hLpos
  have hL2one : 1 ≤ L ^ 2 := Nat.succ_le_of_lt hL2pos
  have hdenBase :
      512 * (2 * (2 * r + 1)) ≤ CD * L ^ 2 := by
    calc
      512 * (2 * (2 * r + 1)) =
          512 * (4 * r + 2) := by ring
      _ ≤ 512 * (4 * (D * L ^ 2) + 2) :=
        Nat.mul_le_mul_left 512
          (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hr) 2)
      _ ≤ 512 * (4 * (D * L ^ 2) + 2 * L ^ 2) :=
        Nat.mul_le_mul_left 512
          (Nat.add_le_add_left (by omega) (4 * (D * L ^ 2)))
      _ = CD * L ^ 2 := by
        dsimp [CD]
        ring
  have hfactor :
      6 * (r * (2 * B) + 2 * r + 2) + 1 ≤
        (6 * CA + 1) * L ^ 6 := by
    calc
      6 * (r * (2 * B) + 2 * r + 2) + 1 ≤
          6 * (CA * L ^ 6) + L ^ 6 :=
        Nat.add_le_add (Nat.mul_le_mul_left 6 hAbound) hL6one
      _ = (6 * CA + 1) * L ^ 6 := by ring
  have hL8pos : 0 < L ^ 8 := Nat.pow_pos hLpos
  have hL8one : 1 ≤ L ^ 8 := Nat.succ_le_of_lt hL8pos
  have hden :
      (512 * (2 * (2 * r + 1))) *
          (6 * (r * (2 * B) + 2 * r + 2) + 1) + 1 ≤
        cAlpha * L ^ 8 := by
    calc
      (512 * (2 * (2 * r + 1))) *
            (6 * (r * (2 * B) + 2 * r + 2) + 1) + 1 ≤
          (CD * L ^ 2) * ((6 * CA + 1) * L ^ 6) + L ^ 8 :=
        Nat.add_le_add (Nat.mul_le_mul hdenBase hfactor) hL8one
      _ = cAlpha * L ^ 8 := by
        dsimp [cAlpha]
        ring
  rcases hphysical with ⟨hone, honeDen, hcut⟩
  refine ⟨hone, ?_, ?_⟩
  · exact honeDen.trans (by simpa [r, L] using hden)
  · intro X Y hcover hdisjoint
    exact (hcut X Y hcover hdisjoint).trans
      (Nat.mul_le_mul_right
        (Section44.edgeBoundary H X Y).card
        (by simpa [r, L] using hden))

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
