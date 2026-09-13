import Lax17Proofs.Source.TreewidthSparsifierTheorem51SegmentCount
import Lax17Proofs.Source.TreewidthSparsifierTheorem51SegmentLinkConcentration
import Lax17Proofs.Source.TreewidthSparsifierThinningUnion
import Lax17Proofs.Source.GridMinorArithmetic

namespace Lax17Proofs

universe u v w

/-!
# One thinning outcome preserving every physical-segment cut

This is the finite union-bound part of Step 3 of Chekuri--Chuzhoy,
*Degree-3 Treewidth Sparsifiers*, Theorem 5.1.  Claim 5.4 supplies edge
connectivity `N` for the segment quotient.  The segment-counting lemma bounds
its order by a fixed polynomial in `h`, `N`, and the universal cut-matching
round constant.  Karger's cut count and the complete-link fixed-cut estimate
then select one genuine thinning outcome which retains a usable `1/256`
fraction of every quotient cut.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

set_option maxHeartbeats 2000000

open ChekuriChuzhoySection5TerminalSkeleton
open ThinningUnion
open BuildState
open BuildState.ExpanderBlocks


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

/-- A fixed graph-independent multiplier large enough for the segment
quotient union bound.  Its dependence on `realizedRoundConstant` is harmless:
that constant is itself universal. -/
noncomputable def segmentRestartMultiplier : ℕ :=
  2 ^ (realizedRoundConstant + 51)

/-- Number `N` of independent cut-matching blocks used in the source proof. -/
noncomputable def segmentRestartCount (h : ℕ) : ℕ :=
  segmentRestartMultiplier * (Nat.log 2 h + 1)

theorem segmentRestartMultiplier_pos :
    0 < segmentRestartMultiplier := by
  unfold segmentRestartMultiplier
  positivity

theorem segmentRestartCount_pos (h : ℕ) :
    0 < segmentRestartCount h := by
  unfold segmentRestartCount
  exact Nat.mul_pos segmentRestartMultiplier_pos (by omega)

theorem segmentRestartCount_eq
    (h : ℕ) :
    segmentRestartCount h =
      2 ^ (realizedRoundConstant + 51) *
        (Nat.log 2 h + 1) := by
  rfl

/-- The number of recorded physical layers in all restarted games. -/
theorem records_length_le_segmentRestartCount
    {G : _root_.SimpleGraph V} {ell h : ℕ}
    {P : StrongPathOfSetsSystem G ell h}
    (E : BuildState.ExpanderBlocks P (segmentRestartCount h)) :
    E.finalState.records.length ≤
      segmentRestartCount h *
        (realizedRoundConstant * Nat.log 2 h) := by
  rw [E.records_length_eq_flattened_length]
  exact E.flattened_length_le

/-- A coarse power-of-two order bound for the physical segment quotient.
Only its logarithm is used by Karger's estimate. -/
theorem segmentIndex_card_le_two_pow
    {G : _root_.SimpleGraph V} {ell h : ℕ}
    {P : StrongPathOfSetsSystem G ell h}
    (E : BuildState.ExpanderBlocks P (segmentRestartCount h))
    (hheight : 2 ≤ h)
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 1 < B) :
    Fintype.card
        (ExactRailSegmentIndex E hbudget hrecords B (by omega)) ≤
      2 ^ (56 + 2 * realizedRoundConstant +
        7 * (Nat.log 2 h + 1)) := by
  let R := realizedRoundConstant
  let L := Nat.log 2 h + 1
  let N := segmentRestartCount h
  have hR : 0 < R := by
    exact realizedRoundConstant_pos
  have hL : 0 < L := by
    simp [L]
  have hlog_le : Nat.log 2 h ≤ L := by
    simp [L]
  have hhpow : h ≤ 2 ^ L := by
    exact (Nat.lt_pow_succ_log_self (by norm_num) h).le
  have hrecordsBound :
      E.finalState.records.length ≤ N * (R * L) := by
    calc
      E.finalState.records.length ≤
          N * (R * Nat.log 2 h) := by
        simpa [N, R] using
          (records_length_le_segmentRestartCount E)
      _ ≤ N * (R * L) := by
        gcongr
  have hpoly :
      Fintype.card
          (ExactRailSegmentIndex E hbudget hrecords B (by omega)) ≤
        17 * N * R * L * h ^ 5 := by
    have hsegments :=
      E.exactRailSegmentIndex_card_le hbudget hrecords B hB
    have hheightPos : 0 < h := by omega
    have hN : 0 < N := by
      exact segmentRestartCount_pos h
    have hbase : 0 < N * R * L * h ^ 4 := by positivity
    have height :
        8 * h ^ 4 + 8 * h ≤ 16 * h ^ 4 := by
      have hh4 : h ≤ h ^ 4 := by
        calc
          h = h * 1 ^ 3 := by simp
          _ ≤ h * h ^ 3 := by
            gcongr
            omega
          _ = h ^ 4 := by ring
      omega
    calc
      Fintype.card
          (ExactRailSegmentIndex E hbudget hrecords B (by omega)) ≤
          h * (1 +
            E.finalState.records.length * (8 * h ^ 4 + 8 * h)) :=
        hsegments
      _ ≤ h * (1 + (N * (R * L)) * (16 * h ^ 4)) := by
        gcongr
      _ ≤ h * (17 * (N * R * L * h ^ 4)) := by
        have hone : 1 ≤ N * R * L * h ^ 4 :=
          Nat.succ_le_iff.mpr hbase
        nlinarith
      _ = 17 * N * R * L * h ^ 5 := by ring
  have hRpow : R ≤ 2 ^ R :=
    GridMinorArithmetic.self_le_two_pow R
  have hLpow : L ≤ 2 ^ L :=
    GridMinorArithmetic.self_le_two_pow L
  have hNpow :
      N ≤ 2 ^ (R + 51) * 2 ^ L := by
    simpa [N, R, L, segmentRestartCount_eq] using
      Nat.mul_le_mul_left (2 ^ (R + 51)) hLpow
  have hfive : 17 ≤ 2 ^ 5 := by norm_num
  have hpowers :
      17 * N * R * L * h ^ 5 ≤
        2 ^ 5 * (2 ^ (R + 51) * 2 ^ L) *
          2 ^ R * 2 ^ L * (2 ^ L) ^ 5 := by
    gcongr
  calc
    Fintype.card
        (ExactRailSegmentIndex E hbudget hrecords B (by omega)) ≤
        17 * N * R * L * h ^ 5 := hpoly
    _ ≤
        2 ^ 5 * (2 ^ (R + 51) * 2 ^ L) *
          2 ^ R * 2 ^ L * (2 ^ L) ^ 5 := hpowers
    _ = 2 ^ (56 + 2 * R + 7 * L) := by
      rw [GridMinorArithmetic.two_pow_pow]
      repeat' rw [← pow_add]
      congr 1
      omega
    _ = 2 ^ (56 + 2 * realizedRoundConstant +
          7 * (Nat.log 2 h + 1)) := by
      rfl

/-- Numerical capacity for Karger's cut count on the segment quotient. -/
theorem segmentRestartCount_failure_capacity
    {h a q : ℕ}
    (hheight : 2 ≤ h) (ha : 0 < a)
    (hq :
      q ≤ 2 ^ (56 + 2 * realizedRoundConstant +
        7 * (Nat.log 2 h + 1))) :
    (2 * q ^ (2 * (a + 1))) * 2 ^ (a + 2) ≤
      4 ^ ((a * segmentRestartCount h) / 256 + 1) := by
  let R := realizedRoundConstant
  let L := Nat.log 2 h + 1
  let D := 56 + 2 * R + 7 * L
  let K := 2 ^ (R + 40) * L
  have hR : 0 < R := realizedRoundConstant_pos
  have hL : 2 ≤ L := by
    have := Nat.log_pos (by norm_num : 1 < 2) hheight
    simp [L]
    omega
  have hRpow : R ≤ 2 ^ R :=
    GridMinorArithmetic.self_le_two_pow R
  have hpowPos : 0 < 2 ^ R := by positivity
  have hprodPos : 0 < 2 ^ R * L := Nat.mul_pos hpowPos (by omega)
  have hD :
      D ≤ K := by
    have hc : 55 ≤ 55 * (2 ^ R * L) := by
      exact Nat.mul_le_mul_left 55 (by omega : 1 ≤ 2 ^ R * L)
    have hr :
        2 * R ≤ 2 * (2 ^ R * L) := by
      calc
        2 * R ≤ 2 * 2 ^ R := Nat.mul_le_mul_left 2 hRpow
        _ ≤ 2 * (2 ^ R * L) :=
          Nat.mul_le_mul_left 2 <| by
            calc
              2 ^ R = 2 ^ R * 1 := by simp
              _ ≤ 2 ^ R * L := Nat.mul_le_mul_left _ (by omega)
    have hl :
        7 * L ≤ 7 * (2 ^ R * L) := by
      apply Nat.mul_le_mul_left 7
      calc
        L = 1 * L := by simp
        _ ≤ 2 ^ R * L := Nat.mul_le_mul_right L (by omega)
    calc
      D ≤ 64 * (2 ^ R * L) := by
        dsimp [D]
        omega
      _ ≤ 2 ^ 40 * (2 ^ R * L) := by
        gcongr
        norm_num
      _ = K := by
        dsimp [K]
        rw [pow_add]
        ring
  have hq' : q ≤ 2 ^ D := by
    simpa [D, R, L] using hq
  have hqpow :
      q ^ (2 * (a + 1)) ≤
        (2 ^ D) ^ (2 * (a + 1)) :=
    Nat.pow_le_pow_left hq' _
  have hdiv :
      (a * segmentRestartCount h) / 256 =
        a * (2 ^ (R + 43) * L) := by
    have hcount :
        segmentRestartCount h =
          256 * (2 ^ (R + 43) * L) := by
      rw [segmentRestartCount_eq]
      dsimp [R, L]
      rw [show realizedRoundConstant + 51 =
          8 + (realizedRoundConstant + 43) by omega, pow_add]
      norm_num
      ring
    rw [hcount]
    rw [show a * (256 * (2 ^ (R + 43) * L)) =
        256 * (a * (2 ^ (R + 43) * L)) by ring]
    simp
  have hK :
      2 ^ (R + 43) * L = 8 * K := by
    dsimp [K]
    rw [show R + 43 = 3 + (R + 40) by omega, pow_add]
    norm_num
    ring
  have hDa :
      D * (a + 1) ≤ K * (2 * a) := by
    have ha2 : a + 1 ≤ 2 * a := by omega
    exact
      (Nat.mul_le_mul_right _ hD).trans
        (Nat.mul_le_mul_left K ha2)
  have hexp :
      1 + D * (2 * (a + 1)) + (a + 2) ≤
        2 * (a * (2 ^ (R + 43) * L) + 1) := by
    rw [hK]
    have hKpos : 0 < K := by
      dsimp [K]
      exact Nat.mul_pos (Nat.pow_pos (by norm_num)) (by omega)
    have haK : a ≤ K * a := by
      calc
        a = 1 * a := by simp
        _ ≤ K * a := Nat.mul_le_mul_right a (by omega)
    have hterm :
        D * (2 * (a + 1)) ≤ 4 * (K * a) := by
      calc
        D * (2 * (a + 1)) = 2 * (D * (a + 1)) := by ring
        _ ≤ 2 * (K * (2 * a)) :=
          Nat.mul_le_mul_left 2 hDa
        _ = 4 * (K * a) := by ring
    have hKaPos : 0 < K * a := Nat.mul_pos hKpos ha
    calc
      1 + D * (2 * (a + 1)) + (a + 2) ≤
          1 + 4 * (K * a) + (K * a + 2) := by omega
      _ ≤ 16 * (K * a) + 2 := by omega
      _ = 2 * (a * (8 * K) + 1) := by ring
  calc
    (2 * q ^ (2 * (a + 1))) * 2 ^ (a + 2) ≤
        (2 * (2 ^ D) ^ (2 * (a + 1))) *
          2 ^ (a + 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hqpow)
    _ = 2 ^ (1 + D * (2 * (a + 1)) + (a + 2)) := by
      rw [GridMinorArithmetic.two_pow_pow]
      change
        2 ^ 1 * 2 ^ (D * (2 * (a + 1))) * 2 ^ (a + 2) =
          2 ^ (1 + D * (2 * (a + 1)) + (a + 2))
      rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ (2 * (a * (2 ^ (R + 43) * L) + 1)) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    _ = 4 ^ (a * (2 ^ (R + 43) * L) + 1) := by
      rw [pow_mul]
      norm_num
    _ = 4 ^ ((a * segmentRestartCount h) / 256 + 1) := by
      rw [hdiv]

namespace BuildState.ExpanderBlocks

/-- A canonical segment index, used only as the fallback owner for vertices
outside all red rails. -/
noncomputable def firstExactRailSegment
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hheight : 2 ≤ h)
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B) :
    ExactRailSegmentIndex E hbudget hrecords B hB := by
  let x : Fin h := ⟨0, by omega⟩
  let D := E.exactRailSegmentation hbudget hrecords x B hB
  exact
    ⟨x, ⟨0, List.length_pos_iff.mpr D.segments_nonempty⟩⟩

/-- One physical thinning outcome simultaneously retains a usable `1/256`
fraction of every cut of the Claim 5.4 segment quotient. -/
theorem exists_segment_cut_preserving_outcome
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hheight : 2 ≤ h)
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length) :
    let N := segmentRestartCount h
    let B := 200 * N ^ 4
    let hB : 0 < B :=
      Nat.mul_pos (by norm_num)
        (Nat.pow_pos (segmentRestartCount_pos h))
    let fallback :=
      E.firstExactRailSegment hheight hbudget hrecords B hB
    ∃ outcome :
        BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget),
      ∀ S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB),
        S.Nonempty → S ≠ Finset.univ →
          ((E.segmentQuotient
              hbudget hrecords B hB fallback).boundary S).card / 256 ≤
            E.usableSegmentBoundaryCount
              hbudget hrecords B hB fallback S outcome := by
  classical
  let N := segmentRestartCount h
  let B := 200 * N ^ 4
  have hN : 0 < N := segmentRestartCount_pos h
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by norm_num) (Nat.pow_pos hN)
  let fallback :=
    E.firstExactRailSegment hheight hbudget hrecords B hB
  let H := E.assembledSupport hbudget
  let I := E.blueThinningInput hbudget
  let W := ExactRailSegmentIndex E hbudget hrecords B hB
  let Q := E.segmentQuotient hbudget hrecords B hB fallback
  let Ω := BlueThinningInput.Outcome (H := H)
  let bad : Finset W → Finset Ω :=
    fun S => Finset.univ.filter fun outcome =>
      E.usableSegmentBoundaryCount
          hbudget hrecords B hB fallback S outcome <
        (Q.boundary S).card / 256
  have hconn : Q.IsEdgeConnected N := by
    exact E.segmentQuotient_isEdgeConnected
      hbudget hheight hrecords hN hB fallback
  have htail :
      ∀ S ∈ ThinningUnion.nontrivialCuts,
        (bad S).card *
            4 ^ ((Q.boundary S).card / 256 + 1) ≤
          Fintype.card Ω := by
    intro S _hS
    have hfixed :=
      E.usableSegmentBoundaryCount_bad_mul_failureFactor_le_total
        hbudget hrecords B hB fallback S
    simpa [bad, Q, Ω, E.segmentQuotient_boundary_card] using hfixed
  have hq :
      Fintype.card W ≤
        2 ^ (56 + 2 * realizedRoundConstant +
          7 * (Nat.log 2 h + 1)) := by
    exact segmentIndex_card_le_two_pow E
      hheight hbudget hrecords B (by
        dsimp [B, N]
        have : 0 < segmentRestartCount h := segmentRestartCount_pos h
        nlinarith [(Nat.pow_pos this :
          0 < segmentRestartCount h ^ 4)])
  have hcapacity :
      ∀ a, 0 < a →
        (ThinningUnion.scaleCuts Q N a).card * 2 ^ (a + 2) ≤
          4 ^ ((a * N) / 256 + 1) := by
    intro a ha
    have hscaleSmall :=
      ThinningUnion.card_scaleCuts_le_smallCuts
        (a := a) Q hN
    have hkarger :=
      Karger.card_smallCuts_le_two_mul_vertexCard_pow_all
        Q hN (by omega : 0 < a + 1) hconn
        (by
          have hWtwo : 2 ≤ Fintype.card W := by
            dsimp [W]
            rw [Fintype.card_sigma]
            calc
              2 ≤ h := hheight
              _ = ∑ _x : Fin h, 1 := by simp
              _ ≤
                  ∑ x : Fin h,
                    Fintype.card
                      (Fin
                        (E.exactRailSegmentation
                          hbudget hrecords x B hB).segments.length) := by
                apply Finset.sum_le_sum
                intro x _hx
                simp only [Fintype.card_fin]
                exact List.length_pos_iff.mpr
                  (E.exactRailSegmentation
                    hbudget hrecords x B hB).segments_nonempty
          exact hWtwo)
    have hscale :
        (ThinningUnion.scaleCuts Q N a).card ≤
          2 * (Fintype.card W) ^ (2 * (a + 1)) :=
      hscaleSmall.trans (by simpa [Q, W] using hkarger)
    have hnum :=
      segmentRestartCount_failure_capacity
        hheight ha hq
    simpa [N] using
      (Nat.mul_le_mul_right _ hscale).trans hnum
  obtain ⟨outcome, houtcome⟩ :=
    ThinningUnion.exists_outcome_avoiding_all_cut_badSets
      Q hN (by norm_num : 0 < 256) hconn bad htail hcapacity
  refine ⟨outcome, ?_⟩
  intro S hS hproper
  have hnot := houtcome S hS hproper
  simp [bad, Q] at hnot
  exact hnot

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
