import Lax17Proofs.Source.TreewidthSparsifierTheorem33
import Lax17Proofs.Source.TreewidthSparsifierTheorem34
import Lax17Proofs.Source.TreewidthSparsifierTheorem51
import Lax17Proofs.Source.DegreeThreeStrongPathOfSetsContract

namespace Lax17Proofs

universe u v w

/-!
# Degree-three treewidth sparsifier: Theorem 1.1

This module composes the proved local forms of Theorems 3.3, 3.4, and 5.1
from Chekuri--Chuzhoy, *Degree-3 Treewidth Sparsifiers*.  Unlike the historical
contract-backed declaration, the result below uses none of the three semantic
paper axioms.
-/

namespace SimpleGraph
namespace TreewidthSparsifier


set_option maxHeartbeats 2000000

/-- The threshold form of Theorem 1.1, obtained from the proved local strong
path-of-sets construction and the proved unit-numerator treewidth bound. -/
theorem degreeThreeTreewidthSparsifierThreshold_proved :
    ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {k t : ℕ},
          1 < k →
            k ≤ treewidth G →
              cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                ∃ H : _root_.SimpleGraph V,
                  H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H := by
  rcases theorem34_localStrongPathOfSets_from_treewidth with
    ⟨cPath, cPathLog, hcPath, hcPathLog, hpath⟩
  rcases
      Theorem51.theorem51_degree3_wellLinked_subgraph_from_localStrongPathOfSets
      with
    ⟨cWidth, cWidthLog, cAlpha, cAlphaLog,
      hcWidth, hcWidthLog, hcAlpha, hcAlphaLog, hminor⟩
  rcases exists_theorem33_unit_treewidth_of_scaledWellLinked with
    ⟨cTw, hcTw, htw⟩
  let cHeight := 2 * cTw * 3 * cAlpha
  let cLen := cWidth + 2
  let cSparse := cPath * cHeight * cLen ^ 50
  let cSparseLog := cAlphaLog + cWidthLog * 50 + cPathLog
  refine ⟨cSparse, cSparseLog, ?_, ?_, ?_⟩
  · dsimp [cSparse, cHeight, cLen]
    positivity
  · dsimp [cSparseLog]
    positivity
  intro V _ _ G k t hk hGtw hlarge
  classical
  by_cases htzero : t = 0
  · subst t
    refine ⟨⊥, bot_le, ?_, by simp⟩
    intro v
    refine ⟨∅, ?_, by simp⟩
    intro u
    simp
  · let L := Nat.log 2 k
    let height := cHeight * t * L ^ cAlphaLog
    let width := cLen * L ^ cWidthLog
    have htpos : 0 < t := Nat.pos_of_ne_zero htzero
    have hLpos : 0 < L := by
      simpa [L] using
        Nat.log_pos (by decide : 1 < 2) (Nat.succ_le_of_lt hk)
    have hcHeight_pos : 0 < cHeight := by
      dsimp [cHeight]
      positivity
    have hcLen_pos : 0 < cLen := by
      dsimp [cLen]
      omega
    have hheight_gt_one : 1 < height := by
      have hrest :
          0 < cTw * 3 * cAlpha * t * L ^ cAlphaLog := by
        positivity
      have hrest_one :
          1 ≤ cTw * 3 * cAlpha * t * L ^ cAlphaLog :=
        Nat.succ_le_of_lt hrest
      dsimp [height, cHeight]
      calc
        1 < 2 := by norm_num
        _ = 2 * 1 := by norm_num
        _ ≤ 2 * (cTw * 3 * cAlpha * t * L ^ cAlphaLog) :=
          Nat.mul_le_mul_left 2 hrest_one
        _ = 2 * cTw * 3 * cAlpha * t * L ^ cAlphaLog := by ring
    have hwidth_gt_one : 1 < width := by
      have hpow_pos : 0 < L ^ cWidthLog := Nat.pow_pos hLpos
      have hcLen_three : 3 ≤ cLen := by
        dsimp [cLen]
        omega
      calc
        1 < 3 * 1 := by norm_num
        _ ≤ cLen * L ^ cWidthLog :=
          Nat.mul_le_mul hcLen_three (Nat.succ_le_of_lt hpow_pos)
    have hheight_even : Even height := by
      refine ⟨cTw * 3 * cAlpha * t * L ^ cAlphaLog, ?_⟩
      dsimp [height, cHeight]
      ring
    have hSparseLog_ge_alpha : cAlphaLog ≤ cSparseLog := by
      dsimp [cSparseLog]
      omega
    have hpow_alpha_le_sparse :
        L ^ cAlphaLog ≤ L ^ cSparseLog :=
      Nat.pow_le_pow_right hLpos hSparseLog_ge_alpha
    have hcoef_height_le_sparse :
        cHeight * t ≤ cSparse * t := by
      have hfactor_pos : 0 < cPath * cLen ^ 50 :=
        Nat.mul_pos hcPath (Nat.pow_pos hcLen_pos)
      have hfactor_one : 1 ≤ cPath * cLen ^ 50 :=
        Nat.succ_le_of_lt hfactor_pos
      calc
        cHeight * t = (cHeight * 1) * t := by ring
        _ ≤ (cHeight * (cPath * cLen ^ 50)) * t :=
          Nat.mul_le_mul_right t
            (Nat.mul_le_mul_left cHeight hfactor_one)
        _ = cSparse * t := by
          dsimp [cSparse]
          ring
    have hheight_le_sparse :
        height ≤ cSparse * t * L ^ cSparseLog := by
      dsimp [height]
      exact Nat.mul_le_mul hcoef_height_le_sparse hpow_alpha_le_sparse
    have hheight_le_k : height ≤ k :=
      hheight_le_sparse.trans
        (Nat.le_of_lt (by simpa [L, cSparseLog] using hlarge))
    have hlog_height_le : Nat.log 2 height ≤ L := by
      simpa [L] using Nat.log_mono_right hheight_le_k
    have hwidth_req :
        cWidth * (Nat.log 2 height) ^ cWidthLog ≤ width := by
      have hpow :
          (Nat.log 2 height) ^ cWidthLog ≤ L ^ cWidthLog :=
        Nat.pow_le_pow_left hlog_height_le cWidthLog
      calc
        cWidth * (Nat.log 2 height) ^ cWidthLog
            ≤ cWidth * L ^ cWidthLog :=
          Nat.mul_le_mul_left cWidth hpow
        _ ≤ cLen * L ^ cWidthLog := by
          exact Nat.mul_le_mul_right (L ^ cWidthLog)
            (by dsimp [cLen]; omega)
        _ = width := by rfl
    have hpath_le_sparse :
        cPath * height * width ^ 50 * L ^ cPathLog ≤
          cSparse * t * L ^ cSparseLog := by
      dsimp [height, width, cSparse, cSparseLog]
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_add, Nat.pow_add]
      ring_nf
      exact le_rfl
    have hpath_large :
        cPath * height * width ^ 50 * L ^ cPathLog < k :=
      lt_of_le_of_lt hpath_le_sparse
        (by simpa [L, cSparseLog] using hlarge)
    rcases hpath G (k := k) (height := height) (width := width)
        hk hheight_gt_one hwidth_gt_one hGtw hpath_large with
      ⟨P⟩
    rcases hminor P hheight_gt_one hheight_even hwidth_req with
      ⟨H, hHG, hdegree, hwell⟩
    refine ⟨H, hHG, hdegree, ?_⟩
    have hlog_height_pos : 0 < Nat.log 2 height := by
      exact Nat.log_pos (by decide : 1 < 2)
        (Nat.succ_le_of_lt hheight_gt_one)
    have halphaDen_pos :
        0 < cAlpha * (Nat.log 2 height) ^ cAlphaLog := by
      positivity
    have hpow_alpha_height :
        (Nat.log 2 height) ^ cAlphaLog ≤ L ^ cAlphaLog :=
      Nat.pow_le_pow_left hlog_height_le cAlphaLog
    have htw_condition :
        cTw * 3 *
            (cAlpha * (Nat.log 2 height) ^ cAlphaLog) * t ≤
          (P.left P.firstIndex).card := by
      calc
        cTw * 3 *
              (cAlpha * (Nat.log 2 height) ^ cAlphaLog) * t ≤
            cTw * 3 * (cAlpha * L ^ cAlphaLog) * t := by
          exact Nat.mul_le_mul_right t
            (Nat.mul_le_mul_left (cTw * 3)
              (Nat.mul_le_mul_left cAlpha hpow_alpha_height))
        _ = cTw * 3 * cAlpha * t * L ^ cAlphaLog := by ring
        _ ≤ 2 * (cTw * 3 * cAlpha * t * L ^ cAlphaLog) := by
          exact Nat.le_mul_of_pos_left _
            (by decide : 0 < 2)
        _ = height := by
          dsimp [height, cHeight]
          ring
        _ = (P.left P.firstIndex).card := by
          symm
          exact P.left_card P.firstIndex
    exact htw H (P.left P.firstIndex) hdegree hwell
      (by decide : 0 < 3) halphaDen_pos htw_condition

end TreewidthSparsifier

namespace DegreeThreeStrongPathOfSetsContract


/-- A same-vertex threshold sparsifier implies the paper-shaped Omega form.
The proof uses the same division-safe rounding as the topological-minor
conversion, but returns the threshold subgraph directly. -/
private theorem degreeThreeTreewidthSparsifierOmega_of_threshold_proved
    {cSparse cSparseLog : ℕ} (hcSparse : 0 < cSparse)
    (hthreshold :
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {k t : ℕ},
          1 < k →
            k ≤ treewidth G →
              cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                ∃ H : _root_.SimpleGraph V,
                  H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H) :
    DegreeThreeTreewidthSparsifierOmega.{u}
      (2 * cSparse) cSparseLog := by
  intro V _ _ G k hk hGtw
  let L := Nat.log 2 k
  let F := cSparse * L ^ cSparseLog
  have hLpos : 0 < L := by
    simpa [L] using
      Nat.log_pos (by decide : 1 < 2) (Nat.succ_le_of_lt hk)
  have hFpos : 0 < F := by
    dsimp [F]
    positivity
  by_cases hsmall : k ≤ 2 * F
  · have htwLarge : 1 < treewidth G := hk.trans_le hGtw
    rcases exists_subgraph_maxDegreeAtMost_three_treewidth_pos htwLarge with
      ⟨H, hHG, hdegree, hHtw⟩
    refine ⟨H, hHG, hdegree, ?_⟩
    calc
      k ≤ 2 * F := hsmall
      _ ≤ 2 * F * treewidth H :=
        Nat.le_mul_of_pos_right (2 * F) hHtw
      _ = (2 * cSparse) * treewidth H * L ^ cSparseLog := by
        dsimp [F]
        ring
      _ = (2 * cSparse) * treewidth H *
          (Nat.log 2 k) ^ cSparseLog := by rfl
  · have hlarge : 2 * F < k := Nat.lt_of_not_ge hsmall
    let t := k / (2 * F) + 1
    have htwCondition :
        cSparse * t * (Nat.log 2 k) ^ cSparseLog < k := by
      have hquotient :
          2 * (F * (k / (2 * F))) ≤ k := by
        calc
          2 * (F * (k / (2 * F))) =
              k / (2 * F) * (2 * F) := by ring
          _ ≤ k := Nat.div_mul_le_self k (2 * F)
      have hFt : F * t < k := by
        dsimp [t]
        rw [Nat.mul_add]
        omega
      calc
        cSparse * t * (Nat.log 2 k) ^ cSparseLog = F * t := by
          dsimp [F, L]
          ring
        _ < k := hFt
    rcases hthreshold G hk hGtw htwCondition with
      ⟨H, hHG, hdegree, hHtw⟩
    refine ⟨H, hHG, hdegree, ?_⟩
    have hdenom : 0 < 2 * F := by positivity
    calc
      k ≤ 2 * F * t := by
        exact Nat.le_of_lt (by
          simpa [t] using Nat.lt_mul_div_succ k hdenom)
      _ ≤ 2 * F * treewidth H :=
        Nat.mul_le_mul_left (2 * F) hHtw
      _ = (2 * cSparse) * treewidth H * L ^ cSparseLog := by
        dsimp [F]
        ring
      _ = (2 * cSparse) * treewidth H *
          (Nat.log 2 k) ^ cSparseLog := by rfl

/-- Work package 2 endpoint: the semantic degree-three treewidth sparsifier
with no project-specific axiom in its theorem closure. -/
theorem degreeThreeTreewidthSparsifierOmega_proved :
    ∃ cSparse cSparseLog : ℕ,
      0 < cSparse ∧ 0 < cSparseLog ∧
        DegreeThreeTreewidthSparsifierOmega.{u}
          cSparse cSparseLog := by
  rcases
      TreewidthSparsifier.degreeThreeTreewidthSparsifierThreshold_proved.{u}
      with
    ⟨cSparse, cSparseLog, hcSparse, hcSparseLog, hthreshold⟩
  exact ⟨2 * cSparse, cSparseLog, by positivity, hcSparseLog,
    degreeThreeTreewidthSparsifierOmega_of_threshold_proved
      hcSparse hthreshold⟩

end DegreeThreeStrongPathOfSetsContract
end SimpleGraph

end Lax17Proofs
