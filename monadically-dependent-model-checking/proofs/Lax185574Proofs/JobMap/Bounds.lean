import Lax185574Proofs.JobMap.Script
import Lax185574Proofs.RamOut
import Lax185574Proofs.RamPipeFwd
import Lax185574Proofs.RamCat
import Lax185574Proofs.LoopGlue
import Lax185574Proofs.LegacyComputing

/-!
Bounds for the composite that runs a program on every job.

`answer_bound`: if a program computes `f u` from the word `u` in the
sense of the hypothesis of `jobMap`, then `f u` is no longer than the
time bound, and its entries are at most twice the sum of the
admissibility bound and the time bound. The answer is the output of a
run at the least word length at which both bounds fit.

`regions`: if `8 (2R + 3)² N ≤ 2^w`, every region of the loop driver up
to round `R` exists and has room for `N`.
-/

namespace Lax185574Proofs.JobMap

open Lax808846.Ram Lax185574.Computing Lax185574Proofs.Words Lax185574Proofs.RamSim
open Lax185574Proofs.RamExec Lax185574Proofs.Simulate Lax185574Proofs.RamCat

/-- The hypothesis of `jobMap` on one job. -/
def JobOK (p : Program) (e c a : ℕ) (f : List ℕ → List ℕ) (u : List ℕ) : Prop :=
  ∀ w, WordAdmissible e c w u → (∀ y t, RunsTo w p u y t → y = f u) ∧
    (c * (u.length + 1) ^ a ≤ 2 ^ w → ∃ t ≤ c * (u.length + 1) ^ a, RunsTo w p u (f u) t)

theorem lt_two_pow_self' (n : ℕ) : n < 2 ^ n := Nat.lt_two_pow_self

/-- **The size of an answer.** -/
theorem answer_bound {p : Program} {e c a : ℕ} {f : List ℕ → List ℕ} {u : List ℕ}
    (h : JobOK p e c a f u) :
    (f u).length ≤ c * (u.length + 1) ^ a ∧
      ∀ y ∈ f u, y ≤ 2 * c * (u.length + maxEntry u + 1) ^ e + 2 * c * (u.length + 1) ^ a := by
  classical
  set A := c * (u.length + maxEntry u + 1) ^ e with hA
  set Tm := c * (u.length + 1) ^ a with hTm
  let Pw : ℕ → Prop := fun w => WordAdmissible e c w u ∧ Tm ≤ 2 ^ w
  have hadm : ∀ w, A ≤ 2 ^ w → WordAdmissible e c w u := by
    intro w hw y hy
    refine le_trans ?_ hw
    have := le_maxEntry hy
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hex : ∃ w, Pw w :=
    ⟨A + Tm, hadm _ (by have := lt_two_pow_self' (A + Tm); omega),
      by have := lt_two_pow_self' (A + Tm); omega⟩
  set w0 := Nat.find hex with hw0
  have hP : Pw w0 := Nat.find_spec hex
  obtain ⟨t, ht, hr⟩ := (h w0 hP.1).2 hP.2
  refine ⟨le_trans (runsTo_out_length hr) ht, fun y hy => ?_⟩
  have hy0 := runsTo_out_lt hr y hy
  rcases Nat.eq_zero_or_pos w0 with h0 | hpos
  · rw [h0] at hy0; omega
  · have hn : ¬ Pw (w0 - 1) := Nat.find_min hex (by omega)
    have h2 : 2 ^ w0 = 2 * 2 ^ (w0 - 1) := by rw [← pow_succ']; congr 1; omega
    have hlt : 2 ^ (w0 - 1) < A + Tm := by
      by_contra hc
      exact hn ⟨hadm _ (by omega), by omega⟩
    have e1 : 2 * c * (u.length + maxEntry u + 1) ^ e = 2 * A := by rw [hA]; ring
    have e2 : 2 * c * (u.length + 1) ^ a = 2 * Tm := by rw [hTm]; ring
    omega

/-- **Room in the regions.** -/
theorem regions {w R N : ℕ} (hN : 1 ≤ N) (h : 8 * (2 * R + 3) ^ 2 * N ≤ 2 ^ w) :
    3 ≤ w ∧ ∀ i ≤ 2 * R + 2, lpSize w i ≠ 0 ∧ N ≤ 2 ^ lpV w i := by
  have h9 : 9 ≤ (2 * R + 3) ^ 2 := by
    have : 3 ≤ 2 * R + 3 := by omega
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ (2 * R + 3) ^ 2 := Nat.pow_le_pow_left this 2
  have hw : 3 ≤ w := by
    by_contra hc
    have : 2 ^ w ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 72 ≤ 8 * (2 * R + 3) ^ 2 * N := by nlinarith
    omega
  refine ⟨hw, fun i hi => lp_room hN ?_⟩
  have h8 := lpCap_eq hw
  have : (i + 1) ^ 2 ≤ (2 * R + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have : (i + 1) ^ 2 * N ≤ (2 * R + 3) ^ 2 * N := Nat.mul_le_mul_right _ this
  nlinarith

theorem lpV_le_cap (w i : ℕ) : 2 ^ lpV w i ≤ lpCap w := by
  simp only [lpV, lpCap]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- A power of two that holds `B · 2^k`. -/
theorem le_pow_sub' {B k v : ℕ} (h : B * 2 ^ k ≤ 2 ^ v) (hB : 1 ≤ B) : k ≤ v ∧ B ≤ 2 ^ (v - k) := by
  have hk : k ≤ v := by
    have : 2 ^ k ≤ 2 ^ v := le_trans (Nat.le_mul_of_pos_left _ hB) h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  refine ⟨hk, ?_⟩
  rw [show 2 ^ v = 2 ^ (v - k) * 2 ^ k by rw [← pow_add]; congr 1; omega] at h
  exact Nat.le_of_mul_le_mul_right h (by positivity)

theorem catLim_eq {w E : ℕ} (h : E ≤ w) : catLim w E = 2 ^ (w - E) - 1 := by
  unfold catLim
  have hw : 2 ^ w = 2 ^ E * 2 ^ (w - E) := by rw [← pow_add]; congr 1; omega
  have hr : 0 < 2 ^ E := by positivity
  have hq : 0 < 2 ^ (w - E) := by positivity
  rw [hw]
  generalize 2 ^ E = A at hr ⊢
  generalize 2 ^ (w - E) = Q at hq ⊢
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm, Nat.mul_sub_one]; omega
  · have : 0 < A * Q := Nat.mul_pos hr hq
    rw [Nat.sub_add_cancel hq, Nat.mul_comm Q A]; omega

end Lax185574Proofs.JobMap
