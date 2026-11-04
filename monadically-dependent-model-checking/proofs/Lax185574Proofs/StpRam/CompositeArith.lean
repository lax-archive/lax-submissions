import Lax185574Proofs.StpRam.Cost
import Lax185574Proofs.LoopGlue

/-!
Arithmetic for the composite of lem:compute-stp: the time of a script
whose middle rounds share one bound (`scriptTime_le`), the time of the
composite as a constant in `k, q` times `(n+1)²(L+1)^(a+1)`
(`time_arith`), and the room of the regions of the driver
(`room_arith`).
-/

namespace Lax185574Proofs.StpRam

open Lax185574Proofs.Simulate Lax185574Proofs.RamSim

theorem scriptTime_le (tG tP : ℕ → ℕ) (Q a b c d : ℕ) (h0 : tG 0 ≤ a)
    (hm : ∀ j, 1 ≤ j → j ≤ Q → tG j ≤ b) (hf : tG (Q + 1) ≤ c) (hp : ∀ j ≤ Q, tP j ≤ d) :
    scriptTime tG tP (Q + 1) 0 ≤ a + Q * b + c + (Q + 1) * (d + 2) + 1 := by
  unfold scriptTime
  rw [← Finset.range_eq_Ico, Finset.sum_range_succ']
  have h1 : ∑ i ∈ Finset.range Q, (tG (i + 1) + tP (i + 1) + 2) ≤ ∑ _i ∈ Finset.range Q, (b + d + 2) :=
    Finset.sum_le_sum fun i hi => by
      have := Finset.mem_range.mp hi
      have := hm (i + 1) (by omega) (by omega)
      have := hp (i + 1) (by omega)
      omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h1
  have h2 := hp 0 (by omega)
  have e : Q * (b + d + 2) = Q * b + Q * (d + 2) := by ring
  have e2 : (Q + 1) * (d + 2) = Q * (d + 2) + (d + 2) := by ring
  omega

/-- The constant of the time of the composite. -/
def tK (k q R1 cM : ℕ) : ℕ :=
  20000 + 7000 * (q + 9) * (q + 9) + 5000 * (q + 1) + 30 * kF k q R1 + (q + 1) * (cM + 2) +
    6 * (R1 + 1) * (q + 1)

set_option maxHeartbeats 2000000 in
theorem time_arith (k q R1 cM n L tw fl sl zl P a b c d Lp : ℕ)
    (hfl : fl ≤ (n + 1) * (L + 1))
    (htw : tw ≤ (q + 1) * (n + 1) * (L + 1)) (hsl : sl ≤ 6 + (fl + n) + tw)
    (hzl : zl ≤ 1 + R1 * (q * n) * (L + 3)) (hLp : 1 ≤ Lp)
    (ha : a ≤ 10 * (winCost n + 9 * (n * (n + 1)) + n * (48 * L + 110) + 100 * (fl + n) + 1030) + 1)
    (hb : b ≤ 10 * (100 * sl + 420) + 1)
    (hc : c ≤ 10 * (readCost n L n tw + finalCost n k q L (q * n) R1 + 20) + 1)
    (hd : d ≤ cM * Lp) (hP : P = (n + 1) * (n + 1) * (L + 1)) :
    a + q * n * b + c + (q * n + 1) * (d + 2) + 1 + zl + 1 ≤ tK k q R1 cM * (P * Lp) := by
  have hF := finalCost_le n k q L R1
  generalize finalCost n k q L (q * n) R1 = Fc at hF hc
  unfold winCost at ha
  unfold readCost dmCost at hc
  have hnn : n * (n + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
  have hnn2 : n * n ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  generalize hU : (n + 1) * (L + 1) = U at *
  have hU1 : n + 1 ≤ U := by rw [← hU]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hUL : L + 1 ≤ U := by rw [← hU]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hPU : P = (n + 1) * U := by rw [hP, ← hU]; ring
  have hnP : (n + 1) * U ≤ P := le_of_eq hPU.symm
  have hUP : U ≤ P := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hnP
  have hP1 : 1 ≤ P := le_trans (by omega) hUP
  have hsq : (n + 1) * (n + 1) ≤ P := le_trans (Nat.mul_le_mul_left _ hU1) hnP
  -- the first round
  have ha' : a ≤ 20000 * P := by
    have h1 : n * (17 * n + 18) ≤ 35 * ((n + 1) * U) := by
      have : n * (17 * n + 18) ≤ 35 * ((n + 1) * (n + 1)) := by nlinarith
      exact le_trans this (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hU1))
    have h2 : n * (48 * L + 110) ≤ 158 * U := by
      rw [← hU]; nlinarith
    omega
  -- the middle rounds
  have hb' : q * n * b ≤ 7000 * (q + 9) * (q + 9) * P := by
    have hsl' : sl ≤ (q + 9) * U := by
      have : (q + 1) * (n + 1) * (L + 1) = (q + 1) * U := by rw [← hU]; ring
      have : (q + 9) * U = (q + 1) * U + 8 * U := by ring
      omega
    have hb2 : b ≤ 7000 * ((q + 9) * U) := by
      have : 1 ≤ (q + 9) * U := Nat.mul_pos (by omega) (by omega)
      omega
    calc q * n * b ≤ ((q + 9) * (n + 1)) * (7000 * ((q + 9) * U)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hb2
      _ = 7000 * (q + 9) * (q + 9) * ((n + 1) * U) := by ring
      _ ≤ 7000 * (q + 9) * (q + 9) * P := Nat.mul_le_mul_left _ hnP
  -- the final round
  have hc' : c ≤ (5000 * (q + 1) + 30 * kF k q R1) * P := by
    have hF' : Fc ≤ 3 * kF k q R1 * P := by
      calc Fc ≤ kF k q R1 * ((n + 1) * U) := hF
        _ ≤ kF k q R1 * (3 * P) := Nat.mul_le_mul_left _ (by omega)
        _ = 3 * kF k q R1 * P := by ring
    have h1 : n * (17 * n + 18) ≤ 35 * ((n + 1) * U) := by
      have : n * (17 * n + 18) ≤ 35 * ((n + 1) * (n + 1)) := by nlinarith
      exact le_trans this (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hU1))
    have h2 : n * (9 * L + 18) ≤ 18 * U := by rw [← hU]; nlinarith
    have h3 : tw ≤ (q + 1) * U := by
      have : (q + 1) * (n + 1) * (L + 1) = (q + 1) * U := by rw [← hU]; ring
      omega
    have h4 : (q + 1) * U ≤ (q + 1) * P := Nat.mul_le_mul_left _ hUP
    have h5 : 1 ≤ (q + 1) * P := Nat.mul_pos (by omega) (by omega)
    have h6 : P ≤ (q + 1) * P := Nat.le_mul_of_pos_left _ (by omega)
    have e : (5000 * (q + 1) + 30 * kF k q R1) * P = 5000 * ((q + 1) * P) + 10 * (3 * kF k q R1 * P) := by
      ring
    omega
  -- the calls
  have hd' : (q * n + 1) * (d + 2) ≤ (q + 1) * (cM + 2) * (P * Lp) := by
    have h1 : d + 2 ≤ (cM + 2) * Lp := by
      have : cM * Lp + 2 ≤ (cM + 2) * Lp := by nlinarith
      omega
    have h2 : q * n + 1 ≤ (q + 1) * P := by
      have : q * n + 1 ≤ (q + 1) * (n + 1) := by nlinarith
      exact le_trans this (Nat.mul_le_mul_left _ (le_trans hU1 hUP))
    calc (q * n + 1) * (d + 2) ≤ ((q + 1) * P) * ((cM + 2) * Lp) := Nat.mul_le_mul h2 h1
      _ = (q + 1) * (cM + 2) * (P * Lp) := by ring
  -- the output
  have hz' : zl + 1 + 1 ≤ 6 * (R1 + 1) * (q + 1) * P := by
    have h1 : R1 * (q * n) * (L + 3) ≤ 3 * ((R1 + 1) * (q + 1) * P) := by
      have : q * n * (L + 3) ≤ (q + 1) * (3 * P) := by
        have : q * n * (L + 3) ≤ (q + 1) * (3 * ((n + 1) * (L + 1))) := by nlinarith
        rw [hU] at this
        exact le_trans this (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hUP))
      calc R1 * (q * n) * (L + 3) = R1 * (q * n * (L + 3)) := by ring
        _ ≤ (R1 + 1) * ((q + 1) * (3 * P)) := Nat.mul_le_mul (by omega) this
        _ = 3 * ((R1 + 1) * (q + 1) * P) := by ring
    have : 1 ≤ (R1 + 1) * (q + 1) * P := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have e : 6 * (R1 + 1) * (q + 1) * P = 6 * ((R1 + 1) * (q + 1) * P) := by ring
    omega
  -- together
  have hPL : P ≤ P * Lp := Nat.le_mul_of_pos_right _ hLp
  unfold tK
  have e : (20000 + 7000 * (q + 9) * (q + 9) + 5000 * (q + 1) + 30 * kF k q R1 + (q + 1) * (cM + 2) +
      6 * (R1 + 1) * (q + 1)) * (P * Lp) =
      (20000 * P + 7000 * (q + 9) * (q + 9) * P + (5000 * (q + 1) + 30 * kF k q R1) * P +
        6 * (R1 + 1) * (q + 1) * P) * Lp + (q + 1) * (cM + 2) * (P * Lp) := by ring
  rw [e]
  have : 20000 * P + 7000 * (q + 9) * (q + 9) * P + (5000 * (q + 1) + 30 * kF k q R1) * P +
      6 * (R1 + 1) * (q + 1) * P ≤ (20000 * P + 7000 * (q + 9) * (q + 9) * P +
        (5000 * (q + 1) + 30 * kF k q R1) * P + 6 * (R1 + 1) * (q + 1) * P) * Lp :=
    Nat.le_mul_of_pos_right _ hLp
  omega

theorem room_arith {X C w e : ℕ} (hX : 1 ≤ X) (he : 7 ≤ e) (Y : ℕ) (hY : 8 * (36 * Y) ≤ 2 ^ 22)
    (hC : 1 ≤ C) (h : 2 ^ 22 * C * X ^ e ≤ 2 ^ w) {Q j : ℕ} (hQ : Q ≤ X ^ 2) (hj : j ≤ Q + 1) (m : ℕ)
    (hm : m ≤ 2 * j + 2) : m ^ 2 * (Y * C * X ^ (e - 4)) ≤ lpCap w ∧ 8 ≤ w := by
  have hX4 : m ≤ 6 * X ^ 2 := by
    have : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hm2 : m ^ 2 ≤ 36 * X ^ 4 := by
    calc m ^ 2 ≤ (6 * X ^ 2) ^ 2 := Nat.pow_le_pow_left hX4 2
      _ = 36 * X ^ 4 := by ring
  have hXe : X ^ 4 * X ^ (e - 4) = X ^ e := by rw [← pow_add]; congr 1; omega
  have h1 : m ^ 2 * (Y * C * X ^ (e - 4)) ≤ 36 * Y * C * X ^ e := by
    calc m ^ 2 * (Y * C * X ^ (e - 4)) ≤ 36 * X ^ 4 * (Y * C * X ^ (e - 4)) := Nat.mul_le_mul_right _ hm2
      _ = 36 * Y * C * (X ^ 4 * X ^ (e - 4)) := by ring
      _ = 36 * Y * C * X ^ e := by rw [hXe]
  have h2 : 8 * (36 * Y * C * X ^ e) ≤ 2 ^ 22 * C * X ^ e := by
    calc 8 * (36 * Y * C * X ^ e) = 8 * (36 * Y) * (C * X ^ e) := by ring
      _ ≤ 2 ^ 22 * (C * X ^ e) := Nat.mul_le_mul_right _ hY
      _ = 2 ^ 22 * C * X ^ e := by ring
  have hXe1 : 1 ≤ X ^ e := Nat.one_le_pow _ _ (by omega)
  have h3 : 2 ^ 22 ≤ 2 ^ w := le_trans (le_trans (Nat.le_mul_of_pos_right _ hC)
    (Nat.le_mul_of_pos_right _ hXe1)) h
  have hw : 22 ≤ w := (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
  have h4 := lpCap_eq (w := w) (by omega)
  exact ⟨by omega, by omega⟩

end Lax185574Proofs.StpRam
