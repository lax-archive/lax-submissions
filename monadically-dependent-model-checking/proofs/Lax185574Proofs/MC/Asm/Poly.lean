import Lax185574Proofs.MC.Asm.PipeTime

/-!
Polynomial estimates of the pipeline time.

Let `M0 = T + |loc q φ| + (q + 1)(1 + q) K + 3` and `γ = aM + aE + aR + 1`
for the degrees of the three callees. Then the cost `mcR` of a round is
at most `C (n + 1)² M0^γ`, and the time bound of `pipe_time` at most a
constant times `(m + 1)(n + 1)² M0^γ` when the input length is at most
`(m + 1)(n + 1) L`. With `T ≤ cT Y^aT` and
`K < Y`, `M0 ≤ C0 Y^(aT + 1)`.
-/

namespace Lax185574Proofs.MC

open Lax185574.WordEncoding

/-- The base of the polynomial bounds. -/
noncomputable def pM0 (T q K : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  T + (toWord (loc q φ)).length + (q + 1) * (1 + q) * K + 3

/-- The degree of the polynomial bounds. -/
def pγ (k : CCst) : ℕ := k.aM + k.aE + k.aR + 1

/-- The constant of `mcR`. -/
noncomputable def pC (cG Ks q : ℕ) (φ : Lax3.FirstOrder.FO 0) (k : CCst) : ℕ :=
  cG * (6 * cG + 8 * (6 + kq q φ) + 7) +
    Ks * (k.cM + k.cE + k.cR + 3 * k.d + 4 * (6 + kq q φ) + 1) + 2

theorem pow_le_M0 {b a M γ : ℕ} (hb : b ≤ M) (ha : a ≤ γ) (hM : 1 ≤ M) : b ^ a ≤ M ^ γ :=
  le_trans (Nat.pow_le_pow_left hb a) (Nat.pow_le_pow_right hM ha)

theorem mcR_le (cG Ks n T q K : ℕ) (φ : Lax3.FirstOrder.FO 0) (k : CCst) :
    mcR cG Ks n T q K φ k ≤ pC cG Ks q φ k * ((n + 1) ^ 2 * pM0 T q K φ ^ pγ k) ∧
    realB n T q K φ k ≤ (k.cM + k.cE + k.cR) * ((n + 1) ^ 2 * pM0 T q K φ ^ pγ k) := by
  set M := pM0 T q K φ with hMd
  set γ := pγ k with hγ
  have hM1 : 1 ≤ M := by simp only [M, pM0]; omega
  have hTM : T + 3 ≤ M := by simp only [M, pM0]; omega
  have hγ1 : 1 ≤ γ := by simp only [γ, pγ]; omega
  have hMγ : M ≤ M ^ γ := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ γ := Nat.pow_le_pow_right hM1 hγ1
  set P1 := M ^ γ with hP1
  set P2 := (n + 1) ^ 2 * P1 with hP2
  have hn2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h12 : P1 ≤ P2 := Nat.le_mul_of_pos_left _ (by omega)
  have h1P : 1 ≤ P1 := Nat.one_le_pow _ _ hM1
  -- the callee bounds
  have hA1 : (T + 3) ^ k.aM ≤ P1 := pow_le_M0 hTM (by simp only [γ, pγ]; omega) hM1
  have hA2 : (T + (toWord (loc q φ)).length + 1) ^ k.aE ≤ P1 :=
    pow_le_M0 (by simp only [M, pM0]; omega) (by simp only [γ, pγ]; omega) hM1
  have hA3 : (T + (q + 1) * (1 + q) * K + 1) ^ k.aR ≤ P1 :=
    pow_le_M0 (by simp only [M, pM0]; omega) (by simp only [γ, pγ]; omega) hM1
  have hrB : realB n T q K φ k ≤ (k.cM + k.cE + k.cR) * P2 := by
    have e1 : k.cM * (n + 1) ^ 2 * (T + 3) ^ k.aM ≤ k.cM * P2 := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hA1)
    have e2 : k.cE * (T + (toWord (loc q φ)).length + 1) ^ k.aE ≤ k.cE * P2 :=
      Nat.mul_le_mul_left _ (le_trans hA2 h12)
    have e3 : k.cR * (n + 1) ^ 2 * (T + (q + 1) * (1 + q) * K + 1) ^ k.aR ≤ k.cR * P2 := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hA3)
    have e : (k.cM + k.cE + k.cR) * P2 = k.cM * P2 + k.cE * P2 + k.cR * P2 := by ring
    simp only [realB]
    omega
  refine ⟨?_, hrB⟩
  -- the head bound and the call bound
  have hH2 : pH2 cG n T ≤ 2 * cG * P2 := by
    have : n * T + (n + 1) ^ 2 ≤ 2 * P2 := by
      have h1 : n * T ≤ (n + 1) ^ 2 * M := by
        calc n * T ≤ (n + 1) ^ 2 * T := Nat.mul_le_mul_right _ (by nlinarith)
          _ ≤ (n + 1) ^ 2 * M := Nat.mul_le_mul_left _ (by omega)
      have h2 : (n + 1) ^ 2 * M ≤ P2 := Nat.mul_le_mul_left _ hMγ
      have h3 : (n + 1) ^ 2 ≤ P2 := Nat.le_mul_of_pos_right _ h1P
      omega
    simp only [pH2]
    calc cG * (n * T + (n + 1) ^ 2) ≤ cG * (2 * P2) := Nat.mul_le_mul_left _ this
      _ = 2 * cG * P2 := by ring
  have hCB : callB n T q φ ≤ 4 * (6 + kq q φ) * P2 := by
    simp only [callB]
    have h1 : T + 6 * (n + 1) + kq q φ ≤ (n + 1) * ((6 + kq q φ) * M) := by
      have haM : (n + 1) * (T + 3) ≤ (n + 1) * M := Nat.mul_le_mul_left _ hTM
      have haT : T ≤ (n + 1) * T := Nat.le_mul_of_pos_left _ (by omega)
      have hcaM : kq q φ ≤ kq q φ * ((n + 1) * M) :=
        Nat.le_mul_of_pos_right _ (Nat.one_le_iff_ne_zero.2 (by positivity))
      have e : (n + 1) * ((6 + kq q φ) * M) = 6 * ((n + 1) * M) + kq q φ * ((n + 1) * M) := by ring
      have e' : (n + 1) * (T + 3) = (n + 1) * T + 3 * (n + 1) := by ring
      omega
    have h2 : 2 * (n + 2) ≤ 4 * (n + 1) := by omega
    calc 2 * (n + 2) * (T + 6 * (n + 1) + kq q φ) ≤ 4 * (n + 1) * ((n + 1) * ((6 + kq q φ) * M)) :=
          Nat.mul_le_mul h2 h1
      _ = 4 * (6 + kq q φ) * ((n + 1) ^ 2 * M) := by ring
      _ ≤ 4 * (6 + kq q φ) * P2 := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hMγ)
  have h1P2 : 1 ≤ P2 := le_trans h1P h12
  simp only [mcR, pC]
  generalize pH2 cG n T = a at hH2
  generalize callB n T q φ = b at hCB
  generalize realB n T q K φ k = r at hrB
  generalize kq q φ = c at hCB ⊢
  have i1 : cG * (3 * a + 2 * b + 7) ≤ cG * ((6 * cG + 8 * (6 + c) + 7) * P2) := by
    refine Nat.mul_le_mul_left _ ?_
    have e : (6 * cG + 8 * (6 + c) + 7) * P2 = 3 * (2 * cG * P2) + 2 * (4 * (6 + c) * P2) + 7 * P2 := by
      ring
    omega
  have i2 : Ks * (r + 3 * k.d + b + 1) ≤
      Ks * ((k.cM + k.cE + k.cR + 3 * k.d + 4 * (6 + c) + 1) * P2) := by
    refine Nat.mul_le_mul_left _ ?_
    have hd : k.d ≤ k.d * P2 := Nat.le_mul_of_pos_right _ h1P2
    have e : (k.cM + k.cE + k.cR + 3 * k.d + 4 * (6 + c) + 1) * P2 =
        (k.cM + k.cE + k.cR) * P2 + 3 * (k.d * P2) + 4 * (6 + c) * P2 + P2 := by ring
    omega
  have e : (cG * (6 * cG + 8 * (6 + c) + 7) +
      Ks * (k.cM + k.cE + k.cR + 3 * k.d + 4 * (6 + c) + 1) + 2) * P2 =
      cG * ((6 * cG + 8 * (6 + c) + 7) * P2) +
        Ks * ((k.cM + k.cE + k.cR + 3 * k.d + 4 * (6 + c) + 1) * P2) + 2 * P2 := by ring
  omega

/-- **The pipeline time is polynomial.** -/
theorem pipe_poly (KL cG Ks n T q K m L Lφ : ℕ) (φ : Lax3.FirstOrder.FO 0) (k : CCst)
    (hL : L ≤ (m + 1) * (n + 1) * Lφ) :
    KL * (2 * cG * L + (m + 2) * mcR cG Ks n T q K φ k + 4) ≤
      KL * (2 * cG * Lφ + 2 * pC cG Ks q φ k + 4) *
        ((m + 1) * ((n + 1) ^ 2 * pM0 T q K φ ^ pγ k)) := by
  refine le_trans (Nat.mul_le_mul_left KL ?_) (le_of_eq (Nat.mul_assoc _ _ _).symm)
  obtain ⟨hA, -⟩ := mcR_le cG Ks n T q K φ k
  set M := pM0 T q K φ ^ pγ k
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by simp only [pM0]; omega)
  have hn1 : n + 1 ≤ (n + 1) ^ 2 := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
  set N := (n + 1) ^ 2
  have i1 : 2 * cG * L ≤ 2 * cG * Lφ * ((m + 1) * (N * M)) := by
    have : L ≤ Lφ * ((m + 1) * (N * M)) := by
      calc L ≤ (m + 1) * (n + 1) * Lφ := hL
        _ ≤ (m + 1) * (N * M) * Lφ := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)
          exact le_trans hn1 (Nat.le_mul_of_pos_right _ hM)
        _ = Lφ * ((m + 1) * (N * M)) := by ring
    calc 2 * cG * L ≤ 2 * cG * (Lφ * ((m + 1) * (N * M))) := Nat.mul_le_mul_left _ this
      _ = 2 * cG * Lφ * ((m + 1) * (N * M)) := by ring
  have i2 : (m + 2) * mcR cG Ks n T q K φ k ≤ 2 * pC cG Ks q φ k * ((m + 1) * (N * M)) := by
    calc (m + 2) * mcR cG Ks n T q K φ k ≤ (2 * (m + 1)) * (pC cG Ks q φ k * (N * M)) :=
          Nat.mul_le_mul (by omega) hA
      _ = 2 * pC cG Ks q φ k * ((m + 1) * (N * M)) := by ring
  have i4 : 4 ≤ 4 * ((m + 1) * (N * M)) := by
    have : 1 ≤ (m + 1) * (N * M) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have e : (2 * cG * Lφ + 2 * pC cG Ks q φ k + 4) * ((m + 1) * (N * M)) =
      2 * cG * Lφ * ((m + 1) * (N * M)) + 2 * pC cG Ks q φ k * ((m + 1) * (N * M)) +
        4 * ((m + 1) * (N * M)) := by ring
  omega

/-- **The base is polynomial in the width.** -/
theorem pM0_le {T q K cT aT : ℕ} (φ : Lax3.FirstOrder.FO 0) (hT : T ≤ cT * (K + 1) ^ aT) :
    pM0 T q K φ ≤ (cT + (toWord (loc q φ)).length + (q + 1) * (1 + q) + 3) * (K + 1) ^ (aT + 1) := by
  have hY : 1 ≤ (K + 1) ^ aT := Nat.one_le_pow _ _ (by omega)
  have e : (K + 1) ^ (aT + 1) = (K + 1) ^ aT * (K + 1) := pow_succ _ _
  rw [e]
  have h1 : T ≤ cT * ((K + 1) ^ aT * (K + 1)) :=
    le_trans hT (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega)))
  have h2 : K + 1 ≤ (K + 1) ^ aT * (K + 1) := Nat.le_mul_of_pos_left _ hY
  generalize (K + 1) ^ aT * (K + 1) = Z at h1 h2 ⊢
  simp only [pM0]
  generalize (toWord (loc q φ)).length = l
  have : (q + 1) * (1 + q) * K ≤ (q + 1) * (1 + q) * Z := Nat.mul_le_mul_left _ (by omega)
  nlinarith

end Lax185574Proofs.MC
