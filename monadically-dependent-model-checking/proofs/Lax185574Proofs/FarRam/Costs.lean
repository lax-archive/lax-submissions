import Lax185574Proofs.FarRam.Sizes


/-!
The costs of the rounds of the far-tree program, bounded by
`K · (‖σ‖ + 1) · (‖τ‖ + 4)²` with `K` depending on the rank only.
-/

namespace Lax185574Proofs.FarRam

open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.Words

section Costs

variable (X : List ℕ) (P L : ℕ) (hX : X.length ≤ P) (hP : 4 ≤ P) (ℓ : ℕ) (hℓ : ℓ ≤ L)
include hX hP hℓ

theorem canonCost_le : canonCost X ℓ ≤ 120 * (L + 1) ^ 2 * P := by
  unfold canonCost
  have h1 : 70 * X.length + 140 ≤ 105 * P := by omega
  have h2 : ℓ * (70 * X.length + 140) + 40 ≤ (L + 1) * (115 * P) := by
    have := Nat.mul_le_mul hℓ h1; nlinarith
  have h3 : ℓ * (ℓ * (70 * X.length + 140) + 40) ≤ (L + 1) * ((L + 1) * (115 * P)) :=
    Nat.mul_le_mul (by omega) h2
  nlinarith

theorem badCost_le : badCost X ℓ ≤ 120 * (L + 1) ^ 2 * P := by
  unfold badCost
  have h1 : 70 * X.length + 150 ≤ 108 * P := by omega
  have h2 : ℓ * (70 * X.length + 150) + 30 ≤ (L + 1) * (116 * P) := by
    have := Nat.mul_le_mul hℓ h1; nlinarith
  have h3 : ℓ * (ℓ * (70 * X.length + 150) + 30) ≤ (L + 1) * ((L + 1) * (116 * P)) :=
    Nat.mul_le_mul (by omega) h2
  nlinarith

theorem radCost_le (E U : ℕ) :
    radCost X ℓ E U ≤ (20 * E + 20 * L + 100 + 300 * (L + 1) ^ 2 * (U + 2)) * P := by
  unfold radCost
  have hc := canonCost_le X P L hX hP ℓ hℓ
  have hb := badCost_le X P L hX hP ℓ hℓ
  generalize hA : (L + 1) ^ 2 = A at hc hb ⊢
  have hA1 : 1 ≤ A := by rw [← hA]; exact Nat.one_le_pow _ _ (by omega)
  have h1 : (canonCost X ℓ + badCost X ℓ + 60) * (U + 1) ≤ (240 * A * P + 60) * (U + 1) :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have hAP : 1 ≤ A * P := by nlinarith
  have h60 : 60 * (U + 1) ≤ 60 * (A * P) * (U + 1) := by nlinarith
  have h2 : (240 * A * P + 60) * (U + 1) + 120 * A * P ≤ 300 * A * (U + 2) * P := by
    have e1 : (240 * A * P + 60) * (U + 1) + 120 * A * P = 240 * (A * P) * (U + 1) + 60 * (U + 1) + 120 * (A * P) := by ring
    have e2 : 300 * A * (U + 2) * P = 300 * (A * P) * (U + 1) + 300 * (A * P) := by ring
    rw [e1, e2]; nlinarith
  have h3 : 20 * E + 20 * ℓ + 100 ≤ (20 * E + 20 * L + 100) * P := by nlinarith
  nlinarith

theorem extCost_le (R : ℕ) (hR : R ≤ P) : extCost X ℓ R ≤ 200 * (L + 1) * P ^ 2 := by
  unfold extCost extBodyCost extInnerCost
  have h1 : ℓ * (70 * X.length + 140) ≤ (L + 1) * (105 * P) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : R * (ℓ * (70 * X.length + 140) + 6 + 40 + 10) ≤ P * ((L + 1) * (105 * P) + 56) :=
    Nat.mul_le_mul hR (by omega)
  nlinarith

end Costs

theorem sum_le_linear (f : ℕ → ℕ) (a c n : ℕ) (g : ℕ → ℕ) (h : ∀ i, f i ≤ a * g i + c) :
    ∑ i ∈ Finset.range n, f i ≤ a * ∑ i ∈ Finset.range n, g i + c * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ]; have := h n; nlinarith

theorem scanCost_le (W : List (List ℕ)) (ℓ R nS P L Nσ : ℕ) (hℓ : ℓ ≤ L) (hR : R ≤ P) (hP : 4 ≤ P)
    (hn : nS ≤ W.length) (htot : total (W.take nS) ≤ Nσ) (hnS : nS ≤ Nσ) :
    scanCost W ℓ R nS ≤ 600 * (L + 1) ^ 2 * P * (Nσ + 1) := by
  unfold scanCost selCost eqCost cntCost blkCost mbCost
  have hcnt : ℓ * (R * (ℓ * (30 + 20) + 20 + 20) + 30) + 10 ≤ 100 * (L + 1) ^ 2 * P := by
    have h1 : R * (ℓ * (30 + 20) + 20 + 20) ≤ P * (50 * (L + 1)) := Nat.mul_le_mul hR (by omega)
    have h2 : ℓ * (R * (ℓ * (30 + 20) + 20 + 20) + 30) ≤ (L + 1) * (P * (50 * (L + 1)) + 30) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hs := sum_le_linear (fun i => R * (36 * (wd W i).length + 120 + 10) + 10 + (R * 40 + 10) +
    (ℓ * (R * (ℓ * (30 + 20) + 20 + 20) + 30) + 10) + 160 + 8) (36 * R)
    (R * 170 + 100 * (L + 1) ^ 2 * P + 188) nS (fun i => (wd W i).length) (fun i => by nlinarith)
  have hsum := sum_wd_length W nS hn
  rw [hsum] at hs
  have h1 : 36 * R * total (W.take nS) ≤ 36 * P * Nσ := Nat.mul_le_mul (by omega) htot
  have h2 : (R * 170 + 100 * (L + 1) ^ 2 * P + 188) * nS ≤ (R * 170 + 100 * (L + 1) ^ 2 * P + 188) * Nσ :=
    Nat.mul_le_mul_left _ hnS
  generalize hA : (L + 1) ^ 2 = A at h2 hs ⊢
  have hA1 : 1 ≤ A := by rw [← hA]; exact Nat.one_le_pow _ _ (by omega)
  have hPA : P ≤ A * P := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : (R * 170 + 100 * A * P + 188) * Nσ ≤ (400 * (A * P)) * Nσ := Nat.mul_le_mul_right _ (by
    have : 100 * A * P = 100 * (A * P) := by ring
    omega)
  have h5 : 36 * P * Nσ ≤ 100 * (A * P) * Nσ := Nat.mul_le_mul_right _ (by omega)
  have e : 600 * A * P * (Nσ + 1) = 400 * (A * P) * Nσ + 100 * (A * P) * Nσ + 100 * (A * P) * Nσ +
    600 * (A * P) := by ring
  have e2 : 36 * R * total (List.take nS W) ≤ 36 * P * Nσ := h1
  rw [e]
  have : 6 ≤ 600 * (A * P) := by omega
  omega

theorem outCost_le (W : List (List ℕ)) (nS Nσ : ℕ) (hn : nS ≤ W.length) (htot : total (W.take nS) ≤ Nσ)
    (hnS : nS ≤ Nσ) : outCost W nS ≤ 110 * (Nσ + 1) := by
  unfold outCost
  have hs := sum_le_linear (fun i => 13 * (wd W i).length + 48) 13 48 nS (fun i => (wd W i).length)
    (fun i => le_rfl)
  rw [sum_wd_length W nS hn] at hs
  omega

open Lax3.DistFO (rhoMinus) in
/-- The constant of the last round. -/
def finK (k q : ℕ) : ℕ :=
  20 * ((k + (q + 1) + 1) * q) + 20 * k + 2000 + 300 * (k + 1) ^ 2 * (9 ^ k * rhoMinus (k + 1) q + 2) +
    1000 * (k + 1) ^ 2

theorem callRound_le {q ℓ : ℕ} (t : Node (q + 1) ℓ) (W : List (List ℕ)) (j Nσ : ℕ)
    (hW : W.length + total W ≤ Nσ + j * ((toWord t).length + 4)) (hj : j ≤ (toWord t).length) :
    headCost t + preCost W (toWord t) + callCost W (toWord t) j + 10 ≤
      800 * (Nσ + 1) * ((toWord t).length + 4) ^ 2 := by
  unfold headCost preCost callCost
  have hl := length_toWord_words W
  set P := (toWord t).length + 4 with hPdef
  have hjP : j * P ≤ P * P := Nat.mul_le_mul (by omega) le_rfl
  have hP1 : P ≤ P * P := Nat.le_mul_of_pos_left _ (by omega)
  have hP16 : 16 ≤ P * P := Nat.mul_le_mul (show 4 ≤ P by omega) (show 4 ≤ P by omega)
  have hZ : 800 * (Nσ + 1) * P ^ 2 = 800 * (Nσ * (P * P)) + 800 * (P * P) := by ring
  have hN : Nσ ≤ Nσ * (P * P) := Nat.le_mul_of_pos_right _ (by omega)
  rw [hZ]
  omega

theorem finalRound_le {q ℓ : ℕ} (t : Node (q + 1) ℓ) (k : ℕ) (W : List (List ℕ)) (nS Nσ : ℕ)
    (hℓk : ℓ ≤ k) (hn : nS ≤ W.length) (htot : total (W.take nS) ≤ Nσ) (hnS : nS ≤ Nσ)
    (hW : W.length + total W ≤ Nσ + (toWord t).length * ((toWord t).length + 4))
    (hR : (Node.exts t).words.length ≤ (toWord t).length) :
    headCost t + preCost W (toWord t) + finalCost (toWord t) W k q ℓ nS (Node.exts t).words.length + 10 ≤
      finK k q * (Nσ + 1) * ((toWord t).length + 4) ^ 2 := by
  have hc1 := callRound_le t W (toWord t).length Nσ hW le_rfl
  unfold callCost at hc1
  have hX : (toWord t).length ≤ (toWord t).length + 4 := by omega
  have hrad := radCost_le (toWord t) _ k hX (by omega) ℓ hℓk ((k + (q + 1) + 1) * q)
    (9 ^ (ℓ - 1) * Lax3.DistFO.rhoMinus (k + 1) q)
  have hU : 9 ^ (ℓ - 1) * Lax3.DistFO.rhoMinus (k + 1) q ≤ 9 ^ k * Lax3.DistFO.rhoMinus (k + 1) q :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hext := extCost_le (toWord t) _ k hX (by omega) ℓ hℓk _ (show (Node.exts t).words.length ≤
    (toWord t).length + 4 by omega)
  have hscan := scanCost_le W ℓ (Node.exts t).words.length nS ((toWord t).length + 4) k Nσ hℓk (by omega)
    (by omega) hn htot hnS
  have hout := outCost_le W nS Nσ hn htot hnS
  have hkA : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hfin : finK k q * (Nσ + 1) * ((toWord t).length + 4) ^ 2 =
      (20 * ((k + (q + 1) + 1) * q) + 20 * k + 2000 +
        300 * (k + 1) ^ 2 * (9 ^ k * Lax3.DistFO.rhoMinus (k + 1) q + 2) + 1000 * (k + 1) ^ 2) *
      ((Nσ + 1) * ((toWord t).length + 4) ^ 2) := by unfold finK; ring
  unfold finalCost
  rw [hfin]
  generalize hPe : (toWord t).length + 4 = P at *
  generalize 9 ^ (ℓ - 1) * Lax3.DistFO.rhoMinus (k + 1) q = U at *
  generalize 9 ^ k * Lax3.DistFO.rhoMinus (k + 1) q = Uk at *
  generalize (k + (q + 1) + 1) * q = E at *
  generalize (k + 1) ^ 2 = A at *
  generalize radCost (toWord t) ℓ E U = rc at *
  generalize extCost (toWord t) ℓ (Node.exts t).words.length = ec at *
  generalize scanCost W ℓ (Node.exts t).words.length nS = sc at *
  generalize outCost W nS = oc at *
  have hA1 : 1 ≤ A := by omega
  have hP4 : 4 ≤ P := by omega
  have hPP : P ≤ P ^ 2 := by nlinarith
  have hZP : P ≤ (Nσ + 1) * P ^ 2 := le_trans hPP (Nat.le_mul_of_pos_left _ (by omega))
  have hZP2 : P ^ 2 ≤ (Nσ + 1) * P ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  have hZN : P * (Nσ + 1) ≤ (Nσ + 1) * P ^ 2 := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hPP
  generalize hZd : (Nσ + 1) * P ^ 2 = Z at *
  have h1 : (20 * E + 20 * k + 100 + 300 * A * (U + 2)) * P ≤
      (20 * E + 20 * k + 100 + 300 * A * (Uk + 2)) * Z :=
    Nat.mul_le_mul (by have := Nat.mul_le_mul_left (300 * A) (show U + 2 ≤ Uk + 2 by omega); omega) hZP
  have h2 : 200 * (k + 1) * P ^ 2 ≤ 200 * (A * Z) := by
    have := Nat.mul_le_mul hkA hZP2
    calc 200 * (k + 1) * P ^ 2 = 200 * ((k + 1) * P ^ 2) := by ring
      _ ≤ 200 * (A * Z) := Nat.mul_le_mul_left _ this
  have h3 : 600 * A * P * (Nσ + 1) ≤ 600 * (A * Z) := by
    calc 600 * A * P * (Nσ + 1) = 600 * (A * (P * (Nσ + 1))) := by ring
      _ ≤ 600 * (A * Z) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hZN)
  have hZ1 : 1 ≤ Z := le_trans (by omega) hZP
  have h4 : 110 * (Nσ + 1) ≤ 110 * Z := by
    have : Nσ + 1 ≤ Z := by rw [← hZd]; exact Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have h5 : 800 * (Nσ + 1) * P ^ 2 = 800 * Z := by rw [← hZd]; ring
  have hAZ : Z ≤ A * Z := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : (20 * E + 20 * k + 2000 + 300 * A * (Uk + 2) + 1000 * A) * Z =
      (20 * E + 20 * k + 100 + 300 * A * (Uk + 2)) * Z + 1900 * Z + 1000 * (A * Z) := by ring
  rw [e1]
  omega

end Lax185574Proofs.FarRam
