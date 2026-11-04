import Lax185574Proofs.StpRam.FinalRead

/-!
The cost of the final round of lem:compute-stp, as a constant in `k, q`
times `(n + 1)² (L + 1)`.
-/

namespace Lax185574Proofs.StpRam

/-- The constant of the final round. -/
def kF (k q R1 : ℕ) : ℕ :=
  2000 * ((q + 1) * (R1 + 1) ^ 2 * (k + q + 2)) + ((q + 1) * (13 * radExp k q 0 + 50) + 100)

theorem innerCost_le (n R1 L c : ℕ) :
    innerCost n L c ≤ 1000 * (R1 + 1) * (c + 1) * ((n + 1) * (L + 1)) := by
  unfold innerCost greedyCost rmCost
  generalize hW : (n + 1) * (L + 1) = W
  have hnW : n + 1 ≤ W := by rw [← hW]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hLW : L + 1 ≤ W := by rw [← hW]; exact Nat.le_mul_of_pos_left _ (by omega)
  have a1 : (36 * L + 130) * n ≤ 166 * W := by rw [← hW]; nlinarith
  have a2 : (32 * n + 6 + 16 * n + 20) * c ≤ 74 * W * c := Nat.mul_le_mul_right _ (by omega)
  have a5 : 11 * n + 20 + 13 * L + 60 ≤ 104 * W := by omega
  have a6 : W ≤ (R1 + 1) * W := Nat.le_mul_of_pos_left _ (by omega)
  have e : 1000 * (R1 + 1) * (c + 1) * W = 1000 * ((R1 + 1) * W) * c + 1000 * ((R1 + 1) * W) := by ring
  rw [e]
  have : 74 * W * c ≤ 1000 * ((R1 + 1) * W) * c := by
    apply Nat.mul_le_mul_right; omega
  omega

set_option maxHeartbeats 1000000 in
theorem finalCost_le (n k q L R1 : ℕ) :
    finalCost n k q L (q * n) R1 ≤ kF k q R1 * ((n + 1) * ((n + 1) * (L + 1))) := by
  have hI := innerCost_le n R1 L (k + q)
  unfold finalCost kF
  generalize innerCost n L (k + q) = I at hI ⊢
  generalize hW : (n + 1) * (L + 1) = W at hI ⊢
  have hnL : (n + 1) * (L + 1) ≤ W := by omega
  have hW1 : 1 ≤ W := by rw [← hW]; exact Nat.mul_pos (by omega) (by omega)
  generalize hP : (n + 1) * W = P
  have hnP : n + 1 ≤ P := by rw [← hP]; exact Nat.le_mul_of_pos_right _ hW1
  have hWP : W ≤ P := by rw [← hP]; exact Nat.le_mul_of_pos_left _ (by omega)
  generalize hZ : (q + 1) * (R1 + 1) ^ 2 * (k + q + 2) = Z
  have hR2 : R1 + 1 ≤ (R1 + 1) ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hZ1 : (q + 1) * (R1 + 1) ≤ Z := by
    rw [← hZ]
    calc (q + 1) * (R1 + 1) = (q + 1) * (R1 + 1) * 1 := by ring
      _ ≤ (q + 1) * (R1 + 1) ^ 2 * (k + q + 2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hR2) (by omega)
  have hZ2 : (q + 1) * (q + 1) ≤ Z := by
    rw [← hZ]
    calc (q + 1) * (q + 1) = (q + 1) * 1 * (q + 1) := by ring
      _ ≤ (q + 1) * (R1 + 1) ^ 2 * (k + q + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))) (by omega)
  have hZ3 : (q + 1) * (R1 + 1) * (R1 + 1) * (k + q + 1) ≤ Z := by
    rw [← hZ]
    calc (q + 1) * (R1 + 1) * (R1 + 1) * (k + q + 1) = (q + 1) * (R1 + 1) ^ 2 * (k + q + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hqnP : q * n ≤ (q + 1) * P := Nat.mul_le_mul (by omega) (by omega)
  -- the sorting part
  have b1 : (2 * (36 * L + 56) + 68) * (q * n) + 8 + 15 ≤ 210 * ((q + 1) * W) := by
    have h1 : (L + 1) * (q * n) ≤ (q + 1) * W := by
      calc (L + 1) * (q * n) ≤ (L + 1) * ((q + 1) * (n + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
        _ = (q + 1) * ((n + 1) * (L + 1)) := by ring
        _ ≤ (q + 1) * W := Nat.mul_le_mul_left _ hnL
    have h2 : (2 * (36 * L + 56) + 68) * (q * n) ≤ 180 * ((L + 1) * (q * n)) := by
      calc _ ≤ (180 * (L + 1)) * (q * n) := Nat.mul_le_mul_right _ (by omega)
        _ = 180 * ((L + 1) * (q * n)) := by ring
    have h3 : 1 ≤ (q + 1) * W := Nat.mul_pos (by omega) hW1
    omega
  have b2 : ((2 * (36 * L + 56) + 68) * (q * n) + 8 + 15) * (q * n + 1) ≤ 210 * Z * P := by
    calc ((2 * (36 * L + 56) + 68) * (q * n) + 8 + 15) * (q * n + 1)
        ≤ (210 * ((q + 1) * W)) * ((q + 1) * (n + 1)) := Nat.mul_le_mul b1 (by
          have : q * n ≤ q * (n + 1) := Nat.mul_le_mul_left _ (by omega)
          have : q * (n + 1) + 1 ≤ (q + 1) * (n + 1) := by rw [Nat.add_mul]; omega
          omega)
      _ = 210 * ((q + 1) * (q + 1)) * ((n + 1) * W) := by ring
      _ ≤ 210 * Z * P := by rw [hP]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hZ2)
  -- the radii
  have b3 : R1 * (q * n * 28 + 20) + 10 ≤ 58 * Z * P := by
    have hqP : 1 ≤ (q + 1) * P := Nat.mul_pos (by omega) (by omega)
    have s1 : q * n * 28 + 20 ≤ 48 * ((q + 1) * P) := by omega
    have s2 : R1 * (q * n * 28 + 20) ≤ (R1 + 1) * (48 * ((q + 1) * P)) := Nat.mul_le_mul (by omega) s1
    have s3 : (R1 + 1) * (48 * ((q + 1) * P)) = 48 * ((q + 1) * (R1 + 1) * P) := by ring
    have s4 : (q + 1) * (R1 + 1) * P ≤ Z * P := Nat.mul_le_mul_right _ hZ1
    have s5 : 1 ≤ (q + 1) * (R1 + 1) * P := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have s6 : 58 * Z * P = 58 * (Z * P) := by ring
    omega
  -- the emitting loops
  have b5 : R1 * (q * n * (I + 8) + 18) + 6 ≤ 1100 * Z * P := by
    have h1 : I + 8 ≤ 1008 * ((R1 + 1) * (k + q + 1) * W) := by
      have : 1 ≤ (R1 + 1) * (k + q + 1) * W := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hW1
      have e : 1000 * (R1 + 1) * (k + q + 1) * W = 1000 * ((R1 + 1) * (k + q + 1) * W) := by ring
      omega
    have h2 : q * n * (I + 8) ≤ (q + 1) * (n + 1) * (1008 * ((R1 + 1) * (k + q + 1) * W)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) h1
    have h3 : (q + 1) * (n + 1) * (1008 * ((R1 + 1) * (k + q + 1) * W)) =
        1008 * ((q + 1) * (R1 + 1) * (k + q + 1) * P) := by rw [← hP]; ring
    have h4 : 1 ≤ (q + 1) * (R1 + 1) * (k + q + 1) * P :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
    have h5 : q * n * (I + 8) + 18 ≤ 1026 * ((q + 1) * (R1 + 1) * (k + q + 1) * P) := by omega
    have h6 : R1 * (q * n * (I + 8) + 18) ≤ (R1 + 1) * (1026 * ((q + 1) * (R1 + 1) * (k + q + 1) * P)) :=
      Nat.mul_le_mul (by omega) h5
    have h7 : (R1 + 1) * (1026 * ((q + 1) * (R1 + 1) * (k + q + 1) * P)) =
        1026 * ((q + 1) * (R1 + 1) * (R1 + 1) * (k + q + 1) * P) := by ring
    have h8 : (q + 1) * (R1 + 1) * (R1 + 1) * (k + q + 1) * P ≤ Z * P := Nat.mul_le_mul_right _ hZ3
    have h9 : 1 ≤ Z * P := le_trans h4 (le_trans (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega)))) h8)
    have h10 : 1100 * Z * P = 1100 * (Z * P) := by ring
    omega
  -- together
  have c1 : (q + 1) * (13 * radExp k q 0 + 50) + 8 + 10 ≤ ((q + 1) * (13 * radExp k q 0 + 50) + 100) * P :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega))
  have e : (2000 * Z + ((q + 1) * (13 * radExp k q 0 + 50) + 100)) * P =
      2000 * (Z * P) + ((q + 1) * (13 * radExp k q 0 + 50) + 100) * P := by ring
  have e2 : 210 * Z * P = 210 * (Z * P) := by ring
  have e3 : 58 * Z * P = 58 * (Z * P) := by ring
  have e4 : 1100 * Z * P = 1100 * (Z * P) := by ring
  rw [e]
  omega

end Lax185574Proofs.StpRam
