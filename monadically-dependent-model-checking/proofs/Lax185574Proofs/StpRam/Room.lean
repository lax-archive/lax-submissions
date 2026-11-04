import Lax185574Proofs.StpRam.Callee
import Lax185574Proofs.StpRam.CompositeArith

/-!
Sizes for the composite of lem:compute-stp in terms of `n` and the
largest tree size `L`, and the room of the regions of the loop
driver at a word length at which the input is admissible.
-/

namespace Lax185574Proofs.StpRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574Proofs.Words Lax185574.TypeTrees
open Lax185574.PartialGraphs Lax185574.ScatterTypes Lax185574.PartialGraphEncoding
open Lax185574Proofs.Simulate Lax185574Proofs.RamSim

variable {n : ℕ}

theorem length_toWord_family_le (G : PartialGraph (Fin n)) (k q : ℕ) :
    (toWord (family G k q)).length ≤ (n + 1) * (maxTreeSize G k q + 1) := by
  have h1 := length_toWord_famF G k q
  have h2 := length_toWord_words (famF G k q)
  have h3 := total_le (famF G k q) (maxTreeSize G k q) (fun u hu => by
    rw [famF, famW, List.mem_ofFn] at hu
    obtain ⟨v, rfl⟩ := hu
    exact le_maxTreeSize G k q v)
  rw [length_famF] at h2 h3
  have : (n + 1) * (maxTreeSize G k q + 1) = n * maxTreeSize G k q + n + maxTreeSize G k q + 1 := by
    ring
  omega

theorem length_toWord_answers_le (G : PartialGraph (Fin n)) (k q : ℕ)
    (hA : ∀ u ∈ answers G k q, u.length ≤ maxTreeSize G k q) :
    (toWord (answers G k q)).length ≤ (q + 1) * (n + 1) * (maxTreeSize G k q + 1) := by
  rw [length_toWord_words, length_answers]
  have h := total_le (answers G k q) (maxTreeSize G k q) hA
  rw [length_answers] at h
  have : (q + 1) * (n + 1) * (maxTreeSize G k q + 1) =
      q * n * maxTreeSize G k q + q * n + (q + n + 1) * (maxTreeSize G k q + 1) := by ring
  have : 1 ≤ (q + n + 1) * (maxTreeSize G k q + 1) := Nat.mul_pos (by omega) (by omega)
  omega

/-- **Room for the glue program.** -/
theorem room_glue {G : PartialGraph (Fin n)} {k q X C w e : ℕ} (hs : Sizes G k q X)
    (hX : X = (xIn G k q).length + maxEntry (xIn G k q) + 1) (he : 7 ≤ e)
    (hC : rK k q + 1 ≤ C) (h : 2 ^ 22 * C * X ^ e ≤ 2 ^ w) {j : ℕ} (hj : j ≤ q * n + 1) :
    lpSize w (2 * j) ≠ 0 ∧ gsz * vB G k q ≤ 2 ^ lpV w (2 * j) ∧ gsz * vB G k q ≤ lpCap w ∧ 8 ≤ w := by
  have hX1 := hs.one
  have hC1 : 1 ≤ C := by omega
  have hv : gsz * vB G k q ≤ 7168 * C * X ^ (e - 4) := by
    rw [vB, ← hX, gsz_eq]
    have : X ^ 3 ≤ X ^ (e - 4) := Nat.pow_le_pow_right hX1 (by omega)
    calc 112 * (64 * (rK k q + 1) * X ^ 3) = 7168 * (rK k q + 1) * X ^ 3 := by ring
      _ ≤ 7168 * C * X ^ (e - 4) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hC) this
  obtain ⟨h1, hw⟩ := room_arith hX1 he 7168 (by norm_num) hC1 h hs.QX hj (2 * j + 1) (by omega)
  obtain ⟨h0, -⟩ := room_arith hX1 he 7168 (by norm_num) hC1 h hs.QX hj 1 (by omega)
  have hpos : 1 ≤ gsz * vB G k q := by
    rw [vB, gsz_eq]; exact Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (Nat.one_le_pow _ _ (by omega)))
  obtain ⟨hs1, hs2⟩ := lp_room (w := w) (i := 2 * j) (N := gsz * vB G k q) hpos
    (le_trans (Nat.mul_le_mul_left _ hv) h1)
  refine ⟨hs1, hs2, ?_, hw⟩
  simpa using le_trans (Nat.mul_le_mul_left _ hv) h0

/-- **Room for the rank shift.** -/
theorem room_shift {G : PartialGraph (Fin n)} {k q X C w e eS cM : ℕ} (hs : Sizes G k q X)
    (he : e = eS + 8) (hC : cM * 4 ^ eS + 1 ≤ C) (h : 2 ^ 22 * C * X ^ e ≤ 2 ^ w) {j : ℕ}
    (hj : j ≤ q * n) :
    lpSize w (2 * j + 1) ≠ 0 ∧ cM * (4 * X) ^ eS + 1 ≤ 2 ^ lpV w (2 * j + 1) := by
  have hX1 := hs.one
  have hC1 : 1 ≤ C := by omega
  have hXe : 1 ≤ X ^ eS := Nat.one_le_pow _ _ (by omega)
  have hv : cM * (4 * X) ^ eS + 1 ≤ 1 * C * X ^ (e - 4) := by
    have : X ^ eS ≤ X ^ (e - 4) := Nat.pow_le_pow_right hX1 (by omega)
    calc cM * (4 * X) ^ eS + 1 ≤ (cM * 4 ^ eS + 1) * X ^ eS := by rw [mul_pow]; nlinarith
      _ ≤ 1 * C * X ^ (e - 4) := by rw [one_mul]; exact Nat.mul_le_mul hC this
  obtain ⟨h1, -⟩ := room_arith hX1 (by omega) 1 (by norm_num) hC1 h hs.QX (j := j) (by omega)
    (2 * j + 1 + 1) (by omega)
  exact lp_room (by omega) (le_trans (Nat.mul_le_mul_left _ hv) h1)

end Lax185574Proofs.StpRam
