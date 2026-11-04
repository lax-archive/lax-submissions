import Lax185574Proofs.ResolveRam.Glue.Input

/-!
Arithmetic on the codes of distances, as the glue program of
lem:resolve-lift computes with them.

A code is `0` for `∞` and `d + 1` for a distance `d` (`dcode`). The least
of two distances has the code `cmin` of their codes (`dcode_min`), and a
sum `a + c + b` the code `cadd` (`dcode_add`). The least distance over
the members of a set of vertices is the fold `cmPre` of `cmin` over the
vertices in order (`dcode_inf`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.PartialGraphs Lax185574.DistanceMatrix Lax185574Proofs.DistMatrix

/-- The code of the least of two distances. -/
def cmin (a b : ℕ) : ℕ := if a = 0 then b else if b = 0 then a else min a b

theorem cmin_zero_left (b : ℕ) : cmin 0 b = b := by simp [cmin]

theorem cmin_zero_right (a : ℕ) : cmin a 0 = a := by unfold cmin; split_ifs <;> omega

theorem cmin_comm (a b : ℕ) : cmin a b = cmin b a := by unfold cmin; split_ifs <;> omega

theorem cmin_le_max (a b : ℕ) : cmin a b ≤ max a b := by unfold cmin; split_ifs <;> omega

theorem dcode_min (a b : ℕ∞) : dcode (min a b) = cmin (dcode a) (dcode b) := by
  induction a using ENat.recTopCoe with
  | top => simp [cmin_zero_left]
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp [cmin]
    | coe b =>
      rw [← (Nat.mono_cast (α := ℕ∞)).map_min, dcode_coe, dcode_coe, dcode_coe]
      simp only [cmin]
      split_ifs <;> simp_all

/-- The code of the distance `a + c + b`. -/
def cadd (a c b : ℕ) : ℕ := if a = 0 ∨ b = 0 then 0 else a + c + b - 1

theorem dcode_add (a b : ℕ∞) (c : ℕ) : dcode (a + c + b) = cadd (dcode a) c (dcode b) := by
  induction a using ENat.recTopCoe with
  | top => simp [cadd]
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp [cadd]
    | coe b =>
      rw [show (a : ℕ∞) + c + b = ((a + c + b : ℕ) : ℕ∞) by push_cast; ring, dcode_coe, dcode_coe,
        dcode_coe]
      simp only [cadd]
      split_ifs <;> simp_all; omega

/-- The code of `a` if a guard holds, and of `∞` otherwise. -/
theorem dcode_guard (a : ℕ∞) (p : Prop) [Decidable p] :
    dcode (a + if p then 0 else ⊤) = if p then dcode a else 0 := by
  split_ifs <;> simp

/-- The fold of `cmin` over the values `f 0, …, f (k - 1)`. -/
def cmPre (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cmin (cmPre f k) (f k)

/-- **The least distance over a set of vertices.** -/
theorem dcode_inf {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (g : Fin n → ℕ∞) :
    dcode ((Finset.univ.filter p).inf g) =
      cmPre (fun j => if h : j < n then (if p ⟨j, h⟩ then dcode (g ⟨j, h⟩) else 0) else 0) n := by
  suffices key : ∀ k ≤ n, dcode ((Finset.univ.filter fun x : Fin n => p x ∧ x.val < k).inf g) =
      cmPre (fun j => if h : j < n then (if p ⟨j, h⟩ then dcode (g ⟨j, h⟩) else 0) else 0) k by
    rw [← key n le_rfl]
    congr 2
    ext x
    simp [x.isLt]
  intro k
  induction k with
  | zero =>
    intro _
    have : (Finset.univ.filter fun x : Fin n => p x ∧ x.val < 0) = ∅ := by
      ext x; simp
    rw [this, Finset.inf_empty, cmPre]
    exact dcode_top
  | succ k ih =>
    intro hk
    rw [cmPre, ← ih (by omega), dif_pos (by omega)]
    by_cases hp : p ⟨k, by omega⟩
    · have : (Finset.univ.filter fun x : Fin n => p x ∧ x.val < k + 1) =
          insert ⟨k, by omega⟩ (Finset.univ.filter fun x : Fin n => p x ∧ x.val < k) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hx : x.val = k
          · exact Or.inl (Fin.ext hx)
          · exact Or.inr ⟨h1, by omega⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨hp, by simp⟩
          · exact ⟨h1, by omega⟩
      rw [this, Finset.inf_insert, if_pos hp, cmin_comm]
      exact dcode_min _ _
    · have : (Finset.univ.filter fun x : Fin n => p x ∧ x.val < k + 1) =
          (Finset.univ.filter fun x : Fin n => p x ∧ x.val < k) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          by_contra hx
          have hx' : x = ⟨k, by omega⟩ := Fin.ext (by simp only; omega)
          exact hp (hx' ▸ h1)
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      rw [this, if_neg hp, cmin_zero_right]

/-- `cmPre` only reads the values below `k`. -/
theorem cmPre_congr {f g : ℕ → ℕ} {k : ℕ} (h : ∀ j < k, f j = g j) : cmPre f k = cmPre g k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [cmPre, cmPre, ih (fun j hj => h j (by omega)), h k (by omega)]

/-- A bound on all values bounds the fold. -/
theorem cmPre_le {f : ℕ → ℕ} {k m : ℕ} (h : ∀ j < k, f j ≤ m) : cmPre f k ≤ m := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [cmPre]
    exact le_trans (cmin_le_max _ _) (max_le (ih fun j hj => h j (by omega)) (h k (by omega)))

end Lax185574Proofs.ResolveRam.Glue
