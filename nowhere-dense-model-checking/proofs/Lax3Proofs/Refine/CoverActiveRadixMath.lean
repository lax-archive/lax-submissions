import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Perm.Basic

/-!
# Stable binary radix sorting for active cover blocks

The block BFS emits a repetition-free list in discovery order, whereas
the recursive member thread consumes each block in increasing vertex
order.  This file isolates the mathematical part of the repair: one
stable low-to-high binary pass preserves the represented multiset and
extends ordering modulo `2^b` to ordering modulo `2^(b+1)`.

The executable RAM pass is proved against `radixPass`; no abstract sorting
oracle is introduced here.
-/

namespace Lax3Proofs.Refine.CoverActiveRadixMath

/-- The numeric value of bit `b`.  This is exactly the result of the RAM
expression `(x >> b) & 1`. -/
def digit (b x : ℕ) : ℕ := (x / 2 ^ b) % 2

/-- The Boolean discriminator used by `List.filter`. -/
def digitZero (b x : ℕ) : Bool := decide (digit b x = 0)

/-- One stable LSD radix pass: zero-bit entries first, then one-bit entries,
with the entering order preserved within each half. -/
def radixPass (b : ℕ) (xs : List ℕ) : List ℕ :=
  xs.filter (digitZero b) ++ xs.filter (fun x => !(digitZero b x))

/-- Run the first `b` binary passes, from bit zero upwards. -/
def radixRounds : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | b + 1, xs => radixPass b (radixRounds b xs)

@[simp] theorem digit_lt (b x : ℕ) : digit b x < 2 := by
  exact Nat.mod_lt _ (by omega)

theorem digit_eq_zero_or_one (b x : ℕ) : digit b x = 0 ∨ digit b x = 1 := by
  have := digit_lt b x
  omega

@[simp] theorem digitZero_eq_true {b x : ℕ} : digitZero b x = true ↔ digit b x = 0 := by
  simp [digitZero]

@[simp] theorem digitZero_eq_false {b x : ℕ} : digitZero b x = false ↔ digit b x = 1 := by
  rw [Bool.eq_false_iff]
  simp only [digitZero, Bool.not_eq_true, decide_eq_false_iff_not]
  have h := digit_eq_zero_or_one b x
  omega

/-- The RAM bit expression computes `digit`. -/
theorem shiftr_and_one_eq_digit (b x : ℕ) :
    Nat.land (x / 2 ^ b) 1 = digit b x := by
  simp [digit, Nat.land_eq]

/-- Splitting modulo the next power of two exposes precisely the current
binary digit. -/
theorem mod_pow_succ_eq (b x : ℕ) :
    x % 2 ^ (b + 1) = x % 2 ^ b + 2 ^ b * digit b x := by
  simpa [digit] using (Nat.mod_pow_succ (x := x) (b := 2) (k := b))

theorem mod_pow_lt (b x : ℕ) : x % 2 ^ b < 2 ^ b :=
  Nat.mod_lt _ (Nat.two_pow_pos b)

/-! ## One stable pass -/

theorem radixPass_perm (b : ℕ) (xs : List ℕ) : List.Perm (radixPass b xs) xs := by
  exact List.filter_append_perm (digitZero b) xs

theorem radixPass_nodup {b : ℕ} {xs : List ℕ} (h : xs.Nodup) :
    (radixPass b xs).Nodup :=
  (List.Perm.nodup_iff (radixPass_perm b xs)).2 h

/-- A stable pass preserves the already-established order of the lower
bits and promotes it to the next modulus. -/
theorem radixPass_pairwise {b : ℕ} {xs : List ℕ}
    (h : xs.Pairwise fun x y => x % 2 ^ b ≤ y % 2 ^ b) :
    (radixPass b xs).Pairwise fun x y => x % 2 ^ (b + 1) ≤ y % 2 ^ (b + 1) := by
  rw [radixPass, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (h.filter (digitZero b)).imp_of_mem fun {x y} hx hy hxy => by
      have hdx : digit b x = 0 := digitZero_eq_true.mp (List.of_mem_filter hx)
      have hdy : digit b y = 0 := digitZero_eq_true.mp (List.of_mem_filter hy)
      rw [mod_pow_succ_eq, mod_pow_succ_eq, hdx, hdy]
      simpa using hxy
  · exact (h.filter fun x => !(digitZero b x)).imp_of_mem fun {x y} hx hy hxy => by
      have hzx : digitZero b x = false := by
        have := List.of_mem_filter hx
        simpa using this
      have hzy : digitZero b y = false := by
        have := List.of_mem_filter hy
        simpa using this
      have hdx : digit b x = 1 := digitZero_eq_false.mp hzx
      have hdy : digit b y = 1 := digitZero_eq_false.mp hzy
      rw [mod_pow_succ_eq, mod_pow_succ_eq, hdx, hdy]
      omega
  · intro x hx y hy
    have hdx : digit b x = 0 := digitZero_eq_true.mp (List.of_mem_filter hx)
    have hzy : digitZero b y = false := by
      have := List.of_mem_filter hy
      simpa using this
    have hdy : digit b y = 1 := digitZero_eq_false.mp hzy
    rw [mod_pow_succ_eq, mod_pow_succ_eq, hdx, hdy]
    have hxmod := mod_pow_lt b x
    omega

/-! ## Iterated passes and final strict order -/

theorem radixRounds_perm (b : ℕ) (xs : List ℕ) : List.Perm (radixRounds b xs) xs := by
  induction b with
  | zero => exact List.Perm.refl _
  | succ b ih =>
      exact (radixPass_perm b (radixRounds b xs)).trans ih

theorem radixRounds_nodup {b : ℕ} {xs : List ℕ} (h : xs.Nodup) :
    (radixRounds b xs).Nodup :=
  (List.Perm.nodup_iff (radixRounds_perm b xs)).2 h

theorem radixRounds_pairwise (b : ℕ) (xs : List ℕ) :
    (radixRounds b xs).Pairwise fun x y => x % 2 ^ b ≤ y % 2 ^ b := by
  induction b with
  | zero => exact List.pairwise_of_forall (fun _ _ => by
      simp only [Nat.pow_zero, Nat.mod_one, le_refl])
  | succ b ih =>
      simpa [radixRounds] using radixPass_pairwise ih

/-- Once the processed power of two covers the vertex universe, the
residue order is ordinary numeric order; nodup upgrades it to strict
order. -/
theorem radixRounds_strict {n bits : ℕ} {xs : List ℕ}
    (hbits : n ≤ 2 ^ bits) (hlt : ∀ x ∈ xs, x < n) (hnd : xs.Nodup) :
    (radixRounds bits xs).Pairwise (fun x y => x < y) := by
  have hperm := radixRounds_perm bits xs
  have hle : (radixRounds bits xs).Pairwise fun x y => x ≤ y :=
    (radixRounds_pairwise bits xs).imp_of_mem fun {x y} hx hy hxy => by
      have hxlt : x < 2 ^ bits := lt_of_lt_of_le (hlt x (hperm.mem_iff.mp hx)) hbits
      have hylt : y < 2 ^ bits := lt_of_lt_of_le (hlt y (hperm.mem_iff.mp hy)) hbits
      simpa [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hxy
  have hne : (radixRounds bits xs).Pairwise fun x y => x ≠ y :=
    radixRounds_nodup hnd
  exact hle.imp₂ (fun _ _ hxy hne => lt_of_le_of_ne hxy hne) hne

/-- The final list represents exactly the entering block. -/
theorem mem_radixRounds_iff {bits x : ℕ} {xs : List ℕ} :
    x ∈ radixRounds bits xs ↔ x ∈ xs :=
  (radixRounds_perm bits xs).mem_iff

/-! ## Axiom audit -/

#print axioms radixPass_pairwise
#print axioms radixRounds_strict

end Lax3Proofs.Refine.CoverActiveRadixMath
