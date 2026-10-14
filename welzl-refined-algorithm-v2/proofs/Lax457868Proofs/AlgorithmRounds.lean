import Mathlib.Tactic
import Mathlib.Data.Nat.Log

/-!
Finite-prefix contraction bounds and the stopping-time consequence for the
refined Welzl algorithm.
-/

namespace Lax457868Proofs.AlgorithmRounds

/-- The recurrence can be iterated for a finite prefix using only the
one-step inequalities inside that prefix. -/
lemma finite_prefix_geometric_bound (n : ℕ → ℕ) (c t : ℕ)
    (hstep : ∀ i, i < t → 2 * n (i + 1) ≤ n i + 2 * c ^ 2) :
    2 ^ t * n t ≤ n 0 + 2 * c ^ 2 * (2 ^ t - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hprefix : ∀ i, i < t → 2 * n (i + 1) ≤ n i + 2 * c ^ 2 := by
        intro i hi
        exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self t))
      have hgeom := ih hprefix
      have hlast := hstep t (Nat.lt_succ_self t)
      have hmul := Nat.mul_le_mul_left (2 ^ t) hlast
      have hpow : 2 ^ (t + 1) = 2 ^ t * 2 := by simp [pow_succ]
      rw [hpow]
      calc
        2 ^ t * 2 * n (t + 1) = 2 ^ t * (2 * n (t + 1)) := by ring
        _ ≤ 2 ^ t * (n t + 2 * c ^ 2) := hmul
        _ = 2 ^ t * n t + 2 * c ^ 2 * 2 ^ t := by ring
        _ ≤ n 0 + 2 * c ^ 2 * (2 ^ t - 1) + 2 * c ^ 2 * 2 ^ t :=
          Nat.add_le_add_right hgeom _
        _ = n 0 + 2 * c ^ 2 * ((2 ^ t - 1) + 2 ^ t) := by ring
        _ = n 0 + 2 * c ^ 2 * (2 ^ (t + 1) - 1) := by
          have hpow' : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by
            rw [pow_succ]
            ring
          rw [hpow']
          congr 2
          omega

/-- At the paper's cutoff `clog₂(n₀)-1`, a finite contraction prefix has
size at most `2k`. -/
lemma finite_prefix_logarithmic_size (n : ℕ → ℕ) (c k r : ℕ)
    (hc : 2 ≤ c) (hk : 6 * c ^ 2 ≤ k) (hn0 : 2 ≤ n 0)
    (hr : Nat.clog 2 (n 0) - 1 ≤ r)
    (hstep : ∀ i, i < r → 2 * n (i + 1) ≤ n i + 2 * c ^ 2) :
    n (Nat.clog 2 (n 0) - 1) ≤ 2 * k := by
  let t := Nat.clog 2 (n 0) - 1
  have hlogpos : 1 ≤ Nat.clog 2 (n 0) := by
    by_contra h
    have hle : Nat.clog 2 (n 0) ≤ 0 := by omega
    have hsmall := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).1 hle
    norm_num at hsmall
    omega
  have htlt : t < Nat.clog 2 (n 0) := by dsimp [t]; omega
  have hprefix : ∀ i, i < t → 2 * n (i + 1) ≤ n i + 2 * c ^ 2 := by
    intro i hi
    exact hstep i (Nat.lt_of_lt_of_le hi hr)
  have hgeom := finite_prefix_geometric_bound n c t hprefix
  have hclog : n 0 ≤ 2 ^ Nat.clog 2 (n 0) :=
    Nat.le_pow_clog (by decide : 1 < 2) (n 0)
  have hpow : 2 ^ Nat.clog 2 (n 0) = 2 ^ t * 2 := by
    have ht : t + 1 = Nat.clog 2 (n 0) := by dsimp [t]; omega
    calc
      2 ^ Nat.clog 2 (n 0) = 2 ^ (t + 1) := by rw [← ht]
      _ = 2 ^ t * 2 := by rw [pow_succ]
  have hbase : n 0 ≤ 2 ^ t * 2 := by omega
  have htpos : 0 < 2 ^ t := by positivity
  have hupper : n 0 + 2 * c ^ 2 * (2 ^ t - 1) ≤
      2 ^ t * (2 + 2 * c ^ 2) := by
    calc
      n 0 + 2 * c ^ 2 * (2 ^ t - 1) ≤
          2 ^ t * 2 + 2 * c ^ 2 * (2 ^ t - 1) :=
        Nat.add_le_add_right hbase _
      _ ≤ 2 ^ t * 2 + 2 * c ^ 2 * 2 ^ t := by
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_left (2 * c ^ 2) (Nat.sub_le (2 ^ t) 1)) _
      _ = 2 ^ t * (2 + 2 * c ^ 2) := by ring
  have hmul : 2 ^ t * n t ≤ 2 ^ t * (2 + 2 * c ^ 2) := hgeom.trans hupper
  have hratio : n t ≤ 2 + 2 * c ^ 2 :=
    Nat.le_of_mul_le_mul_left hmul htpos
  have hsmall : 2 + 2 * c ^ 2 ≤ 2 * k := by nlinarith
  simpa [t, Nat.add_comm] using hratio.trans hsmall

/-- The exact paper cutoff supplies the additive allowance required by the
finite-prefix logarithmic estimate. -/
lemma refined_cutoff_ge_six_sq (c : ℕ) (hc : 2 ≤ c) :
    6 * c ^ 2 ≤ 768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1 := by
  have hlog : 1 ≤ Nat.clog 2 c := by
    by_contra h
    have hle : Nat.clog 2 c ≤ 0 := by omega
    have hsmall := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).1 hle
    norm_num at hsmall
    omega
  have hpow : c ^ 2 ≤ c ^ 5 := by
    have hcubePos : 0 < c ^ 3 := pow_pos (by omega) 3
    have hcube : 1 ≤ c ^ 3 := by omega
    calc
      c ^ 2 = c ^ 2 * 1 := by simp
      _ ≤ c ^ 2 * c ^ 3 := Nat.mul_le_mul_left _ hcube
      _ = c ^ 5 := by ring
  have hfactor : 1 ≤ 64 * Nat.clog 2 c + 1 := by omega
  calc
    6 * c ^ 2 ≤ 768 * c ^ 2 := by omega
    _ ≤ 768 * c ^ 5 := Nat.mul_le_mul_left 768 hpow
    _ ≤ 768 * c ^ 5 * (64 * Nat.clog 2 c + 1) := by
      calc
        768 * c ^ 5 = (768 * c ^ 5) * 1 := by simp
        _ ≤ (768 * c ^ 5) * (64 * Nat.clog 2 c + 1) :=
          Nat.mul_le_mul_left _ hfactor
    _ ≤ 768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c := by
      calc
        _ = (768 * c ^ 5 * (64 * Nat.clog 2 c + 1)) * 1 := by simp
        _ ≤ (768 * c ^ 5 * (64 * Nat.clog 2 c + 1)) * Nat.clog 2 c :=
          Nat.mul_le_mul_left _ hlog
    _ ≤ 768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1 :=
      Nat.le_add_right _ _

/-- If every executed round satisfies the finite contraction recurrence and
the algorithm continues only while its size exceeds `2k`, the number of
successful rounds plus one is at most `clog₂(n₀)`. -/
lemma finite_run_iterations (n : ℕ → ℕ) (c k r : ℕ)
    (hc : 2 ≤ c) (hk : 6 * c ^ 2 ≤ k) (hn0 : 2 ≤ n 0)
    (hstep : ∀ i, i < r → 2 * n (i + 1) ≤ n i + 2 * c ^ 2)
    (hcontinue : ∀ i, i < r → 2 * k < n i) :
    r + 1 ≤ Nat.clog 2 (n 0) := by
  by_contra hbound
  have hlogpos : 1 ≤ Nat.clog 2 (n 0) := by
    by_contra h
    have hle : Nat.clog 2 (n 0) ≤ 0 := by omega
    have hsmall := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).1 hle
    norm_num at hsmall
    omega
  have hcut : Nat.clog 2 (n 0) - 1 ≤ r := by omega
  have hcutlt : Nat.clog 2 (n 0) - 1 < r := by omega
  have hsize := finite_prefix_logarithmic_size n c k r hc hk hn0 hcut hstep
  have hcontinue' := hcontinue (Nat.clog 2 (n 0) - 1) hcutlt
  omega

/-- The exact refined Welzl cutoff also gives the simple `6c²` hypothesis
used in the stopping-time estimate. -/
lemma refined_run_iterations (n : ℕ → ℕ) (c r : ℕ)
    (hc : 2 ≤ c) (hn0 : 2 ≤ n 0)
    (hstep : ∀ i, i < r → 2 * n (i + 1) ≤ n i + 2 * c ^ 2)
    (hcontinue : ∀ i, i < r →
      2 * (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1) < n i) :
    r + 1 ≤ Nat.clog 2 (n 0) := by
  apply finite_run_iterations n c
    (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
    r hc (refined_cutoff_ge_six_sq c hc) hn0 hstep ?_
  exact hcontinue

end Lax457868Proofs.AlgorithmRounds
