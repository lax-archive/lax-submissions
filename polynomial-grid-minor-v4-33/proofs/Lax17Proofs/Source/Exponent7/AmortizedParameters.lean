import Lax17Proofs.Source.Exponent7.AmortizedController

namespace Lax17Proofs

/-!
# Explicit logarithmic-depth parameters

These parameters specialize the amortized slicing controller. If `N` is the
pseudo-grid row count, the initial slicing has width `N` and
`O(ell * log(N)^2 * log(q))` slices. Its Theorem 4.6 cost is therefore
`O(N * ell * polylog(q))`.
-/

namespace SimpleGraph
namespace Exponent7

/-- Recursion depth sufficient to halve an initial width of `N`. -/
def amortizedDepth (N : ℕ) : ℕ :=
  Nat.clog 2 N + 1

/-- The terminal row scale.  This dominates the exact `12*q^4` additive and
Claim 5.3 loss. -/
def exponentSevenDstar (q : ℕ) : ℕ :=
  16 * q ^ 4

/-- Number of initial slices, in the division-free form used by the
productive-potential inequality. -/
def exponentSevenInitialSlices (q N ell : ℕ) : ℕ :=
  (16 * (amortizedDepth N + 1) * (2048 * amortizedDepth N)) *
    (32 * ell * (Nat.log 2 q + 1))

/-- A row-count-independent recursion depth under the standard
`N ≤ 64*q^6` pseudo-grid bound and the power-of-two convention on `q`. -/
def exponentSevenUniformDepth (q : ℕ) : ℕ :=
  6 * (Nat.log 2 q + 1)

/-- Uniform initial slice count for the local theorem. -/
def exponentSevenUniformSlices (q ell : ℕ) : ℕ :=
  (16 * (exponentSevenUniformDepth q + 1) *
      (2048 * exponentSevenUniformDepth q)) *
    (32 * ell * (Nat.log 2 q + 1))

theorem amortizedDepth_pos (N : ℕ) :
    0 < amortizedDepth N := by
  simp [amortizedDepth]

theorem exponentSevenDstar_pos {q : ℕ} (hq : 0 < q) :
    0 < exponentSevenDstar q := by
  simp [exponentSevenDstar, hq]

theorem amortizedLoss_le_exponentSevenDstar (q : ℕ) :
    amortizedLoss q ≤ exponentSevenDstar q := by
  simp [amortizedLoss, exponentSevenDstar]
  omega

theorem exponentSeven_additive_budget
    {q N : ℕ}
    (hN : N ≤ 64 * q ^ 6) :
    N * (4 * q ^ 2) ≤
      (32 * q ^ 4) * (8 * q ^ 4) := by
  calc
    N * (4 * q ^ 2)
        ≤ (64 * q ^ 6) * (4 * q ^ 2) :=
      Nat.mul_le_mul_right (4 * q ^ 2) hN
    _ = (32 * q ^ 4) * (8 * q ^ 4) := by ring

theorem exponentSeven_pruning_budget
    {q N : ℕ}
    (hN : N ≤ 64 * q ^ 6) :
    2 * N * (4 * q ^ 2) ≤
      (32 * q ^ 4) * exponentSevenDstar q := by
  calc
    2 * N * (4 * q ^ 2)
        ≤ 2 * (64 * q ^ 6) * (4 * q ^ 2) :=
      Nat.mul_le_mul_right (4 * q ^ 2)
        (Nat.mul_le_mul_left 2 hN)
    _ = (32 * q ^ 4) * exponentSevenDstar q := by
      simp [exponentSevenDstar]
      ring

theorem exponentSeven_width_depth
    {q N : ℕ}
    (hN : 0 < N) (hq : 0 < q) :
    N ≤
      2 ^ amortizedDepth N *
        amortizedStopThreshold
          (amortizedDepth N) (exponentSevenDstar q) := by
  have hpow0 : N ≤ 2 ^ Nat.clog 2 N :=
    Nat.le_pow_clog Nat.one_lt_two N
  have hpow :
      N ≤ 2 ^ amortizedDepth N := by
    apply hpow0.trans
    apply Nat.pow_le_pow_right (by omega)
    simp [amortizedDepth]
  have hstop :
      0 <
        amortizedStopThreshold
          (amortizedDepth N) (exponentSevenDstar q) := by
    simp [amortizedStopThreshold, amortizedDepth,
      exponentSevenDstar, hq]
  exact hpow.trans
    (Nat.le_mul_of_pos_right (2 ^ amortizedDepth N) hstop)

theorem exponentSeven_initialSlices_pos
    {q N ell : ℕ}
    (hell : 0 < ell) :
    0 < exponentSevenInitialSlices q N ell := by
  simp [exponentSevenInitialSlices, amortizedDepth, hell]

theorem exponentSevenUniformDepth_pos (q : ℕ) :
    0 < exponentSevenUniformDepth q := by
  simp [exponentSevenUniformDepth]

theorem exponentSevenUniformSlices_pos
    {q ell : ℕ} (hell : 0 < ell) :
    0 < exponentSevenUniformSlices q ell := by
  simp [exponentSevenUniformSlices,
    exponentSevenUniformDepth, hell]

theorem exponentSeven_uniform_width_depth
    {q N : ℕ}
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hNupper : N ≤ 64 * q ^ 6)
    (hq : 0 < q) :
    N ≤
      2 ^ exponentSevenUniformDepth q *
        amortizedStopThreshold
          (exponentSevenUniformDepth q)
          (exponentSevenDstar q) := by
  rcases hpow with ⟨r, rfl⟩
  have hpower :
      64 * (2 ^ r) ^ 6 =
        2 ^ exponentSevenUniformDepth (2 ^ r) := by
    simp only [exponentSevenUniformDepth,
      Nat.log_pow (by norm_num : 1 < 2)]
    rw [show 64 = 2 ^ 6 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  have htwo :
      N ≤ 2 ^ exponentSevenUniformDepth (2 ^ r) :=
    hNupper.trans_eq hpower
  have hstop :
      0 <
        amortizedStopThreshold
          (exponentSevenUniformDepth (2 ^ r))
          (exponentSevenDstar (2 ^ r)) := by
    simp [amortizedStopThreshold, exponentSevenUniformDepth,
      exponentSevenDstar]
  exact htwo.trans
    (Nat.le_mul_of_pos_right
      (2 ^ exponentSevenUniformDepth (2 ^ r)) hstop)

theorem exponentSeven_productive_budget
    (q N ell : ℕ) :
    (16 * (amortizedDepth N + 1) *
          (2048 * amortizedDepth N)) *
        (32 * N * ell * (Nat.log 2 q + 1)) ≤
      7 * (exponentSevenInitialSlices q N ell * N) := by
  have heq :
      (16 * (amortizedDepth N + 1) *
            (2048 * amortizedDepth N)) *
          (32 * N * ell * (Nat.log 2 q + 1)) =
        exponentSevenInitialSlices q N ell * N := by
    simp [exponentSevenInitialSlices]
    ring
  rw [heq]
  omega

theorem exponentSeven_terminal_budget
    (q N ell : ℕ) :
    (16 *
          amortizedStopThreshold
            (amortizedDepth N) (exponentSevenDstar q)) *
        (2 * N * ell) ≤
      (7 * (exponentSevenInitialSlices q N ell * N)) *
        (16 * q ^ 4) := by
  let h := amortizedDepth N
  let base := 131072 * h * ell
  have hfactor : 0 < 8 * (h + 1) * (Nat.log 2 q + 1) := by
    positivity
  have hbase :
      base ≤ exponentSevenInitialSlices q N ell := by
    have hmul : base ≤ base *
        (8 * (h + 1) * (Nat.log 2 q + 1)) :=
      Nat.le_mul_of_pos_right base hfactor
    apply hmul.trans_eq
    simp [base, h, exponentSevenInitialSlices]
    ring
  calc
    (16 *
          amortizedStopThreshold
            (amortizedDepth N) (exponentSevenDstar q)) *
        (2 * N * ell)
        = base * (N * (16 * q ^ 4)) := by
          simp [amortizedStopThreshold, exponentSevenDstar, base, h]
          ring
    _ ≤ exponentSevenInitialSlices q N ell *
          (N * (16 * q ^ 4)) :=
      Nat.mul_le_mul_right (N * (16 * q ^ 4)) hbase
    _ ≤ (7 * exponentSevenInitialSlices q N ell) *
          (N * (16 * q ^ 4)) := by
      apply Nat.mul_le_mul_right
      omega
    _ = (7 * (exponentSevenInitialSlices q N ell * N)) *
          (16 * q ^ 4) := by ring

theorem exponentSeven_uniform_productive_budget
    (q N ell : ℕ) :
    (16 * (exponentSevenUniformDepth q + 1) *
          (2048 * exponentSevenUniformDepth q)) *
        (32 * N * ell * (Nat.log 2 q + 1)) ≤
      7 * (exponentSevenUniformSlices q ell * N) := by
  have heq :
      (16 * (exponentSevenUniformDepth q + 1) *
            (2048 * exponentSevenUniformDepth q)) *
          (32 * N * ell * (Nat.log 2 q + 1)) =
        exponentSevenUniformSlices q ell * N := by
    simp [exponentSevenUniformSlices]
    ring
  rw [heq]
  omega

theorem exponentSeven_uniform_terminal_budget
    (q N ell : ℕ) :
    (16 *
          amortizedStopThreshold
            (exponentSevenUniformDepth q)
            (exponentSevenDstar q)) *
        (2 * N * ell) ≤
      (7 * (exponentSevenUniformSlices q ell * N)) *
        (16 * q ^ 4) := by
  let h := exponentSevenUniformDepth q
  let base := 131072 * h * ell
  have hfactor : 0 < 8 * (h + 1) * (Nat.log 2 q + 1) := by
    positivity
  have hbase :
      base ≤ exponentSevenUniformSlices q ell := by
    have hmul : base ≤ base *
        (8 * (h + 1) * (Nat.log 2 q + 1)) :=
      Nat.le_mul_of_pos_right base hfactor
    apply hmul.trans_eq
    simp [base, h, exponentSevenUniformSlices]
    ring
  calc
    (16 *
          amortizedStopThreshold
            (exponentSevenUniformDepth q)
            (exponentSevenDstar q)) *
        (2 * N * ell)
        = base * (N * (16 * q ^ 4)) := by
          simp [amortizedStopThreshold, exponentSevenDstar, base, h]
          ring
    _ ≤ exponentSevenUniformSlices q ell *
          (N * (16 * q ^ 4)) :=
      Nat.mul_le_mul_right (N * (16 * q ^ 4)) hbase
    _ ≤ (7 * exponentSevenUniformSlices q ell) *
          (N * (16 * q ^ 4)) := by
      apply Nat.mul_le_mul_right
      omega
    _ = (7 * (exponentSevenUniformSlices q ell * N)) *
          (16 * q ^ 4) := by ring

end Exponent7
end SimpleGraph

end Lax17Proofs
