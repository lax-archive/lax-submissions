import Mathlib.NumberTheory.Harmonic.Bounds
import Lax17Proofs.Source.ChekuriChuzhoySection5SourcePotential

namespace Lax17Proofs

universe u v w

/-!
# A rational contribution function for Section 5.2

The journal proof defines `rho` using `4 alpha log z` below `w0` and
geometric bins above `w0`.  For Lean we use the equivalent rational
majorant/minorant:

* below `w0`, `4/D` times the rational harmonic number;
* from `w0` onward, a bounded increasing inverse tail.

The harmonic difference supplies exactly the constant drop when a small
cluster is split by a violating cut.  The inverse tail supplies the
`w0 / z` drop used by Claim 5.6.  Unlike a real logarithm followed by
rounding, every comparison remains an exact rational identity.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Rho

open ChekuriChuzhoySection5SourcePotential

/-- The exact rational contribution used in the formal Section 5 potential. -/
noncomputable def rho (w0 D z : Nat) : Rat :=
  if z < w0 then
    4 / (D : Rat) * harmonic z
  else
    4 / (D : Rat) *
      (harmonic w0 + 2 - (w0 : Rat) / ((z : Rat) + 1))

theorem harmonic_nonnegative (n : Nat) :
    (0 : Rat) ≤ harmonic n := by
  unfold harmonic
  apply Finset.sum_nonneg
  intro i _hi
  exact inv_nonneg.mpr (by positivity)

theorem harmonic_mono : Monotone harmonic := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_succ]
  exact le_add_of_nonneg_right (inv_nonneg.mpr (by positivity))

/-- A finite harmonic interval is bounded below by replacing every
denominator with the largest one. -/
theorem harmonic_sub_lower
    {x z : Nat} (hxz : x ≤ z) (hz : 0 < z) :
    ((z - x : Nat) : Rat) / z ≤ harmonic z - harmonic x := by
  let f : Nat → Rat := fun i => ((i + 1 : Nat) : Rat)⁻¹
  have hdecomp :
      harmonic x + ∑ i ∈ Finset.Ico x z, f i = harmonic z := by
    simpa [harmonic, f] using
      Finset.sum_range_add_sum_Ico f hxz
  have hterm :
      ∀ i ∈ Finset.Ico x z, (1 : Rat) / z ≤ f i := by
    intro i hi
    have hiz : i + 1 ≤ z := Finset.mem_Ico.mp hi |>.2
    have hiPos : (0 : Rat) < (i + 1 : Nat) := by positivity
    have hizRat : ((i + 1 : Nat) : Rat) ≤ z := by
      exact_mod_cast hiz
    simpa [f, one_div] using
      one_div_le_one_div_of_le hiPos hizRat
  have hsum :
      ∑ _i ∈ Finset.Ico x z, (1 : Rat) / z ≤
        ∑ i ∈ Finset.Ico x z, f i :=
    Finset.sum_le_sum fun i hi => hterm i hi
  have hcard :
      ∑ _i ∈ Finset.Ico x z, (1 : Rat) / z =
        ((z - x : Nat) : Rat) / z := by
    simp [hxz, div_eq_mul_inv]
  rw [hcard] at hsum
  linarith

theorem rho_nonnegative
    {w0 D : Nat} (hD : 0 < D) (z : Nat) :
    (0 : Rat) ≤ rho w0 D z := by
  by_cases hz : z < w0
  · rw [rho, if_pos hz]
    exact mul_nonneg
      (le_of_lt (div_pos (by norm_num) (by exact_mod_cast hD)))
      (harmonic_nonnegative z)
  · rw [rho, if_neg hz]
    have hwfrac :
        (w0 : Rat) / ((z : Rat) + 1) ≤ 1 := by
      have hwz : w0 ≤ z := Nat.le_of_not_gt hz
      have hwzRat : (w0 : Rat) ≤ (z : Rat) + 1 := by
        exact_mod_cast (hwz.trans (Nat.le_succ z))
      have hzpos : (0 : Rat) < (z : Rat) + 1 := by positivity
      exact (div_le_one hzpos).2 hwzRat
    have hH := harmonic_nonnegative w0
    have hfactor : (0 : Rat) ≤ 4 / D :=
      le_of_lt (div_pos (by norm_num) (by exact_mod_cast hD))
    apply mul_nonneg hfactor
    linarith

private theorem inverse_tail_mono
    (w0 : Nat) :
    Monotone fun z : Nat =>
      (2 : Rat) - (w0 : Rat) / ((z : Rat) + 1) := by
  intro a b hab
  have haPos : (0 : Rat) < (a : Rat) + 1 := by positivity
  have habRat : (a : Rat) + 1 ≤ (b : Rat) + 1 := by
    exact_mod_cast Nat.add_le_add_right hab 1
  have hinv :
      (1 : Rat) / ((b : Rat) + 1) ≤
        1 / ((a : Rat) + 1) :=
    one_div_le_one_div_of_le haPos habRat
  have hw : (0 : Rat) ≤ w0 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hinv hw
  simpa [div_eq_mul_inv] using
    (sub_le_sub_left hmul (2 : Rat))

theorem rho_mono
    {w0 D : Nat} (hD : 0 < D) :
    Monotone (rho w0 D) := by
  intro a b hab
  by_cases ha : a < w0
  · by_cases hb : b < w0
    · rw [rho, if_pos ha, rho, if_pos hb]
      have hH := harmonic_mono hab
      have hfactor : (0 : Rat) ≤ 4 / D :=
        le_of_lt (div_pos (by norm_num) (by exact_mod_cast hD))
      exact mul_le_mul_of_nonneg_left hH hfactor
    · rw [rho, if_pos ha, rho, if_neg hb]
      have haw0 : a ≤ w0 := (Nat.le_of_lt ha).trans (Nat.le_refl _)
      have hH : harmonic a ≤ harmonic w0 := harmonic_mono haw0
      have hwfrac :
          (w0 : Rat) / ((b : Rat) + 1) ≤ 1 := by
        have hwb : w0 ≤ b := Nat.le_of_not_gt hb
        have hwbRat : (w0 : Rat) ≤ (b : Rat) + 1 := by
          exact_mod_cast (hwb.trans (Nat.le_succ b))
        exact (div_le_one (by positivity : (0 : Rat) < (b : Rat) + 1)).2
          hwbRat
      have hinside :
          harmonic a ≤
            harmonic w0 + 2 -
              (w0 : Rat) / ((b : Rat) + 1) := by
        linarith
      have hfactor : (0 : Rat) ≤ 4 / D :=
        le_of_lt (div_pos (by norm_num) (by exact_mod_cast hD))
      exact mul_le_mul_of_nonneg_left hinside hfactor
  · have hb : ¬ b < w0 := fun hb => ha (hab.trans_lt hb)
    rw [rho, if_neg ha, rho, if_neg hb]
    have htail := inverse_tail_mono w0 hab
    have hinside :
        harmonic w0 + 2 -
              (w0 : Rat) / ((a : Rat) + 1) ≤
          harmonic w0 + 2 -
              (w0 : Rat) / ((b : Rat) + 1) := by
      linarith
    have hfactor : (0 : Rat) ≤ 4 / D :=
      le_of_lt (div_pos (by norm_num) (by exact_mod_cast hD))
    exact mul_le_mul_of_nonneg_left hinside hfactor

theorem rho_le_one_twentieth
    {w0 D : Nat} (hD : 0 < D)
    (hsize :
      (80 : Rat) * (harmonic w0 + 2) ≤ D)
    (z : Nat) :
    rho w0 D z ≤ (1 : Rat) / 20 := by
  have hinner :
      (if z < w0 then harmonic z
        else harmonic w0 + 2 -
          (w0 : Rat) / ((z : Rat) + 1)) ≤
        harmonic w0 + 2 := by
    by_cases hz : z < w0
    · rw [if_pos hz]
      have hH : harmonic z ≤ harmonic w0 :=
        harmonic_mono (Nat.le_of_lt hz)
      linarith
    · rw [if_neg hz]
      have hfrac :
          (0 : Rat) ≤ (w0 : Rat) / ((z : Rat) + 1) := by
        positivity
      linarith
  rw [rho]
  split_ifs with hz
  · have hfactor : (0 : Rat) ≤ 4 / D :=
      le_of_lt (div_pos (by norm_num) (by exact_mod_cast hD))
    have hmain :=
      mul_le_mul_of_nonneg_left hinner hfactor
    simp only [hz, if_pos] at hmain
    have hDpos : (0 : Rat) < D := by exact_mod_cast hD
    have hscaled :
        4 / (D : Rat) * (harmonic w0 + 2) ≤
          (1 : Rat) / 20 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hDpos]
      norm_num at hsize ⊢
      linarith
    exact hmain.trans hscaled
  · have hfactor : (0 : Rat) ≤ 4 / D :=
      le_of_lt (div_pos (by norm_num) (by exact_mod_cast hD))
    have hmain :=
      mul_le_mul_of_nonneg_left hinner hfactor
    simp only [hz, if_neg] at hmain
    have hDpos : (0 : Rat) < D := by exact_mod_cast hD
    have hscaled :
        4 / (D : Rat) * (harmonic w0 + 2) ≤
          (1 : Rat) / 20 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hDpos]
      norm_num at hsize ⊢
      linarith
    exact hmain.trans hscaled

theorem real_log_nat_le_two_natLog
    {n cap : Nat} (hn : 0 < n) (hcap : 1 < cap)
    (hncap : n ≤ cap) :
    Real.log (n : Real) ≤ 2 * (Nat.log 2 cap : Real) := by
  let L := Nat.log 2 cap
  have hLpos : 0 < L := Nat.log_pos (by decide : 1 < 2) hcap
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hcapR : (0 : Real) < cap := by positivity
  have hncapR : (n : Real) ≤ cap := by exact_mod_cast hncap
  have hlog :
      Real.log (n : Real) ≤ Real.log (cap : Real) :=
    Real.log_le_log hnR hncapR
  have hpow : cap < 2 ^ (L + 1) := by
    simpa [L, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) cap
  have hpowR : (cap : Real) ≤ ((2 ^ (L + 1) : Nat) : Real) := by
    exact_mod_cast hpow.le
  have hlogPow :
      Real.log (cap : Real) ≤
        Real.log (((2 ^ (L + 1) : Nat) : Real)) :=
    Real.log_le_log hcapR hpowR
  have hcast :
      (((2 ^ (L + 1) : Nat) : Real)) =
        (2 : Real) ^ (L + 1) := by norm_num
  rw [hcast, Real.log_pow] at hlogPow
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h :=
      Real.log_le_sub_one_of_pos
        (x := (2 : Real)) (by norm_num)
    norm_num at h
    exact h
  have hcoef :
      (((L + 1 : Nat) : Real)) ≤ 2 * (L : Real) := by
    exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  calc
    Real.log (n : Real) ≤ Real.log (cap : Real) := hlog
    _ ≤ (((L + 1 : Nat) : Real)) * Real.log 2 := hlogPow
    _ ≤ (((L + 1 : Nat) : Real)) * 1 :=
      mul_le_mul_of_nonneg_left hlogTwo (by positivity)
    _ ≤ 2 * (L : Real) := by simpa using hcoef

theorem harmonic_le_one_add_two_natLog
    {w0 cap : Nat} (hw0 : 0 < w0) (hcap : 1 < cap)
    (hw0cap : w0 ≤ cap) :
    harmonic w0 ≤
      (1 : Rat) + 2 * (Nat.log 2 cap : Nat) := by
  have hHreal := harmonic_le_one_add_log w0
  have hlog := real_log_nat_le_two_natLog hw0 hcap hw0cap
  have hreal :
      ((harmonic w0 : Rat) : Real) ≤
        ((1 : Rat) + 2 * (Nat.log 2 cap : Nat) : Rat) := by
    push_cast
    linarith
  exact_mod_cast hreal

/-- The denominator used throughout Section 5 is large enough to package
`rho` as a bounded source contribution. -/
theorem source_denominator_size
    {w0 cap ell0 : Nat}
    (hw0 : 0 < w0) (hcap : 1 < cap) (hw0cap : w0 ≤ cap)
    (hell0 : 0 < ell0) :
    (80 : Rat) * (harmonic w0 + 2) ≤
      (16 * (20 * ell0) * (Nat.log 2 cap + 1) : Nat) := by
  let L := Nat.log 2 cap
  have hH :
      harmonic w0 ≤ (1 : Rat) + 2 * L :=
    harmonic_le_one_add_two_natLog hw0 hcap hw0cap
  have hn :
      80 * (3 + 2 * L) ≤
        16 * (20 * ell0) * (L + 1) := by
    have hell : 1 ≤ ell0 := hell0
    nlinarith
  have hnRat :
      (80 : Rat) * (3 + 2 * L) ≤
        (16 * (20 * ell0) * (L + 1) : Nat) := by
    exact_mod_cast hn
  dsimp [L] at hH hnRat ⊢
  nlinarith

/-- The sharper endpoint bound used in journal Claim 5.10.  The displayed
source denominator contains the factor `20 * ell0`; retaining it gives the
paper's `1 / (28 ell0)` charge for an edge leaving a dense block. -/
theorem rho_le_one_div_twentyEight_mul
    {w0 cap ell0 : Nat}
    (hw0 : 0 < w0) (hcap : 1 < cap) (hw0cap : w0 ≤ cap)
    (hell0 : 0 < ell0) (z : Nat) :
    rho w0
        (16 * (20 * ell0) * (Nat.log 2 cap + 1)) z ≤
      (1 : Rat) / (28 * ell0) := by
  let L := Nat.log 2 cap
  let D := 16 * (20 * ell0) * (L + 1)
  have hL : 0 < L := Nat.log_pos (by decide : 1 < 2) hcap
  have hH :
      harmonic w0 ≤ (1 : Rat) + 2 * L :=
    harmonic_le_one_add_two_natLog hw0 hcap hw0cap
  have hinner :
      (if z < w0 then harmonic z
        else harmonic w0 + 2 -
          (w0 : Rat) / ((z : Rat) + 1)) ≤
        harmonic w0 + 2 := by
    by_cases hz : z < w0
    · rw [if_pos hz]
      have := harmonic_mono (Nat.le_of_lt hz)
      linarith
    · rw [if_neg hz]
      have hfrac :
          (0 : Rat) ≤ (w0 : Rat) / ((z : Rat) + 1) := by
        positivity
      linarith
  have hnumeric :
      (28 : Rat) * ell0 * 4 * (harmonic w0 + 2) ≤ D := by
    have hLnat : 1 ≤ L := hL
    have hn :
        28 * ell0 * 4 * (3 + 2 * L) ≤
          16 * (20 * ell0) * (L + 1) := by
      nlinarith
    have hnRat :
        (28 : Rat) * ell0 * 4 * (3 + 2 * L) ≤ D := by
      exact_mod_cast hn
    dsimp [D, L] at hnRat ⊢
    nlinarith
  have hDpos : (0 : Rat) < D := by
    dsimp [D]
    positivity
  have hscaled :
      4 / (D : Rat) * (harmonic w0 + 2) ≤
        (1 : Rat) / (28 * ell0) := by
    rw [div_mul_eq_mul_div,
      div_le_div_iff₀ hDpos (by positivity : (0 : Rat) < 28 * ell0)]
    nlinarith
  rw [rho]
  split_ifs with hz
  · have hmain :
        4 / (D : Rat) * harmonic z ≤
          4 / (D : Rat) * (harmonic w0 + 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [hz] using hinner
      · positivity
    exact hmain.trans hscaled
  · have hmain :
        4 / (D : Rat) *
            (harmonic w0 + 2 -
              (w0 : Rat) / ((z : Rat) + 1)) ≤
          4 / (D : Rat) * (harmonic w0 + 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [hz] using hinner
      · positivity
    exact hmain.trans hscaled

/-- The local charge inequality in the proof of Theorem 5.5.  Here `a` and
`b` are the two inherited pieces of the old boundary, `c` is the new cut,
and `a ≤ b` chooses the smaller side. -/
theorem small_split_charge
    {w0 D a b c z : Nat}
    (hD : 4 ≤ D) (hzEq : z = a + b)
    (hab : a ≤ b) (hsparse : D * c < a)
    (hzSmall : z < w0) :
    (11 : Rat) / 10 * c ≤
      (a : Rat) *
        (rho w0 D z - rho w0 D (a + c)) := by
  have hDpos : 0 < D := by omega
  have haPos : 0 < a := lt_of_le_of_lt (Nat.zero_le (D * c)) hsparse
  have hzPos : 0 < z := by omega
  have hc_lt_b : c < b := by
    have hc_le_Dc : c ≤ D * c := by
      calc
        c = 1 * c := by simp
        _ ≤ D * c := Nat.mul_le_mul_right c (by omega)
    exact lt_of_le_of_lt hc_le_Dc (hsparse.trans_le hab)
  have hchild_lt : a + c < z := by omega
  have hchildSmall : a + c < w0 := hchild_lt.trans hzSmall
  have hharm :
      (((z - (a + c) : Nat) : Rat) / z) ≤
        harmonic z - harmonic (a + c) :=
    harmonic_sub_lower hchild_lt.le hzPos
  have hsub : z - (a + c) = b - c := by omega
  rw [hsub] at hharm
  have hDc_le : D * c ≤ a := hsparse.le
  have hDcZ :
      D * c * z ≤ a * z :=
    Nat.mul_le_mul_right z hDc_le
  have haz :
      a * z ≤ 2 * a * b := by
    rw [hzEq]
    nlinarith [Nat.mul_le_mul_left a hab]
  have h4c : 4 * c ≤ b := by
    calc
      4 * c ≤ D * c := Nat.mul_le_mul_right c hD
      _ ≤ a := hsparse.le
      _ ≤ b := hab
  have h4ac : 4 * a * c ≤ a * b := by
    nlinarith [Nat.mul_le_mul_left a h4c]
  have hbc : b - c + c = b := Nat.sub_add_cancel hc_lt_b.le
  have hpoly :
      11 * D * c * z ≤ 40 * a * (b - c) := by
    nlinarith
  rw [rho, if_pos hzSmall, rho, if_pos hchildSmall]
  have hfactor : (0 : Rat) ≤ 4 / D := by positivity
  have hgap :
      4 / (D : Rat) * (((b - c : Nat) : Rat) / z) ≤
        4 / (D : Rat) *
          (harmonic z - harmonic (a + c)) :=
    mul_le_mul_of_nonneg_left hharm hfactor
  have hpolyRat :
      (11 : Rat) * D * c * z ≤
        40 * a * ((b - c : Nat) : Rat) := by
    exact_mod_cast hpoly
  have hden : (0 : Rat) < 10 * D * z := by positivity
  have hnumeric :
      (11 : Rat) / 10 * c ≤
        (a : Rat) *
          (4 / (D : Rat) *
            (((b - c : Nat) : Rat) / z)) := by
    rw [show (11 : Rat) / 10 * c =
        (11 * D * c * z) / (10 * D * z) by
          field_simp
          <;> ring,
      show (a : Rat) *
          (4 / (D : Rat) * (((b - c : Nat) : Rat) / z)) =
        (40 * a * ((b - c : Nat) : Rat)) / (10 * D * z) by
          field_simp
          <;> ring]
    exact (div_le_div_iff_of_pos_right hden).2 hpolyRat
  rw [mul_sub] at hgap
  exact hnumeric.trans (mul_le_mul_of_nonneg_left hgap (by positivity))

/-- The large-cluster case of Claim 5.6.  The old boundary has size
`z = a + b`; the new boundary of the smaller side has size `a + c`.
The first strict inequality is the sparse-cut condition, and the second is
the truncation at `w0 / 2`, with denominators cleared.  The inverse tail of
`rho` pays the complete `11/10` charge of every newly crossing cut edge. -/
theorem large_split_charge
    {w0 D a b c z : Nat}
    (hD : 4 ≤ D) (hzEq : z = a + b)
    (hab : a ≤ b) (hsparse : D * c < a)
    (hcap : 2 * D * c < w0)
    (hzLarge : w0 ≤ z) (hchildLarge : w0 ≤ a + c) :
    (11 : Rat) / 10 * c ≤
      (a : Rat) *
        (rho w0 D z - rho w0 D (a + c)) := by
  have hDpos : 0 < D := by omega
  have haPos : 0 < a := lt_of_le_of_lt (Nat.zero_le (D * c)) hsparse
  have hbPos : 0 < b := haPos.trans_le hab
  have hc_lt_b : c < b := by
    have hc_le_Dc : c ≤ D * c := by
      calc
        c = 1 * c := by simp
        _ ≤ D * c := Nat.mul_le_mul_right c (by omega)
    exact lt_of_le_of_lt hc_le_Dc (hsparse.trans_le hab)
  have hchild_lt : a + c < z := by omega
  by_cases hc : c = 0
  · subst c
    simp only [Nat.cast_zero, mul_zero, zero_le]
    exact mul_nonneg (by positivity)
      (sub_nonneg.mpr (rho_mono hDpos hchild_lt.le))
  have hcPos : 0 < c := Nat.pos_of_ne_zero hc
  have h4c_lt_a : 4 * c < a := by
    exact lt_of_le_of_lt (Nat.mul_le_mul_right c hD) hsparse
  have htwo_child : 2 * (a + c + 1) ≤ 3 * a := by omega
  have hz_bound : z + 1 ≤ 3 * b := by omega
  have hthree_b : 3 * b ≤ 4 * (b - c) := by omega
  have hmulOne :
      2 * (a + c + 1) * (z + 1) ≤
        3 * a * (3 * b) :=
    Nat.mul_le_mul htwo_child hz_bound
  have hmulTwo :
      3 * a * (3 * b) ≤
        3 * a * (4 * (b - c)) :=
    Nat.mul_le_mul_left (3 * a) hthree_b
  have hratioNat :
      (a + c + 1) * (z + 1) ≤
        6 * a * (b - c) := by
    nlinarith [hmulOne.trans hmulTwo]
  have hratioRat :
      (1 : Rat) / 6 ≤
        (a : Rat) * ((b - c : Nat) : Rat) /
          (((a + c : Nat) : Rat) + 1) / ((z : Rat) + 1) := by
    have hratioCast :
        (((a + c + 1) * (z + 1) : Nat) : Rat) ≤
          ((6 * a * (b - c) : Nat) : Rat) := by
      exact_mod_cast hratioNat
    have hleftPos : (0 : Rat) < ((a + c : Nat) : Rat) + 1 := by
      positivity
    have hzOnePos : (0 : Rat) < (z : Rat) + 1 := by positivity
    rw [div_div]
    apply (le_div_iff₀ (mul_pos hleftPos hzOnePos)).2
    push_cast at hratioCast
    calc
      (1 : Rat) / 6 *
          ((((a + c : Nat) : Rat) + 1) * ((z : Rat) + 1)) ≤
          (1 / 6) * (6 * (a : Rat) * ((b - c : Nat) : Rat)) :=
        mul_le_mul_of_nonneg_left (by simpa using hratioCast) (by norm_num)
      _ = (a : Rat) * ((b - c : Nat) : Rat) := by ring
  have hscale : (0 : Rat) ≤ 4 * w0 / D := by positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hratioRat hscale
  have hcapNat : 33 * D * c ≤ 20 * w0 := by
    nlinarith
  have hcapRat :
      (11 : Rat) / 10 * c ≤
        (2 : Rat) * w0 / (3 * D) := by
    have hcapCast :
        (33 : Rat) * D * c ≤ 20 * w0 := by
      exact_mod_cast hcapNat
    have hden : (0 : Rat) < 30 * D := by positivity
    rw [show (11 : Rat) / 10 * c =
        (33 * D * c) / (30 * D) by
          field_simp
          ring,
      show (2 : Rat) * w0 / (3 * D) =
        (20 * w0) / (30 * D) by
          field_simp
          ring]
    exact (div_le_div_iff_of_pos_right hden).2 hcapCast
  have hlower :
      (2 : Rat) * w0 / (3 * D) ≤
        (4 * w0 / (D : Rat)) *
          ((a : Rat) * ((b - c : Nat) : Rat) /
            (((a + c : Nat) : Rat) + 1) / ((z : Rat) + 1)) := by
    calc
      (2 : Rat) * w0 / (3 * D) =
          (4 * w0 / (D : Rat)) * ((1 : Rat) / 6) := by
            field_simp
            ring
      _ ≤ _ := hscaled
  rw [rho, if_neg (Nat.not_lt.mpr hzLarge),
    rho, if_neg (Nat.not_lt.mpr hchildLarge)]
  apply hcapRat.trans
  apply hlower.trans_eq
  have hzCast :
      ((z - (a + c) : Nat) : Rat) =
        (z : Rat) - (a + c : Nat) := by
    rw [Nat.cast_sub hchild_lt.le]
  have hsub : z - (a + c) = b - c := by omega
  rw [← hsub, hzCast]
  field_simp
  ring

/-- The threshold-crossing case in Claim 5.6: the parent is large but the
chosen child becomes small.  The unit jump built into the inverse tail pays
more than the complete new-edge charge. -/
theorem large_to_small_split_charge
    {w0 D a c z : Nat}
    (hD : 4 ≤ D) (hsparse : D * c < a)
    (hzLarge : w0 ≤ z) (hchildSmall : a + c < w0) :
    (11 : Rat) / 10 * c ≤
      (a : Rat) *
        (rho w0 D z - rho w0 D (a + c)) := by
  have hDpos : 0 < D := by omega
  have hchild_le : a + c ≤ w0 := hchildSmall.le
  have hH : harmonic (a + c) ≤ harmonic w0 :=
    harmonic_mono hchild_le
  have hfrac :
      (w0 : Rat) / ((z : Rat) + 1) ≤ 1 := by
    have hwz : (w0 : Rat) ≤ (z : Rat) + 1 := by
      exact_mod_cast hzLarge.trans (Nat.le_succ z)
    exact (div_le_one (by positivity)).2 hwz
  have hinside :
      (1 : Rat) ≤
        harmonic w0 + 2 -
            (w0 : Rat) / ((z : Rat) + 1) -
          harmonic (a + c) := by
    linarith
  have hfactor : (0 : Rat) ≤ 4 / D := by positivity
  have hgap :
      (4 : Rat) / D ≤
        rho w0 D z - rho w0 D (a + c) := by
    rw [rho, if_neg (Nat.not_lt.mpr hzLarge),
      rho, if_pos hchildSmall]
    have := mul_le_mul_of_nonneg_left hinside hfactor
    linarith
  have hsparseRat : (D : Rat) * c ≤ a := by
    exact_mod_cast hsparse.le
  have hpay :
      (11 : Rat) / 10 * c ≤ (a : Rat) * (4 / D) := by
    have hDpositive : (0 : Rat) < D := by exact_mod_cast hDpos
    calc
      (11 : Rat) / 10 * c ≤ (4 * a) / D := by
        apply (le_div_iff₀ hDpositive).2
        nlinarith
      _ = (a : Rat) * (4 / D) := by ring
  exact hpay.trans (mul_le_mul_of_nonneg_left hgap (by positivity))

/-- Package the basic properties once the numerical upper bound has been
proved.  The upper-bound theorem below supplies the final field at the source
parameters. -/
noncomputable def boundedContributionOfUpper
    (w0 D : Nat) (hD : 0 < D)
    (hupper : ∀ z, rho w0 D z ≤ (1 : Rat) / 20) :
    BoundedContribution where
  rho := rho w0 D
  nonnegative := rho_nonnegative hD
  monotone := rho_mono hD
  upper := hupper

noncomputable def boundedContribution
    (w0 D : Nat) (hD : 0 < D)
    (hsize : (80 : Rat) * (harmonic w0 + 2) ≤ D) :
    BoundedContribution :=
  boundedContributionOfUpper w0 D hD
    (rho_le_one_twentieth hD hsize)

noncomputable def sourceBoundedContribution
    (w0 cap ell0 : Nat)
    (hw0 : 0 < w0) (hcap : 1 < cap) (hw0cap : w0 ≤ cap)
    (hell0 : 0 < ell0) :
    BoundedContribution :=
  let D := 16 * (20 * ell0) * (Nat.log 2 cap + 1)
  boundedContribution w0 D (by
    dsimp [D]
    positivity) (source_denominator_size hw0 hcap hw0cap hell0)

end ChekuriChuzhoySection5Rho
end SimpleGraph

end Lax17Proofs
