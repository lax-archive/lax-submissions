import Lax235315Proofs.Construction.TracePartitions
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-!
Finite counting form of the sampling estimate in Section 3.4 of the paper.
-/

namespace Lax235315Proofs.Construction.Sampling

open Finset
open Lax235315Proofs.Construction.TracePartitions

private theorem factor_le {a x i : ℕ} (ha : 0 < a) (hx : x ≤ a)
    (hi : i < a - x) :
    ((↑(a - x - i) : ℝ) / (↑(a - i) : ℝ)) ≤
      (↑(a - x) : ℝ) / (a : ℝ) := by
  have hixa : i ≤ a := by omega
  have hix : x + i ≤ a := by omega
  rw [Nat.sub_sub, Nat.cast_sub hix, Nat.cast_sub hixa, Nat.cast_sub hx]
  push_cast
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have haipos : (0 : ℝ) < (a : ℝ) - i := by
    exact_mod_cast (Nat.sub_pos_of_lt (show i < a by omega))
  rw [div_le_div_iff₀ haipos hapos]
  nlinarith [show (0 : ℝ) ≤ (x : ℝ) * i by positivity]

private theorem descFactorial_ratio_le_pow {a x s : ℕ} (ha : 0 < a)
    (hx : x ≤ a) (hs : s ≤ a - x) :
    (↑((a - x).descFactorial s) : ℝ) /
        (↑(a.descFactorial s) : ℝ) ≤
      ((↑(a - x) : ℝ) / (a : ℝ)) ^ s := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  push_cast
  rw [← Finset.prod_div_distrib]
  calc
    ∏ i ∈ Finset.range s,
        ((↑(a - x - i) : ℝ) / (↑(a - i) : ℝ)) ≤
      ∏ _i ∈ Finset.range s,
        ((↑(a - x) : ℝ) / (a : ℝ)) := by
          apply Finset.prod_le_prod
          · intro i hi
            positivity
          · intro i hi
            apply factor_le ha hx
            have := Finset.mem_range.1 hi
            omega
    _ = ((↑(a - x) : ℝ) / (a : ℝ)) ^ s := by
      rw [Finset.prod_const, Finset.card_range]

private theorem choose_ratio_eq_descFactorial_ratio {a x s : ℕ}
    (hs : s ≤ a) :
    (↑((a - x).choose s) : ℝ) / (↑(a.choose s) : ℝ) =
      (↑((a - x).descFactorial s) : ℝ) /
        (↑(a.descFactorial s) : ℝ) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hf : (↑s.factorial : ℝ) ≠ 0 := by positivity
  have ha : (↑(a.choose s) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hs))
  field_simp

/-- Hypergeometric avoidance is bounded by the corresponding exponential
estimate. This is the analytic inequality used in Lemma 3.7. -/
theorem choose_ratio_le_exp {a x s : ℕ} (ha : 0 < a) (hx : x ≤ a)
    (hs : s ≤ a) :
    (↑((a - x).choose s) : ℝ) / (↑(a.choose s) : ℝ) ≤
      Real.exp (-((s : ℝ) / a * x)) := by
  by_cases hsx : s ≤ a - x
  · calc
      (↑((a - x).choose s) : ℝ) / (↑(a.choose s) : ℝ) =
          (↑((a - x).descFactorial s) : ℝ) /
            (↑(a.descFactorial s) : ℝ) :=
        choose_ratio_eq_descFactorial_ratio hs
      _ ≤ ((↑(a - x) : ℝ) / (a : ℝ)) ^ s :=
        descFactorial_ratio_le_pow ha hx hsx
      _ = (1 - (x : ℝ) / a) ^ s := by
        congr 1
        rw [Nat.cast_sub hx]
        field_simp
      _ ≤ (Real.exp (-(x : ℝ) / a)) ^ s := by
        apply pow_le_pow_left₀
        · have : (0 : ℝ) ≤ 1 - x / a := by
            rw [sub_nonneg, div_le_one (by exact_mod_cast ha)]
            exact_mod_cast hx
          exact this
        · have hexp := Real.add_one_le_exp (-(x : ℝ) / a)
          calc
            1 - (x : ℝ) / a = -(x : ℝ) / a + 1 := by ring
            _ ≤ Real.exp (-(x : ℝ) / a) := hexp
      _ = Real.exp (-((s : ℝ) / a * x)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  · have hzero : (a - x).choose s = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [hzero, Nat.cast_zero, zero_div]
    exact (Real.exp_pos _).le

/-- Ceiling division supplies at least the requested sampling rate. -/
theorem le_mul_sampleSize {a c : ℕ} (hc : 1 ≤ c) :
    a ≤ 2 * c ^ 2 * sampleSize a c := by
  unfold sampleSize
  have hd : 0 < 2 * c ^ 2 :=
    Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have h := Nat.lt_mul_div_succ (a + 2 * c ^ 2 - 1) hd
  rw [Nat.mul_add] at h
  omega

theorem sampleSize_le_self {a c : ℕ} (hc : 1 ≤ c) (ha : 0 < a) :
    sampleSize a c ≤ a := by
  have hd : 1 < 2 * c ^ 2 := by
    have hc2 : 1 ≤ c ^ 2 := Nat.one_le_pow 2 c (by omega)
    omega
  have hdiv : a / (2 * c ^ 2) < a := Nat.div_lt_self ha hd
  exact (sampleSize_le_div_add_one hc).trans (by omega)

/-- The ceiling sample size and the large symmetric-difference hypothesis
give the exponent `3L` in Lemma 3.7. -/
theorem three_mul_le_sample_rate {a c x L : ℕ}
    (ha : 0 < a) (hc : 1 ≤ c) (hx : 6 * c ^ 2 * L ≤ x) :
    (3 * L : ℝ) ≤ (sampleSize a c : ℝ) / a * x := by
  let d := 2 * c ^ 2
  let s := sampleSize a c
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hceil : a ≤ d * s := by
    simpa [d, s] using le_mul_sampleSize (a := a) hc
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hsratio : (1 : ℝ) / d ≤ (s : ℝ) / a := by
    rw [div_le_div_iff₀ hdR haR]
    exact_mod_cast (by simpa [Nat.mul_comm] using hceil)
  have hxR : (3 * L : ℝ) ≤ (x : ℝ) / d := by
    rw [le_div_iff₀ hdR]
    exact_mod_cast (by
      change 3 * L * (2 * c ^ 2) ≤ x
      calc
        3 * L * (2 * c ^ 2) = 6 * c ^ 2 * L := by ring
        _ ≤ x := hx)
  calc
    (3 * L : ℝ) ≤ (x : ℝ) / d := hxR
    _ = (1 / d) * x := by ring
    _ ≤ ((s : ℝ) / a) * x :=
      mul_le_mul_of_nonneg_right hsratio (by positivity)
    _ = (sampleSize a c : ℝ) / a * x := by rfl

/-- `e^{-3L}` is at most `2^{-3L}`. -/
theorem exp_neg_three_mul_le_half_pow (L : ℕ) :
    Real.exp (-(3 * L : ℝ)) ≤ (1 / 2 : ℝ) ^ (3 * L) := by
  calc
    Real.exp (-(3 * L : ℝ)) = Real.exp (-1) ^ (3 * L) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ ≤ (1 / 2 : ℝ) ^ (3 * L) := by
      exact pow_le_pow_left₀ (Real.exp_pos _).le
        Real.exp_neg_one_lt_half.le _

/-- The finite family of uniformly sampled `s`-subsets of `A`. -/
def samples {α : Type*} [DecidableEq α] (A : Finset α) (s : ℕ) :
    Finset (Finset α) := A.powersetCard s

/-- Samples avoiding `X`. -/
def misses {α : Type*} [DecidableEq α] (A X : Finset α) (s : ℕ) :
    Finset (Finset α) :=
  (samples A s).filter fun W => Disjoint W X

theorem card_samples {α : Type*} [DecidableEq α] (A : Finset α) (s : ℕ) :
    (samples A s).card = A.card.choose s := by
  simp [samples, Finset.card_powersetCard]

theorem card_misses {α : Type*} [DecidableEq α]
    (A X : Finset α) (s : ℕ) (hX : X ⊆ A) :
    (misses A X s).card = (A.card - X.card).choose s := by
  have heq : misses A X s = (A \ X).powersetCard s := by
    ext W
    simp only [misses, samples, Finset.mem_filter,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hWA, hcard⟩, hdisj⟩
      refine ⟨?_, hcard⟩
      intro w hw
      exact Finset.mem_sdiff.mpr
        ⟨hWA hw, fun hwX => Finset.disjoint_left.1 hdisj hw hwX⟩
    · rintro ⟨hWAX, hcard⟩
      refine ⟨⟨fun w hw => (Finset.mem_sdiff.mp (hWAX hw)).1, hcard⟩, ?_⟩
      rw [Finset.disjoint_left]
      intro w hwW hwX
      exact (Finset.mem_sdiff.mp (hWAX hwW)).2 hwX
  rw [heq, Finset.card_powersetCard, Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr hX]

/-- **Lemma 3.7 (finite counting form).** A uniform sample of the paper's
size misses a set of at least `6c²L` elements on at most a `N⁻³` fraction
of the sample space, whenever `|A| ≤ N ≤ 2^L`. -/
theorem uniform_sample_miss_fraction_le {α : Type*} [DecidableEq α]
    {A X : Finset α} {c N L : ℕ}
    (hc : 1 ≤ c) (hA : A.Nonempty) (hX : X ⊆ A)
    (hXcard : 6 * c ^ 2 * L ≤ X.card)
    (hAN : A.card ≤ N) (hNpow : N ≤ 2 ^ L) :
    ((misses A X (sampleSize A.card c)).card : ℝ) /
        (samples A (sampleSize A.card c)).card ≤
      1 / (N : ℝ) ^ 3 := by
  have ha : 0 < A.card := Finset.card_pos.mpr hA
  have hs : sampleSize A.card c ≤ A.card := sampleSize_le_self hc ha
  have hxle : X.card ≤ A.card := Finset.card_le_card hX
  rw [card_misses A X _ hX, card_samples]
  calc
    (↑((A.card - X.card).choose (sampleSize A.card c)) : ℝ) /
        ↑(A.card.choose (sampleSize A.card c)) ≤
        Real.exp (-(((sampleSize A.card c : ℕ) : ℝ) / A.card * X.card)) :=
      choose_ratio_le_exp ha hxle hs
    _ ≤ Real.exp (-(3 * L : ℝ)) := by
      rw [Real.exp_le_exp]
      have := three_mul_le_sample_rate ha hc hXcard
      linarith
    _ ≤ (1 / 2 : ℝ) ^ (3 * L) := exp_neg_three_mul_le_half_pow L
    _ = 1 / ((2 : ℝ) ^ L) ^ 3 := by
      simp [show 3 * L = L * 3 by omega, pow_mul]
    _ ≤ 1 / (N : ℝ) ^ 3 := by
      have hNpos : (0 : ℝ) < N := by
        have : 0 < N := lt_of_lt_of_le ha hAN
        exact_mod_cast this
      have hpowpos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
      apply one_div_le_one_div_of_le
      · positivity
      · exact pow_le_pow_left₀ hNpos.le (by exact_mod_cast hNpow) 3

/-- Symmetric difference for finite sets, kept explicit so the finite sample
count never depends on coercions to `Set`. -/
def finSymmDiff {α : Type*} [DecidableEq α]
    (X Y : Finset α) : Finset α :=
  (X \ Y) ∪ (Y \ X)

theorem finSymmDiff_subset {α : Type*} [DecidableEq α]
    {A X Y : Finset α} (hX : X ⊆ A) (hY : Y ⊆ A) :
    finSymmDiff X Y ⊆ A := by
  intro a ha
  rcases Finset.mem_union.mp ha with ha | ha
  · exact hX (Finset.mem_sdiff.mp ha).1
  · exact hY (Finset.mem_sdiff.mp ha).1

/-- Samples witnessing that one fixed pair of traces is both far apart and
not distinguished. -/
def pairBadSamples {α : Type*} [DecidableEq α]
    (A X Y : Finset α) (c L : ℕ) : Finset (Finset α) :=
  if 6 * c ^ 2 * L ≤ (finSymmDiff X Y).card then
    misses A (finSymmDiff X Y) (sampleSize A.card c)
  else ∅

/-- Union of the bad samples over all ordered pairs in a finite trace
family. Ordered pairs make the union bound slightly looser but simpler. -/
def familyBadSamples {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (R : Finset ι) (F : ι → Finset α) (ground : Finset α)
    (c L : ℕ) : Finset (Finset α) :=
  (R ×ˢ R).biUnion fun p => pairBadSamples ground (F p.1) (F p.2) c L

/-- **Lemma 3.8 (union-bound core).** If `R` indexes traces contained in
`A`, the fraction of samples failing to distinguish a far pair is at most
`|R|²/N³`. -/
theorem family_bad_fraction_le {α ι : Type*}
    [DecidableEq α] [DecidableEq ι]
    {A : Finset α} {R : Finset ι} {F : ι → Finset α}
    {c N L : ℕ}
    (hc : 1 ≤ c) (hA : A.Nonempty)
    (hF : ∀ r ∈ R, F r ⊆ A)
    (hAN : A.card ≤ N) (hNpow : N ≤ 2 ^ L) :
    ((familyBadSamples R F A c L).card : ℝ) /
        (samples A (sampleSize A.card c)).card ≤
      (R.card : ℝ) ^ 2 / (N : ℝ) ^ 3 := by
  let S := samples A (sampleSize A.card c)
  let P := R ×ˢ R
  let bad : ι × ι → Finset (Finset α) := fun p =>
    pairBadSamples A (F p.1) (F p.2) c L
  have ha : 0 < A.card := Finset.card_pos.mpr hA
  have hs : sampleSize A.card c ≤ A.card := sampleSize_le_self hc ha
  have hScard : S.card = A.card.choose (sampleSize A.card c) :=
    card_samples _ _
  have hSpos : (0 : ℝ) < S.card := by
    rw [hScard]
    exact_mod_cast Nat.choose_pos hs
  have hpair : ∀ p ∈ P,
      ((bad p).card : ℝ) / S.card ≤ 1 / (N : ℝ) ^ 3 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    unfold bad pairBadSamples
    split_ifs with hlarge
    · exact uniform_sample_miss_fraction_le hc hA
        (finSymmDiff_subset (hF p.1 hp1) (hF p.2 hp2))
        hlarge hAN hNpow
    · simp
  have hcard : (familyBadSamples R F A c L).card ≤
      ∑ p ∈ P, (bad p).card := by
    unfold familyBadSamples
    exact Finset.card_biUnion_le
  calc
    ((familyBadSamples R F A c L).card : ℝ) / S.card ≤
        (∑ p ∈ P, ((bad p).card : ℝ)) / S.card := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ = ∑ p ∈ P, ((bad p).card : ℝ) / S.card := by
      rw [Finset.sum_div]
    _ ≤ ∑ _p ∈ P, 1 / (N : ℝ) ^ 3 :=
      Finset.sum_le_sum fun p hp => hpair p hp
    _ = (R.card : ℝ) ^ 2 / (N : ℝ) ^ 3 := by
      simp [P, Finset.card_product]
      ring

/-- The numerical last step of Lemma 3.8: at most `c|A|` traces and
`|A|≤N` turn `|R|²/N³` into `c²/N`. -/
theorem family_bad_fraction_le_csq_div {α ι : Type*}
    [DecidableEq α] [DecidableEq ι]
    {A : Finset α} {R : Finset ι} {F : ι → Finset α}
    {c N L : ℕ}
    (hc : 1 ≤ c) (hA : A.Nonempty)
    (hF : ∀ r ∈ R, F r ⊆ A)
    (hRcard : R.card ≤ c * A.card)
    (hAN : A.card ≤ N) (hNpow : N ≤ 2 ^ L) :
    ((familyBadSamples R F A c L).card : ℝ) /
        (samples A (sampleSize A.card c)).card ≤
      (c : ℝ) ^ 2 / N := by
  have hbase := family_bad_fraction_le hc hA hF hAN hNpow
  apply hbase.trans
  have ha : 0 < A.card := Finset.card_pos.mpr hA
  have hNnat : 0 < N := lt_of_lt_of_le ha hAN
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hRN : (R.card : ℝ) ≤ c * N := by
    exact_mod_cast hRcard.trans
      (Nat.mul_le_mul_left c hAN)
  rw [div_le_div_iff₀ (pow_pos hN 3) hN]
  have hsquare : (R.card : ℝ) ^ 2 ≤ ((c : ℝ) * N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hRN 2
  calc
    (R.card : ℝ) ^ 2 * N ≤ ((c : ℝ) * N) ^ 2 * N :=
      mul_le_mul_of_nonneg_right hsquare hN.le
    _ = (c : ℝ) ^ 2 * N ^ 3 := by ring

end Lax235315Proofs.Construction.Sampling
