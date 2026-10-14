import Mathlib.Tactic
import Lax457868Proofs.SamplerLocalProbability

/-!
Finite paired-swap counting for epsilon nets in set systems with linear
shatter growth. The sample space is represented by finite functions and all
probability bounds are cross-multiplied cardinality inequalities.
-/

namespace Lax457868Proofs.SamplerEpsilonNet

open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerUniformDraws
open Lax457868Proofs.SamplerLocalProbability

variable {α : Type*} [DecidableEq α]

/-- The ordered pairs of draws used by the double-sampling argument. -/
abbrev PairTape (X : Finset α) (s : ℕ) :=
  Fin s → ({a // a ∈ X} × {a // a ∈ X})

/-- First tape after swapping the two entries in each selected coordinate. -/
def swappedFirst {X : Finset α} {s : ℕ} (pairs : PairTape X s)
    (swaps : Fin s → Bool) : Tape X s :=
  fun i => if swaps i then (pairs i).2 else (pairs i).1

/-- Second tape after the same coordinate-wise swaps. -/
def swappedSecond {X : Finset α} {s : ℕ} (pairs : PairTape X s)
    (swaps : Fin s → Bool) : Tape X s :=
  fun i => if swaps i then (pairs i).1 else (pairs i).2

/-- Positions at which exactly one member of a paired draw lies in `D`. -/
def xorPositions {X : Finset α} {s : ℕ} (pairs : PairTape X s)
    (D : Finset α) : Finset (Fin s) :=
  Finset.univ.filter fun i => ((pairs i).1.val ∈ D) ≠ ((pairs i).2.val ∈ D)

/-- Number of coordinates of a tape that hit a set. -/
def hitCount (D : Finset α) {X : Finset α} {s : ℕ}
    (tape : Tape X s) : ℕ :=
  (Finset.univ.filter fun i => (tape i).val ∈ D).card

/-- A swap assignment makes the first tape miss `D` and the second hit it at
least `q` times. -/
def swapGood (D : Finset α) {X : Finset α} {s : ℕ} (q : ℕ)
    (pairs : PairTape X s) (swaps : Fin s → Bool) : Prop :=
  Misses D (swappedFirst pairs swaps) ∧
    q ≤ hitCount D (swappedSecond pairs swaps)

/-- The distinct ground elements appearing among the `2s` paired draws. -/
def pairSupport {X : Finset α} {s : ℕ} (pairs : PairTape X s) : Finset α :=
  (Finset.univ.image fun i => (pairs i).1.val) ∪
    (Finset.univ.image fun i => (pairs i).2.val)

/-- The support of a paired tape contains at most `2s` distinct elements. -/
lemma pairSupport_card_le {X : Finset α} {s : ℕ} (pairs : PairTape X s) :
    (pairSupport pairs).card ≤ 2 * s := by
  unfold pairSupport
  calc
    (Finset.univ.image (fun i => (pairs i).1.val) ∪
        Finset.univ.image (fun i => (pairs i).2.val)).card ≤
      (Finset.univ.image (fun i => (pairs i).1.val)).card +
        (Finset.univ.image (fun i => (pairs i).2.val)).card := Finset.card_union_le _ _
    _ ≤ Finset.univ.card + Finset.univ.card := by
      exact Nat.add_le_add
        (Finset.card_image_le (s := Finset.univ)
          (f := fun i => (pairs i).1.val))
        (Finset.card_image_le (s := Finset.univ)
          (f := fun i => (pairs i).2.val))
    _ = s + s := by simp
    _ = 2 * s := by omega

/-- The finite event that some range in a family is missed by the first
swapped tape while the second hits it at least `q` times. -/
def familySwapGood (F : Finset (Finset α)) {X : Finset α} {s : ℕ}
    (q : ℕ) (pairs : PairTape X s) (swaps : Fin s → Bool) : Prop :=
  ∃ D ∈ F, swapGood D q pairs swaps

noncomputable instance familySwapGoodDecidable
    (F : Finset (Finset α)) {X : Finset α} {s : ℕ}
    (q : ℕ) (pairs : PairTape X s) :
    DecidablePred (familySwapGood F q pairs) := fun _ => Classical.propDecidable _

/-- Swapping bits only inspect memberships on `pairSupport`; sets with the
same trace there define identical local events. -/
lemma swapGood_of_trace_eq
    {X : Finset α} {s q : ℕ} (pairs : PairTape X s)
    (D E : Finset α) (swaps : Fin s → Bool)
    (htrace : D ∩ pairSupport pairs = E ∩ pairSupport pairs) :
    swapGood D q pairs swaps → swapGood E q pairs swaps := by
  classical
  have hmem (a : α) (ha : a ∈ pairSupport pairs) : a ∈ D ↔ a ∈ E := by
    have h := congrArg (fun T : Finset α => a ∈ T) htrace
    simpa [Finset.mem_inter, ha] using h
  rintro ⟨hmiss, hhit⟩
  refine ⟨?_, ?_⟩
  · intro i
    have hi : (swappedFirst pairs swaps i).val ∈ pairSupport pairs := by
      by_cases hs : swaps i <;> simp [swappedFirst, pairSupport, hs]
    exact (hmem _ hi).not.mp (hmiss i)
  · have hcounts : hitCount D (swappedSecond pairs swaps) =
        hitCount E (swappedSecond pairs swaps) := by
      unfold hitCount
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hi : (swappedSecond pairs swaps i).val ∈ pairSupport pairs := by
        by_cases hs : swaps i <;> simp [swappedSecond, pairSupport, hs]
      exact hmem _ hi
    rw [← hcounts]
    exact hhit

/-- Cardinality of a finite union is bounded by the sum of its member
cardinalities. -/
lemma card_biUnion_le_sum {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (S : Finset γ) (G : γ → Finset δ) :
    (S.biUnion G).card ≤ ∑ x ∈ S, (G x).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.biUnion_insert]
      calc
        (G a ∪ S.biUnion G).card ≤ (G a).card + (S.biUnion G).card :=
          Finset.card_union_le _ _
        _ ≤ (G a).card + ∑ x ∈ S, (G x).card := Nat.add_le_add_left ih _
        _ = ∑ x ∈ insert a S, (G x).card := by simp [ha]

noncomputable instance swapGoodDecidable
    {X : Finset α} {s : ℕ} (D : Finset α) (q : ℕ)
    (pairs : PairTape X s) : DecidablePred (swapGood D q pairs) :=
  fun _ => Classical.propDecidable _

/-- If the first tape misses `D`, the second tape hits at exactly the positions
where a pair has exactly one entry in `D`. -/
lemma hitCount_swappedSecond_eq_xorPositions
    {X : Finset α} {s : ℕ} (D : Finset α) (pairs : PairTape X s)
    (swaps : Fin s → Bool)
    (hmiss : Misses D (swappedFirst pairs swaps)) :
    hitCount D (swappedSecond pairs swaps) = (xorPositions pairs D).card := by
  classical
  unfold hitCount xorPositions
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hsecond
    have hfirst : (swappedFirst pairs swaps i).val ∉ D := hmiss i
    by_cases hswap : swaps i
    · have ha : (pairs i).1.val ∈ D := by
        simpa [swappedSecond, hswap] using hsecond
      have hb : (pairs i).2.val ∉ D := by
        simpa [swappedFirst, hswap] using hfirst
      simp [ha, hb]
    · have ha : (pairs i).1.val ∉ D := by
        simpa [swappedFirst, hswap] using hfirst
      have hb : (pairs i).2.val ∈ D := by
        simpa [swappedSecond, hswap] using hsecond
      simp [ha, hb]
  · intro hx
    by_cases ha : (pairs i).1.val ∈ D
    · by_cases hb : (pairs i).2.val ∈ D
      · simp [ha, hb] at hx
      · by_cases hswap : swaps i
        · simp [swappedSecond, hswap, ha]
        · have hf := hmiss i
          simp [swappedFirst, hswap, ha] at hf
    · by_cases hb : (pairs i).2.val ∈ D
      · by_cases hswap : swaps i
        · have hf := hmiss i
          simp [swappedFirst, hswap, hb] at hf
        · simp [swappedSecond, hswap, hb]
      · simp [ha, hb] at hx

/-- On every xor position, a successful first-miss assignment has its swap bit
forced by the first entry's membership bit. -/
lemma swapBit_forced_on_xor
    {X : Finset α} {s : ℕ} (D : Finset α) (pairs : PairTape X s)
    (swaps : Fin s → Bool) (hmiss : Misses D (swappedFirst pairs swaps))
    {i : Fin s} (hi : i ∈ xorPositions pairs D) :
    swaps i = decide ((pairs i).1.val ∈ D) := by
  classical
  by_cases ha : (pairs i).1.val ∈ D
  · by_cases hb : (pairs i).2.val ∈ D
    · simp [xorPositions, ha, hb] at hi
    · have hxor : i ∈ xorPositions pairs D := by
        simp [xorPositions, ha, hb]
      by_cases hswap : swaps i
      · simp [hswap, ha]
      · have hf := hmiss i
        simp [swappedFirst, hswap, ha] at hf
  · by_cases hb : (pairs i).2.val ∈ D
    · have hxor : i ∈ xorPositions pairs D := by
        simp [xorPositions, ha, hb]
      by_cases hswap : swaps i
      · have hf := hmiss i
        simp [swappedFirst, hswap, hb] at hf
      · simp [hswap, ha]
    · simp [xorPositions, ha, hb] at hi

/-- For fixed paired draws and one range, at most `2^(s-q)` swap assignments
make the first tape miss while the second hits at least `q` times. -/
lemma card_swapGood_le
    {X : Finset α} {s q : ℕ} (hq : q ≤ s) (D : Finset α)
    (pairs : PairTape X s) :
    Fintype.card {swaps : Fin s → Bool // swapGood D q pairs swaps} ≤
      2 ^ (s - q) := by
  classical
  let forced := xorPositions pairs D
  let free := Finset.univ \ forced
  by_cases hcard0 : Fintype.card
      {swaps : Fin s → Bool // swapGood D q pairs swaps} = 0
  · simp [hcard0]
  · have hnonempty : Nonempty
        {swaps : Fin s → Bool // swapGood D q pairs swaps} :=
      Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard0)
    rcases hnonempty with ⟨w⟩
    have hforced : q ≤ forced.card := by
      have h := w.property.2
      rw [hitCount_swappedSecond_eq_xorPositions D pairs w.1 w.property.1] at h
      exact h
    let restrict :
        {swaps : Fin s → Bool // swapGood D q pairs swaps} →
          ({i : Fin s // i ∈ free} → Bool) :=
      fun swaps i => swaps.1 i.1
    have hinj : Function.Injective restrict := by
      intro a b hab
      apply Subtype.ext
      funext i
      by_cases hi : i ∈ forced
      · have ha := swapBit_forced_on_xor D pairs a.1 a.2.1 hi
        have hb := swapBit_forced_on_xor D pairs b.1 b.2.1 hi
        rw [ha, hb]
      · have hfree : i ∈ free := by simp [free, hi]
        have := congrFun hab ⟨i, hfree⟩
        exact this
    have hcard := Fintype.card_le_of_injective restrict hinj
    have hfreeCard : free.card = s - forced.card := by
      simp [free, Finset.card_sdiff_of_subset forced.subset_univ]
    have hcardTarget :
        Fintype.card ({i : Fin s // i ∈ free} → Bool) = 2 ^ free.card := by
      simp [Fintype.card_fun]
    calc
      Fintype.card {swaps : Fin s → Bool // swapGood D q pairs swaps} ≤
          Fintype.card ({i : Fin s // i ∈ free} → Bool) := hcard
      _ = 2 ^ free.card := hcardTarget
      _ = 2 ^ (s - forced.card) := by rw [hfreeCard]
      _ ≤ 2 ^ (s - q) := Nat.pow_le_pow_right (by omega)
        (Nat.sub_le_sub_left hforced s)

/-- Replacing a range by its trace on the paired sample leaves the family
swap event unchanged. -/
lemma familySwapGood_iff_traceImage
    {X : Finset α} {s q : ℕ} (F : Finset (Finset α))
    (pairs : PairTape X s) (swaps : Fin s → Bool) :
    familySwapGood F q pairs swaps ↔
      familySwapGood (F.image fun D => D ∩ pairSupport pairs) q pairs swaps := by
  classical
  constructor
  · rintro ⟨D, hD, hgood⟩
    refine ⟨D ∩ pairSupport pairs, Finset.mem_image.mpr ⟨D, hD, rfl⟩, ?_⟩
    apply swapGood_of_trace_eq pairs D (D ∩ pairSupport pairs) swaps ?_ hgood
    simp [Finset.inter_assoc]
  · rintro ⟨D, hD, hgood⟩
    rcases Finset.mem_image.mp hD with ⟨E, hE, rfl⟩
    refine ⟨E, hE, ?_⟩
    apply swapGood_of_trace_eq pairs (E ∩ pairSupport pairs) E swaps ?_ hgood
    simp [Finset.inter_assoc]

/-- Swap assignments with a family witness are bounded by summing the
single-range fiber bound. -/
lemma card_familySwapGood_le
    {X : Finset α} {s q : ℕ} (hq : q ≤ s)
    (F : Finset (Finset α)) (pairs : PairTape X s) :
    (Finset.univ.filter fun swaps : Fin s → Bool =>
      familySwapGood F q pairs swaps).card ≤
        F.card * 2 ^ (s - q) := by
  classical
  let goodBits := fun D : Finset α =>
    (Finset.univ.filter fun swaps : Fin s → Bool => swapGood D q pairs swaps)
  let allGood := Finset.univ.filter fun swaps : Fin s → Bool =>
    familySwapGood F q pairs swaps
  have hsubset : allGood ⊆ F.biUnion goodBits := by
    intro swaps hswaps
    rcases Finset.mem_filter.mp hswaps with ⟨_, ⟨D, hD, hgood⟩⟩
    exact Finset.mem_biUnion.mpr ⟨D, hD, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood⟩⟩
  have hfiber (D : Finset α) : (goodBits D).card ≤ 2 ^ (s - q) := by
    have hcount : (goodBits D).card =
        Fintype.card {swaps : Fin s → Bool // swapGood D q pairs swaps} := by
      symm
      exact Fintype.card_ofFinset (goodBits D) (by
        intro swaps
        change swaps ∈ goodBits D ↔ swapGood D q pairs swaps
        simp [goodBits])
    rw [hcount]
    exact card_swapGood_le hq D pairs
  have hsum : (∑ D ∈ F, (goodBits D).card) ≤
      ∑ D ∈ F, 2 ^ (s - q) := by
    apply Finset.sum_le_sum
    intro D hD
    exact hfiber D
  calc
    allGood.card ≤ (F.biUnion goodBits).card := Finset.card_le_card hsubset
    _ ≤ ∑ D ∈ F, (goodBits D).card := card_biUnion_le_sum F goodBits
    _ ≤ ∑ D ∈ F, 2 ^ (s - q) := hsum
    _ = F.card * 2 ^ (s - q) := by simp [Finset.sum_const]

/-- If the family has at most `c |Y|` traces on every finite `Y`, then for
fixed paired draws the number of swap assignments witnessing a missed
majority range is at most `2 c s 2^(s-q)`. -/
lemma card_familySwapGood_le_of_traceBound
    {X : Finset α} {s q c : ℕ} (hq : q ≤ s)
    (F : Finset (Finset α)) (pairs : PairTape X s)
    (htrace : ∀ Y : Finset α,
      (F.image fun D => D ∩ Y).card ≤ c * Y.card) :
    (Finset.univ.filter fun swaps : Fin s → Bool =>
      familySwapGood F q pairs swaps).card ≤
        (2 * c * s) * 2 ^ (s - q) := by
  classical
  let traced := F.image fun D => D ∩ pairSupport pairs
  have hevents :
      Finset.univ.filter (fun swaps : Fin s → Bool =>
        familySwapGood F q pairs swaps) =
      Finset.univ.filter (fun swaps : Fin s → Bool =>
        familySwapGood traced q pairs swaps) := by
    apply Finset.filter_congr
    intro swaps _
    exact familySwapGood_iff_traceImage F pairs swaps
  rw [hevents]
  have hbase := card_familySwapGood_le hq traced pairs
  have htraced : traced.card ≤ c * (2 * s) := by
    dsimp [traced]
    calc
      (F.image fun D => D ∩ pairSupport pairs).card ≤
          c * (pairSupport pairs).card := htrace (pairSupport pairs)
      _ ≤ c * (2 * s) := Nat.mul_le_mul_left c (pairSupport_card_le pairs)
  calc
    (Finset.univ.filter (fun swaps : Fin s → Bool =>
      familySwapGood traced q pairs swaps)).card ≤ traced.card * 2 ^ (s - q) := hbase
    _ ≤ (2 * c * s) * 2 ^ (s - q) := by
      calc
        traced.card * 2 ^ (s - q) ≤
            (c * (2 * s)) * 2 ^ (s - q) :=
          Nat.mul_le_mul_right _ htraced
        _ = (2 * c * s) * 2 ^ (s - q) := by ring

end Lax457868Proofs.SamplerEpsilonNet
