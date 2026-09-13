import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# A finite lower-tail estimate for the degree-three thinning

The proof of Theorem 5.1 only needs a finite counting argument.  On a
vertex-disjoint family of blue edges, the two endpoint choices give four
equiprobable local assignments and at least one assignment preserves the
edge.  The lemma below is the elementary exponential-moment estimate used in
the later union bound.  It avoids introducing a measure-theory API for a
finite sample space.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51
namespace ThinningConcentration

/-- Normalize one fair bit so that the prescribed value becomes zero. -/
def normalizeBit (expected : Fin 2) : Fin 2 ≃ Fin 2 :=
  Equiv.swap expected 0

@[simp] theorem normalizeBit_eq_zero_iff
    (expected value : Fin 2) :
    normalizeBit expected value = 0 ↔ value = expected := by
  fin_cases expected <;> fin_cases value <;> decide

/-- Package two independently normalized bits into one four-valued
coordinate. -/
def localWordEquiv (expected : Fin 2 → Fin 2) :
    (Fin 2 → Fin 2) ≃ Fin 4 :=
  (Equiv.piCongrRight fun k => normalizeBit (expected k)).trans
    ((finTwoArrowEquiv (Fin 2)).trans finProdFinEquiv)

@[simp] theorem localWordEquiv_eq_zero_iff
    (expected value : Fin 2 → Fin 2) :
    localWordEquiv expected value = 0 ↔
      ∀ k, value k = expected k := by
  constructor
  · intro h
    have hp := congrArg Fin.val h
    change
      ((normalizeBit (expected 1)) (value 1)).val +
          2 * ((normalizeBit (expected 0)) (value 0)).val = 0 at hp
    have hp0 :
        (normalizeBit (expected 0)) (value 0) = 0 := by
      apply Fin.ext
      omega
    have hp1 :
        (normalizeBit (expected 1)) (value 1) = 0 := by
      apply Fin.ext
      omega
    intro k
    fin_cases k
    · exact (normalizeBit_eq_zero_iff _ _).mp
        hp0
    · exact (normalizeBit_eq_zero_iff _ _).mp
        hp1
  · intro h
    have h0 :
        normalizeBit (expected 0) (value 0) = 0 :=
      (normalizeBit_eq_zero_iff _ _).mpr (h 0)
    have h1 :
        normalizeBit (expected 1) (value 1) = 0 :=
      (normalizeBit_eq_zero_iff _ _).mpr (h 1)
    apply Fin.ext
    change
      ((normalizeBit (expected 1)) (value 1)).val +
          2 * ((normalizeBit (expected 0)) (value 0)).val = 0
    simp [h0, h1]

/-- Repackage pairs of independent bits as a word over a four-letter
alphabet. -/
def wordEquiv {n : ℕ} (expected : Fin n × Fin 2 → Fin 2) :
    (Fin n × Fin 2 → Fin 2) ≃ (Fin n → Fin 4) :=
  (Equiv.curry (Fin n) (Fin 2) (Fin 2)).trans
    (Equiv.piCongrRight fun i =>
      localWordEquiv fun k => expected (i, k))

@[simp] theorem wordEquiv_apply_eq_zero_iff
    {n : ℕ} (expected value : Fin n × Fin 2 → Fin 2)
    (i : Fin n) :
    wordEquiv expected value i = 0 ↔
      ∀ k, value (i, k) = expected (i, k) := by
  exact localWordEquiv_eq_zero_iff _ _

/-- Split a finite coordinate type into the range of an injection and its
complement. -/
noncomputable def splitCoordinates
    {A B : Type*} (f : A → B) (hf : Function.Injective f) :
    B ≃ A ⊕ {b : B // b ∉ Set.range f} := by
  classical
  exact
    (Equiv.Set.sumCompl (Set.range f)).symm.trans
      (Equiv.sumCongr (Equiv.ofInjective f hf).symm (Equiv.refl _))

@[simp] theorem splitCoordinates_symm_inl
    {A B : Type*} (f : A → B) (hf : Function.Injective f) (a : A) :
    (splitCoordinates f hf).symm (Sum.inl a) = f a := by
  classical
  simp [splitCoordinates]

/-- Independent coordinates selected by an injection form the first factor
of a function space; two bits per selected object are then packaged as a
four-valued word. -/
noncomputable def independentWordSplit
    {B : Type*} {n : ℕ}
    (slot : Fin n × Fin 2 → B)
    (hslot : Function.Injective slot)
    (expected : Fin n × Fin 2 → Fin 2) :
    (B → Fin 2) ≃
      (Fin n → Fin 4) ×
        ({b : B // b ∉ Set.range slot} → Fin 2) :=
  ((splitCoordinates slot hslot).arrowCongr (Equiv.refl (Fin 2))).trans
    ((Equiv.sumArrowEquivProdArrow
      (Fin n × Fin 2)
      {b : B // b ∉ Set.range slot}
      (Fin 2)).trans
        ((wordEquiv expected).prodCongr (Equiv.refl _)))

theorem independentWordSplit_first_apply
    {B : Type*} {n : ℕ}
    (slot : Fin n × Fin 2 → B)
    (hslot : Function.Injective slot)
    (expected : Fin n × Fin 2 → Fin 2)
    (ω : B → Fin 2) (i : Fin n) :
    (independentWordSplit slot hslot expected ω).1 i =
      wordEquiv expected (fun z => ω (slot z)) i := by
  classical
  change
    wordEquiv expected
        (fun z =>
          ω ((splitCoordinates slot hslot).symm (Sum.inl z))) i =
      wordEquiv expected (fun z => ω (slot z)) i
  congr 2

/-- The number of coordinates of a four-valued word equal to the distinguished
value `0`. -/
def safeCount {n : ℕ} (f : Fin n → Fin 4) : ℕ :=
  (Finset.univ.filter fun i => f i = 0).card

/-- The multiplicative moment attached to a four-valued word. -/
def momentWeight {n : ℕ} (f : Fin n → Fin 4) : ℕ :=
  ∏ i, if f i = 0 then 1 else 4

theorem momentWeight_eq_pow {n : ℕ} (f : Fin n → Fin 4) :
    momentWeight f = 4 ^ (n - safeCount f) := by
  classical
  rw [momentWeight, safeCount]
  calc
    (∏ i, if f i = 0 then 1 else 4) =
        ∏ i ∈ (Finset.univ.filter fun i => f i ≠ 0), 4 := by
      rw [Finset.prod_ite]
      simp
    _ = 4 ^ (Finset.univ.filter fun i => f i ≠ 0).card := by
      simp
    _ = 4 ^ (n -
        (Finset.univ.filter fun i => f i = 0).card) := by
      congr 1
      have hpartition :=
        Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin n)))
          (p := fun i => f i = 0)
      have huniv : (Finset.univ : Finset (Fin n)).card = n := by
        simp
      rw [huniv] at hpartition
      apply Nat.eq_sub_of_add_eq
      simpa [Nat.add_comm] using hpartition

/-- The total exponential moment is `13^n`: one local assignment has weight
one and the other three have weight four. -/
theorem sum_momentWeight (n : ℕ) :
    ∑ f : Fin n → Fin 4, momentWeight f = 13 ^ n := by
  classical
  change
    (∑ f : Fin n → Fin 4,
      ∏ i, if f i = 0 then 1 else 4) = 13 ^ n
  calc
    (∑ f : Fin n → Fin 4,
        ∏ i, if f i = 0 then 1 else 4) =
        ∏ _i : Fin n,
          ∑ x : Fin 4, if x = 0 then 1 else 4 := by
      rw [Fintype.prod_sum]
    _ = ∏ _i : Fin n, 13 := by
      have hlocal :
          (∑ x : Fin 4, if x = 0 then 1 else 4) = 13 := by
        decide
      rw [hlocal]
    _ = 13 ^ n := by simp

/-- Words of length `16t` having fewer than `t` safe coordinates satisfy the
integer lower-tail bound used by the thinning proof. -/
theorem badWords_mul_pow_le (t : ℕ) :
    ((Finset.univ.filter fun f : Fin (16 * t) → Fin 4 =>
        safeCount f < t).card) * 4 ^ (15 * t + 1) ≤
      13 ^ (16 * t) := by
  classical
  let bad : Finset (Fin (16 * t) → Fin 4) :=
    Finset.univ.filter fun f => safeCount f < t
  have hpoint :
      ∀ f ∈ bad, 4 ^ (15 * t + 1) ≤ momentWeight f := by
    intro f hf
    have hsafe : safeCount f < t := by
      simpa [bad] using hf
    have hsafeLength : safeCount f ≤ 16 * t := by
      exact (Finset.card_filter_le _ _).trans (by simp)
    rw [momentWeight_eq_pow]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    apply Nat.le_sub_of_add_le
    omega
  calc
    bad.card * 4 ^ (15 * t + 1) =
        ∑ f ∈ bad, 4 ^ (15 * t + 1) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ f ∈ bad, momentWeight f :=
      Finset.sum_le_sum fun f hf => hpoint f hf
    _ ≤ ∑ f : Fin (16 * t) → Fin 4, momentWeight f := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ bad)
    _ = 13 ^ (16 * t) := sum_momentWeight (16 * t)

/-- A convenient power-of-four relaxation of the preceding moment bound. -/
theorem badWords_mul_pow_le_pow_four (t : ℕ) :
    ((Finset.univ.filter fun f : Fin (16 * t) → Fin 4 =>
        safeCount f < t).card) * 4 ^ (15 * t + 1) ≤
      4 ^ (30 * t) := by
  refine (badWords_mul_pow_le t).trans ?_
  calc
    13 ^ (16 * t) = (13 ^ 16) ^ t := by
      rw [pow_mul]
    _ ≤ (4 ^ 30) ^ t := by
      exact Nat.pow_le_pow_left (by norm_num) _
    _ = 4 ^ (30 * t) := by
      rw [pow_mul]

/-- In probability language, the bad words occupy at most a
`4 ^ (-(t+1))` fraction of all four-valued words.  The multiplication form is
the one used by the finite union bound. -/
theorem badWords_mul_failureFactor_le_total (t : ℕ) :
    ((Finset.univ.filter fun f : Fin (16 * t) → Fin 4 =>
        safeCount f < t).card) * 4 ^ (t + 1) ≤
      4 ^ (16 * t) := by
  classical
  by_cases ht : t = 0
  · subst t
    simp [safeCount]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    let badCard :=
      (Finset.univ.filter fun f : Fin (16 * t) → Fin 4 =>
        safeCount f < t).card
    have hmoment :
        badCard * 4 ^ (15 * t + 1) ≤ 4 ^ (30 * t) := by
      simpa [badCard] using badWords_mul_pow_le_pow_four t
    have hexp : 30 * t = (15 * t - 1) + (15 * t + 1) := by
      omega
    have hfactor :
        badCard ≤ 4 ^ (15 * t - 1) := by
      have hmoment' :
          badCard * 4 ^ (15 * t + 1) ≤
            4 ^ (15 * t - 1) * 4 ^ (15 * t + 1) := by
        calc
          badCard * 4 ^ (15 * t + 1) ≤ 4 ^ (30 * t) := hmoment
          _ = 4 ^ (15 * t - 1) * 4 ^ (15 * t + 1) := by
            rw [← pow_add, ← hexp]
      exact Nat.le_of_mul_le_mul_right hmoment' (by positivity)
    calc
      badCard * 4 ^ (t + 1) ≤
          4 ^ (15 * t - 1) * 4 ^ (t + 1) :=
        Nat.mul_le_mul_right _ hfactor
      _ = 4 ^ (16 * t) := by
        rw [← pow_add]
        congr 1
        omega

/-- Transport the four-valued-word estimate across an arbitrary finite sample
space.  The equivalence separates the `16t` independent local assignments
from all unused choices.  The supplied inequality says that every locally
safe assignment gives a genuinely retained object. -/
theorem badOutcomes_mul_failureFactor_le_total
    {Ω R : Type*} [Fintype Ω] [Fintype R]
    (t : ℕ)
    (split : Ω ≃ (Fin (16 * t) → Fin 4) × R)
    (retained : Ω → ℕ)
    (hsafe : ∀ ω, safeCount (split ω).1 ≤ retained ω) :
    ((Finset.univ.filter fun ω : Ω => retained ω < t).card) *
        4 ^ (t + 1) ≤
      Fintype.card Ω := by
  classical
  let badWords : Finset (Fin (16 * t) → Fin 4) :=
    Finset.univ.filter fun f => safeCount f < t
  let badOutcomes : Finset Ω :=
    Finset.univ.filter fun ω => retained ω < t
  let encode :
      {ω : Ω // ω ∈ badOutcomes} →
        {f : Fin (16 * t) → Fin 4 // f ∈ badWords} × R :=
    fun ω =>
      ⟨⟨(split ω.1).1, by
          simp only [badWords, Finset.mem_filter, Finset.mem_univ, true_and]
          have hretained : retained ω.1 < t := by
            have hmem := ω.2
            change ω.1 ∈
              Finset.univ.filter (fun z : Ω => retained z < t) at hmem
            exact (Finset.mem_filter.mp hmem).2
          exact (hsafe ω.1).trans_lt hretained⟩,
        (split ω.1).2⟩
  have hencode : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply split.injective
    have hfirst :
        (split x.1).1 = (split y.1).1 :=
      congrArg (fun z => z.1.1) hxy
    have hsecond :
        (split x.1).2 = (split y.1).2 :=
      congrArg (fun z => z.2) hxy
    exact Prod.ext hfirst hsecond
  have hbad :
      badOutcomes.card ≤ badWords.card * Fintype.card R := by
    calc
      badOutcomes.card =
          Fintype.card {ω : Ω // ω ∈ badOutcomes} := by
        rw [Fintype.card_coe]
      _ ≤ Fintype.card
          ({f : Fin (16 * t) → Fin 4 // f ∈ badWords} × R) :=
        Fintype.card_le_of_injective encode hencode
      _ = badWords.card * Fintype.card R := by
        rw [Fintype.card_prod, Fintype.card_coe]
  have hword :
      badWords.card * 4 ^ (t + 1) ≤ 4 ^ (16 * t) := by
    simpa [badWords] using badWords_mul_failureFactor_le_total t
  have htotal :
      Fintype.card Ω = 4 ^ (16 * t) * Fintype.card R := by
    calc
      Fintype.card Ω =
          Fintype.card ((Fin (16 * t) → Fin 4) × R) :=
        Fintype.card_congr split
      _ = Fintype.card (Fin (16 * t) → Fin 4) *
          Fintype.card R := Fintype.card_prod _ _
      _ = 4 ^ (16 * t) * Fintype.card R := by simp
  calc
    (Finset.univ.filter fun ω : Ω => retained ω < t).card *
        4 ^ (t + 1) =
        badOutcomes.card * 4 ^ (t + 1) := by rfl
    _ ≤ (badWords.card * Fintype.card R) * 4 ^ (t + 1) :=
      Nat.mul_le_mul_right _ hbad
    _ = (badWords.card * 4 ^ (t + 1)) * Fintype.card R := by
      ac_rfl
    _ ≤ 4 ^ (16 * t) * Fintype.card R :=
      Nat.mul_le_mul_right _ hword
    _ = Fintype.card Ω := htotal.symm

/-- Apply the word estimate to an actual binary choice space.  The right
summand supplies private dummy bits for endpoints at which an edge is
unconditionally retained.  These dummy choices cancel from both sides, so
the conclusion counts only genuine outcomes. -/
theorem binaryOutcomes_bad_mul_failureFactor_le_total
    {B : Type*} [Fintype B] [DecidableEq B]
    (t : ℕ)
    (slot :
      Fin (16 * t) × Fin 2 →
        B ⊕ (Fin (16 * t) × Fin 2))
    (hslot : Function.Injective slot)
    (expected : Fin (16 * t) × Fin 2 → Fin 2)
    (retained : (B → Fin 2) → ℕ)
    (hsafe :
      ∀ ω : B ⊕ (Fin (16 * t) × Fin 2) → Fin 2,
        safeCount
            (wordEquiv expected fun z => ω (slot z)) ≤
          retained (fun b => ω (Sum.inl b))) :
    ((Finset.univ.filter fun ω : B → Fin 2 =>
        retained ω < t).card) * 4 ^ (t + 1) ≤
      Fintype.card (B → Fin 2) := by
  classical
  let A := Fin (16 * t) × Fin 2
  let Augmented := B ⊕ A → Fin 2
  let actual (ω : Augmented) : B → Fin 2 :=
    fun b => ω (Sum.inl b)
  let remainder (ω : Augmented) : A → Fin 2 :=
    fun a => ω (Sum.inr a)
  let badActual : Finset (B → Fin 2) :=
    Finset.univ.filter fun ω => retained ω < t
  let badAugmented : Finset Augmented :=
    Finset.univ.filter fun ω => retained (actual ω) < t
  let splitAugmented :
      Augmented ≃
        (Fin (16 * t) → Fin 4) ×
          ({b : B ⊕ A // b ∉ Set.range slot} → Fin 2) :=
    independentWordSplit slot hslot expected
  have hsafe' :
      ∀ ω : Augmented,
        safeCount (splitAugmented ω).1 ≤
          retained (actual ω) := by
    intro ω
    rw [show (splitAugmented ω).1 =
        wordEquiv expected (fun z => ω (slot z)) by
      funext i
      exact independentWordSplit_first_apply
        slot hslot expected ω i]
    exact hsafe ω
  have haugmented :=
    badOutcomes_mul_failureFactor_le_total
      t splitAugmented (fun ω : Augmented => retained (actual ω))
      hsafe'
  let badSplit :
      {ω : Augmented // ω ∈ badAugmented} ≃
        {ω : B → Fin 2 // ω ∈ badActual} × (A → Fin 2) := {
    toFun := fun ω =>
      ⟨⟨actual ω.1, by
          have hmem := ω.2
          change ω.1 ∈ Finset.univ.filter
            (fun z : Augmented => retained (actual z) < t) at hmem
          change actual ω.1 ∈ Finset.univ.filter
            (fun z : B → Fin 2 => retained z < t)
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hmem).2⟩⟩,
        remainder ω.1⟩
    invFun := fun p =>
      ⟨Sum.elim p.1.1 p.2, by
          change Sum.elim p.1.1 p.2 ∈
            Finset.univ.filter
              (fun z : Augmented => retained (actual z) < t)
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hmem := p.1.2
          change p.1.1 ∈ Finset.univ.filter
            (fun z : B → Fin 2 => retained z < t) at hmem
          simpa [actual] using (Finset.mem_filter.mp hmem).2⟩
    left_inv := by
      intro ω
      apply Subtype.ext
      funext z
      cases z <;> rfl
    right_inv := by
      intro p
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl
  }
  have hbadCard :
      badAugmented.card =
        badActual.card * Fintype.card (A → Fin 2) := by
    calc
      badAugmented.card =
          Fintype.card {ω : Augmented // ω ∈ badAugmented} := by
        rw [Fintype.card_coe]
      _ = Fintype.card
          ({ω : B → Fin 2 // ω ∈ badActual} × (A → Fin 2)) :=
        Fintype.card_congr badSplit
      _ = badActual.card * Fintype.card (A → Fin 2) := by
        rw [Fintype.card_prod, Fintype.card_coe]
  have htotalCard :
      Fintype.card Augmented =
        Fintype.card (B → Fin 2) *
          Fintype.card (A → Fin 2) := by
    calc
      Fintype.card Augmented =
          Fintype.card ((B → Fin 2) × (A → Fin 2)) :=
        Fintype.card_congr
          (Equiv.sumArrowEquivProdArrow B A (Fin 2))
      _ = _ := Fintype.card_prod _ _
  have haugmented' :
      (badActual.card * 4 ^ (t + 1)) *
          Fintype.card (A → Fin 2) ≤
        Fintype.card (B → Fin 2) *
          Fintype.card (A → Fin 2) := by
    calc
      (badActual.card * 4 ^ (t + 1)) *
          Fintype.card (A → Fin 2) =
          badAugmented.card * 4 ^ (t + 1) := by
        rw [hbadCard]
        ac_rfl
      _ ≤ Fintype.card Augmented := by
        simpa [badAugmented] using haugmented
      _ = _ := htotalCard
  exact Nat.le_of_mul_le_mul_right haugmented' (by positivity)

end ThinningConcentration
end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
