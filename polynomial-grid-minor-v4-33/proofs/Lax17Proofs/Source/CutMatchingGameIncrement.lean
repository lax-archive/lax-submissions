import Lax17Proofs.Source.CutMatchingGameCrossing

namespace Lax17Proofs

universe u v w

/-!
# One-round mass estimates for the cut-matching game

This file formalizes the counting part of the proof of Lemma 4.5 in Section 4
of the cut-matching-game paper.  Once a low-crossing start vertex is fixed,
at least a constant amount of its probability mass lies on vertices of the
small side whose matched partner has much smaller mass.
-/

namespace SimpleGraph
namespace CutMatchingGame

open scoped BigOperators


variable {X : Type u} [Fintype X] [DecidableEq X]

/-- Mass of one row of a transition matrix on a finite set of destinations. -/
noncomputable def rowMassOn (P : X → X → ℝ) (S : Finset X) (u : X) : ℝ :=
  ∑ v ∈ S, P u v

omit [Fintype X] [DecidableEq X] in
theorem rowMassOn_nonneg {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v) (S : Finset X) (u : X) :
    0 ≤ rowMassOn P S u := by
  unfold rowMassOn
  exact Finset.sum_nonneg fun v _ => hP u v

/-- A row decomposes as the mass on `T` plus the mass on its complement. -/
theorem rowMassOn_add_rowCrossingMass
    {P : X → X → ℝ}
    (hrow : ∀ u, (∑ v : X, P u v) = 1)
    (T : Finset X) (u : X) :
    rowMassOn P T u + rowCrossingMass P T u = 1 := by
  classical
  have hdisj : Disjoint T (vertexComplement T) :=
    disjoint_vertexComplement T
  have hunion : T ∪ vertexComplement T = (Finset.univ : Finset X) := by
    ext x
    simp [vertexComplement]
  calc
    rowMassOn P T u + rowCrossingMass P T u
        = (∑ v ∈ T, P u v) + ∑ v ∈ vertexComplement T, P u v := rfl
    _ = ∑ v ∈ T ∪ vertexComplement T, P u v := by
          rw [Finset.sum_union hdisj]
    _ = ∑ v ∈ (Finset.univ : Finset X), P u v := by rw [hunion]
    _ = 1 := by simpa using hrow u

/-- The positive binary-entropy gap at ratio `2/3`.  This is the constant
hidden in the paper's `Ω(1)` one-row entropy increase. -/
noncomputable def entropyGapConstant : ℝ :=
  Real.log 2 - Real.binEntropy (2 / 3)

theorem entropyGapConstant_pos : 0 < entropyGapConstant := by
  have hanti := Real.binEntropy_strictAntiOn
  have hlt :
      Real.binEntropy (2 / 3 : ℝ) < Real.binEntropy (2⁻¹ : ℝ) := by
    exact hanti
      (by norm_num : (2⁻¹ : ℝ) ∈ Set.Icc (2⁻¹ : ℝ) 1)
      (by norm_num : (2 / 3 : ℝ) ∈ Set.Icc (2⁻¹ : ℝ) 1)
      (by norm_num : (2⁻¹ : ℝ) < 2 / 3)
  unfold entropyGapConstant
  exact sub_pos.mpr (by simpa using hlt)

/-- Entropy gained by averaging the two parts `s * a` and `s * (1-a)`,
written using binary entropy. -/
theorem entropy_pair_gap_eq_decomp (s a : ℝ) :
    2 * entropyTerm (s / 2) -
        (entropyTerm (s * a) + entropyTerm (s * (1 - a))) =
      s * (Real.log 2 - Real.binEntropy a) := by
  have hhalf : s / 2 = s * (2 : ℝ)⁻¹ := by ring
  unfold entropyTerm
  rw [hhalf]
  rw [Real.negMulLog_mul, Real.negMulLog_mul, Real.negMulLog_mul]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [show Real.negMulLog ((2 : ℝ)⁻¹) = (2 : ℝ)⁻¹ * Real.log 2 by
    simp [Real.negMulLog, Real.log_inv]]
  ring

/-- Exact binary-entropy expression for the entropy gained by averaging two
masses whose sum is nonzero. -/
theorem entropy_pair_gap_eq
    {p q : ℝ} (hs : p + q ≠ 0) :
    2 * entropyTerm ((p + q) / 2) -
        (entropyTerm p + entropyTerm q) =
      (p + q) * (Real.log 2 - Real.binEntropy (p / (p + q))) := by
  let s := p + q
  let a := p / (p + q)
  have hp :
      p = s * a := by
    dsimp [s, a]
    field_simp [hs]
  have hq :
      q = s * (1 - a) := by
    dsimp [s, a]
    field_simp [hs]
    ring
  calc
    2 * entropyTerm ((p + q) / 2) -
        (entropyTerm p + entropyTerm q)
        = 2 * entropyTerm (s / 2) -
            (entropyTerm (s * a) + entropyTerm (s * (1 - a))) := by
          change
            2 * entropyTerm (s / 2) -
                (entropyTerm p + entropyTerm q) =
              2 * entropyTerm (s / 2) -
                (entropyTerm (s * a) + entropyTerm (s * (1 - a)))
          rw [hp, hq]
    _ = s * (Real.log 2 - Real.binEntropy a) :=
          entropy_pair_gap_eq_decomp s a
    _ = (p + q) * (Real.log 2 - Real.binEntropy (p / (p + q))) := by
          rfl

/-- If `p` is at least twice `q`, then averaging the two entries increases
entropy by at least `entropyGapConstant * p`. -/
theorem entropyGapConstant_mul_left_le_pair_gap
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hratio : 2 * q ≤ p) :
    entropyGapConstant * p ≤
      2 * entropyTerm ((p + q) / 2) -
        (entropyTerm p + entropyTerm q) := by
  by_cases hpzero : p = 0
  · have hqzero : q = 0 := by nlinarith
    simp [hpzero, hqzero]
  · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hpzero)
    have hs_pos : 0 < p + q := by positivity
    have hs_ne : p + q ≠ 0 := ne_of_gt hs_pos
    let a : ℝ := p / (p + q)
    have ha_ge_two_thirds : (2 / 3 : ℝ) ≤ a := by
      have hmul : (2 / 3 : ℝ) * (p + q) ≤ p := by
        nlinarith
      exact (le_div_iff₀ hs_pos).2 hmul
    have ha_le_one : a ≤ 1 := by
      have hp_le_sum : p ≤ p + q := by nlinarith
      exact (div_le_one hs_pos).2 hp_le_sum
    have ha_mem : a ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
      constructor
      · exact (by norm_num : (2⁻¹ : ℝ) ≤ 2 / 3) |>.trans ha_ge_two_thirds
      · exact ha_le_one
    have htwo_mem : (2 / 3 : ℝ) ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
      norm_num
    have hentropy_le :
        Real.binEntropy a ≤ Real.binEntropy (2 / 3 : ℝ) := by
      exact (Real.binEntropy_strictAntiOn.le_iff_ge ha_mem htwo_mem).2
        ha_ge_two_thirds
    have hgap_le :
        entropyGapConstant ≤ Real.log 2 - Real.binEntropy a := by
      unfold entropyGapConstant
      nlinarith
    have hgap_nonneg : 0 ≤ Real.log 2 - Real.binEntropy a :=
      (le_of_lt entropyGapConstant_pos).trans hgap_le
    have hconst_nonneg : 0 ≤ entropyGapConstant :=
      le_of_lt entropyGapConstant_pos
    have hp_le_sum : p ≤ p + q := by nlinarith
    have hmul₁ : entropyGapConstant * p ≤ entropyGapConstant * (p + q) :=
      mul_le_mul_of_nonneg_left hp_le_sum hconst_nonneg
    have hmul₂ :
        entropyGapConstant * (p + q) ≤
          (Real.log 2 - Real.binEntropy a) * (p + q) :=
      mul_le_mul_of_nonneg_right hgap_le (le_of_lt hs_pos)
    have hmain :
        entropyGapConstant * p ≤
          (p + q) * (Real.log 2 - Real.binEntropy a) := by
      calc
        entropyGapConstant * p ≤ entropyGapConstant * (p + q) := hmul₁
        _ ≤ (Real.log 2 - Real.binEntropy a) * (p + q) := hmul₂
        _ = (p + q) * (Real.log 2 - Real.binEntropy a) := by ring
    simpa [a, entropy_pair_gap_eq hs_ne] using hmain

namespace LazyRound

variable (R : LazyRound X)

/-- Vertices of `T` whose mass is at least twice the mass on their mate. -/
noncomputable def goodVertices (P : X → X → ℝ) (T : Finset X) (u : X) :
    Finset X :=
  T.filter fun v => 2 * P u (R.matching.mate v) ≤ P u v

/-- Vertices of `T` that are not good. -/
noncomputable def badVertices (P : X → X → ℝ) (T : Finset X) (u : X) :
    Finset X :=
  T.filter fun v => ¬ 2 * P u (R.matching.mate v) ≤ P u v

theorem mem_goodVertices {P : X → X → ℝ} {T : Finset X} {u v : X} :
    v ∈ R.goodVertices P T u ↔
      v ∈ T ∧ 2 * P u (R.matching.mate v) ≤ P u v := by
  simp [goodVertices]

theorem mem_badVertices {P : X → X → ℝ} {T : Finset X} {u v : X} :
    v ∈ R.badVertices P T u ↔
      v ∈ T ∧ ¬ 2 * P u (R.matching.mate v) ≤ P u v := by
  simp [badVertices]

theorem rowMassOn_good_add_bad
    (P : X → X → ℝ) (T : Finset X) (u : X) :
    rowMassOn P (R.goodVertices P T u) u +
      rowMassOn P (R.badVertices P T u) u =
        rowMassOn P T u := by
  classical
  unfold rowMassOn goodVertices badVertices
  simpa using
    (Finset.sum_filter_add_sum_filter_not
      (s := T)
      (p := fun v => 2 * P u (R.matching.mate v) ≤ P u v)
      (f := fun v => P u v))

/-- If `T` lies on the left side of the round bisection, then every vertex of
`T` is matched outside `T`. -/
theorem mate_not_mem_of_mem_left_subset
    {T : Finset X} (hTleft : ∀ v ∈ T, v ∈ R.cut.left)
    {v : X} (hv : v ∈ T) :
    R.matching.mate v ∉ T := by
  intro hmateT
  have hvleft : v ∈ R.cut.left := hTleft v hv
  have hmateRight : R.matching.mate v ∈ R.cut.right :=
    R.matching.mate_mem_right_of_mem_left hvleft
  have hmateLeft : R.matching.mate v ∈ R.cut.left :=
    hTleft (R.matching.mate v) hmateT
  exact R.cut.not_mem_left_of_mem_right hmateRight hmateLeft

/-- The bad mass is controlled by twice the mass already outside `T`. -/
theorem rowMassOn_badVertices_le_two_mul_crossing
    {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v)
    {T : Finset X} (hTleft : ∀ v ∈ T, v ∈ R.cut.left)
    (u : X) :
    rowMassOn P (R.badVertices P T u) u ≤
      2 * rowCrossingMass P T u := by
  classical
  let Bad := R.badVertices P T u
  have hpoint :
      ∀ v ∈ Bad, P u v ≤ 2 * P u (R.matching.mate v) := by
    intro v hv
    have hbad := (R.mem_badVertices.mp (by simpa [Bad] using hv)).2
    exact le_of_lt (lt_of_not_ge hbad)
  have hbad_to_cross :
      (∑ v ∈ Bad, P u (R.matching.mate v)) ≤ rowCrossingMass P T u := by
    let imageBad := Bad.image R.matching.mate
    have himage_eq :
        (∑ w ∈ imageBad, P u w) =
          ∑ v ∈ Bad, P u (R.matching.mate v) := by
      unfold imageBad
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact R.matching.mate_injective hxy
    have hsubset : imageBad ⊆ vertexComplement T := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨v, hvBad, hvw⟩
      have hvT : v ∈ T :=
        (R.mem_badVertices.mp (by simpa [Bad] using hvBad)).1
      have hmate_not : R.matching.mate v ∉ T :=
        R.mate_not_mem_of_mem_left_subset hTleft hvT
      exact mem_vertexComplement.mpr (by simpa [hvw] using hmate_not)
    have hle_image :
        (∑ w ∈ imageBad, P u w) ≤ rowCrossingMass P T u := by
      unfold rowCrossingMass
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun w _ _ => hP u w)
    exact himage_eq ▸ hle_image
  calc
    rowMassOn P (R.badVertices P T u) u
        = ∑ v ∈ Bad, P u v := rfl
    _ ≤ ∑ v ∈ Bad, 2 * P u (R.matching.mate v) := by
          exact Finset.sum_le_sum hpoint
    _ = 2 * ∑ v ∈ Bad, P u (R.matching.mate v) := by
          rw [Finset.mul_sum]
    _ ≤ 2 * rowCrossingMass P T u := by
          nlinarith

/-- For a low-crossing start vertex, at least `1/4` probability mass lies on
good vertices of `T`. -/
theorem one_four_le_rowMassOn_goodVertices
    {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v)
    (hrow : ∀ u, (∑ v : X, P u v) = 1)
    {T : Finset X} (hTleft : ∀ v ∈ T, v ∈ R.cut.left)
    {u : X} (hlow : rowCrossingMass P T u ≤ (1 / 4 : ℝ)) :
    (1 / 4 : ℝ) ≤ rowMassOn P (R.goodVertices P T u) u := by
  have hsplit := R.rowMassOn_good_add_bad P T u
  have hrow_split := rowMassOn_add_rowCrossingMass hrow T u
  have hbad :=
    R.rowMassOn_badVertices_le_two_mul_crossing hP hTleft u
  nlinarith

/-- The entropy increase of one row in a round dominates
`entropyGapConstant` times the mass on good vertices. -/
theorem entropyGapConstant_mul_rowMassOn_goodVertices_le_rowEntropy_gain
    {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v)
    {T : Finset X} (hTleft : ∀ v ∈ T, v ∈ R.cut.left)
    (u : X) :
    entropyGapConstant * rowMassOn P (R.goodVertices P T u) u ≤
      rowEntropy (R.updateMatrix P u) - rowEntropy (P u) := by
  classical
  let Good := R.goodVertices P T u
  let gain : X → ℝ := fun v =>
    2 * entropyTerm ((P u v + P u (R.matching.mate v)) / 2) -
      (entropyTerm (P u v) + entropyTerm (P u (R.matching.mate v)))
  have hGood_subset_left : Good ⊆ R.cut.left := by
    intro v hv
    exact hTleft v ((R.mem_goodVertices.mp (by simpa [Good] using hv)).1)
  have hgain_nonneg_left : ∀ v ∈ R.cut.left, 0 ≤ gain v := by
    intro v hv
    have h :=
      entropyTerm_add_le_two_mul_entropyTerm_average
        (hP u v) (hP u (R.matching.mate v))
    dsimp [gain]
    nlinarith
  have hgood_term :
      ∀ v ∈ Good, entropyGapConstant * P u v ≤ gain v := by
    intro v hv
    have hvGood := R.mem_goodVertices.mp (by simpa [Good] using hv)
    have hratio : 2 * P u (R.matching.mate v) ≤ P u v := hvGood.2
    dsimp [gain]
    exact entropyGapConstant_mul_left_le_pair_gap
      (hP u v) (hP u (R.matching.mate v)) hratio
  have hbefore_sub :
      rowEntropy (P u) =
        ∑ x : {x : X // x ∈ R.cut.left},
          (entropyTerm (P u x) +
            entropyTerm (P u (R.matching.rightEndpoint x))) := by
    unfold rowEntropy
    rw [MatchingAcross.sum_eq_sum_left_add_sum_right (B := R.cut)
      (fun x => entropyTerm (P u x))]
    rw [R.matching.sum_right_eq_sum_left
      (fun x => entropyTerm (P u x))]
    rw [← Finset.sum_add_distrib]
  have hbefore_sub' :
      rowEntropy (P u) =
        ∑ x : {x : X // x ∈ R.cut.left},
          (entropyTerm (P u x) +
            entropyTerm (P u (R.matching.mate x))) := by
    rw [hbefore_sub]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [R.matching.mate_of_mem_left x.2]
  have hbefore :
      rowEntropy (P u) =
        ∑ v ∈ R.cut.left,
          (entropyTerm (P u v) +
            entropyTerm (P u (R.matching.mate v))) := by
    rw [hbefore_sub']
    rw [← Finset.sum_subtype R.cut.left (fun _ => Iff.rfl)
      (fun v => entropyTerm (P u v) +
        entropyTerm (P u (R.matching.mate v)))]
  have hafter_sub :
      rowEntropy (R.updateMatrix P u) =
        ∑ x : {x : X // x ∈ R.cut.left},
          2 * entropyTerm
            ((P u x + P u (R.matching.rightEndpoint x)) / 2) := by
    unfold rowEntropy LazyRound.updateMatrix
    rw [MatchingAcross.sum_eq_sum_left_add_sum_right (B := R.cut)
      (fun x => entropyTerm (R.matching.lazyStep (P u) x))]
    rw [R.matching.sum_right_eq_sum_left
      (fun x => entropyTerm (R.matching.lazyStep (P u) x))]
    simp_rw [R.matching.lazyStep_left (P u),
      R.matching.lazyStep_rightEndpoint (P u)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  have hafter_sub' :
      rowEntropy (R.updateMatrix P u) =
        ∑ x : {x : X // x ∈ R.cut.left},
          2 * entropyTerm ((P u x + P u (R.matching.mate x)) / 2) := by
    rw [hafter_sub]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [R.matching.mate_of_mem_left x.2]
  have hafter :
      rowEntropy (R.updateMatrix P u) =
        ∑ v ∈ R.cut.left,
          2 * entropyTerm ((P u v + P u (R.matching.mate v)) / 2) := by
    rw [hafter_sub']
    rw [← Finset.sum_subtype R.cut.left (fun _ => Iff.rfl)
      (fun v => 2 * entropyTerm
        ((P u v + P u (R.matching.mate v)) / 2))]
  have hgain_eq :
      rowEntropy (R.updateMatrix P u) - rowEntropy (P u) =
        ∑ v ∈ R.cut.left, gain v := by
    rw [hafter, hbefore]
    rw [← Finset.sum_sub_distrib]
  calc
    entropyGapConstant * rowMassOn P Good u
        = ∑ v ∈ Good, entropyGapConstant * P u v := by
          unfold rowMassOn
          rw [Finset.mul_sum]
    _ ≤ ∑ v ∈ Good, gain v := by
          exact Finset.sum_le_sum hgood_term
    _ ≤ ∑ v ∈ R.cut.left, gain v := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hGood_subset_left
            (fun v _ _ => hgain_nonneg_left v ‹v ∈ R.cut.left›)
    _ = rowEntropy (R.updateMatrix P u) - rowEntropy (P u) := hgain_eq.symm

/-- Low crossing probability gives a uniform one-row entropy increase. -/
theorem entropyGapConstant_div_four_le_rowEntropy_gain_of_lowCrossing
    {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v)
    (hrow : ∀ u, (∑ v : X, P u v) = 1)
    {T : Finset X} (hTleft : ∀ v ∈ T, v ∈ R.cut.left)
    {u : X} (hlow : rowCrossingMass P T u ≤ (1 / 4 : ℝ)) :
    entropyGapConstant / 4 ≤
      rowEntropy (R.updateMatrix P u) - rowEntropy (P u) := by
  have hmass :=
    R.one_four_le_rowMassOn_goodVertices hP hrow hTleft hlow
  have hgain :=
    R.entropyGapConstant_mul_rowMassOn_goodVertices_le_rowEntropy_gain
      hP hTleft u
  have hconst_nonneg : 0 ≤ entropyGapConstant :=
    le_of_lt entropyGapConstant_pos
  nlinarith

end LazyRound

/-- Row entropy gain for a single lazy round. -/
noncomputable def rowEntropyGain (R : LazyRound X) (P : X → X → ℝ) (u : X) :
    ℝ :=
  rowEntropy (R.updateMatrix P u) - rowEntropy (P u)

theorem rowEntropyGain_nonneg
    (R : LazyRound X) {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v) (u : X) :
    0 ≤ rowEntropyGain R P u := by
  unfold rowEntropyGain LazyRound.updateMatrix
  have h :=
    R.matching.rowEntropy_le_rowEntropy_lazyStep (p := P u)
      (fun v => hP u v)
  nlinarith

theorem entropyPotential_updateMatrix_sub_eq_sum_rowEntropyGain
    (R : LazyRound X) (P : X → X → ℝ) :
    entropyPotential (R.updateMatrix P) - entropyPotential P =
      ∑ u : X, rowEntropyGain R P u := by
  unfold entropyPotential rowEntropyGain
  rw [← Finset.sum_sub_distrib]

/-- Potential-level form of the low-crossing row increment: each low-crossing
start contributes at least `entropyGapConstant / 4`, and all other rows have
nonnegative entropy gain. -/
theorem entropyGapConstant_div_four_mul_lowCrossingStarts_card_le_potential_gain
    (R : LazyRound X) {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v)
    (hrow : ∀ u, (∑ v : X, P u v) = 1)
    {T : Finset X} (hTleft : ∀ v ∈ T, v ∈ R.cut.left) :
    (entropyGapConstant / 4) *
        ((lowCrossingStarts P T (1 / 4)).card : ℝ) ≤
      entropyPotential (R.updateMatrix P) - entropyPotential P := by
  classical
  let Low := lowCrossingStarts P T (1 / 4)
  have hlow :
      ∀ u ∈ Low, entropyGapConstant / 4 ≤ rowEntropyGain R P u := by
    intro u hu
    have huLow := mem_lowCrossingStarts.mp (by simpa [Low] using hu)
    unfold rowEntropyGain
    exact R.entropyGapConstant_div_four_le_rowEntropy_gain_of_lowCrossing
      hP hrow hTleft (by simpa [one_div] using huLow.2)
  have hnonneg : ∀ u, 0 ≤ rowEntropyGain R P u :=
    rowEntropyGain_nonneg R hP
  calc
    (entropyGapConstant / 4) * (Low.card : ℝ)
        = ∑ _u ∈ Low, entropyGapConstant / 4 := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ∑ u ∈ Low, rowEntropyGain R P u := by
          exact Finset.sum_le_sum hlow
    _ ≤ ∑ u : X, rowEntropyGain R P u := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by intro u _; exact Finset.mem_univ u)
            (fun u _ _ => hnonneg u)
    _ = entropyPotential (R.updateMatrix P) - entropyPotential P := by
          rw [entropyPotential_updateMatrix_sub_eq_sum_rowEntropyGain]

/-- Lemma 4.5 in its local analytic form: if the total crossing probability
from `T` is at most `|T|/8`, then the next round increases the entropy
potential by at least `entropyGapConstant * |T| / 8`, provided the cut player
places `T` on the left side of the bisection. -/
theorem entropyGapConstant_mul_card_div_eight_le_potential_gain_of_crossingMass_le
    (R : LazyRound X) {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v)
    (hrow : ∀ u, (∑ v : X, P u v) = 1)
    {T : Finset X} (hTleft : ∀ v ∈ T, v ∈ R.cut.left)
    (hmass : crossingMass P T ≤ (T.card : ℝ) / 8) :
    entropyGapConstant * (T.card : ℝ) / 8 ≤
      entropyPotential (R.updateMatrix P) - entropyPotential P := by
  classical
  let Low := lowCrossingStarts P T (1 / 4)
  have hcard_nat :
      T.card ≤ 2 * Low.card := by
    simpa [Low] using
      card_le_two_mul_lowCrossingStarts_card_of_crossingMass_le
        hP hmass
  have hcard_real : (T.card : ℝ) / 2 ≤ (Low.card : ℝ) := by
    have hcast : (T.card : ℝ) ≤ 2 * (Low.card : ℝ) := by
      exact_mod_cast hcard_nat
    nlinarith
  have hpotential :=
    entropyGapConstant_div_four_mul_lowCrossingStarts_card_le_potential_gain
      R hP hrow hTleft
  have hconst_nonneg : 0 ≤ entropyGapConstant :=
    le_of_lt entropyGapConstant_pos
  nlinarith

/-- Lemma 4.5 specialized to a walk history: if the current history has fewer
than one quarter as many boundary matching edges across `T` as vertices in
`T`, and the next bisection places `T` on its left side, then appending the
next matching round raises the potential by a constant times `|T|`. -/
theorem entropyGapConstant_mul_card_div_eight_le_walkMatrix_append_potential_gain
    (rounds : List (LazyRound X)) (R : LazyRound X) {T : Finset X}
    (hTleft : ∀ v ∈ T, v ∈ R.cut.left)
    (hboundary : 4 * edgeBoundaryCount rounds T ≤ T.card) :
    entropyGapConstant * (T.card : ℝ) / 8 ≤
      entropyPotential (walkMatrix (rounds ++ [R])) -
        entropyPotential (walkMatrix rounds) := by
  have hcross :=
    crossingMass_walkMatrix_le_edgeBoundaryCount_div_two rounds T
  have hboundary_real :
      (4 * edgeBoundaryCount rounds T : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast hboundary
  have hmass :
      crossingMass (walkMatrix rounds) T ≤ (T.card : ℝ) / 8 := by
    nlinarith
  have hgain :=
    entropyGapConstant_mul_card_div_eight_le_potential_gain_of_crossingMass_le
      R
      (fun u v => walkMatrix_nonneg rounds u v)
      (fun u => walkMatrix_row_sum rounds u)
      hTleft hmass
  rwa [walkMatrix_append_singleton]

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
