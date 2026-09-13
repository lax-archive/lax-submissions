import Lax17Proofs.Source.CutMatchingGameExpansion

namespace Lax17Proofs

universe u v w

/-!
# Crossing probability for cut-matching random walks

For a vertex set `T`, Lemma 4.6 of the cut-matching-game paper bounds the
total probability, over all starts in `T`, that the lazy walks have crossed to
`Tᶜ`.  This file introduces that quantity and proves the elementary base and
monotonicity facts needed for the full crossing bound.
-/

namespace SimpleGraph
namespace CutMatchingGame

open scoped BigOperators


variable {X : Type u} [Fintype X] [DecidableEq X]

/-- The complement of a finite vertex set inside the full finite type. -/
def vertexComplement (S : Finset X) : Finset X :=
  Finset.univ \ S

@[simp]
theorem mem_vertexComplement {S : Finset X} {x : X} :
    x ∈ vertexComplement S ↔ x ∉ S := by
  simp [vertexComplement]

@[simp]
theorem vertexComplement_empty :
    vertexComplement (∅ : Finset X) = Finset.univ := by
  ext x
  simp [vertexComplement]

@[simp]
theorem vertexComplement_univ :
    vertexComplement (Finset.univ : Finset X) = ∅ := by
  ext x
  simp [vertexComplement]

theorem disjoint_vertexComplement (S : Finset X) :
    Disjoint S (vertexComplement S) := by
  rw [Finset.disjoint_left]
  intro x hx hxc
  exact (mem_vertexComplement.mp hxc) hx

namespace LazyRound

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- The image of the outside of `T` under the matching involution of a round. -/
noncomputable def mateImageOutside (R : LazyRound X) (T : Finset X) :
    Finset X :=
  (vertexComplement T).image R.matching.mate

theorem mem_mateImageOutside {R : LazyRound X} {T : Finset X} {x : X} :
    x ∈ R.mateImageOutside T ↔ R.matching.mate x ∉ T := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hyx⟩
    have hmate : R.matching.mate x = y := by
      calc
        R.matching.mate x = R.matching.mate (R.matching.mate y) := by rw [hyx]
        _ = y := R.matching.mate_mate y
    exact fun hxT => (mem_vertexComplement.mp hy) (by simpa [hmate] using hxT)
  · intro hx
    exact Finset.mem_image.mpr
      ⟨R.matching.mate x, by simpa using hx, R.matching.mate_mate x⟩

theorem mateImageOutside_subset_outside_union_inside
    (R : LazyRound X) (T : Finset X) :
    R.mateImageOutside T ⊆ vertexComplement T ∪ R.insideWithMateOutside T := by
  classical
  intro x hx
  have hxmate : R.matching.mate x ∉ T := R.mem_mateImageOutside.mp hx
  by_cases hxT : x ∈ T
  · exact Finset.mem_union.mpr (Or.inr
      (R.mem_insideWithMateOutside.mpr ⟨hxT, hxmate⟩))
  · exact Finset.mem_union.mpr (Or.inl (mem_vertexComplement.mpr hxT))

theorem sum_mateImageOutside_eq
    (R : LazyRound X) (T : Finset X) (f : X → ℝ) :
    (∑ x ∈ R.mateImageOutside T, f x) =
      ∑ x ∈ vertexComplement T, f (R.matching.mate x) := by
  classical
  unfold mateImageOutside
  rw [Finset.sum_image]
  intro x _ y _ hxy
  exact R.matching.mate_injective hxy

theorem sum_mateImageOutside_le
    (R : LazyRound X) (T : Finset X) {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ R.mateImageOutside T, f x) ≤
      (∑ x ∈ vertexComplement T, f x) +
        ∑ x ∈ R.insideWithMateOutside T, f x := by
  classical
  have hsubset := R.mateImageOutside_subset_outside_union_inside T
  have hdisj : Disjoint (vertexComplement T) (R.insideWithMateOutside T) := by
    rw [Finset.disjoint_left]
    intro x hxOutside hxInside
    exact (mem_vertexComplement.mp hxOutside)
      ((R.mem_insideWithMateOutside.mp hxInside).1)
  calc
    (∑ x ∈ R.mateImageOutside T, f x)
        ≤ ∑ x ∈ vertexComplement T ∪ R.insideWithMateOutside T, f x := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun x _ _ => hf x)
    _ = (∑ x ∈ vertexComplement T, f x) +
          ∑ x ∈ R.insideWithMateOutside T, f x := by
          rw [Finset.sum_union hdisj]

end LazyRound

/-- For one starting vertex `u`, the probability mass lying outside `T`. -/
noncomputable def rowCrossingMass {X : Type u} [Fintype X] [DecidableEq X]
    (P : X → X → ℝ) (T : Finset X) (u : X) : ℝ :=
  ∑ v ∈ vertexComplement T, P u v

/-- Total probability, over starts in `T`, of being outside `T`. -/
noncomputable def crossingMass {X : Type u} [Fintype X] [DecidableEq X]
    (P : X → X → ℝ) (T : Finset X) : ℝ :=
  ∑ u ∈ T, rowCrossingMass P T u

theorem rowCrossingMass_nonneg {X : Type u} [Fintype X] [DecidableEq X]
    {P : X → X → ℝ} (hP : ∀ u v, 0 ≤ P u v)
    (T : Finset X) (u : X) :
    0 ≤ rowCrossingMass P T u := by
  unfold rowCrossingMass
  exact Finset.sum_nonneg fun v _ => hP u v

theorem crossingMass_nonneg {X : Type u} [Fintype X] [DecidableEq X]
    {P : X → X → ℝ} (hP : ∀ u v, 0 ≤ P u v)
    (T : Finset X) :
    0 ≤ crossingMass P T := by
  unfold crossingMass
  exact Finset.sum_nonneg fun u _ => rowCrossingMass_nonneg hP T u

/-- At time zero no walk starting in `T` has crossed to `Tᶜ`. -/
theorem crossingMass_pointMass_eq_zero
    {X : Type u} [Fintype X] [DecidableEq X] (T : Finset X) :
    crossingMass (pointMassMatrix (X := X)) T = 0 := by
  classical
  unfold crossingMass rowCrossingMass pointMassMatrix
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have hvu : v ≠ u := by
    intro h
    exact (mem_vertexComplement.mp hv) (by simpa [h] using hu)
  simp [hvu]

/-- A row-crossing mass is at most the whole row mass. -/
theorem rowCrossingMass_le_rowSum
    {X : Type u} [Fintype X] [DecidableEq X]
    {P : X → X → ℝ} (hP : ∀ u v, 0 ≤ P u v)
    (T : Finset X) (u : X) :
    rowCrossingMass P T u ≤ ∑ v : X, P u v := by
  unfold rowCrossingMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro v hv; exact Finset.mem_univ v)
    (fun v _ _ => hP u v)

/-- If rows are probability distributions, each row-crossing mass is at most
one. -/
theorem rowCrossingMass_le_one
    {X : Type u} [Fintype X] [DecidableEq X]
    {P : X → X → ℝ} (hP : ∀ u v, 0 ≤ P u v)
    (hrow : ∀ u, (∑ v : X, P u v) = 1)
    (T : Finset X) (u : X) :
    rowCrossingMass P T u ≤ 1 := by
  exact (rowCrossingMass_le_rowSum hP T u).trans_eq (hrow u)

/-- The total crossing mass from `T` is at most `|T|` for a stochastic
transition matrix. -/
theorem crossingMass_le_card
    {X : Type u} [Fintype X] [DecidableEq X]
    {P : X → X → ℝ} (hP : ∀ u v, 0 ≤ P u v)
    (hrow : ∀ u, (∑ v : X, P u v) = 1)
    (T : Finset X) :
    crossingMass P T ≤ (T.card : ℝ) := by
  unfold crossingMass
  calc
    (∑ u ∈ T, rowCrossingMass P T u)
        ≤ ∑ _u ∈ T, (1 : ℝ) := by
          exact Finset.sum_le_sum fun u _ => rowCrossingMass_le_one hP hrow T u
    _ = (T.card : ℝ) := by simp

/-- A single lazy matching round can increase the crossing mass of one row by
at most half the mass sitting on vertices of `T` whose mate is outside `T`. -/
theorem rowCrossingMass_updateMatrix_le
    {X : Type u} [Fintype X] [DecidableEq X]
    (R : LazyRound X) {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v)
    (T : Finset X) (u : X) :
    rowCrossingMass (R.updateMatrix P) T u ≤
      rowCrossingMass P T u +
        (∑ w ∈ R.insideWithMateOutside T, P u w) / 2 := by
  classical
  have hsecond :
      (∑ v ∈ vertexComplement T, P u (R.matching.mate v)) ≤
        rowCrossingMass P T u +
          ∑ w ∈ R.insideWithMateOutside T, P u w := by
    rw [← R.sum_mateImageOutside_eq T (fun w => P u w)]
    exact R.sum_mateImageOutside_le T (fun w => hP u w)
  unfold rowCrossingMass at hsecond
  unfold rowCrossingMass LazyRound.updateMatrix MatchingAcross.lazyStep
  calc
    (∑ v ∈ vertexComplement T,
        (P u v + P u (R.matching.mate v)) / 2)
        = (∑ v ∈ vertexComplement T, P u v) / 2 +
            (∑ v ∈ vertexComplement T, P u (R.matching.mate v)) / 2 := by
          calc
            (∑ v ∈ vertexComplement T,
                (P u v + P u (R.matching.mate v)) / 2)
                = (∑ v ∈ vertexComplement T,
                    (P u v + P u (R.matching.mate v))) / 2 := by
                  rw [Finset.sum_div]
            _ = ((∑ v ∈ vertexComplement T, P u v) +
                    ∑ v ∈ vertexComplement T, P u (R.matching.mate v)) / 2 := by
                  rw [Finset.sum_add_distrib]
            _ = (∑ v ∈ vertexComplement T, P u v) / 2 +
                    (∑ v ∈ vertexComplement T, P u (R.matching.mate v)) / 2 := by
                  ring
    _ ≤ (∑ v ∈ vertexComplement T, P u v) +
          (∑ w ∈ R.insideWithMateOutside T, P u w) / 2 := by
          nlinarith [hsecond]

/-- The total column mass from a set of starting vertices into a finite set of
destinations is at most the number of destinations, provided every column has
total mass one. -/
theorem sum_over_starts_insideWithMateOutside_le_card
    {X : Type u} [Fintype X] [DecidableEq X]
    (R : LazyRound X) {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v)
    (hcol : ∀ v, (∑ u : X, P u v) = 1)
    (T : Finset X) :
    (∑ u ∈ T, ∑ w ∈ R.insideWithMateOutside T, P u w) ≤
      ((R.insideWithMateOutside T).card : ℝ) := by
  classical
  calc
    (∑ u ∈ T, ∑ w ∈ R.insideWithMateOutside T, P u w)
        = ∑ w ∈ R.insideWithMateOutside T, ∑ u ∈ T, P u w := by
          rw [Finset.sum_comm]
    _ ≤ ∑ _w ∈ R.insideWithMateOutside T, (1 : ℝ) := by
          exact Finset.sum_le_sum fun w _ => by
            calc
              (∑ u ∈ T, P u w) ≤ ∑ u : X, P u w := by
                exact Finset.sum_le_sum_of_subset_of_nonneg
                  (by intro u _; exact Finset.mem_univ u)
                  (fun u _ _ => hP u w)
              _ = 1 := hcol w
    _ = ((R.insideWithMateOutside T).card : ℝ) := by simp

/-- One round of the lazy walk increases the total crossing probability across
`T` by at most half the number of matching edges crossing `T`. -/
theorem crossingMass_updateMatrix_le
    {X : Type u} [Fintype X] [DecidableEq X]
    (R : LazyRound X) {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v)
    (hcol : ∀ v, (∑ u : X, P u v) = 1)
    (T : Finset X) :
    crossingMass (R.updateMatrix P) T ≤
      crossingMass P T + ((R.edgeBoundary T).card : ℝ) / 2 := by
  classical
  let I := R.insideWithMateOutside T
  have hinside :
      (∑ u ∈ T, ∑ w ∈ I, P u w) ≤ (I.card : ℝ) := by
    simpa [I] using
      sum_over_starts_insideWithMateOutside_le_card R hP hcol T
  have hIcard : (I.card : ℝ) ≤ ((R.edgeBoundary T).card : ℝ) := by
    exact_mod_cast R.insideWithMateOutside_card_le_edgeBoundary_card T
  unfold crossingMass
  calc
    (∑ u ∈ T, rowCrossingMass (R.updateMatrix P) T u)
        ≤ ∑ u ∈ T,
            (rowCrossingMass P T u + (∑ w ∈ I, P u w) / 2) := by
          exact Finset.sum_le_sum fun u _ => by
            simpa [I] using rowCrossingMass_updateMatrix_le R hP T u
    _ = (∑ u ∈ T, rowCrossingMass P T u) +
          (∑ u ∈ T, ∑ w ∈ I, P u w) / 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ (∑ u ∈ T, rowCrossingMass P T u) +
          ((R.edgeBoundary T).card : ℝ) / 2 := by
          nlinarith

/-- Lemma 4.6 in list-history form, with an arbitrary stochastic starting
matrix: the crossing mass after a history is bounded by the initial crossing
mass plus half the number of boundary matching-edge instances in the history. -/
theorem crossingMass_applyRounds_le
    {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v)
    (hcol : ∀ v, (∑ u : X, P u v) = 1)
    (T : Finset X) :
    crossingMass (applyRounds rounds P) T ≤
      crossingMass P T + (edgeBoundaryCount rounds T : ℝ) / 2 := by
  induction rounds generalizing P with
  | nil =>
      simp
  | cons R rest ih =>
      have hP' : ∀ u v, 0 ≤ R.updateMatrix P u v :=
        R.updateMatrix_nonneg hP
      have hcol' : ∀ v, (∑ u : X, R.updateMatrix P u v) = 1 :=
        R.updateMatrix_col_sum hcol
      have hrest := ih hP' hcol'
      have hone := crossingMass_updateMatrix_le R hP hcol T
      calc
        crossingMass (applyRounds (R :: rest) P) T
            = crossingMass (applyRounds rest (R.updateMatrix P)) T := rfl
        _ ≤ crossingMass (R.updateMatrix P) T +
              (edgeBoundaryCount rest T : ℝ) / 2 := hrest
        _ ≤ crossingMass P T + ((R.edgeBoundary T).card : ℝ) / 2 +
              (edgeBoundaryCount rest T : ℝ) / 2 := by
              nlinarith
        _ = crossingMass P T + (edgeBoundaryCount (R :: rest) T : ℝ) / 2 := by
              simp [edgeBoundaryCount]
              ring

/-- Lemma 4.6 for the walk started from point masses. -/
theorem crossingMass_walkMatrix_le_edgeBoundaryCount_div_two
    {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) (T : Finset X) :
    crossingMass (walkMatrix rounds) T ≤
      (edgeBoundaryCount rounds T : ℝ) / 2 := by
  have h := crossingMass_applyRounds_le rounds
    (fun u v => pointMassMatrix.nonneg u v)
    pointMassMatrix.col_sum T
  simpa [walkMatrix, crossingMass_pointMass_eq_zero T] using h

/-- Starts in `T` whose crossing probability is at most a chosen threshold. -/
noncomputable def lowCrossingStarts {X : Type u} [Fintype X] [DecidableEq X]
    (P : X → X → ℝ) (T : Finset X) (threshold : ℝ) : Finset X :=
  T.filter fun u => rowCrossingMass P T u ≤ threshold

theorem mem_lowCrossingStarts {X : Type u} [Fintype X] [DecidableEq X]
    {P : X → X → ℝ} {T : Finset X} {threshold : ℝ} {u : X} :
    u ∈ lowCrossingStarts P T threshold ↔
      u ∈ T ∧ rowCrossingMass P T u ≤ threshold := by
  simp [lowCrossingStarts]

theorem lowCrossingStarts_subset {X : Type u} [Fintype X] [DecidableEq X]
    (P : X → X → ℝ) (T : Finset X) (threshold : ℝ) :
    lowCrossingStarts P T threshold ⊆ T := by
  intro u hu
  exact (mem_lowCrossingStarts.mp hu).1

/-- Markov-style counting step used after Lemma 4.6: if the average crossing
probability over `T` is at most `1/8`, then at least half the starts in `T`
have crossing probability at most `1/4`. -/
theorem card_le_two_mul_lowCrossingStarts_card_of_crossingMass_le
    {X : Type u} [Fintype X] [DecidableEq X]
    {P : X → X → ℝ} {T : Finset X}
    (hP : ∀ u v, 0 ≤ P u v)
    (hmass : crossingMass P T ≤ (T.card : ℝ) / 8) :
    T.card ≤ 2 * (lowCrossingStarts P T (1 / 4)).card := by
  classical
  let Good := lowCrossingStarts P T (1 / 4)
  let Bad := T.filter fun u => ¬ rowCrossingMass P T u ≤ (1 / 4 : ℝ)
  have hpart : Good.card + Bad.card = T.card := by
    simpa [Good, Bad, lowCrossingStarts] using
      (Finset.card_filter_add_card_filter_not
        (s := T) (p := fun u => rowCrossingMass P T u ≤ (1 / 4 : ℝ)))
  by_contra hnot
  have hltGood : 2 * Good.card < T.card := Nat.lt_of_not_ge hnot
  have hBadLarge : T.card < 2 * Bad.card := by
    omega
  have hBadNonempty : Bad.Nonempty := by
    by_contra hnone
    have hBadEmpty : Bad = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hBadZero : Bad.card = 0 := Finset.card_eq_zero.mpr hBadEmpty
    omega
  have hbad_sum_lt :
      (Bad.card : ℝ) * (1 / 4 : ℝ) <
        ∑ u ∈ Bad, rowCrossingMass P T u := by
    calc
      (Bad.card : ℝ) * (1 / 4 : ℝ)
          = ∑ _u ∈ Bad, (1 / 4 : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ < ∑ u ∈ Bad, rowCrossingMass P T u := by
        exact Finset.sum_lt_sum_of_nonempty hBadNonempty
          (fun u hu => by
            have hbad : ¬ rowCrossingMass P T u ≤ (1 / 4 : ℝ) := by
              simpa [Bad] using (Finset.mem_filter.mp hu).2
            exact lt_of_not_ge hbad)
  have hbad_le_mass :
      ∑ u ∈ Bad, rowCrossingMass P T u ≤ crossingMass P T := by
    unfold crossingMass
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro u hu
        exact (Finset.mem_filter.mp hu).1)
      (fun u _ huBad => rowCrossingMass_nonneg hP T u)
  have hTlt :
      (T.card : ℝ) / 8 < crossingMass P T := by
    have hBadCard : (T.card : ℝ) / 8 < (Bad.card : ℝ) * (1 / 4 : ℝ) := by
      nlinarith [show (T.card : ℝ) < 2 * (Bad.card : ℝ) by
        exact_mod_cast hBadLarge]
    exact hBadCard.trans (hbad_sum_lt.trans_le hbad_le_mass)
  exact (not_lt_of_ge hmass) hTlt

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
