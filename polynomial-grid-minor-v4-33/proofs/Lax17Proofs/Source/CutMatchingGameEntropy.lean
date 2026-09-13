import Lax17Proofs.Source.CutMatchingGameWalk
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen

namespace Lax17Proofs

universe u v w

/-!
# Entropy potential for the cut-matching game

This file defines the Shannon entropy potential used in Section 4 and proves
the local concavity inequality behind Lemma 4.4(3): averaging two
nonnegative probabilities does not decrease their combined entropy.
-/

namespace SimpleGraph
namespace CutMatchingGame

open scoped BigOperators


/-- Entropy contribution of one probability mass.  Mathlib's `negMulLog`
implements the convention `-0 * log 0 = 0`. -/
noncomputable def entropyTerm (x : ℝ) : ℝ :=
  Real.negMulLog x

@[simp]
theorem entropyTerm_zero : entropyTerm 0 = 0 := by
  simp [entropyTerm]

@[simp]
theorem entropyTerm_one : entropyTerm 1 = 0 := by
  simp [entropyTerm]

/-- Entropy of one row of a random-walk matrix. -/
noncomputable def rowEntropy {X : Type u} [Fintype X] (p : X → ℝ) : ℝ :=
  ∑ v : X, entropyTerm (p v)

/-- The paper's potential `Ψ`: the sum of row entropies over all starting
vertices. -/
noncomputable def entropyPotential {X : Type u} [Fintype X] (P : X → X → ℝ) : ℝ :=
  ∑ u : X, rowEntropy (P u)

/-- The two-point entropy inequality used when one matching edge averages two
probabilities. -/
theorem entropyTerm_add_le_two_mul_entropyTerm_average
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    entropyTerm p + entropyTerm q ≤
      2 * entropyTerm ((p + q) / 2) := by
  have hconc :=
    Real.strictConcaveOn_negMulLog.concaveOn.2
      (show p ∈ Set.Ici (0 : ℝ) by simpa using hp)
      (show q ∈ Set.Ici (0 : ℝ) by simpa using hq)
      (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
      (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
      (by norm_num : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1)
  have hhalf :
      (entropyTerm p + entropyTerm q) / 2 ≤
        entropyTerm ((p + q) / 2) := by
    unfold entropyTerm
    convert hconc using 1 <;> ring_nf
  nlinarith

namespace MatchingAcross

variable {X : Type u} [Fintype X] [DecidableEq X] {B : Bisection X}
variable (M : MatchingAcross B)

/-- Sum over all vertices, split according to the two sides of the bisection. -/
theorem sum_eq_sum_left_add_sum_right (f : X → ℝ) :
    (∑ x : X, f x) =
      (∑ x : {x : X // x ∈ B.left}, f x) +
        (∑ x : {x : X // x ∈ B.right}, f x) := by
  classical
  have hunion :
      (∑ x ∈ B.left ∪ B.right, f x) =
        (∑ x ∈ B.left, f x) + (∑ x ∈ B.right, f x) := by
    exact Finset.sum_union B.disjoint
  calc
    (∑ x : X, f x) = ∑ x ∈ (Finset.univ : Finset X), f x := by
      rfl
    _ = ∑ x ∈ B.left ∪ B.right, f x := by
      rw [B.cover]
    _ = (∑ x ∈ B.left, f x) + (∑ x ∈ B.right, f x) := hunion
    _ = (∑ x : {x : X // x ∈ B.left}, f x) +
          (∑ x : {x : X // x ∈ B.right}, f x) := by
      rw [Finset.sum_subtype B.left (fun _ => Iff.rfl) f]
      rw [Finset.sum_subtype B.right (fun _ => Iff.rfl) f]

/-- Reindex a sum over the right side by the matching bijection from the
left side. -/
theorem sum_right_eq_sum_left (f : X → ℝ) :
    (∑ y : {x : X // x ∈ B.right}, f y) =
      ∑ x : {x : X // x ∈ B.left}, f (M.rightEndpoint x) := by
  have h := Fintype.sum_bijective M.toEquiv M.toEquiv.bijective
    (fun x : {x : X // x ∈ B.left} => f (M.rightEndpoint x))
    (fun y : {x : X // x ∈ B.right} => f y)
    (fun _ => rfl)
  exact h.symm

theorem lazyStep_left (p : X → ℝ) (x : {x : X // x ∈ B.left}) :
    M.lazyStep p x = (p x + p (M.rightEndpoint x)) / 2 := by
  simp [MatchingAcross.lazyStep, M.mate_of_mem_left x.2]

theorem lazyStep_rightEndpoint (p : X → ℝ)
    (x : {x : X // x ∈ B.left}) :
    M.lazyStep p (M.rightEndpoint x) =
      (p x + p (M.rightEndpoint x)) / 2 := by
  rw [MatchingAcross.lazyStep, M.mate_of_mem_right (M.rightEndpoint_mem x),
    M.leftEndpoint_rightEndpoint]
  ring

/-- Lemma 4.4(3) in row form: one lazy matching round cannot decrease the
entropy of a random-walk distribution. -/
theorem rowEntropy_le_rowEntropy_lazyStep {p : X → ℝ}
    (hp : ∀ x, 0 ≤ p x) :
    rowEntropy p ≤ rowEntropy (M.lazyStep p) := by
  classical
  have hbefore :
      rowEntropy p =
        ∑ x : {x : X // x ∈ B.left},
          (entropyTerm (p x) + entropyTerm (p (M.rightEndpoint x))) := by
    unfold rowEntropy
    rw [MatchingAcross.sum_eq_sum_left_add_sum_right (B := B)
      (fun x => entropyTerm (p x))]
    rw [M.sum_right_eq_sum_left (fun x => entropyTerm (p x))]
    rw [← Finset.sum_add_distrib]
  have hafter :
      rowEntropy (M.lazyStep p) =
        ∑ x : {x : X // x ∈ B.left},
          2 * entropyTerm ((p x + p (M.rightEndpoint x)) / 2) := by
    unfold rowEntropy
    rw [MatchingAcross.sum_eq_sum_left_add_sum_right (B := B)
      (fun x => entropyTerm (M.lazyStep p x))]
    rw [M.sum_right_eq_sum_left
      (fun x => entropyTerm (M.lazyStep p x))]
    simp_rw [M.lazyStep_left p, M.lazyStep_rightEndpoint p]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hbefore, hafter]
  exact Finset.sum_le_sum fun x _hx =>
    entropyTerm_add_le_two_mul_entropyTerm_average
      (hp x) (hp (M.rightEndpoint x))

end MatchingAcross

namespace LazyRound

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- Lemma 4.4(3) in potential form for a single round. -/
theorem entropyPotential_le_updateMatrix (R : LazyRound X)
    {P : X → X → ℝ} (hP : ∀ u v, 0 ≤ P u v) :
    entropyPotential P ≤ entropyPotential (R.updateMatrix P) := by
  classical
  unfold entropyPotential
  exact Finset.sum_le_sum fun u _hu =>
    R.matching.rowEntropy_le_rowEntropy_lazyStep (fun v => hP u v)

end LazyRound

/-- Entropy potential is nondecreasing along any finite matching history. -/
theorem entropyPotential_le_applyRounds
    {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v) :
    entropyPotential P ≤ entropyPotential (applyRounds rounds P) := by
  induction rounds generalizing P with
  | nil =>
      exact le_rfl
  | cons R rest ih =>
      exact (R.entropyPotential_le_updateMatrix hP).trans
        (ih (R.updateMatrix_nonneg hP))

/-- Starting from the point-mass matrix, the potential after a finite history
is nonnegative and at least the initial value. -/
theorem entropyPotential_pointMass_le_walkMatrix
    {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) :
    entropyPotential (pointMassMatrix (X := X)) ≤
      entropyPotential (walkMatrix rounds) :=
  entropyPotential_le_applyRounds rounds
    (fun u v => pointMassMatrix.nonneg u v)

/-- Lemma 4.4(2) in row form: entropy of a probability distribution on `n`
points is at most `log n`. -/
theorem rowEntropy_le_log_card
    {X : Type u} [Fintype X] (p : X → ℝ)
    (hn : 0 < Fintype.card X)
    (hp_nonneg : ∀ x, 0 ≤ p x)
    (hp_sum : (∑ x : X, p x) = 1) :
    rowEntropy p ≤ Real.log (Fintype.card X : ℝ) := by
  classical
  let n : ℕ := Fintype.card X
  have hnreal_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnreal_ne : (n : ℝ) ≠ 0 := ne_of_gt hnreal_pos
  have hweight :
      (∑ x ∈ (Finset.univ : Finset X), ((n : ℝ)⁻¹ : ℝ)) = 1 := by
    rw [Finset.sum_const]
    simp [n, hnreal_ne]
  have hJ :=
    Real.strictConcaveOn_negMulLog.concaveOn.le_map_sum
      (t := (Finset.univ : Finset X))
      (w := fun _ : X => ((n : ℝ)⁻¹ : ℝ))
      (p := p)
      (fun _ _ => inv_nonneg.mpr (le_of_lt hnreal_pos))
      hweight
      (fun x _ => (show p x ∈ Set.Ici (0 : ℝ) by simpa using hp_nonneg x))
  have hJ' :
      (∑ x : X, (n : ℝ)⁻¹ * Real.negMulLog (p x)) ≤
        Real.negMulLog (∑ x : X, (n : ℝ)⁻¹ * p x) := by
    simpa [smul_eq_mul] using hJ
  have hleft :
      (∑ x : X, (n : ℝ)⁻¹ * Real.negMulLog (p x)) =
        (n : ℝ)⁻¹ * rowEntropy p := by
    rw [← Finset.mul_sum]
    simp [rowEntropy, entropyTerm]
  have harg :
      (∑ x : X, (n : ℝ)⁻¹ * p x) = (n : ℝ)⁻¹ := by
    rw [← Finset.mul_sum, hp_sum, mul_one]
  have hright :
      Real.negMulLog ((n : ℝ)⁻¹) =
        (n : ℝ)⁻¹ * Real.log (n : ℝ) := by
    simp [Real.negMulLog, Real.log_inv]
  have hscaled :
      (n : ℝ)⁻¹ * rowEntropy p ≤
        (n : ℝ)⁻¹ * Real.log (n : ℝ) := by
    simpa [hleft, harg, hright] using hJ'
  have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt hnreal_pos)
  have hninv : (n : ℝ) * (n : ℝ)⁻¹ = 1 := by
    field_simp [hnreal_ne]
  rw [← mul_assoc, hninv, one_mul, ← mul_assoc, hninv, one_mul] at hmul
  simpa [n] using hmul

/-- Lemma 4.4(2): the total potential is at most `n log n` for a
row-stochastic nonnegative matrix. -/
theorem entropyPotential_le_card_mul_log_card
    {X : Type u} [Fintype X] (P : X → X → ℝ)
    (hn : 0 < Fintype.card X)
    (hP_nonneg : ∀ u v, 0 ≤ P u v)
    (hrow : ∀ u, (∑ v : X, P u v) = 1) :
    entropyPotential P ≤
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) := by
  classical
  unfold entropyPotential
  calc
    (∑ u : X, rowEntropy (P u))
        ≤ ∑ _u : X, Real.log (Fintype.card X : ℝ) := by
          exact Finset.sum_le_sum fun u _ =>
            rowEntropy_le_log_card (P u) hn (fun v => hP_nonneg u v) (hrow u)
    _ = (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- Lemma 4.4(2) specialized to the random-walk matrix generated by a finite
matching history. -/
theorem entropyPotential_walkMatrix_le_card_mul_log_card
    {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) (hn : 0 < Fintype.card X) :
    entropyPotential (walkMatrix rounds) ≤
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) :=
  entropyPotential_le_card_mul_log_card (walkMatrix rounds) hn
    (fun u v => walkMatrix_nonneg rounds u v)
    (fun u => walkMatrix_row_sum rounds u)

namespace pointMassMatrix

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- Lemma 4.4(1) in row form: a point mass has zero entropy. -/
theorem rowEntropy_eq_zero (u : X) :
    rowEntropy (pointMassMatrix (X := X) u) = 0 := by
  classical
  unfold rowEntropy pointMassMatrix
  change (∑ x ∈ (Finset.univ : Finset X),
    entropyTerm (if x = u then (1 : ℝ) else 0)) = 0
  rw [Finset.sum_eq_single u]
  · simp [entropyTerm]
  · intro v _hv hvu
    simp [hvu, entropyTerm]
  · intro hu
    exact False.elim (hu (Finset.mem_univ u))

/-- Lemma 4.4(1): the initial potential is zero. -/
theorem entropyPotential_eq_zero :
    entropyPotential (pointMassMatrix (X := X)) = 0 := by
  simp [entropyPotential, rowEntropy_eq_zero]

end pointMassMatrix

/-- Lemma 4.4(3) specialized to histories starting from point masses. -/
theorem entropyPotential_walkMatrix_nonneg
    {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) :
    0 ≤ entropyPotential (walkMatrix rounds) := by
  have hmono := entropyPotential_pointMass_le_walkMatrix (X := X) rounds
  rw [pointMassMatrix.entropyPotential_eq_zero] at hmono
  exact hmono

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
