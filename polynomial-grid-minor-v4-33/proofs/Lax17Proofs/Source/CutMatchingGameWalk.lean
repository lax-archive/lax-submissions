import Lax17Proofs.Source.CutMatchingGameRandomWalk

namespace Lax17Proofs

universe u v w

/-!
# Random-walk matrices for cut-matching histories

This file packages a finite sequence of cut-matching rounds as the transition
history for the lazy random walks used in Section 4.  It proves the
row-stochastic and column-stochastic invariants corresponding to Lemma 4.3.
-/

namespace SimpleGraph
namespace CutMatchingGame

open scoped BigOperators


/-- One abstract cut-matching round, with its full bisection and perfect
matching. -/
structure LazyRound (X : Type u) [Fintype X] [DecidableEq X] where
  cut : Bisection X
  matching : MatchingAcross cut

namespace LazyRound

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- Extensionality for lazy rounds.  The matching field is dependent on the
cut, so the second hypothesis is heterogeneous. -/
@[ext]
theorem ext (R S : LazyRound X) (hcut : R.cut = S.cut)
    (hmatching : HEq R.matching S.matching) : R = S := by
  cases R
  cases S
  cases hcut
  cases hmatching
  rfl

/-- Apply one lazy random-walk step to every row of a transition matrix. -/
noncomputable def updateMatrix (R : LazyRound X) (P : X → X → ℝ) : X → X → ℝ :=
  fun u => R.matching.lazyStep (P u)

theorem updateMatrix_nonneg (R : LazyRound X) {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v) :
    ∀ u v, 0 ≤ R.updateMatrix P u v := by
  intro u v
  exact R.matching.lazyStep_nonneg (fun x => hP u x) v

theorem updateMatrix_row_sum (R : LazyRound X) {P : X → X → ℝ}
    (hrow : ∀ u, (∑ v : X, P u v) = 1) :
    ∀ u, (∑ v : X, R.updateMatrix P u v) = 1 := by
  intro u
  rw [updateMatrix, R.matching.sum_lazyStep (P u), hrow u]

theorem updateMatrix_col_sum (R : LazyRound X) {P : X → X → ℝ}
    (hcol : ∀ v, (∑ u : X, P u v) = 1) :
    ∀ v, (∑ u : X, R.updateMatrix P u v) = 1 := by
  intro v
  calc
    (∑ u : X, R.updateMatrix P u v)
        = ∑ u : X, (P u v + P u (R.matching.mate v)) / 2 := by
          rfl
    _ = ((∑ u : X, P u v) + (∑ u : X, P u (R.matching.mate v))) / 2 := by
          rw [← Finset.sum_div]
          rw [Finset.sum_add_distrib]
    _ = (1 + 1) / 2 := by
          rw [hcol v, hcol (R.matching.mate v)]
    _ = 1 := by norm_num

end LazyRound

/-- Initial transition matrix: all mass starting at `u` is at `u`. -/
noncomputable def pointMassMatrix {X : Type u} [DecidableEq X] : X → X → ℝ :=
  fun u v => if v = u then 1 else 0

namespace pointMassMatrix

variable {X : Type u} [Fintype X] [DecidableEq X]

omit [Fintype X] in
theorem nonneg (u v : X) : 0 ≤ pointMassMatrix (X := X) u v := by
  unfold pointMassMatrix
  split <;> norm_num

theorem row_sum (u : X) : (∑ v : X, pointMassMatrix (X := X) u v) = 1 := by
  unfold pointMassMatrix
  simp

theorem col_sum (v : X) : (∑ u : X, pointMassMatrix (X := X) u v) = 1 := by
  unfold pointMassMatrix
  simp

end pointMassMatrix

/-- Apply a list of lazy rounds to an existing transition matrix. -/
noncomputable def applyRounds {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) (P : X → X → ℝ) : X → X → ℝ :=
  match rounds with
  | [] => P
  | R :: rest => applyRounds rest (R.updateMatrix P)

@[simp]
theorem applyRounds_nil {X : Type u} [Fintype X] [DecidableEq X]
    (P : X → X → ℝ) :
    applyRounds ([] : List (LazyRound X)) P = P := rfl

@[simp]
theorem applyRounds_cons {X : Type u} [Fintype X] [DecidableEq X]
    (R : LazyRound X) (rest : List (LazyRound X)) (P : X → X → ℝ) :
    applyRounds (R :: rest) P = applyRounds rest (R.updateMatrix P) := rfl

/-- Appending one round updates the transition matrix produced by the previous
history.  This is the list-form version of Lemma 4.3(2). -/
theorem applyRounds_append_singleton {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) (R : LazyRound X) (P : X → X → ℝ) :
    applyRounds (rounds ++ [R]) P = R.updateMatrix (applyRounds rounds P) := by
  induction rounds generalizing P with
  | nil =>
      rfl
  | cons A rest ih =>
      simp [applyRounds, ih]

/-- Transition matrix after a finite cut-matching history. -/
noncomputable def walkMatrix {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) : X → X → ℝ :=
  applyRounds rounds pointMassMatrix

@[simp]
theorem walkMatrix_nil {X : Type u} [Fintype X] [DecidableEq X] :
    walkMatrix ([] : List (LazyRound X)) = pointMassMatrix := rfl

/-- Lemma 4.3(2) for a history extended by one matching round. -/
theorem walkMatrix_append_singleton {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) (R : LazyRound X) :
    walkMatrix (rounds ++ [R]) = R.updateMatrix (walkMatrix rounds) := by
  exact applyRounds_append_singleton rounds R pointMassMatrix

theorem applyRounds_nonneg {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) {P : X → X → ℝ}
    (hP : ∀ u v, 0 ≤ P u v) :
    ∀ u v, 0 ≤ applyRounds rounds P u v := by
  induction rounds generalizing P with
  | nil =>
      exact hP
  | cons R rest ih =>
      exact ih (R.updateMatrix_nonneg hP)

theorem applyRounds_row_sum {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) {P : X → X → ℝ}
    (hrow : ∀ u, (∑ v : X, P u v) = 1) :
    ∀ u, (∑ v : X, applyRounds rounds P u v) = 1 := by
  induction rounds generalizing P with
  | nil =>
      exact hrow
  | cons R rest ih =>
      exact ih (R.updateMatrix_row_sum hrow)

theorem applyRounds_col_sum {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) {P : X → X → ℝ}
    (hcol : ∀ v, (∑ u : X, P u v) = 1) :
    ∀ v, (∑ u : X, applyRounds rounds P u v) = 1 := by
  induction rounds generalizing P with
  | nil =>
      exact hcol
  | cons R rest ih =>
      exact ih (R.updateMatrix_col_sum hcol)

/-- Lemma 4.3(3): every row of the random-walk matrix sums to one. -/
theorem walkMatrix_row_sum {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) (u : X) :
    (∑ v : X, walkMatrix rounds u v) = 1 :=
  applyRounds_row_sum rounds pointMassMatrix.row_sum u

/-- Lemma 4.3(4): every column of the random-walk matrix sums to one. -/
theorem walkMatrix_col_sum {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) (v : X) :
    (∑ u : X, walkMatrix rounds u v) = 1 :=
  applyRounds_col_sum rounds pointMassMatrix.col_sum v

/-- Nonnegativity of every random-walk probability. -/
theorem walkMatrix_nonneg {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) (u v : X) :
    0 ≤ walkMatrix rounds u v :=
  applyRounds_nonneg rounds (fun u v => pointMassMatrix.nonneg u v) u v

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
