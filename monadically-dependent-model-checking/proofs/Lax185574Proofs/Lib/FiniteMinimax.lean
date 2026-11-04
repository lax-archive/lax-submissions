import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.Linarith

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-!
The finite weighted alternative needed for bounded VC duality. Sion's
minimax theorem supplies the distributions. The subsequent conversion
of these distributions to bounded vertex sets needs the half-net lemma.
-/

namespace Lax185574Proofs.Lib.FiniteMinimax

open scoped BigOperators

universe u v

variable {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]

def payoff (M : X → Y → ℝ) (p : X → ℝ) (q : Y → ℝ) : ℝ :=
  ∑ x, ∑ y, p x * q y * M x y

def payoffLeft (M : X → Y → ℝ) (q : Y → ℝ) : (X → ℝ) →ₗ[ℝ] ℝ where
  toFun p := payoff M p q
  map_add' p p' := by simp [payoff, add_mul, Finset.sum_add_distrib]
  map_smul' r p := by simp [payoff, Finset.mul_sum, mul_assoc]

def payoffRight (M : X → Y → ℝ) (p : X → ℝ) : (Y → ℝ) →ₗ[ℝ] ℝ where
  toFun q := payoff M p q
  map_add' q q' := by simp [payoff, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' r q := by simp [payoff, Finset.mul_sum, mul_left_comm, mul_assoc]

/-- A finite matrix admits optimal probability distributions in the
maximin/minimax sense. -/
theorem exists_distributions [Nonempty X] [Nonempty Y] (M : X → Y → ℝ) :
    ∃ p ∈ stdSimplex ℝ X, ∃ q ∈ stdSimplex ℝ Y,
      ∀ p' ∈ stdSimplex ℝ X, ∀ q' ∈ stdSimplex ℝ Y,
        payoff M p' q ≤ payoff M p q' := by
  classical
  have neX : (stdSimplex ℝ X).Nonempty :=
    ⟨Pi.single (Classical.arbitrary X) 1, single_mem_stdSimplex _ _⟩
  have neY : (stdSimplex ℝ Y).Nonempty :=
    ⟨Pi.single (Classical.arbitrary Y) 1, single_mem_stdSimplex _ _⟩
  obtain ⟨q, hq, p, hp, h⟩ := Sion.exists_isSaddlePointOn
    (f := fun q p => payoff M p q)
    neY (convex_stdSimplex ℝ Y) (isCompact_stdSimplex ℝ Y)
    (fun p _ => (payoffRight M p).continuous_on_pi.continuousOn.lowerSemicontinuousOn)
    (fun p _ => ((payoffRight M p).convexOn (convex_stdSimplex ℝ Y)).quasiconvexOn)
    (convex_stdSimplex ℝ X) neX (isCompact_stdSimplex ℝ X)
    (fun q _ => (payoffLeft M q).continuous_on_pi.continuousOn.upperSemicontinuousOn)
    (fun q _ => ((payoffLeft M q).concaveOn (convex_stdSimplex ℝ X)).quasiconcaveOn)
  exact ⟨p, hp, q, hq, fun p' hp' q' hq' => h q' hq' p' hp'⟩

/--
Either a distribution on rows gives every column at least half
its mass in neighbors, or a distribution on columns gives every row
at least half its mass in nonneighbors. -/
theorem relation_half_alternative [Nonempty X] [Nonempty Y] (R : X → Y → Prop)
    [DecidableRel R] :
    (∃ p ∈ stdSimplex ℝ X, ∀ y, (1 : ℝ) / 2 ≤ ∑ x, if R x y then p x else 0) ∨
    (∃ q ∈ stdSimplex ℝ Y, ∀ x, (1 : ℝ) / 2 ≤ ∑ y, if ¬ R x y then q y else 0) := by
  classical
  let M (x : X) (y : Y) : ℝ := if R x y then 1 else 0
  obtain ⟨p, hp, q, hq, h⟩ := exists_distributions M
  have hrow (x : X) : payoff M (Pi.single x 1) q = ∑ y, if R x y then q y else 0 := by
    unfold payoff
    rw [Finset.sum_eq_single x]
    · simp [M, mul_ite]
    · intro x' _ hxx
      simp [hxx]
    · simp
  have hcol (y : Y) : payoff M p (Pi.single y 1) = ∑ x, if R x y then p x else 0 := by
    unfold payoff
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_eq_single y]
    · simp [M, mul_ite]
    · intro y' _ hyy
      simp [hyy]
    · simp
  by_cases hv : (1 : ℝ) / 2 ≤ payoff M p q
  · left
    refine ⟨p, hp, fun y => ?_⟩
    exact hv.trans (by simpa [hcol y] using h p hp (Pi.single y 1) (single_mem_stdSimplex _ _))
  · right
    refine ⟨q, hq, fun x => ?_⟩
    have hx : (∑ y, if R x y then q y else 0) ≤ payoff M p q := by
      simpa [hrow x] using h (Pi.single x 1) (single_mem_stdSimplex _ _) q hq
    have hsum : (∑ y, if R x y then q y else 0) +
        (∑ y, if ¬ R x y then q y else 0) = 1 := by
      rw [← Finset.sum_add_distrib, ← hq.2]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : R x y <;> simp [hy]
    linarith

end Lax185574Proofs.Lib.FiniteMinimax
