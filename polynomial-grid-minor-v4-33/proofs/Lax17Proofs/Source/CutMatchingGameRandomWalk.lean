import Lax17Proofs.Source.CutMatchingGameDefs

namespace Lax17Proofs

universe u v w

/-!
# Lazy random walks for the cut-matching game

Section 4 of the cut-matching-game paper analyzes the sequence of perfect
matchings through the lazy random walk that, in a round, stays put with
probability `1/2` and crosses the matching edge with probability `1/2`.

This file formalizes the round update and proves the basic stochastic
invariants used in Lemma 4.3: nonnegativity and preservation of total mass.
-/

namespace SimpleGraph
namespace CutMatchingGame

open scoped BigOperators


namespace MatchingAcross

variable {X : Type u} [Fintype X] [DecidableEq X] {B : Bisection X}
variable (M : MatchingAcross B)

/-- The mate of a vertex under a matching across a full bisection. -/
noncomputable def mate (x : X) : X :=
  if hx : x ∈ B.left then
    M.rightEndpoint ⟨x, hx⟩
  else
    M.leftEndpoint ⟨x, (B.mem_right_iff_not_mem_left x).2 hx⟩

theorem mate_of_mem_left {x : X} (hx : x ∈ B.left) :
    M.mate x = M.rightEndpoint ⟨x, hx⟩ := by
  simp [mate, hx]

theorem mate_of_mem_right {x : X} (hx : x ∈ B.right) :
    M.mate x = M.leftEndpoint ⟨x, hx⟩ := by
  have hnot : x ∉ B.left := B.not_mem_left_of_mem_right hx
  simp [mate, hnot]

theorem mate_mem_right_of_mem_left {x : X} (hx : x ∈ B.left) :
    M.mate x ∈ B.right := by
  rw [M.mate_of_mem_left hx]
  exact M.rightEndpoint_mem ⟨x, hx⟩

theorem mate_mem_left_of_mem_right {x : X} (hx : x ∈ B.right) :
    M.mate x ∈ B.left := by
  rw [M.mate_of_mem_right hx]
  exact M.leftEndpoint_mem ⟨x, hx⟩

/-- The matching mate operation is an involution. -/
theorem mate_mate (x : X) : M.mate (M.mate x) = x := by
  by_cases hx : x ∈ B.left
  · rw [M.mate_of_mem_left hx]
    rw [M.mate_of_mem_right (M.rightEndpoint_mem ⟨x, hx⟩)]
    exact M.leftEndpoint_rightEndpoint ⟨x, hx⟩
  · have hxright : x ∈ B.right := (B.mem_right_iff_not_mem_left x).2 hx
    rw [M.mate_of_mem_right hxright]
    rw [M.mate_of_mem_left (M.leftEndpoint_mem ⟨x, hxright⟩)]
    exact M.rightEndpoint_leftEndpoint ⟨x, hxright⟩

theorem mate_injective : Function.Injective M.mate := by
  intro x y hxy
  calc
    x = M.mate (M.mate x) := (M.mate_mate x).symm
    _ = M.mate (M.mate y) := by rw [hxy]
    _ = y := M.mate_mate y

theorem mate_surjective : Function.Surjective M.mate := by
  intro x
  exact ⟨M.mate x, M.mate_mate x⟩

theorem mate_bijective : Function.Bijective M.mate :=
  ⟨M.mate_injective, M.mate_surjective⟩

/-- One lazy matching step applied to a mass function. -/
noncomputable def lazyStep (p : X → ℝ) : X → ℝ :=
  fun x => (p x + p (M.mate x)) / 2

theorem lazyStep_nonneg {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) :
    ∀ x, 0 ≤ M.lazyStep p x := by
  intro x
  unfold lazyStep
  exact div_nonneg (add_nonneg (hp x) (hp (M.mate x))) (by norm_num)

theorem sum_mate (p : X → ℝ) :
    (∑ x : X, p (M.mate x)) = ∑ x : X, p x := by
  exact Fintype.sum_bijective M.mate M.mate_bijective
    (fun x => p (M.mate x)) p (fun _ => rfl)

/-- A lazy matching step preserves total mass. -/
theorem sum_lazyStep (p : X → ℝ) :
    (∑ x : X, M.lazyStep p x) = ∑ x : X, p x := by
  calc
    (∑ x : X, M.lazyStep p x)
        = ∑ x : X, (p x + p (M.mate x)) / 2 := by
          rfl
    _ = ((∑ x : X, p x) + (∑ x : X, p (M.mate x))) / 2 := by
          rw [← Finset.sum_div]
          rw [Finset.sum_add_distrib]
    _ = ((∑ x : X, p x) + (∑ x : X, p x)) / 2 := by
          rw [M.sum_mate p]
    _ = ∑ x : X, p x := by ring

/-- A finite probability distribution, represented as a real-valued function. -/
def IsProbability (p : X → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∑ x : X, p x) = 1

theorem lazyStep_isProbability {p : X → ℝ} (hp : IsProbability p) :
    IsProbability (M.lazyStep p) := by
  constructor
  · exact M.lazyStep_nonneg hp.1
  · rw [M.sum_lazyStep p, hp.2]

end MatchingAcross

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
