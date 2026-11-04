import Lax185574.TreeLocality
import Lax185574Proofs.WalkDistance
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Proof of the locality of type trees, following the proof of lem:locality.
-/

namespace Lax185574Proofs.TreeLocality

open Lax185574.PartialGraphs Lax185574.GaifmanGraph
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574.TreeLocality Lax185574Proofs.WalkDistance
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The sum `∑_{i=1}^{m} ρ⁺(k+i, q−i)` of the guard radii of the first
`m` extension steps. -/
def guardSum (k q m : ℕ) : ℕ := ∑ i ∈ Finset.range m, rhoPlus (k + i + 1) (q - i - 1)

theorem guardSum_succ (k q m : ℕ) :
    guardSum k q (m + 1) = guardSum k q m + rhoPlus (k + (m + 1)) (q - (m + 1)) := by
  rw [guardSum, Finset.sum_range_succ, ← guardSum]
  congr 2

theorem guardSum_mono (k q : ℕ) {m m' : ℕ} (h : m ≤ m') : guardSum k q m ≤ guardSum k q m' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- The horizon inequality behind the lemma: the guard radii of `m` steps,
plus the largest radius of an atom after these steps, stay within
`ρ⁺(k, q)`. It follows from `ρ⁺(k+i+1, q−i−1) ≤ ρ⁺(k+i, q−i) / 2`. -/
theorem guardSum_add_le (k q : ℕ) :
    ∀ m, m ≤ q → guardSum k q m + rhoPlus (k + m) (q - m) ≤ rhoPlus k q
  | 0, _ => by simp [guardSum]
  | m + 1, hm => by
    have ih := guardSum_add_le k q m (by omega)
    have h2 := two_mul_rhoPlus_le_rhoPlus (k + m) (q - (m + 1))
    rw [show q - (m + 1) + 1 = q - m by omega, show k + m + 1 = k + (m + 1) by omega] at h2
    rw [guardSum_succ]
    omega

theorem drank_distColorLt {k q ℓ r Y : ℕ} {i : Fin ℓ} (h : DRank k q (.distColorLt r Y i)) :
    r ≤ rhoPlus k q := by
  cases h
  assumption

/--
---
conclusion: Lax185574.TreeLocality.ball_of_guarded
---
By induction along the tuple and the triangle inequality, the entry `vᵢ`
is within `∑_{i'=1}^{i} ρ⁺(k+i', q−i')` of `v₀`. A color mentioned in a
true atom of rank `(k+j, q−j)` has a vertex within the radius of the atom,
at most `ρ⁺(k+j, q−j)`, of an entry. The horizon inequality
`guardSum_add_le` bounds both distances by `ρ⁺(k, q)`.
-/
theorem ball_of_guarded {V : Type*} (G : PartialGraph V) (k q j : ℕ) (hj : j ≤ q)
    (v : Fin (j + 1) → V)
    (hv : ∀ i : Fin (j + 1), 0 < i.val → ∃ i' : Fin (j + 1), i'.val < i.val ∧
      WithinDist G.resolved (rhoPlus (k + i.val) (q - i.val)) (v i') (v i)) :
    (∀ i, v i ∈ G.ball (rhoPlus k q) (v 0)) ∧
    ∀ φ ∈ atp G (k + j) (q - j) v, ∀ Y : ℕ, MentionsColor Y φ →
      ∃ u ∈ G.ball (rhoPlus k q) (v 0), G.color u = Y := by
  have hdist : ∀ (m : ℕ) (i : Fin (j + 1)), i.val ≤ m →
      WithinDist G.resolved (guardSum k q i.val) (v 0) (v i) := by
    intro m
    induction m with
    | zero =>
      intro i hi
      have : i = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      subst this
      exact withinDist_refl _ _ _
    | succ m ih =>
      intro i hi
      rcases Nat.lt_or_ge i.val (m + 1) with h | h
      · exact ih i (by omega)
      · obtain ⟨i', hi', hw⟩ := hv i (by omega)
        have h1 := ih i' (by omega)
        have h2 := withinDist_trans h1 hw
        obtain ⟨t, ht⟩ : ∃ t, i.val = t + 1 := ⟨i.val - 1, by omega⟩
        refine withinDist_mono ?_ h2
        rw [ht, guardSum_succ]
        have := guardSum_mono k q (show i'.val ≤ t by omega)
        rw [← ht]
        omega
  have hS := guardSum_add_le k q j hj
  have hball : ∀ i : Fin (j + 1), WithinDist G.resolved (guardSum k q j) (v 0) (v i) :=
    fun i => withinDist_mono (guardSum_mono k q (by omega)) (hdist j i (by omega))
  refine ⟨fun i => withinDist_mono (by omega) (hball i), ?_⟩
  rintro φ ⟨hatom, hrank, hsat⟩ Y hY
  cases φ with
  | color Y' i =>
    simp only [MentionsColor] at hY
    subst hY
    exact ⟨v i, withinDist_mono (by omega) (hball i), hsat⟩
  | distColorLt r Y' i =>
    simp only [MentionsColor] at hY
    subst hY
    have hr := drank_distColorLt hrank
    · obtain ⟨u, hu, p, hp⟩ := hsat
      refine ⟨u, withinDist_mono ?_ (withinDist_trans (hball i) ⟨p, le_refl _⟩), hu⟩
      omega
  | _ => simp [MentionsColor] at hY

end Lax185574Proofs.TreeLocality
