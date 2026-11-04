import Lax185574Proofs.Lib.Internal.EpsilonNets
import Lax185574Proofs.Lib.EpsilonApproximation
import Mathlib.Tactic.Linarith

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.EpsilonNets

open Lax185574Proofs.Lib.Internal.EpsilonNets Lax185574Proofs.Lib.EpsilonApproximation

universe u

/--
Approximate the distribution to error `ε / 2` on all ranges and take
the set of sampled points. If a range is missed, its empirical frequency
is zero, contradicting its mass being at least `ε`.
-/
theorem finite_epsilon_net (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (𝓕 : Finset (Finset α)), 𝓕.vcDim ≤ d →
      ∀ p ∈ stdSimplex ℝ α, ∃ S : Finset α,
        S.card ≤ N ∧ IsEpsilonNet 𝓕 p ε S := by
  classical
  obtain ⟨N, _, hN⟩ := finite_vc_approximation d (ε / 2) (by linarith)
  refine ⟨N, ?_⟩
  intro α _ _ 𝓕 hd p hp
  obtain ⟨sample, hsample⟩ := hN α 𝓕 hd p hp
  refine ⟨Finset.univ.image sample, ?_, ?_⟩
  · simpa using Finset.card_image_le (s := Finset.univ) (f := sample)
  intro A hA hmass
  by_contra hnot
  have hmiss : ∀ i, sample i ∉ A := by
    intro i hi
    exact hnot ⟨sample i, Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩⟩
  have hdev := hsample A hA
  simp only [hmiss, ↓reduceIte, Finset.sum_const_zero, zero_div, sub_zero] at hdev
  have := le_abs_self (∑ x ∈ A, p x)
  linarith

end Lax185574Proofs.Lib.EpsilonNets
