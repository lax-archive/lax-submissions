import Lax185574Proofs.Lib.Internal.EpsilonNets
import Lax185574Proofs.Lib.EpsilonSource.FiniteSupportUC

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-!
Bridge from the finite-support uniform-convergence theorem to finite
weighted set systems. Each range is represented by its Boolean membership
test; this changes neither its probability nor the family's VC dimension.

The mathematical approximation proof is in the attributed `EpsilonSource`
modules. This file only transports that theorem to the public concept's
`Finset.vcDim`, probability-simplex, and empirical-frequency interfaces.
-/

namespace Lax185574Proofs.Lib.EpsilonApproximation

open EpsilonSource

universe u

/--
One positive sample size uniformly approximates every finite set system
of the prescribed VC dimension under every probability distribution.
-/
theorem finite_vc_approximation (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (𝓕 : Finset (Finset α)), 𝓕.vcDim ≤ d →
      ∀ p ∈ stdSimplex ℝ α, ∃ sample : Fin N → α,
        ∀ A ∈ 𝓕,
          |(∑ x ∈ A, p x) - (∑ i : Fin N, if sample i ∈ A then (1 : ℝ) else 0) / N| ≤ ε := by
  classical
  obtain ⟨N, hN, happrox⟩ := finite_support_vc_approx d ε hε
  refine ⟨N, hN, ?_⟩
  intro α _ _ 𝓕 hd p hp
  let tests : Finset (α → Bool) := 𝓕.image (fun A x => decide (x ∈ A))
  have hfamily : boolFamilyToFinsetFamily tests = 𝓕 := by
    simp only [boolFamilyToFinsetFamily, tests, Finset.image_image, Function.comp_def]
    have hf : (fun A : Finset α =>
        Finset.univ.filter (fun x => decide (x ∈ A) = true)) = id := by
      funext A
      ext x
      simp
    rw [hf]
    exact Finset.image_id
  have hvc : EpsilonSource.Finset.boolVCDim tests ≤ d := by
    simpa only [EpsilonSource.Finset.boolVCDim, hfamily] using hd
  let μ : FinitePMF α := ⟨p, hp.1, hp.2⟩
  obtain ⟨sample, hsample⟩ := happrox tests hvc μ
  refine ⟨sample, ?_⟩
  intro A hA
  have hdev := hsample (fun x => decide (x ∈ A))
    (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
  rw [boolTestExpectation_empirical_eq_avg] at hdev
  have htrue : boolTestExpectation μ (fun x => decide (x ∈ A)) = ∑ x ∈ A, p x := by
    simp [boolTestExpectation, trueExpectation, μ, mul_ite]
  rw [htrue] at hdev
  simpa only [decide_eq_true_eq] using hdev

end Lax185574Proofs.Lib.EpsilonApproximation
