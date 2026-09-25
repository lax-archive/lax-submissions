import Lax235315Proofs.Construction.KeySampling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
Counting consequences of the uniform collision-free key sampler.
-/

namespace Lax235315Proofs.Construction.KeySamplingBounds

open Finset
open Lax235315Proofs.Construction.KeySampling
open Lax235315Proofs.Construction.Sampling

/-- Collision-free assignments whose selected sample belongs to `bad`. -/
def badInjections {α : Type*} [Fintype α] [DecidableEq α]
    (M s : ℕ) (bad : Finset (Finset α)) : Finset (KeyInjection α M) :=
  Finset.univ.filter fun f => keySample f s ∈ bad

lemma keySample_mem_samples {α : Type*} [Fintype α] [DecidableEq α]
    {M s : ℕ} (f : KeyInjection α M) (hs : s ≤ Fintype.card α) :
    keySample f s ∈ samples (Finset.univ : Finset α) s := by
  simp only [samples, Finset.mem_powersetCard]
  exact ⟨keySample_subset_univ f, card_keySample f hs⟩

lemma card_badInjections_eq_sum {α : Type*} [Fintype α] [DecidableEq α]
    {M s : ℕ} (bad : Finset (Finset α)) :
    (badInjections M s bad).card =
      ∑ W ∈ bad, (sampleFiber M s W).card := by
  classical
  simpa [badInjections, sampleFiber] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (s := (Finset.univ : Finset (KeyInjection α M)))
      (t := bad) (g := fun f => keySample f s)).symm

lemma card_injections_eq_sum_samples {α : Type*} [Fintype α]
    [DecidableEq α] {M s : ℕ} (hs : s ≤ Fintype.card α) :
    Fintype.card (KeyInjection α M) =
      ∑ W ∈ samples (Finset.univ : Finset α) s,
        (sampleFiber M s W).card := by
  classical
  rw [Fintype.card, Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (KeyInjection α M)))
    (t := samples (Finset.univ : Finset α) s)
    (f := fun f => keySample f s)]
  · apply Finset.sum_congr rfl
    intro W hW
    rfl
  · intro f _
    exact keySample_mem_samples f hs

/-- After conditioning on no key collision, membership in any family of
fixed-size samples has exactly the uniform-subset frequency. -/
lemma card_badInjections_mul_samples {α : Type*} [Fintype α]
    [DecidableEq α] {M s : ℕ} (hs : s ≤ Fintype.card α)
    {bad : Finset (Finset α)}
    (hbad : bad ⊆ samples (Finset.univ : Finset α) s) :
    (badInjections M s bad).card *
        (samples (Finset.univ : Finset α) s).card =
      bad.card * Fintype.card (KeyInjection α M) := by
  classical
  obtain ⟨W₀, hW₀⟩ :=
    (Finset.powersetCard_nonempty (s := (Finset.univ : Finset α))
      (n := s)).2 hs
  let d := (sampleFiber M s W₀).card
  have hall : ∀ W ∈ samples (Finset.univ : Finset α) s,
      (sampleFiber M s W).card = d := by
    intro W hW
    exact card_sampleFiber_eq hW hW₀
  have hbadfib : ∀ W ∈ bad, (sampleFiber M s W).card = d := by
    intro W hW
    exact hall W (hbad hW)
  rw [card_badInjections_eq_sum, card_injections_eq_sum_samples hs,
    Finset.sum_const_nat hbadfib, Finset.sum_const_nat hall]
  ring

end Lax235315Proofs.Construction.KeySamplingBounds
