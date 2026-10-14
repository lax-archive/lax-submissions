import Lax457868.RefinedSample

/-!
Elementary consequences of the refined-sample contract. The randomized
construction itself is not assumed here.
-/

namespace Lax457868Proofs.RefinedSample

open Lax195003.WelzlOrders
open Lax457868.RefinedSample

/-- Refinement is preserved when more ground-set elements are observed. -/
lemma refinedSample_mono {α : Type*} (𝓕 : SetSystem α) (A W U : Set α)
    (m k : ℕ) (hW : IsRefinedSample 𝓕 A W m k)
    (hWU : W ⊆ U) (hUA : U ⊆ A) (hsize : U.ncard ≤ m) :
    IsRefinedSample 𝓕 A U m k := by
  rcases hW with ⟨hA, hfamily, -, -, hsep⟩
  refine ⟨hA, hfamily, hUA, hsize, ?_⟩
  intro X hX Y hY htrace
  apply hsep X hX Y hY
  ext x
  have hmem := congrArg (fun S : Set α => x ∈ S) htrace
  simp only [Set.mem_inter_iff] at hmem ⊢
  constructor
  · intro hx
    exact ⟨(hmem.mp ⟨hx.1, hWU hx.2⟩).1, hx.2⟩
  · intro hx
    exact ⟨(hmem.mpr ⟨hx.1, hWU hx.2⟩).1, hx.2⟩

/-- A sample remains valid if its allowed disagreement threshold is increased. -/
lemma refinedSample_weakenDisagreement {α : Type*} (𝓕 : SetSystem α)
    (A W : Set α) (m k k' : ℕ) (h : IsRefinedSample 𝓕 A W m k)
    (hkk' : k ≤ k') : IsRefinedSample 𝓕 A W m k' := by
  rcases h with ⟨hA, hfamily, hWA, hsize, hsep⟩
  refine ⟨hA, hfamily, hWA, hsize, ?_⟩
  intro X hX Y hY htrace
  exact (hsep X hX Y hY htrace).trans hkk'

end Lax457868Proofs.RefinedSample
