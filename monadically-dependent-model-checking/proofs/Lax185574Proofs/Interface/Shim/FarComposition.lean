import Lax185574.FarComposition
import Lax185574Proofs.Interface.Poly

/-!
The statement of `Lax185574.FarComposition` for the older notion
`Lax185574.Computing.Computes`, derived from the concept.
-/

namespace Lax185574Proofs.Shim.FarComposition

open Lax808846.Ram Lax185574.Encoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax3.DistFO (rhoMinus rhoPlus)
open Lax185574Proofs.Interface

theorem exists_program_compose :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ₁ ℓ₂ : ℕ) (u₁ : Fin ℓ₁ → Fin n)
        (u₂ : Fin ℓ₂ → Fin n),
        1 ≤ ℓ₁ → 1 ≤ ℓ₂ → ℓ₁ + ℓ₂ ≤ k →
        (∀ i j, ¬ WithinDist G.resolved (rhoMinus k q) (u₁ i) (u₂ j)) →
        Computes p e c (tree G k q u₁, tree G k q u₂) (tree G k q (Fin.append u₁ u₂))
          (fun m => c * (m + 1) ^ a) := by
  obtain ⟨A, hA⟩ := Lax185574.FarComposition.exists_program_compose
  refine ⟨A.program, 2 * A.wordExponent, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := hA k q
  exact ⟨c, a + 1, fun n G ℓ₁ ℓ₂ u₁ u₂ h₁ h₂ h₃ hfar =>
    poly_of_computes
      (N := ((encode (tree G k q u₁)).length : ℝ) + (encode (tree G k q u₂)).length)
      (by rw [length_encode_prod]; push_cast; rfl)
      (encode_prod_ne_nil _ (encode_typeTree_ne_nil _)) (h n G ℓ₁ ℓ₂ u₁ u₂ h₁ h₂ h₃ hfar)⟩

end Lax185574Proofs.Shim.FarComposition
