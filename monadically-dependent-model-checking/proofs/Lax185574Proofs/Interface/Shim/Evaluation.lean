import Lax185574.Evaluation
import Lax185574Proofs.Interface.Poly

/-!
The statement of `Lax185574.Evaluation` for the older notion
`Lax185574.Computing.Computes`, derived from the concept.
-/

namespace Lax185574Proofs.Shim.Evaluation

open Lax808846.Ram Lax185574.Encoding Lax185574.Computing Lax185574.Algorithms
open Lax185574.PartialGraphs Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO
open Lax185574.TypeTrees Lax185574Proofs.Interface

open Classical in
theorem exists_program_eval :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n)
        (φ : DistFO ℓ), ℓ ≤ k → DRank k q φ →
        Computes p e c (tree G k q u, φ) (decide (Sat G u φ))
          (fun m => c * (m + 1) ^ a) := by
  obtain ⟨A, hA⟩ := Lax185574.Evaluation.exists_program_eval
  refine ⟨A.program, 2 * A.wordExponent, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := hA k q
  refine ⟨c, a + 1, fun n G ℓ u φ hℓ hφ => ?_⟩
  have h' := h n G ℓ u φ hℓ hφ
  unfold Algorithm.Decides at h'
  convert poly_of_computes
    (N := ((encode (tree G k q u)).length : ℝ) + (encode φ).length)
    (by rw [length_encode_prod]; push_cast; rfl)
    (encode_prod_ne_nil _ (encode_typeTree_ne_nil _)) h'

end Lax185574Proofs.Shim.Evaluation
