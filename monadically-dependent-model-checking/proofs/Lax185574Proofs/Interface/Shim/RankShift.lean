import Lax185574.RankShift
import Lax185574Proofs.Interface.Poly

/-!
The statement of `Lax185574.RankShift` for the older notion
`Lax185574.Computing.Computes`, derived from the concept.
-/

namespace Lax185574Proofs.Shim.RankShift

open Lax808846.Ram Lax185574.Encoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574Proofs.Interface

theorem exists_program_shift :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n),
        1 ≤ ℓ → ℓ ≤ k →
        Computes p e c (tree G k (q + 1) u) (tree G (k + 1) q u)
          (fun m => c * (m + 1) ^ a) := by
  obtain ⟨A, hA⟩ := Lax185574.RankShift.exists_program_shift
  refine ⟨A.program, 2 * A.wordExponent, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := hA k q
  exact ⟨c, a + 1, fun n G ℓ u h₁ h₂ =>
    poly_of_computes rfl (encode_typeTree_ne_nil _) (h n G ℓ u h₁ h₂)⟩

end Lax185574Proofs.Shim.RankShift
