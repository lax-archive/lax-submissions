import Lax185574.MergeLift
import Lax185574Proofs.Interface.Poly

/-!
The statement of `Lax185574.MergeLift` for the older notion
`Lax185574.Computing.Computes`, derived from the concept.
-/

namespace Lax185574Proofs.Shim.MergeLift

open Lax808846.Ram Lax185574.Encoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ConstructionSequences
open Lax185574Proofs.Interface

theorem exists_program_mergeLift :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n) (P Q : ℕ),
        ℓ ≤ k → P ≠ Q →
        Computes p e c (tree G k q u, P, Q) (tree (merge G P Q) k q u)
          (fun m => c * (m + 1) ^ a) := by
  obtain ⟨A, hA⟩ := Lax185574.MergeLift.exists_program_mergeLift
  refine ⟨A.program, 2 * A.wordExponent, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := hA k q
  refine ⟨c, a + 1, fun n G ℓ u P Q hℓ hPQ => ?_⟩
  have hτ := one_le_length_encode_typeTree (tree G k q u)
  refine old_of_computes_nat (((encode (tree G k q u)).length + 1) ^ a) (by push_cast; rfl)
    (encode_prod_ne_nil _ (encode_typeTree_ne_nil _)) ?_ (h n G ℓ u P Q hℓ hPQ)
  show _ ≤ c * ((encode (tree G k q u, P, Q)).length + 1) ^ (a + 1)
  rw [length_encode_prod]
  calc c * ((encode (tree G k q u)).length + 1) ^ a + c
      ≤ c * ((encode (tree G k q u)).length + (encode (P, Q)).length + 1) ^ a + c := by
        gcongr; omega
    _ ≤ _ := mul_pow_add_le a (by omega)

end Lax185574Proofs.Shim.MergeLift
