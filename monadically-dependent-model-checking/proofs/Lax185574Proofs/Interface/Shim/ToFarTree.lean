import Lax185574.ToFarTree
import Lax185574Proofs.Interface.Poly

/-!
The statement of `Lax185574.ToFarTree` for the older notion
`Lax185574.Computing.Computes`, derived from the concept.
-/

namespace Lax185574Proofs.Shim.ToFarTree

open Lax808846.Ram Lax185574.Encoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes Lax185574.FarTrees
open Lax185574Proofs.Interface

theorem exists_program_ftree :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n),
        1 ≤ ℓ → ℓ ≤ k →
        Computes p e c (tree G k (q + 1) u, stp G k (q + 1)) (ftree G k (q + 1) u)
          (fun _ => c * (wordLength (stp G k (q + 1)) + 1) *
            (wordLength (tree G k (q + 1) u) + 1) ^ a) := by
  obtain ⟨A, hA⟩ := Lax185574.ToFarTree.exists_program_ftree
  refine ⟨A.program, 2 * A.wordExponent, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := hA k q
  refine ⟨c, a + 1, fun n G ℓ u h₁ h₂ => ?_⟩
  have hτ := one_le_length_encode_typeTree (tree G k (q + 1) u)
  refine old_of_computes_nat (((encode (stp G k (q + 1))).length + 1) *
      ((encode (tree G k (q + 1) u)).length + 1) ^ a) (by push_cast; rfl)
    (encode_prod_ne_nil _ (encode_typeTree_ne_nil _)) ?_ (h n G ℓ u h₁ h₂)
  show _ ≤ c * ((encode (stp G k (q + 1))).length + 1) *
    ((encode (tree G k (q + 1) u)).length + 1) ^ (a + 1)
  rw [mul_assoc]
  refine mul_add_le_mul (Nat.one_le_iff_ne_zero.mpr (by positivity)) ?_
  rw [← mul_assoc, mul_comm 2, mul_assoc]
  exact Nat.mul_le_mul_left _ (two_mul_pow_le a hτ)

end Lax185574Proofs.Shim.ToFarTree
