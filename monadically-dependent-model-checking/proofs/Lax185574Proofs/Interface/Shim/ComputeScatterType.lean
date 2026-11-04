import Lax185574.ComputeScatterType
import Lax185574Proofs.Interface.Poly

/-!
The statement of `Lax185574.ComputeScatterType` for the older notion
`Lax185574.Computing.Computes`, derived from the concept.
-/

namespace Lax185574Proofs.Shim.ComputeScatterType

open Lax808846.Ram Lax185574.Encoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.ScatterTypes Lax185574.TypeTrees
open Lax185574.DistanceMatrix Lax185574Proofs.Interface

theorem exists_program_stp :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)), 1 ≤ k → 1 ≤ n →
        Computes p e c (G, k, q, distMatrix G, family G k q) (stp G k q)
          (fun _ => c * (n + 1) ^ 2 * (maxTreeSize G k q + 1) ^ a) := by
  obtain ⟨A, hA⟩ := Lax185574.ComputeScatterType.exists_program_stp
  refine ⟨A.program, 2 * A.wordExponent, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := hA k q
  refine ⟨c, a, fun n G hk hn => ?_⟩
  refine old_of_computes_nat (n ^ 2 * (maxTreeSize G k q + 1) ^ a) (by push_cast; rfl)
    (encode_prod_ne_nil _ (encode_partialGraph_ne_nil G)) ?_ (h n G hk hn)
  have hX := Nat.one_le_pow a (maxTreeSize G k q + 1) (Nat.succ_pos _)
  show c * (n ^ 2 * (maxTreeSize G k q + 1) ^ a) + c ≤
    c * (n + 1) ^ 2 * (maxTreeSize G k q + 1) ^ a
  have h1 : n ^ 2 * (maxTreeSize G k q + 1) ^ a + 1 ≤
      (n + 1) ^ 2 * (maxTreeSize G k q + 1) ^ a := by nlinarith
  calc c * (n ^ 2 * (maxTreeSize G k q + 1) ^ a) + c
      = c * (n ^ 2 * (maxTreeSize G k q + 1) ^ a + 1) := by ring
    _ ≤ c * ((n + 1) ^ 2 * (maxTreeSize G k q + 1) ^ a) := Nat.mul_le_mul_left c h1
    _ = c * (n + 1) ^ 2 * (maxTreeSize G k q + 1) ^ a := by ring

end Lax185574Proofs.Shim.ComputeScatterType
