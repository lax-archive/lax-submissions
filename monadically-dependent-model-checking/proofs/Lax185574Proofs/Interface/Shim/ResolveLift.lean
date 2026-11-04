import Lax185574.ResolveLift
import Lax185574Proofs.Interface.Poly

/-!
The statement of `Lax185574.ResolveLift` for the older notion
`Lax185574.Computing.Computes`, derived from the concept.
-/

namespace Lax185574Proofs.Shim.ResolveLift

open Lax808846.Ram Lax185574.Encoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ConstructionSequences
open Lax185574.DistanceMatrix Lax185574.ResolveLift Lax185574Proofs.Interface

theorem exists_program_resolveLift :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool), 1 ≤ k →
        Computes p e c (G, distMatrix G, P, Q, s, family G k q)
          (resolveBy G s P Q, distMatrix (resolveBy G s P Q), family (resolveBy G s P Q) k q)
          (fun _ => c * (n + 1) ^ 2 *
            (maxTreeSize G k q + treeCount G (resolveBy G s P Q) k q + 1) ^ a) ∧
        ∀ b : Fin n, wordLength (tree (resolveBy G s P Q) k q ![b]) ≤
          c * (treeCount G (resolveBy G s P Q) k q + 1) ^ a := by
  obtain ⟨A, hA⟩ := Lax185574.ResolveLift.exists_program_resolveLift
  refine ⟨A.program, 2 * A.wordExponent, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := hA k q
  refine ⟨c, a, fun n G P Q s hk => ?_⟩
  obtain ⟨hc, hsize⟩ := h n G P Q s hk
  refine ⟨?_, hsize⟩
  set X := (maxTreeSize G k q + treeCount G (resolveBy G s P Q) k q + 1) ^ a with hXdef
  refine old_of_computes_nat (n ^ 2 * X) (by rw [hXdef]; push_cast; rfl)
    (encode_prod_ne_nil _ (encode_partialGraph_ne_nil G)) ?_ hc
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (Nat.succ_pos _)
  show c * (n ^ 2 * X) + c ≤ c * (n + 1) ^ 2 * X
  have h1 : n ^ 2 * X + 1 ≤ (n + 1) ^ 2 * X := by
    have e : (n + 1) ^ 2 * X = n ^ 2 * X + (2 * n + 1) * X := by ring
    have : 1 * 1 ≤ (2 * n + 1) * X := Nat.mul_le_mul (by omega) hX
    omega
  calc c * (n ^ 2 * X) + c = c * (n ^ 2 * X + 1) := by ring
    _ ≤ c * ((n + 1) ^ 2 * X) := Nat.mul_le_mul_left c h1
    _ = c * (n + 1) ^ 2 * X := by ring

end Lax185574Proofs.Shim.ResolveLift
