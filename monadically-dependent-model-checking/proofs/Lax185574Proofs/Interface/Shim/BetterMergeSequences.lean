import Lax185574.BetterMergeSequences
import Lax185574Proofs.LegacyComputing
import Lax185574Proofs.Interface.KitG3

/-!
The statement of `Lax185574.BetterMergeSequences` for simple graphs on
`Fin n` and the older `Lax185574.Computing.Computes`, derived from the
concept. The word-length exponent doubles and the constant of the time
bound doubles.
-/

namespace Lax185574Proofs.Shim.BetterMergeSequences

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax808846.Ram Lax185574.Encoding Lax185574.Computing
open Lax185574.Partitions Lax185574.MergeSequences Lax185574.Chains
open Lax185574.VCDimension Lax185574.Colorings Lax185574.FirstOrderTypes
open Lax185574.BetterMergeSequences Lax185574Proofs.Interface Lax185574Proofs.Interface.KitG3

theorem exists_mergeSequence_of_chain :
    ∃ (φeq φR : (withColors Language.graph 2).Formula (Fin 2)),
      quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
      ∃ (p : Program) (e : ℕ)
        (M : ∀ n : ℕ, SimpleGraph (Fin n) → List (Finset (Fin n)) →
          List (Setoid (Fin n) × SimpleGraph (Fin n))),
        (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
          IsMergeSequence G (M n G S) ∧ (M n G S).length = S.length ∧
            StagesDefinable G (M n G S) φeq φR ∧
            ∀ r : ℕ, 1 ≤ r →
              mergeWidth r (M n G S) ≤
                chainWidth G (5 * r + 1) S *
                  neighborhoodComplexity G (chainWidth G (5 * r + 1) S)) ∧
        ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
          Computes p e c (G, S) (M n G S) (fun _ => c * (S.length + 1) * (n + 1) ^ 3) := by
  obtain ⟨φeq, φR, h1, h2, A, c, M, hM⟩ :=
    Lax185574.BetterMergeSequences.exists_mergeSequence_of_chain
  refine ⟨φeq, φR, h1, h2, A.program, 2 * A.wordExponent, fun n G S => M (toGraph G) S,
    fun n G S hS => ?_, 2 * c, fun n G S hS => ?_⟩
  · obtain ⟨a1, a2, a3, a4, -⟩ := hM (toGraph G) S hS
    exact ⟨a1, a2, a4, a3⟩
  · have hA := computes_congr (a' := (G, S)) (encode_graph_pair (toGraph G) S) rfl
      (hM (toGraph G) S hS).2.2.2.2
    refine oldComputes_mono (Nat.le_mul_of_pos_left c two_pos) (fun _ => le_rfl)
      (old_of_computes (encode_pair_list_ne_nil G S) ?_ hA)
    have := one_le_succ_mul_succ_pow S.length n 3
    simp only [toGraph_n]
    push_cast
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    nlinarith

end Lax185574Proofs.Shim.BetterMergeSequences
