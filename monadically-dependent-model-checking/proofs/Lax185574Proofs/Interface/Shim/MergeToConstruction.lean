import Lax185574.MergeToConstruction
import Lax185574Proofs.LegacyComputing
import Lax185574Proofs.Interface.KitG3

/-!
The statement of `Lax185574.MergeToConstruction` for simple graphs on
`Fin n` and the older `Lax185574.Computing.Computes`, derived from the
concept. The word-length exponent doubles and the constant of the time
bound doubles.
-/

namespace Lax185574Proofs.Shim.MergeToConstruction

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax808846.Ram Lax185574.Encoding Lax185574.Computing
open Lax185574.Partitions Lax185574.MergeSequences Lax185574.BetterMergeSequences
open Lax185574.ConstructionSequences Lax185574.ConstructionWidth
open Lax185574.LocalDefinability Lax185574.FirstOrderTypes
open Lax185574Proofs.Interface Lax185574Proofs.Interface.KitG3

theorem exists_constructionSequence_of_mergeSequence :
    ∃ (p : Program) (e A : ℕ)
      (M : ∀ n : ℕ, SimpleGraph (Fin n) → List (Setoid (Fin n) × SimpleGraph (Fin n)) →
        Script n),
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ms : List (Setoid (Fin n) × SimpleGraph (Fin n))),
        IsMergeSequence G ms →
          IsConstructionSequence G (M n G ms).run ∧
          (∀ v ∈ encode (M n G ms), v ≤ wordLength (M n G ms) + n) ∧
          (M n G ms).run.length ≤ A * (n + 1) * (mergeWidth 1 ms + 1) ∧
          ∀ r : ℕ, 1 ≤ r →
            constructionWidth r (M n G ms).run ≤ max 1 (mergeWidth r ms) ∧
            ((∃ φeq φR : (withColors Language.graph 2).Formula (Fin 2),
                quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
                  StagesDefinable G ms φeq φR) →
              IsRadiusDefinable G (M n G ms).run r (2 * ms.length + 1)
                (max 1 (mergeWidth r ms)) 7)) ∧
      ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n))
        (ms : List (Setoid (Fin n) × SimpleGraph (Fin n))), IsMergeSequence G ms →
          Computes p e c (G, ms) (M n G ms) (fun _ => c * (ms.length + 1) * (n + 1) ^ 2) := by
  obtain ⟨A, c, K, script, hM⟩ :=
    Lax185574.MergeToConstruction.exists_constructionSequence_of_mergeSequence
  refine ⟨A.program, 2 * A.wordExponent, K, fun n G ms => script (toGraph G) ms,
    fun n G ms hm => ?_, 2 * c, fun n G ms hm => ?_⟩
  · obtain ⟨a1, a2, a3, a4, -⟩ := hM (toGraph G) ms hm
    exact ⟨a1, a2, a3, a4⟩
  · have hA := computes_congr (a' := (G, ms)) (encode_graph_pair (toGraph G) ms) rfl
      (hM (toGraph G) ms hm).2.2.2.2
    refine oldComputes_mono (Nat.le_mul_of_pos_left c two_pos) (fun _ => le_rfl)
      (old_of_computes (encode_pair_list_ne_nil G ms) ?_ hA)
    have := one_le_succ_mul_succ_pow ms.length n 2
    simp only [toGraph_n]
    push_cast
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    nlinarith

end Lax185574Proofs.Shim.MergeToConstruction
