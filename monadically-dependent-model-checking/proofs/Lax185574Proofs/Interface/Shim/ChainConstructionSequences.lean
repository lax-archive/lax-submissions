import Lax185574.ChainConstructionSequences
import Lax185574Proofs.LegacyComputing
import Lax185574Proofs.Interface.KitG3

/-!
The statement of `Lax185574.ChainConstructionSequences` for simple
graphs on `Fin n` and the older `Lax185574.Computing.Computes`, derived
from the concept. The word-length exponent doubles and the constant of
the time bound doubles.
-/

namespace Lax185574Proofs.Shim.ChainConstructionSequences

open Lax808846.Ram Lax185574.Encoding Lax185574.Computing
open Lax185574.Chains Lax185574.VCDimension
open Lax185574.ConstructionSequences Lax185574.ConstructionWidth
open Lax185574.LocalDefinability Lax185574.ChainConstructionSequences
open Lax185574Proofs.Interface Lax185574Proofs.Interface.KitG3

theorem exists_constructionSequence_of_chain :
    ∃ (p : Program) (e A : ℕ)
      (M : ∀ n : ℕ, SimpleGraph (Fin n) → List (Finset (Fin n)) → Script n),
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
        IsConstructionSequence G (M n G S).run ∧
        (∀ v ∈ encode (M n G S), v ≤ wordLength (M n G S) + n) ∧
        (M n G S).run.length ≤ A * (n + 1) * (chainBound G S 1 + 1) ∧
        ∀ r : ℕ, 1 ≤ r →
          constructionWidth r (M n G S).run ≤ chainBound G S r ∧
            IsRadiusDefinable G (M n G S).run r (2 * S.length + 1) (chainBound G S r) 7) ∧
      ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
        Computes p e c (G, S) (M n G S) (fun _ => c * (S.length + 1) * (n + 1) ^ 3) := by
  obtain ⟨A, c, K, script, hM⟩ :=
    Lax185574.ChainConstructionSequences.exists_constructionSequence_of_chain
  refine ⟨A.program, 2 * A.wordExponent, K, fun n G S => script (toGraph G) S,
    fun n G S hS => ?_, 2 * c, fun n G S hS => ?_⟩
  · obtain ⟨a1, a2, a3, a4, -⟩ := hM (toGraph G) S hS
    exact ⟨a1, a2, a3, a4⟩
  · have hA := computes_congr (a' := (G, S)) (encode_graph_pair (toGraph G) S) rfl
      (hM (toGraph G) S hS).2.2.2.2
    refine oldComputes_mono (Nat.le_mul_of_pos_left c two_pos) (fun _ => le_rfl)
      (old_of_computes (encode_pair_list_ne_nil G S) ?_ hA)
    have := one_le_succ_mul_succ_pow S.length n 3
    simp only [toGraph_n]
    push_cast
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    nlinarith

end Lax185574Proofs.Shim.ChainConstructionSequences
