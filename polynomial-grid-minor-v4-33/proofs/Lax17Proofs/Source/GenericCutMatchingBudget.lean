import Lax17Proofs.Source.CutMatchingGameBudget
import Lax17Proofs.Source.GenericCutMatchingTranscript

namespace Lax17Proofs

universe u v w

/-!
# A generic logarithmic cut-matching budget

This module converts the entropy budget into a binary-logarithmic round bound
for any positive even terminal type whose cardinality is at most the ambient
parameter `k`.
-/

namespace SimpleGraph
namespace CutMatchingGame

open scoped BigOperators


variable {X : Type u} [Fintype X] [DecidableEq X]

/-- The real logarithm of a positive finite cardinality bounded by `k` is at
most twice the binary logarithm of `k`. -/
theorem real_log_card_le_two_natLog_of_card_le
    {k : ℕ} (hk : 1 < k) (hn : 0 < Fintype.card X)
    (hnk : Fintype.card X ≤ k) :
    Real.log (Fintype.card X : ℝ) ≤ 2 * (Nat.log 2 k : ℝ) := by
  let L := Nat.log 2 k
  have hLpos : 0 < L := Nat.log_pos (by decide : 1 < 2) hk
  have hnR : 0 < (Fintype.card X : ℝ) := by exact_mod_cast hn
  have hkR : 0 < (k : ℝ) := by positivity
  have hnkR : (Fintype.card X : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk
  have hlog_nk :
      Real.log (Fintype.card X : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log hnR hnkR
  have hkpow : k < 2 ^ (L + 1) := by
    simpa [L, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) k
  have hkpowR : (k : ℝ) ≤ ((2 ^ (L + 1) : ℕ) : ℝ) := by
    exact_mod_cast hkpow.le
  have hlog_kpow :
      Real.log (k : ℝ) ≤ Real.log (((2 ^ (L + 1) : ℕ) : ℝ)) :=
    Real.log_le_log hkR hkpowR
  have hpowcast : (((2 ^ (L + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (L + 1) := by
    norm_num
  rw [hpowcast, Real.log_pow] at hlog_kpow
  have hlogtwo_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
    norm_num at h
    exact h
  have hLone : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLpos
  have hlog_k_le : Real.log (k : ℝ) ≤ 2 * (L : ℝ) := by
    have hcoef_nonneg : 0 ≤ (((L + 1 : ℕ) : ℝ)) := by positivity
    have hnat : L + 1 ≤ 2 * L := by omega
    have hcoef : (((L + 1 : ℕ) : ℝ)) ≤ 2 * (L : ℝ) := by
      exact_mod_cast hnat
    calc
      Real.log (k : ℝ) ≤ (((L + 1 : ℕ) : ℝ)) * Real.log 2 := hlog_kpow
      _ ≤ (((L + 1 : ℕ) : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hlogtwo_le_one hcoef_nonneg
      _ ≤ 2 * (L : ℝ) := by simpa using hcoef
  exact hlog_nk.trans (by simpa [L] using hlog_k_le)

/-- A universal positive constant gives a half-expander transcript in at most
`cRound * log_2(k)` rounds, while retaining responder provenance. -/
theorem exists_generic_log_round_halfExpander_with_followsResponder :
    ∃ cRound : ℕ, 0 < cRound ∧
      ∀ {X : Type u} [Fintype X] [DecidableEq X] {k : ℕ},
        1 < k → 0 < Fintype.card X → Even (Fintype.card X) →
          Fintype.card X ≤ k →
            ∀ responder : SequentialResponder X,
              ∃ rounds : List (LazyRound X),
                rounds.length ≤ cRound * Nat.log 2 k ∧
                  IsHalfEdgeExpander rounds ∧
                    FollowsResponder responder 0 rounds := by
  rcases exists_phaseRoundConstant with ⟨C, hCpos, hC⟩
  refine ⟨16 * C + 1, by omega, ?_⟩
  intro X _ _ k hk hn heven hnk responder
  let L := Nat.log 2 k
  let phaseLength := C * L
  have hLpos : 0 < L := Nat.log_pos (by decide : 1 < 2) hk
  rcases heven with ⟨m, hm⟩
  have hm' : 2 * m = Fintype.card X := by omega
  have hlog :=
    real_log_card_le_two_natLog_of_card_le (X := X) hk hn hnk
  have hnR : 0 < (Fintype.card X : ℝ) := by exact_mod_cast hn
  have hLposR : 0 < (L : ℝ) := by exact_mod_cast hLpos
  have hgap_pos : 0 < entropyGapConstant := entropyGapConstant_pos
  have hright :
      2 * (L : ℝ) <
        entropyGapConstant * (phaseLength : ℝ) / 32 := by
    have hphaseCast : (phaseLength : ℝ) = (C : ℝ) * (L : ℝ) := by
      simp [phaseLength]
    rw [hphaseCast]
    nlinarith
  have hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X 1 4 * (phaseLength : ℝ) := by
    unfold sparseCutRoundIncrement
    norm_num
    have hlog' :
        Real.log (Fintype.card X : ℝ) ≤ 2 * (L : ℝ) := by
      simpa [L] using hlog
    nlinarith
  rcases exists_list_halfExpander_with_followsResponder
      (X := X) hm' responder phaseLength hn hbudget with
    ⟨rounds, hlen, hhalf, hfollow⟩
  refine ⟨rounds, ?_, hhalf, hfollow⟩
  rw [hlen]
  dsimp [phaseLength]
  nlinarith

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
