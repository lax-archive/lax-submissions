import Lax235315Proofs.Construction.WelzlProgram
import Lax808846Proofs.Spec
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Verified computation of the ceiling binary logarithm used by the driver. -/

namespace Lax235315Proofs.Construction.WelzlLog

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram

def LogInv (n : ℕ) (τ : Env) : Prop :=
  τ.vars "n" = n ∧ τ.vars "qpow" = 2 ^ τ.vars "L" ∧
    τ.vars "L" ≤ Nat.clog 2 n

lemma computeLog_run {B n : ℕ} {σ : Env}
    (hn : σ.vars "n" = n)
    (hpowB : 2 ^ Nat.clog 2 n < B)
    (hlogB : Nat.clog 2 n + 1 < B) :
    ∃ σ', Run B computeLog σ σ' (12 * Nat.clog 2 n + 8) ∧
      σ'.vars "n" = n ∧ σ'.vars "L" = Nat.clog 2 n ∧
      σ'.vars "qpow" = 2 ^ Nat.clog 2 n := by
  let test : Cond := .lt (.var "qpow") (.var "n")
  let body : Com := seqs [
    .assign "qpow" (.mul (.var "qpow") (.lit 2)), inc "L"]
  have hdef : ∀ τ, LogInv n τ → ∃ v, test.evalB B τ = some v := by
    intro τ hτ
    obtain ⟨hnτ, hqτ, hLτ⟩ := hτ
    have hqB : τ.vars "qpow" < B := by
      rw [hqτ]
      exact lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hLτ) hpowB
    have hnB : n < B := lt_of_le_of_lt (Nat.le_pow_clog (by omega) n) hpowB
    exact ⟨decide (τ.vars "qpow" < τ.vars "n"), by
      simp [test, hqB, hnτ, hnB]⟩
  have hbody : Spec B
      (fun τ => LogInv n τ ∧ test.evalB B τ = some true)
      body
      (fun τ τ' => LogInv n τ' ∧
        Nat.clog 2 n - τ'.vars "L" < Nat.clog 2 n - τ.vars "L") 8 := by
    rintro τ ⟨⟨hnτ, hqτ, hLτ⟩, ht⟩
    have hq_lt_n : τ.vars "qpow" < n := by
      simpa [test, hnτ] using lt_of_condLt_true ht
    have hLlt : τ.vars "L" < Nat.clog 2 n := by
      rw [hqτ] at hq_lt_n
      exact (Nat.lt_clog_iff_pow_lt (by omega)).2 hq_lt_n
    have hq2B : τ.vars "qpow" * 2 < B := by
      rw [hqτ, ← Nat.pow_succ]
      exact lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by omega)) hpowB
    have hLB : τ.vars "L" + 1 < B := lt_of_le_of_lt (by omega) hlogB
    have hqB : τ.vars "qpow" < B := by
      have : 0 < τ.vars "qpow" := by rw [hqτ]; positivity
      omega
    have htwoB : 2 < B := by omega
    have hLB₀ : τ.vars "L" < B := by omega
    have honeB : 1 < B := by omega
    let τ₁ := τ.setVar "qpow" (τ.vars "qpow" * 2)
    let τ₂ := τ₁.setVar "L" (τ.vars "L" + 1)
    have r₁ : Run B (.assign "qpow" (.mul (.var "qpow") (.lit 2)))
        τ τ₁ 4 := by
      exact Run.assign (evalB_bin (evalB_var hqB) (evalB_lit htwoB) hq2B)
    have r₂ : Run B (inc "L") τ₁ τ₂ 4 := by
      apply Run.assign
      exact evalB_bin (evalB_var (by simpa [τ₁] using hLB₀))
        (evalB_lit honeB) (by simpa [τ₁] using hLB)
    refine ⟨τ₂, ?_, ?_⟩
    · simpa [body, seqs] using r₁.seq r₂
    · refine ⟨?_, ?_⟩
      · simpa [LogInv, τ₂, τ₁, hnτ, hqτ, Nat.pow_succ] using hLlt
      · simp [τ₂, τ₁]
        omega
  have hloop : Spec B (LogInv n)
      (.while test body)
      (fun _ τ => LogInv n τ ∧ test.evalB B τ = some false)
      (12 * Nat.clog 2 n + 4) := by
    apply Spec.while_count (I := LogInv n)
      (V := fun τ => Nat.clog 2 n - τ.vars "L") (Kb := 8)
    · exact hdef
    · exact hbody
    · exact fun _ h => h
    · intro τ hτ
      dsimp [test]
      omega
  have hshape : computeLog =
      .seq (.assign "L" (.lit 0))
        (.seq (.assign "qpow" (.lit 1)) (.while test body)) := by
    simp [computeLog, test, body, seqs]
  rw [hshape]
  let σ₀ := σ.setVar "L" 0
  let σ₁ := σ₀.setVar "qpow" 1
  have hzeroB : 0 < B := by omega
  have honeB : 1 < B := by omega
  have r₀ : Run B (.assign "L" (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit hzeroB)
  have r₁ : Run B (.assign "qpow" (.lit 1)) σ₀ σ₁ 2 :=
    Run.assign (evalB_lit honeB)
  have hI₁ : LogInv n σ₁ := by simp [LogInv, σ₁, σ₀, hn]
  obtain ⟨τ, rloop, hpost⟩ := hloop.run hI₁
  obtain ⟨⟨hn', hq', hL'⟩, hfalse⟩ := hpost
  have hn_le_q : n ≤ τ.vars "qpow" := by
    simpa [test, hn'] using le_of_condLt_false hfalse
  have hclog_le : Nat.clog 2 n ≤ τ.vars "L" := by
    rw [hq'] at hn_le_q
    exact (Nat.clog_le_iff_le_pow (by omega)).2 hn_le_q
  refine ⟨τ, (r₀.seq (r₁.seq rloop)).mono (by omega), hn', by omega, ?_⟩
  rw [hq']
  congr
  omega

end Lax235315Proofs.Construction.WelzlLog
