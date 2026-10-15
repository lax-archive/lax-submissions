import Mathlib.Tactic
import Lax808846Proofs.Imp
import Lax808846Proofs.Reasoning
import Lax457868Proofs.SaturatedCutoff
import Lax457868Proofs.DrawLogSetup

/-!
Concrete IMP+ source commands for the guarded arithmetic used by the
refined Welzl cutoff.  Multiplication is reached only after its quotient
guard, and addition only after the remaining-capacity guard.
-/

namespace Lax457868Proofs.SaturatedCutoffSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Compute `min n (a*b)` into `cutResult`. -/
def satMulCommand : Com :=
  .ite (.eq (.var "cutB") (.lit 0))
    (.assign "cutResult" (.lit 0))
    (.ite (.lt (.div (.var "n") (.var "cutB")) (.var "cutA"))
      (.assign "cutResult" (.var "n"))
      (.assign "cutResult" (.mul (.var "cutA") (.var "cutB"))))

/-- Compute `min n (a+b)` into `cutResult`. -/
def satAddCommand : Com :=
  .ite (.lt (.var "n") (.var "cutA"))
    (.assign "cutResult" (.var "n"))
    (.ite (.lt (.sub (.var "n") (.var "cutA")) (.var "cutB"))
      (.assign "cutResult" (.var "n"))
      (.assign "cutResult" (.add (.var "cutA") (.var "cutB"))))

private lemma varEval {B : ℕ} {σ : Env} (x : String) (h : σ.vars x < B) :
    (Expr.var x).evalB B σ = some (σ.vars x) := evalB_var h

/-- The source multiplication performs no oversized product: its only
executed product branch is guarded by `a ≤ n / b`. -/
lemma satMulCommand_run {B : ℕ} {σ : Env}
    (hn : σ.vars "n" < B) (ha : σ.vars "cutA" < B)
    (hb : σ.vars "cutB" < B) :
    ∃ σ', Run B satMulCommand σ σ' 14 ∧
      σ'.vars "cutResult" = satMul (σ.vars "n") (σ.vars "cutA") (σ.vars "cutB") ∧
      (∀ x, x ≠ "cutResult" → σ'.vars x = σ.vars x) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let n := σ.vars "n"
  let a := σ.vars "cutA"
  let b := σ.vars "cutB"
  have hneval : (Expr.var "n").evalB B σ = some n := varEval "n" hn
  have hae : (Expr.var "cutA").evalB B σ = some a := varEval "cutA" ha
  have hbe : (Expr.var "cutB").evalB B σ = some b := varEval "cutB" hb
  by_cases hz : b = 0
  · let σ' := σ.setVar "cutResult" 0
    have hcond : (Cond.eq (.var "cutB") (.lit 0)).evalB B σ = some true := by
      simp [Cond.evalB, hbe, evalB_lit (by omega : 0 < B), hz]
    have hassign : Run B (.assign "cutResult" (.lit 0)) σ σ' 2 := by
      simpa [σ'] using Run.assign (evalB_lit (by omega : 0 < B))
    have hr := Run.ite_true (d := .ite (.lt (.div (.var "n") (.var "cutB"))
        (.var "cutA")) (.assign "cutResult" (.var "n"))
        (.assign "cutResult" (.mul (.var "cutA") (.var "cutB")))) hcond hassign
    refine ⟨σ', hr.mono (by norm_num [Cond.size, Expr.size] :
      1 + (Cond.eq (.var "cutB") (.lit 0)).size + 2 ≤ 14), ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ', satMul, b, hz]
    · intro x hx; simp [σ', Env.setVar, hx]
    · rfl
    · rfl
    · rfl
  · have hdivval : n / b < B := by
      exact (Nat.div_le_self n b).trans_lt hn
    have hdiv : (Expr.div (.var "n") (.var "cutB")).evalB B σ = some (n / b) :=
      evalB_bin hneval hbe (by simpa using hdivval)
    have hcondEval : (Cond.lt (.div (.var "n") (.var "cutB")) (.var "cutA")).evalB B σ =
        some (decide (n / b < a)) := by
      exact evalB_condLt hdiv hae
    by_cases hguard : n / b < a
    · let σ' := σ.setVar "cutResult" n
      have htruth : (Cond.lt (.div (.var "n") (.var "cutB")) (.var "cutA")).evalB B σ =
          some true := by
        rw [evalB_condLt hdiv hae]
        simp [hguard]
      have hinner : Run B
          (.ite (.lt (.div (.var "n") (.var "cutB")) (.var "cutA"))
            (.assign "cutResult" (.var "n"))
          (.assign "cutResult" (.mul (.var "cutA") (.var "cutB")))) σ σ' 8 := by
        exact Run.ite_true (d := .assign "cutResult" (.mul (.var "cutA") (.var "cutB")))
          htruth
          (by simpa [σ', n] using Run.assign (x := "cutResult") (varEval "n" hn))
      have houter : Run B satMulCommand σ σ' 12 := by
        exact Run.ite_false (d := .ite (.lt (.div (.var "n") (.var "cutB"))
            (.var "cutA")) (.assign "cutResult" (.var "n"))
            (.assign "cutResult" (.mul (.var "cutA") (.var "cutB"))))
          (by simpa [hz] using (evalB_condEq hbe (evalB_lit (by omega : 0 < B)))) hinner
      refine ⟨σ', houter.mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
      · have hnot : ¬ a ≤ n / b := by omega
        simp [σ', satMul, n, a, b, hz, hnot]
      · intro x hx; simp [σ', Env.setVar, hx]
      · rfl
      · rfl
      · rfl
    · let p := a * b
      let σ' := σ.setVar "cutResult" p
      have hsafe : a ≤ n / b := by omega
      have hp : p ≤ n := by
        have hh := (Nat.le_div_iff_mul_le (by omega : 0 < b)).mp hsafe
        simpa [p, Nat.mul_comm] using hh
      have hpeval : (Expr.mul (.var "cutA") (.var "cutB")).evalB B σ = some p := by
        exact evalB_bin hae hbe (by dsimp [p]; omega)
      have hassign : Run B (.assign "cutResult" (.mul (.var "cutA") (.var "cutB"))) σ σ' 4 := by
        simpa [σ'] using Run.assign hpeval
      have hfalse : (Cond.lt (.div (.var "n") (.var "cutB")) (.var "cutA")).evalB B σ =
          some false := by
        rw [evalB_condLt hdiv hae]
        simp [hguard]
      have hinner : Run B
          (.ite (.lt (.div (.var "n") (.var "cutB")) (.var "cutA"))
            (.assign "cutResult" (.var "n"))
          (.assign "cutResult" (.mul (.var "cutA") (.var "cutB")))) σ σ' 10 := by
        exact Run.ite_false (d := .assign "cutResult" (.mul (.var "cutA") (.var "cutB")))
          hfalse hassign
      have houter : Run B satMulCommand σ σ' 14 := by
        exact Run.ite_false (d := .ite (.lt (.div (.var "n") (.var "cutB"))
            (.var "cutA")) (.assign "cutResult" (.var "n"))
            (.assign "cutResult" (.mul (.var "cutA") (.var "cutB"))))
          (by simpa [hz] using (evalB_condEq hbe (evalB_lit (by omega : 0 < B)))) hinner
      refine ⟨σ', houter, ?_, ?_, ?_, ?_, ?_⟩
      · simp [σ', satMul, n, a, b, hz, hsafe, p]
      · intro x hx; simp [σ', Env.setVar, hx]
      · rfl
      · rfl
      · rfl

/-- The source addition performs the sum only after proving that it fits
inside the caller's word bound. -/
lemma satAddCommand_run {B : ℕ} {σ : Env}
    (hn : σ.vars "n" < B) (ha : σ.vars "cutA" < B)
    (hb : σ.vars "cutB" < B) :
    ∃ σ', Run B satAddCommand σ σ' 14 ∧
      σ'.vars "cutResult" = satAdd (σ.vars "n") (σ.vars "cutA") (σ.vars "cutB") ∧
      (∀ x, x ≠ "cutResult" → σ'.vars x = σ.vars x) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let n := σ.vars "n"
  let a := σ.vars "cutA"
  let b := σ.vars "cutB"
  have hneval : (Expr.var "n").evalB B σ = some n := varEval "n" hn
  have hae : (Expr.var "cutA").evalB B σ = some a := varEval "cutA" ha
  have hbe : (Expr.var "cutB").evalB B σ = some b := varEval "cutB" hb
  have hfirst : (Cond.lt (.var "n") (.var "cutA")).evalB B σ =
      some (decide (n < a)) := evalB_condLt hneval hae
  by_cases hna : n < a
  · let σ' := σ.setVar "cutResult" n
    have hrun : Run B satAddCommand σ σ' 6 := by
      exact Run.ite_true (d := .ite (.lt (.sub (.var "n") (.var "cutA"))
          (.var "cutB")) (.assign "cutResult" (.var "n"))
          (.assign "cutResult" (.add (.var "cutA") (.var "cutB"))))
        (by rw [hfirst]; simp [hna])
        (by simpa [satAddCommand] using Run.assign (x := "cutResult") (varEval "n" hn))
    refine ⟨σ', hrun.mono (by norm_num [Cond.size, Expr.size] : 6 ≤ 14), ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ', satAdd, n, a, hna]
    · intro x hx; simp [σ', Env.setVar, hx]
    · rfl
    · rfl
    · rfl
  · have han : a ≤ n := by omega
    have hsub : (Expr.sub (.var "n") (.var "cutA")).evalB B σ = some (n - a) := by
      exact evalB_bin hneval hae (by dsimp [n, a]; omega)
    have hsecond : (Cond.lt (.sub (.var "n") (.var "cutA")) (.var "cutB")).evalB B σ =
        some (decide (n - a < b)) := evalB_condLt hsub hbe
    by_cases hsumGuard : n - a < b
    · let σ' := σ.setVar "cutResult" n
      have hrun : Run B satAddCommand σ σ' 12 := by
        exact Run.ite_false (d := .ite (.lt (.sub (.var "n") (.var "cutA"))
            (.var "cutB")) (.assign "cutResult" (.var "n"))
            (.assign "cutResult" (.add (.var "cutA") (.var "cutB"))))
          (by rw [hfirst]; simp [hna])
          (Run.ite_true (d := .assign "cutResult" (.add (.var "cutA") (.var "cutB")))
            (by rw [hsecond]; simp [hsumGuard])
            (by simpa [σ', n] using Run.assign (x := "cutResult") (varEval "n" hn)))
      refine ⟨σ', hrun.mono (by norm_num : 12 ≤ 14), ?_, ?_, ?_, ?_, ?_⟩
      · simp [σ', satAdd, n, a, b, han, hsumGuard]
      · intro x hx; simp [σ', Env.setVar, hx]
      · rfl
      · rfl
      · rfl
    · let s := a + b
      let σ' := σ.setVar "cutResult" s
      have hsafe : b ≤ n - a := by omega
      have hs : s ≤ n := by dsimp [s]; omega
      have hsumEval : (Expr.add (.var "cutA") (.var "cutB")).evalB B σ = some s := by
        exact evalB_bin hae hbe (by dsimp [s]; omega)
      have hassign : Run B (.assign "cutResult" (.add (.var "cutA") (.var "cutB"))) σ σ' 4 := by
        simpa [σ', s] using Run.assign hsumEval
      have hrun : Run B satAddCommand σ σ' 14 := by
        exact Run.ite_false (d := .ite (.lt (.sub (.var "n") (.var "cutA"))
            (.var "cutB")) (.assign "cutResult" (.var "n"))
            (.assign "cutResult" (.add (.var "cutA") (.var "cutB"))))
          (by rw [hfirst]; simp [hna])
          (Run.ite_false (d := .assign "cutResult" (.add (.var "cutA") (.var "cutB")))
            (by rw [hsecond]; simp [hsumGuard]) hassign)
      refine ⟨σ', hrun, ?_, ?_, ?_, ?_, ?_⟩
      · simp [σ', satAdd, n, a, b, han, hsumGuard, s]
      · intro x hx; simp [σ', Env.setVar, hx]
      · rfl
      · rfl
      · rfl

end Lax457868Proofs.SaturatedCutoffSource
