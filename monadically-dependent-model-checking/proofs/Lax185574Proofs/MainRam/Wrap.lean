import Lax185574Proofs.MainRam.Defs
import Lax185574Proofs.Words.Computes

/-!
The output program of a thread: it copies its two input entries, the
flag of the validation and the answer, to the output.
-/

namespace Lax185574Proofs.MainRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Simulation

/-- Copy two entries. -/
def wrapCom : Com :=
  .seq (.read "a") (.seq (.write (.var "a")) (.seq (.read "b") (.write (.var "b"))))

/-- The layout of the output program. -/
def wrapLayout : Layout where
  scalars := ["a", "b"]
  arrays := []
  temps := 4

theorem wrapCom_ok : Com.Ok wrapLayout wrapCom := by
  simp [wrapCom, wrapLayout, Com.Ok, Expr.Ok]

/-- **The output program.** -/
theorem wrapSpec : WrapSpec (compileProgram wrapLayout wrapCom) (wrapLayout.const * 6 + 1) := by
  intro v a b hv ha hb
  have h16 : 16 ≤ 2 ^ v := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
  set σ₀ := initEnv (fun _ => 0) [a, b]
  set σ₁ := { σ₀.setVar "a" a with inp := [b] }
  set σ₂ := { σ₁ with out := σ₁.out ++ [a] }
  set σ₃ := { σ₂.setVar "b" b with inp := [] }
  set σ₄ := { σ₃ with out := σ₃.out ++ [b] }
  have r1 : Run 4 (.read "a") σ₀ σ₁ 1 := Run.read rfl
  have r2 : Run 4 (.write (.var "a")) σ₁ σ₂ (1 + (Expr.var "a").size) :=
    Run.write (evalB_var (by simp [σ₁, Env.setVar]; omega))
  have r3 : Run 4 (.read "b") σ₂ σ₃ 1 := Run.read rfl
  have r4 : Run 4 (.write (.var "b")) σ₃ σ₄ (1 + (Expr.var "b").size) :=
    Run.write (evalB_var (by simp [σ₃, σ₂, σ₁, Env.setVar]; omega))
  have hr : Run 4 wrapCom σ₀ σ₄ 6 := by
    unfold wrapCom
    exact (r1.seq (r2.seq (r3.seq r4))).mono (by simp)
  obtain ⟨k, hk, hbs⟩ := hr
  have hfit : wrapLayout.FitsWords 4 v :=
    ⟨by norm_num, by omega, by simp [Layout.span, wrapLayout]; omega⟩
  obtain ⟨t, ht, hrun⟩ := compileProgram_runsTo hfit wrapCom_ok
    (by intro u hu; simp at hu; omega) hbs
  have hout : σ₄.out = [a, b] := by simp [σ₄, σ₃, σ₂, σ₁, σ₀, initEnv]
  rw [hout] at hrun
  exact ⟨t, le_trans ht (by have := Nat.mul_le_mul_left wrapLayout.const hk; omega), hrun⟩

end Lax185574Proofs.MainRam
