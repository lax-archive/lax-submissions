import Lax808846Proofs.Bounds
import Lax808846Proofs.Reasoning
import Mathlib.Tactic

/-! Source execution is stable under appending unread input after a run.
This is the generic noninterference principle behind adaptive bit blocks. -/

namespace Lax235315Proofs.Construction.InputSuffixFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def appendInput (σ : Env) (tail : List ℕ) : Env :=
  { σ with inp := σ.inp ++ tail }

@[simp] lemma appendInput_vars (σ : Env) (tail : List ℕ) :
    (appendInput σ tail).vars = σ.vars := rfl

@[simp] lemma appendInput_arrs (σ : Env) (tail : List ℕ) :
    (appendInput σ tail).arrs = σ.arrs := rfl

@[simp] lemma appendInput_out (σ : Env) (tail : List ℕ) :
    (appendInput σ tail).out = σ.out := rfl

@[simp] lemma appendInput_inp (σ : Env) (tail : List ℕ) :
    (appendInput σ tail).inp = σ.inp ++ tail := rfl

@[simp] lemma expr_evalB_appendInput {B : ℕ} (e : Expr)
    (σ : Env) (tail : List ℕ) :
    e.evalB B (appendInput σ tail) = e.evalB B σ := by
  induction e with
  | lit _ => rfl
  | var _ => rfl
  | get _ i ih => simp [Expr.evalB, ih]
  | bin _ e f ihe ihf => simp [Expr.evalB, ihe, ihf]

@[simp] lemma cond_evalB_appendInput {B : ℕ} (b : Cond)
    (σ : Env) (tail : List ℕ) :
    b.evalB B (appendInput σ tail) = b.evalB B σ := by
  cases b <;> simp [Cond.evalB]

lemma bigStepB_appendInput {B k : ℕ} {c : Com} {σ σ' : Env}
    (h : BigStepB B c σ σ' k) (tail : List ℕ) :
    BigStepB B c (appendInput σ tail) (appendInput σ' tail) k := by
  induction h with
  | skip => exact .skip
  | assign he =>
      simpa [appendInput, Env.setVar] using
        (BigStepB.assign (σ := appendInput _ tail)
          (by simpa using he))
  | store hi he hk =>
      simpa [appendInput, Env.setArr] using
        (BigStepB.store (σ := appendInput _ tail)
          (by simpa using hi) (by simpa using he) (by simpa using hk))
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite_true hb _ ih => exact .ite_true (by simpa using hb) ih
  | ite_false hb _ ih => exact .ite_false (by simpa using hb) ih
  | while_true hb _ _ ih₁ ih₂ => exact .while_true (by simpa using hb) ih₁ ih₂
  | while_false hb => exact .while_false (by simpa using hb)
  | @read σ₀ x v rest hread =>
      simpa [appendInput, Env.setVar, hread] using
        (BigStepB.read (σ := appendInput σ₀ tail) (x := x)
          (v := v) (rest := rest ++ tail)
          (by simp [appendInput, hread]))
  | write he =>
      simpa [appendInput] using
        (BigStepB.write (σ := appendInput _ tail) (by simpa using he))

lemma run_appendInput {B K : ℕ} {c : Com} {σ σ' : Env}
    (h : Run B c σ σ' K) (tail : List ℕ) :
    Run B c (appendInput σ tail) (appendInput σ' tail) K := by
  obtain ⟨k, hk, hstep⟩ := h
  exact ⟨k, hk, bigStepB_appendInput hstep tail⟩

/-- A command run that reads no elements from an empty input can be reused
unchanged on any input tape; the tape is preserved as the suffix. -/
lemma run_on_any_input_of_empty {B K : ℕ} {c : Com} {σ σ' : Env}
    (h : Run B c σ σ' K) (hin : σ.inp = []) (hout : σ'.inp = [])
    (tail : List ℕ) :
    Run B c {σ with inp := tail} {σ' with inp := tail} K := by
  have h' := run_appendInput h tail
  simpa [appendInput, hin, hout] using h'

end Lax235315Proofs.Construction.InputSuffixFrame
