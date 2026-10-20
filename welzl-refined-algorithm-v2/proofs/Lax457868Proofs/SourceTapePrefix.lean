import Lax808846Proofs.Reasoning

/-! A bounded source run depends only on the input words it actually reads.
This transfers a clocked run proved using a padded tape back to its finite
input prefix without changing its result or execution cost. -/

namespace Lax457868Proofs.SourceTapePrefix

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

lemma evalB_with_input (B : ℕ) (e : Expr) (σ : Env) (input : List ℕ) :
    e.evalB B {σ with inp := input} = e.evalB B σ := by
  induction e <;> simp_all [Expr.evalB]

lemma condEvalB_with_input (B : ℕ) (b : Cond) (σ : Env) (input : List ℕ) :
    b.evalB B {σ with inp := input} = b.evalB B σ := by
  cases b <;> simp only [Cond.evalB, evalB_with_input]

/-- The consumed prefix is no longer than the execution cost. Any suffix
can replace the unread input, preserving the exact bounded derivation. -/
lemma consumed_prefix {B k : ℕ} {c : Com} {σ τ : Env}
    (h : BigStepB B c σ τ k) :
    ∃ pre : List ℕ, σ.inp = pre ++ τ.inp ∧ pre.length ≤ k ∧
      ∀ rest : List ℕ, BigStepB B c {σ with inp := pre ++ rest}
        {τ with inp := rest} k := by
  induction h with
  | skip => exact ⟨[], rfl, by simp, fun _ => .skip⟩
  | @assign σ x e v h =>
    refine ⟨[], rfl, by simp, fun rest => ?_⟩
    simpa only [List.nil_append, Env.setVar] using
      (BigStepB.assign (σ := {σ with inp := rest}) (by rw [evalB_with_input]; exact h))
  | @store σ a i e k v hi he hk =>
    refine ⟨[], rfl, by simp, fun rest => ?_⟩
    simpa only [List.nil_append, Env.setArr] using
      (BigStepB.store (σ := {σ with inp := rest}) (by rw [evalB_with_input]; exact hi)
        (by rw [evalB_with_input]; exact he) hk)
  | seq h₁ h₂ ih₁ ih₂ =>
    obtain ⟨p, hp, hpk, hpr⟩ := ih₁
    obtain ⟨q, hq, hqk, hqr⟩ := ih₂
    refine ⟨p ++ q, ?_, by simp only [List.length_append]; omega, ?_⟩
    · rw [hp, hq, List.append_assoc]
    · intro rest
      simpa only [List.append_assoc] using (hpr (q ++ rest)).seq (hqr rest)
  | ite_true hb h ih =>
    obtain ⟨p, hp, hpk, hpr⟩ := ih
    refine ⟨p, hp, by omega, fun rest => ?_⟩
    exact .ite_true (by rw [condEvalB_with_input]; exact hb) (hpr rest)
  | ite_false hb h ih =>
    obtain ⟨p, hp, hpk, hpr⟩ := ih
    refine ⟨p, hp, by omega, fun rest => ?_⟩
    exact .ite_false (by rw [condEvalB_with_input]; exact hb) (hpr rest)
  | while_true hb h₁ h₂ ih₁ ih₂ =>
    obtain ⟨p, hp, hpk, hpr⟩ := ih₁
    obtain ⟨q, hq, hqk, hqr⟩ := ih₂
    refine ⟨p ++ q, ?_, by simp only [List.length_append]; omega, ?_⟩
    · rw [hp, hq, List.append_assoc]
    · intro rest
      simpa only [List.append_assoc] using
        (BigStepB.while_true (by rw [condEvalB_with_input]; exact hb)
          (hpr (q ++ rest)) (hqr rest))
  | while_false hb =>
    refine ⟨[], rfl, by simp, fun rest => ?_⟩
    exact .while_false (by rw [condEvalB_with_input]; exact hb)
  | @read σ x v rest h =>
    refine ⟨[v], h, by simp, fun tail => ?_⟩
    exact .read rfl
  | write h =>
    refine ⟨[], rfl, by simp, fun rest => ?_⟩
    exact .write (by rw [evalB_with_input]; exact h)

/-- Truncating the initial tape to at least the source cost preserves every
observable result. The unread suffix is shortened by exactly that truncation. -/
lemma run_on_prefix {B K N : ℕ} {c : Com} {σ τ : Env}
    (h : Run B c σ τ K) (hKN : K ≤ N) :
    ∃ used : ℕ, used ≤ K ∧
      Run B c {σ with inp := σ.inp.take N}
        {τ with inp := τ.inp.take (N - used)} K := by
  obtain ⟨k, hk, hrun⟩ := h
  obtain ⟨pre, hin, hlen, hreplay⟩ := consumed_prefix hrun
  refine ⟨pre.length, hlen.trans hk, k, hk, ?_⟩
  have htake : σ.inp.take N = pre ++ τ.inp.take (N - pre.length) := by
    rw [hin, List.take_append, List.take_of_length_le (by omega)]
  rw [htake]
  exact hreplay _

/-- A run established with extra padding executes on the original finite
tape whenever that tape contains at least as many words as the run's cost. -/
lemma run_without_padding {B K : ℕ} {c : Com} {σ τ : Env}
    (input padding : List ℕ)
    (hin : σ.inp = input ++ padding) (hK : K ≤ input.length)
    (h : Run B c σ τ K) :
    ∃ τ' : Env, Run B c {σ with inp := input} τ' K ∧
      τ'.vars = τ.vars ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out := by
  obtain ⟨used, _, hr⟩ := run_on_prefix h hK
  have heq : σ.inp.take input.length = input := by simp [hin]
  rw [heq] at hr
  exact ⟨_, hr, rfl, rfl, rfl⟩

end Lax457868Proofs.SourceTapePrefix
