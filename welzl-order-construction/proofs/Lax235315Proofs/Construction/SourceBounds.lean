import Lax235315Proofs.Construction.MachineBridge
import Mathlib.Tactic

/-! A persistent bound on all source memory and unread input. It supplies the
workspace bounds needed when composing successive verified driver stages. -/

namespace Lax235315Proofs.Construction.SourceBounds
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlSetup
open Lax235315Proofs.Construction.DriverSetup
open Lax235315Proofs.Construction.MachineBridge
open Lax195003.WordRamRandomness Lax11.GraphEncoding

/-- Every scalar, stored array entry, and unread input word fits below B. -/
structure ValuesBounded (B : ℕ) (σ : Env) : Prop where
  vars : ∀ v, σ.vars v < B
  arrays : ∀ a v, v ∈ σ.arrs a → v < B
  input : σ.InpBounded B

lemma ValuesBounded.setVar {B : ℕ} {σ : Env} (h : ValuesBounded B σ)
    (name : String) {v : ℕ} (hv : v < B) : ValuesBounded B (σ.setVar name v) := by
  refine ⟨?_, h.arrays, h.input⟩
  intro y
  simp only [Env.setVar]
  split_ifs
  · exact hv
  · exact h.vars y

lemma ValuesBounded.setArr {B : ℕ} {σ : Env} (h : ValuesBounded B σ)
    (name : String) (i : ℕ) {v : ℕ} (hv : v < B) :
    ValuesBounded B (σ.setArr name i v) := by
  refine ⟨h.vars, ?_, h.input⟩
  intro a x hx
  simp only [Env.setArr] at hx
  split_ifs at hx with ha
  · rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · exact h.arrays name x hx
    · exact hv
  · exact h.arrays a x hx

/-- The input premise is essential: source reads do not themselves test bounds. -/
lemma bigStep_preserves {B k : ℕ} {c : Com} {σ σ' : Env}
    (hr : BigStepB B c σ σ' k) (h : ValuesBounded B σ) :
    ValuesBounded B σ' := by
  induction hr with
  | skip => exact h
  | assign he => exact h.setVar _ (Expr.lt_of_evalB he)
  | store hi he hk => exact h.setArr _ _ (Expr.lt_of_evalB he)
  | seq h₁ h₂ ih₁ ih₂ => exact ih₂ (ih₁ h)
  | ite_true hb hc ih => exact ih h
  | ite_false hb hc ih => exact ih h
  | while_true hb hc hw ihc ihw => exact ihw (ihc h)
  | while_false hb => exact h
  | @read σ name v rest hin =>
      have hv : v < B := h.input v (by rw [hin]; simp)
      have hset := h.setVar name hv
      refine ⟨hset.vars, hset.arrays, ?_⟩
      intro x hx
      exact h.input x (by rw [hin]; simp [hx])
  | write he => exact ⟨h.vars, h.arrays, h.input⟩

lemma run_preserves {B C : ℕ} {c : Com} {σ σ' : Env}
    (hr : Run B c σ σ' C) (h : ValuesBounded B σ) : ValuesBounded B σ' := by
  obtain ⟨k, hk, hr⟩ := hr
  exact bigStep_preserves hr h

lemma init_valuesBounded {B : ℕ} (ext : String → ℕ) {input : List ℕ}
    (hB : 0 < B) (hin : ∀ v ∈ input, v < B) : ValuesBounded B (initEnv ext input) := by
  refine ⟨fun _ => hB, ?_, hin⟩
  intro a v hv
  simp only [initEnv, List.mem_replicate] at hv
  simpa [hv.2] using hB

/-- Setup produces both the canonical driver state and a global memory bound,
for every finite random tape and every valid CSR graph. -/
lemma setup_ready_bounded {c n T : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (ρ : Fin T → Bool) :
    ∃ σ, Run (sourceBound c x) setup
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
        ((c :: x) ++ bitTape ρ)) σ (40 * (x.length + Nat.clog 2 n + 1)) ∧
      Ready c n x (bitTape ρ) σ ∧ ValuesBounded (sourceBound c x) σ := by
  obtain ⟨σ, hr, hready⟩ := setup_run (B := sourceBound c x) (c := c) (bits := bitTape ρ) hx
    (by dsimp [sourceBound]; omega)
  refine ⟨σ, hr, hready, run_preserves hr ?_⟩
  exact init_valuesBounded _ (by dsimp [sourceBound]; omega) (input_bounded hx ρ)

end Lax235315Proofs.Construction.SourceBounds
