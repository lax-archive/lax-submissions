import Lax235315Proofs.Construction.SourceBounds

/-! The representative indicator arrays contain actual zero-one values.
This matters because deletion tests zero, whereas partition membership tests
one. The property is verified against every store in the literal program. -/

namespace Lax235315Proofs.Construction.BitArrays
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram

def ArrayBits (a : String) (σ : Env) : Prop := ∀ v ∈ σ.arrs a, v ≤ 1

/-- Syntactic check that every write to this array stores a bit literal. -/
def storesBits (a : String) : Com → Bool
  | .store b _ e => if b = a then
      match e with | .lit v => decide (v ≤ 1) | _ => false
    else true
  | .seq c d | .ite _ c d => storesBits a c && storesBits a d
  | .while _ c => storesBits a c
  | _ => true

lemma ArrayBits.setArr {a b : String} {σ : Env} {i v : ℕ}
    (h : ArrayBits a σ) (hv : b = a → v ≤ 1) :
    ArrayBits a (σ.setArr b i v) := by
  intro x hx
  by_cases hab : a = b
  · subst b
    simp only [Env.setArr] at hx
    rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · exact h x hx
    · exact hv rfl
  · exact h x (by simpa [Env.setArr, hab] using hx)

lemma bigStep_preserves {B k : ℕ} {a : String} {c : Com} {σ σ' : Env}
    (hr : BigStepB B c σ σ' k) (hcode : storesBits a c = true)
    (h : ArrayBits a σ) : ArrayBits a σ' := by
  induction hr with
  | skip => exact h
  | assign he => exact h
  | @store σ b i e k v hi he hk =>
      apply h.setArr
      intro hba
      subst b
      simp only [storesBits, if_pos rfl] at hcode
      cases e <;> simp at hcode
      case lit x =>
        have hx := hcode
        have hv := (evalB_lit_iff.mp he).1
        omega
  | seq h₁ h₂ ih₁ ih₂ =>
      have hc := Bool.and_eq_true_iff.mp hcode
      exact ih₂ hc.2 (ih₁ hc.1 h)
  | ite_true hb hc ih => exact ih (Bool.and_eq_true_iff.mp hcode).1 h
  | ite_false hb hc ih => exact ih (Bool.and_eq_true_iff.mp hcode).2 h
  | while_true hb hc hw ihc ihw => exact ihw hcode (ihc hcode h)
  | while_false hb => exact h
  | read hin => exact h
  | write he => exact h

lemma run_preserves {B C : ℕ} {a : String} {c : Com} {σ σ' : Env}
    (hr : Run B c σ σ' C) (hcode : storesBits a c = true)
    (h : ArrayBits a σ) : ArrayBits a σ' := by
  obtain ⟨k, _, hr⟩ := hr
  exact bigStep_preserves hr hcode h

lemma init_arrayBits (a : String) (ext : String → ℕ) (input : List ℕ) :
    ArrayBits a (initEnv ext input) := by
  intro v hv
  simp only [initEnv, List.mem_replicate] at hv
  omega

lemma reductionRound_nextA_bits {B C : ℕ} {σ σ' : Env}
    (hr : Run B reductionRound σ σ' C) (h : ArrayBits "nextA" σ) :
    ArrayBits "nextA" σ' := run_preserves hr (by decide) h

lemma reductionRound_nextB_bits {B C : ℕ} {σ σ' : Env}
    (hr : Run B reductionRound σ σ' C) (h : ArrayBits "nextB" σ) :
    ArrayBits "nextB" σ' := run_preserves hr (by decide) h

lemma welzlCom_next_bits {B C : ℕ} {ext : String → ℕ} {input : List ℕ} {σ : Env}
    (hr : Run B welzlCom (initEnv ext input) σ C) :
    ArrayBits "nextA" σ ∧ ArrayBits "nextB" σ := by
  exact ⟨run_preserves hr (by decide) (init_arrayBits _ _ _),
    run_preserves hr (by decide) (init_arrayBits _ _ _)⟩

end Lax235315Proofs.Construction.BitArrays
