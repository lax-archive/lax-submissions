import Lax185574Proofs.ResolveRam.Glue.Lib

/-!
The values of a bounded run stay below the bound.

`EnvLt B σ`: every scalar, every array entry and every input number of
`σ` is below `B`. A bounded run keeps this (`Run.envLt`), since every
value it stores is the value of a bounded evaluation or an input number.
The initial environment of a round has it when the input is below `B`
(`envLt_init`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- All values of an environment are below `B`. -/
structure EnvLt (B : ℕ) (σ : Env) : Prop where
  vars : ∀ y, σ.vars y < B
  arrs : ∀ a, ∀ v ∈ σ.arrs a, v < B
  inp : ∀ v ∈ σ.inp, v < B

theorem evalB_lt {B : ℕ} {σ : Env} {e : Expr} {v : ℕ} (h : e.evalB B σ = some v) : v < B :=
  (Expr.eval_and_lt_of_evalB h).2

theorem BigStepB.envLt {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k)
    (hσ : EnvLt B σ) : EnvLt B σ' := by
  induction h with
  | skip => exact hσ
  | assign h =>
    refine ⟨fun y => ?_, hσ.arrs, hσ.inp⟩
    simp only [Env.setVar]; split_ifs
    · exact evalB_lt h
    · exact hσ.vars y
  | store _ he _ =>
    refine ⟨hσ.vars, fun a v hv => ?_, hσ.inp⟩
    simp only [Env.setArr] at hv; split_ifs at hv with ha
    · subst ha
      rcases List.mem_or_eq_of_mem_set hv with hv | rfl
      · exact hσ.arrs _ v hv
      · exact evalB_lt he
    · exact hσ.arrs a v hv
  | seq _ _ ih ih' => exact ih' (ih hσ)
  | ite_true _ _ ih => exact ih hσ
  | ite_false _ _ ih => exact ih hσ
  | while_true _ _ _ ih ih' => exact ih' (ih hσ)
  | while_false _ => exact hσ
  | @read σ x v rest h =>
    have hv : v < B := hσ.inp v (by rw [h]; simp)
    refine ⟨fun y => ?_, hσ.arrs, fun u hu => hσ.inp u (by rw [h]; exact List.mem_cons_of_mem _ hu)⟩
    simp only [Env.setVar]; split_ifs
    · exact hv
    · exact hσ.vars y
  | write _ => exact ⟨hσ.vars, hσ.arrs, hσ.inp⟩

/-- **A bounded run keeps all values below the bound.** -/
theorem Run.envLt {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) (hσ : EnvLt B σ) :
    EnvLt B σ' := by
  obtain ⟨_, _, hb⟩ := h; exact BigStepB.envLt hb hσ

theorem envLt_init {B W : ℕ} (ext : String → ℕ) {u : List ℕ} (hu : ∀ v ∈ u, v < B) (hW : W < B) :
    EnvLt B ((initEnv ext u).setVar "W" W) := by
  refine ⟨fun y => ?_, fun a v hv => ?_, fun v hv => hu v (by simpa [Env.setVar, initEnv] using hv)⟩
  · simp only [Env.setVar, initEnv]; split_ifs <;> omega
  · simp only [Env.setVar, initEnv, List.mem_replicate] at hv; omega

theorem EnvLt.setVar {B : ℕ} {σ : Env} (h : EnvLt B σ) (x : String) {v : ℕ} (hv : v < B) :
    EnvLt B (σ.setVar x v) := by
  refine ⟨fun y => ?_, h.arrs, h.inp⟩
  simp only [Env.setVar]; split_ifs
  · exact hv
  · exact h.vars y

end Lax185574Proofs.ResolveRam.Glue
