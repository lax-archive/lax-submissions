import Lax185574Proofs.Chain.Ram.TypesRam

/-!
Truth values as the numbers `0` and `1`: conjunction as a product,
disjunction and exclusive or as the bitwise operations, negation as
`1 - x`, and `x < y` as `1 - (1 - (y - x))`.
-/

namespace Lax185574Proofs.Chain.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Conversions.Ram

/-- `1` if the first value is smaller, else `0`. -/
def ltX (e f : Expr) : Expr := .sub (.lit 1) (.sub (.lit 1) (.sub f e))

@[simp] theorem size_ltX (e f : Expr) : (ltX e f).size = e.size + f.size + 5 := by
  simp [ltX]; ring

/-- Negation. -/
def notX (e : Expr) : Expr := .sub (.lit 1) e

@[simp] theorem size_notX (e : Expr) : (notX e).size = e.size + 2 := by simp [notX]; ring

variable {B : ℕ} {σ : Env} {e f : Expr}

theorem evalB_ltX {a b : ℕ} (he : e.evalB B σ = some a) (hf : f.evalB B σ = some b)
    (ha : a < B) (hb : b < B) (hB : 1 < B) : (ltX e f).evalB B σ = some (ind (a < b)) := by
  have h1 := evalB_bin (op := .sub) hf he (by simp; omega)
  have h2 := evalB_bin (op := .sub) (evalB_lit (n := 1) (σ := σ) hB) h1 (by simp; omega)
  have h3 := evalB_bin (op := .sub) (evalB_lit (n := 1) (σ := σ) hB) h2 (by simp; omega)
  unfold ltX; rw [h3]
  unfold ind
  by_cases h : a < b
  · simp [h]; omega
  · simp [h]; omega

theorem evalB_notX {p : Prop} (he : e.evalB B σ = some (ind p)) (hB : 1 < B) :
    (notX e).evalB B σ = some (ind (¬ p)) := by
  have := evalB_bin (op := .sub) (evalB_lit (n := 1) (σ := σ) hB) he
    (by have := ind_le_one p; simp; omega)
  unfold notX; rw [this]; simp [one_sub_ind]

theorem evalB_and01 {p q : Prop} (he : e.evalB B σ = some (ind p))
    (hf : f.evalB B σ = some (ind q)) (hB : 1 < B) :
    (Expr.mul e f).evalB B σ = some (ind (p ∧ q)) := by
  have := evalB_bin (op := .mul) he hf (by
    have := ind_le_one p; have := ind_le_one q; simp; nlinarith)
  rw [Expr.mul_def, this]
  simp only [Bop.apply_mul]
  unfold ind
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem evalB_or01 {p q : Prop} (he : e.evalB B σ = some (ind p))
    (hf : f.evalB B σ = some (ind q)) (hB : 1 < B) :
    (Expr.or e f).evalB B σ = some (ind (p ∨ q)) := by
  have := evalB_bin (op := .or) he hf (by
    rw [Bop.apply_or, lor_ind]; have := ind_le_one (p ∨ q); omega)
  rw [Expr.or_def, this, Bop.apply_or, lor_ind]

theorem xor_ind (p q : Prop) : Nat.xor (ind p) (ind q) = ind (¬ (p ↔ q)) := by
  unfold ind
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> decide

theorem evalB_xor01 {p q : Prop} (he : e.evalB B σ = some (ind p))
    (hf : f.evalB B σ = some (ind q)) (hB : 1 < B) :
    (Expr.xor e f).evalB B σ = some (ind (¬ (p ↔ q))) := by
  have := evalB_bin (op := .xor) he hf (by
    rw [Bop.apply_xor, xor_ind]; have := ind_le_one (¬ (p ↔ q)); omega)
  rw [Expr.xor_def, this, Bop.apply_xor, xor_ind]

theorem evalB_eqX' {a b : ℕ} (he : e.evalB B σ = some a) (hf : f.evalB B σ = some b)
    (ha : a < B) (hb : b < B) (hB : 1 < B) :
    (eqX e f).evalB B σ = some (ind (a = b)) := evalB_eqX he hf ha hb hB

end Lax185574Proofs.Chain.Ram
