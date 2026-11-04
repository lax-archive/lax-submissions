import Lax185574Proofs.ResolveRam.Glue.PCT0
import Lax185574Proofs.ResolveRam.Glue.HW
import Lax185574Proofs.Conversions.Ram.MergeOut

/-!
The matrices of the resolved graph as expressions.

The tests of the matrix fill are arithmetic on `0`/`1` values: equality
`eqX`, negation `notX`, conjunction `andX` and disjunction `orX`. The
entry `(a, b)` of the edges after the resolve is
`E[a,b] ∨ (s ∧ a ≠ b ∧ between ∧ ¬ N[a,b])` (`rsE`, `rsE_evalB`), and
the non-edges are the same with `E`, `N` exchanged and the sign negated.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram

/-- Equality of two values. -/
def eqX (e f : Expr) : Expr := .sub (.sub (.lit 1) (.sub e f)) (.sub f e)

/-- Negation of a `0`/`1` value. -/
def notX (e : Expr) : Expr := .sub (.lit 1) e

/-- Conjunction of `0`/`1` values. -/
def andX (e f : Expr) : Expr := .mul e f

/-- Disjunction of `0`/`1` values. -/
def orX (e f : Expr) : Expr := .sub (.add e f) (.mul e f)

variable {B : ℕ} {σ : Env}

theorem eqX_evalB {e f : Expr} {x y : ℕ} (he : e.evalB B σ = some x) (hf : f.evalB B σ = some y)
    (hB : 1 < B) : (eqX e f).evalB B σ = some (ind (x = y)) := by
  have hx := Expr.lt_of_evalB he
  have hy := Expr.lt_of_evalB hf
  unfold eqX ind
  simp only [Expr.sub_def, evalB_bin_iff, evalB_lit_iff, Bop.apply_sub]
  refine ⟨1 - (x - y), y - x, ⟨1, x - y, ⟨rfl, hB⟩, ⟨x, y, he, hf, rfl, by omega⟩, rfl, by omega⟩,
    ⟨y, x, hf, he, rfl, by omega⟩, ?_, ?_⟩ <;> split_ifs <;> omega

theorem notX_evalB {e : Expr} {p : Prop} (he : e.evalB B σ = some (ind p)) (hB : 1 < B) :
    (notX e).evalB B σ = some (ind (¬ p)) := by
  have hv : 1 - ind p = ind (¬ p) := by unfold ind; by_cases h : p <;> simp [h]
  have h1 := ind_le_one p
  unfold notX
  simp only [Expr.sub_def, evalB_bin_iff, evalB_lit_iff, Bop.apply_sub]
  exact ⟨1, ind p, ⟨rfl, hB⟩, he, hv.symm, by omega⟩

theorem andX_evalB {e f : Expr} {p q : Prop} (he : e.evalB B σ = some (ind p))
    (hf : f.evalB B σ = some (ind q)) (hB : 1 < B) : (andX e f).evalB B σ = some (ind (p ∧ q)) := by
  have hv : ind p * ind q = ind (p ∧ q) := by
    unfold ind; by_cases h : p <;> by_cases h' : q <;> simp [h, h']
  have h1 := ind_le_one (p ∧ q)
  unfold andX
  simp only [Expr.mul_def, evalB_bin_iff, Bop.apply_mul]
  exact ⟨ind p, ind q, he, hf, hv.symm, by omega⟩

theorem orX_evalB {e f : Expr} {p q : Prop} (he : e.evalB B σ = some (ind p))
    (hf : f.evalB B σ = some (ind q)) (hB : 2 < B) : (orX e f).evalB B σ = some (ind (p ∨ q)) := by
  have hv : ind p + ind q - ind p * ind q = ind (p ∨ q) := by
    unfold ind; by_cases h : p <;> by_cases h' : q <;> simp [h, h']
  have h1 := ind_le_one p
  have h2 := ind_le_one q
  have h3 := ind_le_one (p ∨ q)
  have h4 : ind p * ind q ≤ 1 := by nlinarith
  unfold orX
  simp only [Expr.sub_def, Expr.add_def, Expr.mul_def, evalB_bin_iff, Bop.apply_mul, Bop.apply_add,
    Bop.apply_sub]
  exact ⟨ind p + ind q, ind p * ind q, ⟨ind p, ind q, he, hf, rfl, by omega⟩, ⟨ind p, ind q, he, hf, rfl, by omega⟩,
    hv.symm, by omega⟩

/-- The pair `a, b` lies between the classes of `gp` and `gq`. -/
def btwX : Expr :=
  orX (andX (eqX (.get "co" (.var "a")) (.var "gp")) (eqX (.get "co" (.var "b")) (.var "gq")))
    (andX (eqX (.get "co" (.var "b")) (.var "gp")) (eqX (.get "co" (.var "a")) (.var "gq")))

/-- **Entry `(a, b)` of a resolved relation.** -/
def rsE (M₁ M₂ : String) (sg : Expr) : Expr :=
  orX (.get M₁ (rm "a" "b")) (andX sg (andX (notX (eqX (.var "a") (.var "b")))
    (andX btwX (notX (.get M₂ (rm "a" "b"))))))

open Classical in
theorem rsE_evalB {M₁ M₂ : String} {sg : Expr} {n i j P Q : ℕ} {col : ℕ → ℕ} {R₁ R₂ : ℕ → ℕ → Prop}
    {S : Prop} (ha : σ.vars "a" = i) (hb : σ.vars "b" = j) (hn : σ.vars "n" = n) (hi : i < n) (hj : j < n)
    (h₁ : Mat σ M₁ n fun u v => ind (R₁ u v)) (h₂ : Mat σ M₂ n fun u v => ind (R₂ u v))
    (hco : σ.arrs "co" = arrOf n col) (hP : σ.vars "gp" = P) (hQ : σ.vars "gq" = Q)
    (hsg : sg.evalB B σ = some (ind S)) (hB : n * n + n + 3 < B) (hcol : ∀ v < n, col v < B)
    (hPB : P < B) (hQB : Q < B) :
    (rsE M₁ M₂ sg).evalB B σ = some (ind (R₁ i j ∨ (S ∧ ¬ i = j ∧
      ((col i = P ∧ col j = Q) ∨ (col j = P ∧ col i = Q)) ∧ ¬ R₂ i j))) := by
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hij : i * n + j < n * n := by
    have := Nat.mul_le_mul_right n (show i + 1 ≤ n by omega)
    rw [Nat.add_mul] at this; omega
  have e₁ : (Expr.get M₁ (rm "a" "b")).evalB B σ = some (ind (R₁ i j)) :=
    h₁.evalB hn ha hb hi hj (by omega) (by omega) (by unfold ind; split_ifs <;> omega)
  have e₂ : (Expr.get M₂ (rm "a" "b")).evalB B σ = some (ind (R₂ i j)) :=
    h₂.evalB hn ha hb hi hj (by omega) (by omega) (by unfold ind; split_ifs <;> omega)
  have ca : (Expr.get "co" (.var "a")).evalB B σ = some (col i) := by
    simp only [evalB_get_iff, evalB_var_iff, hco, ha]
    exact ⟨i, ⟨rfl, by omega⟩, getElem?_arrOf col hi, hcol i hi⟩
  have cb : (Expr.get "co" (.var "b")).evalB B σ = some (col j) := by
    simp only [evalB_get_iff, evalB_var_iff, hco, hb]
    exact ⟨j, ⟨rfl, by omega⟩, getElem?_arrOf col hj, hcol j hj⟩
  have vp : (Expr.var "gp").evalB B σ = some P := by simp [hP, hPB]
  have vq : (Expr.var "gq").evalB B σ = some Q := by simp [hQ, hQB]
  have hB1 : 1 < B := by omega
  have hB2 : 2 < B := by omega
  have hbt : btwX.evalB B σ = some (ind ((col i = P ∧ col j = Q) ∨ (col j = P ∧ col i = Q))) :=
    orX_evalB (andX_evalB (eqX_evalB ca vp hB1) (eqX_evalB cb vq hB1) hB1)
      (andX_evalB (eqX_evalB cb vp hB1) (eqX_evalB ca vq hB1) hB1) hB2
  have hab : (eqX (.var "a") (.var "b")).evalB B σ = some (ind (i = j)) :=
    eqX_evalB (by simp [ha]; omega) (by simp [hb]; omega) hB1
  exact orX_evalB e₁ (andX_evalB hsg (andX_evalB (notX_evalB hab hB1)
    (andX_evalB hbt (notX_evalB e₂ hB1) hB1) hB1) hB1) hB2

/-! ### The length of a graph word -/

theorem sum_map_le (l : List ℕ) (f : ℕ → ℕ) (c : ℕ) (h : ∀ v, f v ≤ c) : (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; have := h a; nlinarith

theorem length_graphWord_le (n : ℕ) (N : ℕ → ℕ → Prop) : (graphWord n N).length ≤ 1 + n * (2 * n + 1) := by
  classical
  simp only [graphWord, List.length_cons, List.length_flatMap, length_elemFrames]
  have := sum_map_le (List.range n) (fun v => 2 * (below n (N v)).length + 1) (2 * n + 1)
    (fun v => by have := length_below_le n (N v); omega)
  simp only [List.length_range] at this
  omega

end Lax185574Proofs.ResolveRam.Glue
