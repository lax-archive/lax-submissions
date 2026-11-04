import Lax185574.FirstOrderLogic
import Lax710763.Transductions
import Mathlib.ModelTheory.Graph

/-!
Mathlib formulas over graphs with colors as formulas of
`Lax185574.FirstOrderLogic`.

A bounded mathlib formula over the language of graphs expanded by `c`
unary color predicates, with free variables `Fin p` and `m` bound
positions, becomes a formula with colors from `Fin c` and the free
variables `x₀, …, x_{p+m-1}`. The free variable `i` becomes `xᵢ` and the
bound position `j` becomes `x_{p+j}`. Terms are variables, since the
language has no function symbols. Falsity becomes `∃ x, x ≠ x`,
implication is expressed by negation and conjunction, and the universal
quantifier by `¬∃¬`. The translation preserves the semantics.
-/

namespace Lax185574Proofs.Interface

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.FirstOrderLogic Lax710763.Transductions

variable {c p : ℕ}

/-- The variable a term of the colored language stands for. -/
def termVar {m : ℕ} : (withColors Language.graph c).Term (Fin p ⊕ Fin m) → Fin (p + m)
  | .var (.inl i) => Fin.castAdd m i
  | .var (.inr j) => Fin.natAdd p j
  | .func f _ => isEmptyElim f

/-- An atom `R(v)` of the colored language, for a relation symbol `R`. -/
def relFormula {N : ℕ} :
    {l : ℕ} → (withColors Language.graph c).Relations l → (Fin l → Fin N) →
      Lax185574.FirstOrderLogic.Formula (Fin c) N
  | _, Sum.inl .adj, v => .adj (v 0) (v 1)
  | _, Sum.inr (.color d), v => .color d (v 0)

/-- A bounded mathlib formula over graphs with `c` colors, as a formula
with colors from `Fin c` whose variables are the free variables
followed by the bound positions. -/
def Formula.ofBounded :
    {m : ℕ} → (withColors Language.graph c).BoundedFormula (Fin p) m →
      Lax185574.FirstOrderLogic.Formula (Fin c) (p + m)
  | _, .falsum => .ex (.not (.eq (Fin.last _) (Fin.last _)))
  | _, .equal t₁ t₂ => .eq (termVar t₁) (termVar t₂)
  | _, .rel R ts => relFormula R fun i => termVar (ts i)
  | _, .imp φ ψ => .not (.and (Formula.ofBounded φ) (.not (Formula.ofBounded ψ)))
  | _, .all φ => .not (.ex (.not (Formula.ofBounded φ)))

/-- A mathlib formula over graphs with `c` colors and free variables
`Fin p`, as a formula with colors from `Fin c` and the free variables
`x₀, …, x_{p-1}`. -/
def Formula.ofMathlib (φ : (withColors Language.graph c).Formula (Fin p)) :
    Lax185574.FirstOrderLogic.Formula (Fin c) p :=
  Formula.ofBounded φ

section Semantics

variable (G : Graph) (col : Fin c → Set (Fin G.n))

theorem termVar_realize {m : ℕ} (t : (withColors Language.graph c).Term (Fin p ⊕ Fin m))
    (v : Fin p → Fin G.n) (xs : Fin m → Fin G.n) :
    Fin.append v xs (termVar t) =
      (letI := G.toSimpleGraph.structure
       letI := colorStructure col
       t.realize (Sum.elim v xs)) := by
  match t with
  | .var (.inl i) => exact Fin.append_left v xs i
  | .var (.inr j) => exact Fin.append_right v xs j
  | .func f _ => exact isEmptyElim f

theorem holds_relFormula {N l : ℕ} (R : (withColors Language.graph c).Relations l)
    (w : Fin l → Fin G.n) (a : Fin N → Fin G.n) (v : Fin l → Fin N) (hw : a ∘ v = w) :
    (relFormula R v).Holds G col a ↔
      (letI := G.toSimpleGraph.structure
       letI := colorStructure col
       Structure.RelMap R w) := by
  subst hw
  match l, R with
  | _, Sum.inl .adj => exact Iff.rfl
  | _, Sum.inr (.color d) => exact Iff.rfl

theorem holds_ofBounded_iff {m : ℕ} (φ : (withColors Language.graph c).BoundedFormula (Fin p) m)
    (v : Fin p → Fin G.n) (xs : Fin m → Fin G.n) :
    (Formula.ofBounded φ).Holds G col (Fin.append v xs) ↔
      (letI := G.toSimpleGraph.structure
       letI := colorStructure col
       φ.Realize v xs) := by
  let _ := G.toSimpleGraph.structure
  let _ := colorStructure col
  induction φ with
  | falsum =>
    simp only [Formula.ofBounded, Formula.Holds, Fin.snoc_last, not_true_eq_false,
      exists_false, BoundedFormula.Realize]
  | equal t₁ t₂ =>
    simp only [Formula.ofBounded, Formula.Holds, BoundedFormula.Realize, termVar_realize G col]
  | rel R ts =>
    refine (holds_relFormula G col R _ _ _ rfl).trans ?_
    simp only [BoundedFormula.Realize, Function.comp_def, termVar_realize G col]
  | imp φ ψ ihφ ihψ =>
    simp only [Formula.ofBounded, Formula.Holds, BoundedFormula.Realize, ihφ, ihψ]
    tauto
  | all φ ih =>
    simp only [Formula.ofBounded, Formula.Holds, BoundedFormula.Realize, not_exists, not_not]
    refine forall_congr' fun a => ?_
    rw [← Fin.append_snoc]
    exact ih _

/-- The translation holds in the colored graph exactly when the mathlib
formula does, in the form of `Lax710763.Transductions.RealizeIn`. -/
theorem holds_ofMathlib_iff (φ : (withColors Language.graph c).Formula (Fin p))
    (a : Fin p → Fin G.n) :
    (Formula.ofMathlib φ).Holds G col a ↔ RealizeIn G.toSimpleGraph.structure col φ a := by
  have h : Fin.append a (Fin.elim0 : Fin 0 → Fin G.n) = a := by
    rw [Fin.append_elim0]
    rfl
  have h0 : (default : Fin 0 → Fin G.n) = Fin.elim0 := Subsingleton.elim _ _
  unfold Formula.ofMathlib RealizeIn Formula.Realize
  rw [h0, ← holds_ofBounded_iff G col φ a Fin.elim0, h]

end Semantics

end Lax185574Proofs.Interface
