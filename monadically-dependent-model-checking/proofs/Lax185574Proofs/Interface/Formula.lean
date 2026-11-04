import Lax185574.FirstOrderLogic
import Lax185574.Encodings
import Lax710763.Transductions
import Mathlib.ModelTheory.Graph

/-!
Formulas of `Lax185574.FirstOrderLogic` in the older logics of the archive.

A formula without colors becomes a formula `FO k` of `Lax3.FirstOrder`.
A formula with colors from `Fin c` becomes a mathlib formula over the
language of graphs expanded by `c` unary color predicates, the colored
language of `Lax710763.Transductions`. Lax3's logic has no colors, so the
colored case needs mathlib. Both translations keep the variables, since
all three logics number them as de Bruijn levels, with the quantifier
binding the next variable. Each translation preserves the semantics.
-/

namespace Lax185574Proofs.Interface

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.FirstOrderLogic Lax3.FirstOrder Lax710763.Transductions

/-! ## Formulas without colors as formulas of Lax3 -/

/-- A formula without colors, as a formula of `Lax3.FirstOrder`. -/
def Formula.toFO : {k : ℕ} → Lax185574.FirstOrderLogic.Formula Empty k → FO k
  | _, .adj i j => .adj i j
  | _, .eq i j => .eq i j
  | _, .not φ => .not (Formula.toFO φ)
  | _, .and φ ψ => .and (Formula.toFO φ) (Formula.toFO ψ)
  | _, .ex φ => .ex (Formula.toFO φ)
  | _, .color c _ => c.elim

theorem sat_toFO_iff (G : Graph) (col : Empty → Set (Fin G.n)) {k : ℕ}
    (φ : Lax185574.FirstOrderLogic.Formula Empty k) (a : Fin k → Fin G.n) :
    Sat G.toSimpleGraph a (Formula.toFO φ) ↔ φ.Holds G col a := by
  induction φ with
  | adj i j => rfl
  | eq i j => rfl
  | not φ ih => exact not_congr (ih a)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ a) (ihψ a)
  | ex φ ih => exact exists_congr fun v => ih (Fin.snoc a v)
  | color c _ => exact c.elim

/-- `G ⊨ φ` is satisfaction of the translated sentence in Lax3's logic. -/
theorem models_iff_sat (G : Graph) (φ : Sentence) :
    G ⊨ φ ↔ Sat G.toSimpleGraph Fin.elim0 (Formula.toFO φ) :=
  (sat_toFO_iff G Empty.elim φ Fin.elim0).symm

/-! ## Formulas with colors as mathlib formulas -/

/-- A formula with colors from `Fin c`, as a bounded mathlib formula over
graphs with `c` colors, whose free variables are the bound positions. -/
def Formula.toBounded {c : ℕ} :
    {k : ℕ} → Lax185574.FirstOrderLogic.Formula (Fin c) k →
      (withColors Language.graph c).BoundedFormula Empty k
  | _, .adj i j => Relations.boundedFormula₂ (Sum.inl adj) (&i) (&j)
  | _, .eq i j => Term.bdEqual (&i) (&j)
  | _, .not φ => (Formula.toBounded φ).not
  | _, .and φ ψ => Formula.toBounded φ ⊓ Formula.toBounded ψ
  | _, .ex φ => (Formula.toBounded φ).ex
  | _, .color d i => Relations.boundedFormula₁ (Sum.inr (ColorRel.color d)) (&i)

theorem realize_toBounded_iff {c : ℕ} (G : Graph) (col : Fin c → Set (Fin G.n)) {k : ℕ}
    (φ : Lax185574.FirstOrderLogic.Formula (Fin c) k) (a : Fin k → Fin G.n) :
    (letI := G.toSimpleGraph.structure
     letI := colorStructure col
     (Formula.toBounded φ).Realize (Empty.elim : Empty → Fin G.n) a) ↔
      φ.Holds G col a := by
  let _ := G.toSimpleGraph.structure
  let _ := colorStructure col
  induction φ with
  | adj i j => exact Iff.rfl
  | eq i j => exact Iff.rfl
  | not φ ih => exact not_congr (ih a)
  | and φ ψ ihφ ihψ =>
    exact BoundedFormula.realize_inf.trans (and_congr (ihφ a) (ihψ a))
  | ex φ ih => exact BoundedFormula.realize_ex.trans (exists_congr fun v => ih (Fin.snoc a v))
  | color d i => exact Iff.rfl

/-- A formula with colors from `Fin c` and the free variables
`x₀, …, x_{k-1}`, as a mathlib formula with free variables `Fin k` over
graphs with `c` colors. -/
noncomputable def Formula.toMathlib {c k : ℕ} (φ : Lax185574.FirstOrderLogic.Formula (Fin c) k) :
    (withColors Language.graph c).Formula (Fin k) :=
  (Formula.toBounded φ).toFormula.relabel (Sum.elim Empty.elim id)

/-- The translation holds in the colored graph exactly when the formula
does, in the form of `Lax710763.Transductions.RealizeIn`. -/
theorem realizeIn_toMathlib_iff {c : ℕ} (G : Graph) (col : Fin c → Set (Fin G.n)) {k : ℕ}
    (φ : Lax185574.FirstOrderLogic.Formula (Fin c) k) (a : Fin k → Fin G.n) :
    RealizeIn G.toSimpleGraph.structure col (Formula.toMathlib φ) a ↔ φ.Holds G col a := by
  rw [← realize_toBounded_iff G col φ a]
  unfold RealizeIn Formula.toMathlib
  let _ := G.toSimpleGraph.structure
  let _ := colorStructure col
  rw [Formula.realize_relabel, BoundedFormula.realize_toFormula]
  apply iff_of_eq
  congr 1
  funext x
  exact x.elim

end Lax185574Proofs.Interface
