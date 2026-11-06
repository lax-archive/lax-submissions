import Lax185574.PhiPsiPatterns
import Lax710763.MonadicDependence
import Lax710763.Transductions
import Mathlib.Tactic.FinCases

/-!
The formula `γ(x̄, ȳ) = ∃z (U(z) ∧ φ(x̄, z) ∧ ψ(ȳ, z))` of graphs with
one color `U`, used to encode an arbitrary bipartite relation into a
large clean `(φ, ψ)`-pattern.
-/

namespace Lax185574Proofs.PatternFormula

open FirstOrder FirstOrder.Language
open Lax710763.Transductions Lax185574.PhiPsiPatterns

/-- The language of graphs with one color. -/
abbrev L1 : Language := withColors Language.graph 1

variable {p p' : ℕ}

/-- `φ(x̄, z)` with `x̄` placed by `f` among the free variables and `z` the
bound variable. -/
def place {β : Type} {q : ℕ} (φ : Language.graph.Formula (Fin q ⊕ Fin 1)) (f : Fin q → β) :
    L1.BoundedFormula β 1 :=
  BoundedFormula.relabel (Sum.elim (fun i => Sum.inl (f i)) fun _ => Sum.inr 0)
    ((LHom.sumInl : Language.graph →ᴸ L1).onFormula φ)

/-- The color predicate `U(z)` on the bound variable. -/
def colorZ {β : Type} : L1.BoundedFormula β 1 :=
  (LHom.sumInr : colorLanguage 1 →ᴸ L1).onBoundedFormula
    (Relations.boundedFormula₁ (ColorRel.color 0 : (colorLanguage 1).Relations 1)
      (Term.var (Sum.inr 0)))

/-- The formula `γ`. -/
def gamma (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) : L1.Formula (Fin p ⊕ Fin p') :=
  BoundedFormula.ex (colorZ ⊓ place φ Sum.inl ⊓ place ψ Sum.inr)

theorem realizeIn_gamma {n : ℕ} (G : SimpleGraph (Fin n)) (colors : Fin 1 → Set (Fin n))
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1))
    (u : Fin p → Fin n) (w : Fin p' → Fin n) :
    RealizeIn G.structure colors (gamma φ ψ) (Sum.elim u w) ↔
      ∃ z ∈ colors 0, Holds G φ u z ∧ Holds G ψ w z := by
  let _ := G.structure
  let _ := colorStructure colors
  have hplace : ∀ {q : ℕ} (χ : Language.graph.Formula (Fin q ⊕ Fin 1))
      (f : Fin q → Fin p ⊕ Fin p') (z : Fin n),
      (place χ f).Realize (Sum.elim u w) (Fin.snoc default z) ↔
        Holds G χ (Sum.elim u w ∘ f) z := by
    intro q χ f z
    unfold place Holds
    rw [BoundedFormula.realize_relabel]
    unfold Formula.Realize
    rw [show (LHom.sumInl : Language.graph →ᴸ L1).onFormula χ =
      LHom.sumInl.onBoundedFormula χ from rfl, LHom.realize_onBoundedFormula]
    have h1 : (Sum.elim (Sum.elim u w) ((Fin.snoc (default : Fin 0 → Fin n) z : Fin 1 → Fin n) ∘
        Fin.castAdd 0) ∘ Sum.elim (fun i => Sum.inl (f i)) fun _ => Sum.inr 0) =
        Sum.elim (Sum.elim u w ∘ f) ![z] := by
      funext x
      rcases x with i | i
      · rfl
      · fin_cases i; rfl
    rw [h1]
    exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))
  unfold RealizeIn gamma
  rw [Formula.Realize, BoundedFormula.realize_ex]
  refine exists_congr fun z => ?_
  simp only [BoundedFormula.realize_inf, hplace]
  have hc : colorZ.Realize (Sum.elim u w) (Fin.snoc (default : Fin 0 → Fin n) z) ↔ z ∈ colors 0 := by
    unfold colorZ
    rw [LHom.realize_onBoundedFormula]
    rfl
  rw [hc, Sum.elim_comp_inl, Sum.elim_comp_inr, and_assoc]

end Lax185574Proofs.PatternFormula
