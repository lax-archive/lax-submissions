import Lax185574.Colorings
import Lax185574.FirstOrderTypes
import Lax185574Proofs.LocalToGlobal

/-!
Renaming the colors of a formula of colored graphs. A map `f` from `k`
colors to `k'` colors turns a formula with `k` color symbols into one
with `k'` color symbols, replacing the `i`-th color by the `f(i)`-th.
The new formula holds in the expansion by `k'` color sets exactly when
the old one holds in the expansion by the color sets composed with `f`.
The quantifier rank does not change.
-/

namespace Lax185574Proofs.Conversions.ColorMaps

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.Colorings Lax185574.FirstOrderTypes

universe z

/-- The map of color languages renaming the colors along `f`. -/
def colorLangMap {k k' : ℕ} (f : Fin k → Fin k') : colorLanguage k →ᴸ colorLanguage k' where
  onFunction := fun _ e => isEmptyElim (α := Empty) e
  onRelation := fun _ R => match R with
    | .color i => .color (f i)

/-- The map of colored graph languages renaming the colors along `f`. -/
def colorMap {k k' : ℕ} (f : Fin k → Fin k') :
    withColors Language.graph k →ᴸ withColors Language.graph k' :=
  LHom.sumMap (LHom.id _) (colorLangMap f)

/-- Rename the colors of a formula along `f`. -/
def recolor {k k' : ℕ} (f : Fin k → Fin k') {α : Type*} {n : ℕ}
    (φ : (withColors Language.graph k).BoundedFormula α n) :
    (withColors Language.graph k').BoundedFormula α n :=
  (colorMap f).onBoundedFormula φ

theorem quantifierRank_recolor {k k' : ℕ} (f : Fin k → Fin k') {α : Type*} {n : ℕ}
    (φ : (withColors Language.graph k).BoundedFormula α n) :
    quantifierRank (recolor f φ) = quantifierRank φ :=
  Lax185574Proofs.LocalToGlobal.quantifierRank_onBoundedFormula _ φ

theorem isExpansionOn_colorMap {V : Type z} (G : SimpleGraph V) {k k' : ℕ}
    (f : Fin k → Fin k') (colors : Fin k' → Set V) :
    @LHom.IsExpansionOn _ _ (colorMap f) V (expansion G (colors ∘ f)) (expansion G colors) := by
  refine @LHom.IsExpansionOn.mk _ _ (colorMap f) V (expansion G (colors ∘ f))
    (expansion G colors) ?_ ?_
  · intro n F
    rcases F with F | F
    · exact isEmptyElim (α := Empty) F
    · exact isEmptyElim (α := Empty) F
  · intro n R x
    rcases R with R | R
    · rfl
    · cases R
      rfl

theorem realize_recolor {V : Type z} (G : SimpleGraph V) {k k' : ℕ} (f : Fin k → Fin k')
    (colors : Fin k' → Set V) {α : Type*} {n : ℕ}
    (φ : (withColors Language.graph k).BoundedFormula α n) (v : α → V) (xs : Fin n → V) :
    @BoundedFormula.Realize _ V (expansion G colors) _ _ (recolor f φ) v xs ↔
      @BoundedFormula.Realize _ V (expansion G (colors ∘ f)) _ _ φ v xs := by
  let _ := expansion G colors
  let _ := expansion G (colors ∘ f)
  have := isExpansionOn_colorMap G f colors
  exact LHom.realize_onBoundedFormula (colorMap f) φ

theorem realize_recolor_formula {V : Type z} (G : SimpleGraph V) {k k' : ℕ}
    (f : Fin k → Fin k') (colors : Fin k' → Set V) {α : Type*}
    (φ : (withColors Language.graph k).Formula α) (v : α → V) :
    @Formula.Realize _ V (expansion G colors) _ (recolor f φ) v ↔
      @Formula.Realize _ V (expansion G (colors ∘ f)) _ φ v :=
  realize_recolor G f colors φ v default

end Lax185574Proofs.Conversions.ColorMaps
