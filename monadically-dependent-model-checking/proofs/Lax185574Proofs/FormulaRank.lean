import Lax185574.FirstOrderTypes

/-!
Relabeling the variables of a formula does not change its quantifier
rank. Counting images of a set under two maps, one of which factors
through the other.
-/

namespace Lax185574Proofs.FormulaRank

open FirstOrder FirstOrder.Language Lax185574.FirstOrderTypes

universe u v w w'

variable {L : Language.{u, v}} {α : Type w} {β : Type w'}

theorem quantifierRank_relabel {m : ℕ} (g : α → β ⊕ Fin m) :
    ∀ {k : ℕ} (φ : L.BoundedFormula α k), quantifierRank (φ.relabel g) = quantifierRank φ
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel _ _ => rfl
  | _, .imp φ ψ => by
      rw [BoundedFormula.relabel_imp]
      simp only [quantifierRank, quantifierRank_relabel g φ, quantifierRank_relabel g ψ]
  | _, .all φ => by
      rw [BoundedFormula.relabel_all]
      simp only [quantifierRank, quantifierRank_relabel g φ]

theorem quantifierRank_formula_relabel (g : α → β) (φ : L.Formula α) :
    quantifierRank (φ.relabel g) = quantifierRank φ :=
  quantifierRank_relabel _ φ

/-- If `g` identifies no more elements than `f`, the image of `f` is at
most as large as the image of `g`, provided the latter is finite. -/
theorem ncard_image_le_of_factor {γ δ ε : Type*} {X : Set γ} (f : γ → δ) (g : γ → ε)
    (h : ∀ a ∈ X, ∀ b ∈ X, g a = g b → f a = f b) (hfin : (g '' X).Finite) :
    (f '' X).ncard ≤ (g '' X).ncard := by
  classical
  rcases X.eq_empty_or_nonempty with rfl | ⟨x₀, -⟩
  · simp
  refine Set.ncard_le_ncard_of_injOn (fun d => if hd : d ∈ f '' X then g (Classical.choose hd)
    else g x₀) ?_ ?_ hfin
  · intro d hd
    simp only [hd, dite_true]
    exact ⟨_, (Classical.choose_spec hd).1, rfl⟩
  · intro d hd d' hd' e
    simp only [hd, hd', dite_true] at e
    have h1 := Classical.choose_spec hd
    have h2 := Classical.choose_spec hd'
    rw [← h1.2, ← h2.2]
    exact h _ h1.1 _ h2.1 e

end Lax185574Proofs.FormulaRank
