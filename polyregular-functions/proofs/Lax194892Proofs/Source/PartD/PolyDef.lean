/-
Part D: the polyregular functions -- the definition.

Definition `def:polyregular-functions` and the family of prime polyregular functions were
originally stated in `RequestProject/PartD/Statements.lean`; they have been moved here,
unchanged, so that the constructions used in the proof of Theorem
`thm:for-transducers-are-polyregular` can be developed before the statements of the numbered
results.  `RequestProject/PartD/Statements.lean` imports this file, so the names
`Transducers.PolyregularFam` and `Transducers.IsPolyregular` are unchanged.

The file also collects the elementary closure properties of the polyregular functions that are
used later: a regular function is polyregular, marked squaring is polyregular, and the
polyregular functions are closed under composition.
-/
import Lax194892Proofs.Source.PartD.MarkedSquare
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

/-! ## Polyregular functions (Definition `def:polyregular-functions`) -/

/-- The family of prime polyregular functions: regular functions and marked
squaring. -/
def PolyregularFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  IsRegularFun f ∨
  (∃ (A₀ : Type) (e : A ≃ A₀) (e' : B ≃ A₀ ⊕ A₀),
      ∀ w, f w = (markedSquare A₀ (w.map e)).map e'.symm)

/-- **Definition `def:polyregular-functions` (Polyregular functions).**  A string-to-string function
is polyregular if it is a finite composition of regular functions and marked
squaring. -/
def IsPolyregular {A B : Type} (f : List A → List B) : Prop :=
  CompClosure PolyregularFam A B f

/-! ## Elementary closure properties -/

variable {A B C : Type}

/-- A polyregular function stays polyregular if it is replaced by a function with the same
values. -/
lemma IsPolyregular.congr {f g : List A → List B} (hf : IsPolyregular f)
    (h : ∀ w, f w = g w) : IsPolyregular g := by
  have : f = g := funext h
  exact this ▸ hf

/-- Every regular function is polyregular. -/
lemma IsPolyregular.of_regular {f : List A → List B} (hf : IsRegularFun f) : IsPolyregular f :=
  CompClosure.base (Or.inl hf)

/-- The identity is polyregular. -/
lemma isPolyregular_id : IsPolyregular (id : List A → List A) := CompClosure.id A

/-- The polyregular functions are closed under composition. -/
lemma IsPolyregular.comp {f : List A → List B} {g : List B → List C} [Finite B]
    (hf : IsPolyregular f) (hg : IsPolyregular g) : IsPolyregular (g ∘ f) :=
  CompClosure.comp hf hg

/-- The polyregular functions are closed under composition (pointwise form). -/
lemma IsPolyregular.comp' {f : List A → List B} {g : List B → List C} [Finite B]
    {h : List A → List C} (hf : IsPolyregular f) (hg : IsPolyregular g)
    (hh : ∀ w, h w = g (f w)) : IsPolyregular h :=
  (hf.comp hg).congr (fun w => (hh w).symm)

/-- Marked squaring is polyregular. -/
lemma isPolyregular_markedSquare (A : Type) : IsPolyregular (markedSquare A) :=
  CompClosure.base (Or.inr ⟨A, Equiv.refl _, Equiv.refl _, by intro w; simp⟩)

end Lax194892Proofs.Transducers
