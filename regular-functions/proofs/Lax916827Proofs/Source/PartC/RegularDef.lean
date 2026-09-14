/-
The prime regular functions and the regular functions (Definition `def:regular-functions`) of
*Transducers* (M. Bojańczyk), together with their basic closure properties.

These definitions were originally stated in `RequestProject/PartC/Statements.lean`; they have been
moved here, unchanged, so that the constructions used in the proofs of Lemma
`lem:regular-closure-properties`, Claim `claim:conditional` and Theorem
`thm:2dfa-decomposition-into-primes` can be developed before the statements of the numbered results.
`RequestProject/PartC/Statements.lean` imports this file, so the names `Transducers.mapReverse`,
`Transducers.mapDuplicate`, `Transducers.RegularFam` and `Transducers.IsRegularFun` are unchanged.

The file also collects the elementary facts about regular functions that are
used everywhere later: a rational function is regular, `mapReverse` and
`mapDuplicate` are regular, regular functions are closed under composition, and
a homomorphism (in particular a letter-to-letter map) is a rational, hence
regular, function.
-/
import Lax916827Proofs.Source.PartC.RatBuild
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## The prime regular functions (Definition `def:regular-functions`) -/

/-- The map reverse function `w₁ # ⋯ # wₙ ↦ reverse w₁ # ⋯ # reverse wₙ`. -/
def mapReverse (A : Type) : List (Option A) → List (Option A) := mapLift List.reverse

/-- The map duplicate function `w₁ # ⋯ # wₙ ↦ w₁w₁ # ⋯ # wₙwₙ`. -/
def mapDuplicate (A : Type) : List (Option A) → List (Option A) :=
  mapLift (fun w => w ++ w)

/-- The family of prime regular functions: rational functions, map reverse and
map duplicate.  The last two have type `(A + 1)* → (A + 1)*`, which is expressed
by the bijections `e` and `e'` with `Option A₀`. -/
def RegularFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  IsRationalFun f ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapReverse A₀ (w.map e)).map e'.symm) ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapDuplicate A₀ (w.map e)).map e'.symm)

/-- **Definition `def:regular-functions` (Regular functions).**  A string-to-string function is
regular if it is a finite composition of rational functions, map reverse and map
duplicate. -/
def IsRegularFun {A B : Type} (f : List A → List B) : Prop := CompClosure RegularFam A B f

/-! ## Elementary closure properties -/

variable {A B C : Type}

/-- A regular function stays regular if it is replaced by a function with the
same values. -/
lemma IsRegularFun.congr {f g : List A → List B} (hf : IsRegularFun f)
    (h : ∀ w, f w = g w) : IsRegularFun g := by
  have : f = g := funext h
  exact this ▸ hf

/-- Every rational function is regular. -/
lemma IsRegularFun.of_rational {f : List A → List B} (hf : IsRationalFun f) :
    IsRegularFun f :=
  CompClosure.base (Or.inl hf)

/-- The identity is regular. -/
lemma isRegularFun_id : IsRegularFun (id : List A → List A) := CompClosure.id A

/-- Regular functions are closed under composition. -/
lemma IsRegularFun.comp {f : List A → List B} {g : List B → List C} [Finite B]
    (hf : IsRegularFun f) (hg : IsRegularFun g) : IsRegularFun (g ∘ f) :=
  CompClosure.comp hf hg

/-- Regular functions are closed under composition (pointwise form). -/
lemma IsRegularFun.comp' {f : List A → List B} {g : List B → List C} [Finite B]
    {h : List A → List C} (hf : IsRegularFun f) (hg : IsRegularFun g)
    (hh : ∀ w, h w = g (f w)) : IsRegularFun h :=
  (hf.comp hg).congr (fun w => (hh w).symm)

/-- Map reverse is regular. -/
lemma isRegularFun_mapReverse (A₀ : Type) : IsRegularFun (mapReverse A₀) :=
  CompClosure.base (Or.inr (Or.inl ⟨A₀, Equiv.refl _, Equiv.refl _, by intro w; simp⟩))

/-- Map duplicate is regular. -/
lemma isRegularFun_mapDuplicate (A₀ : Type) : IsRegularFun (mapDuplicate A₀) :=
  CompClosure.base (Or.inr (Or.inr ⟨A₀, Equiv.refl _, Equiv.refl _, by intro w; simp⟩))

/-- A homomorphism is a regular function. -/
theorem isRegularFun_homOf [Finite A] [Finite B] (φ : A → List B) :
    IsRegularFun (homOf φ) :=
  IsRegularFun.of_rational (isRationalFun_homOf φ)

/-- A letter-to-letter map is a regular function. -/
theorem isRegularFun_map [Finite A] [Finite B] (h : A → B) :
    IsRegularFun (fun w : List A => w.map h) :=
  IsRegularFun.of_rational (isRationalFun_map h)

end Lax916827Proofs.Transducers
