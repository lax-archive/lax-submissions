/-
Part D: every polyregular function is computed by a for-transducer.

This is the left-to-right inclusion of Theorem `thm:for-transducers-are-polyregular`.  The proof
is an induction on the definition of the polyregular functions as the closure of the prime
polyregular functions under composition (Definition `def:polyregular-functions`): the primes are
handled in `RequestProject/PartD/ForPrimes.lean` and the composition step is Lemma
`lem:for-closed-under-composition`.
-/
import Lax194892Proofs.Source.PartD.ForPrimes
import Lax194892Proofs.Source.PartD.ForCompTop
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

variable {A B C : Type}

/-- A function computed by a for-transducer stays so when it is replaced by a function with the
same values. -/
lemma IsForTransducer.congr {f g : List A → List B} (hf : IsForTransducer f)
    (h : ∀ w, f w = g w) : IsForTransducer g := by
  obtain ⟨P, hP⟩ := hf
  exact ⟨P, fun w => (hP w).trans (h w)⟩

/-- A letter-to-letter map is computed by a for-transducer. -/
lemma isForTransducer_map [Finite A] (φ : A → B) :
    IsForTransducer (fun w : List A => w.map φ) := by
  refine (isForTransducer_homOf (fun a => [φ a])).congr (fun w => ?_)
  simp only [homOf]
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

/-- The identity is computed by a for-transducer. -/
lemma isForTransducer_id [Finite A] : IsForTransducer (id : List A → List A) :=
  (isForTransducer_map (id : A → A)).congr (fun w => by simp)

/-- **Every regular function is computed by a for-transducer.** -/
theorem isForTransducer_of_isRegularFun :
    ∀ {A B : Type} {f : List A → List B}, CompClosure RegularFam A B f →
      Finite A → Finite B → IsForTransducer f := by
  intro A B f hf
  induction hf with
  | @base A B f h =>
      intro hA hB
      rcases h with hrat | ⟨A₀, e, e', hfe⟩ | ⟨A₀, e, e', hfe⟩
      · exact isForTransducer_of_isRationalFun hrat
      · haveI : Finite A₀ := Finite.of_injective (fun a : A₀ => e.symm (some a))
          (fun a b hab => by simpa using e.symm.injective hab)
        refine IsForTransducer.congr
          (forTransducer_comp_aux (forTransducer_comp_aux (isForTransducer_map (e : A → Option A₀))
            (isForTransducer_mapReverse A₀)) (isForTransducer_map (e'.symm : Option A₀ → B)))
          (fun w => (hfe w).symm)
      · haveI : Finite A₀ := Finite.of_injective (fun a : A₀ => e.symm (some a))
          (fun a b hab => by simpa using e.symm.injective hab)
        refine IsForTransducer.congr
          (forTransducer_comp_aux (forTransducer_comp_aux (isForTransducer_map (e : A → Option A₀))
            (isForTransducer_mapDuplicate A₀)) (isForTransducer_map (e'.symm : Option A₀ → B)))
          (fun w => (hfe w).symm)
  | id A => intro hA _; exact isForTransducer_id
  | comp _ _ ihf ihg =>
      intro hA hC
      exact forTransducer_comp_aux (ihf hA ‹Finite _›) (ihg ‹Finite _› hC)

/-- **Every polyregular function is computed by a for-transducer.** -/
theorem isForTransducer_of_isPolyregular :
    ∀ {A B : Type} {f : List A → List B}, CompClosure PolyregularFam A B f →
      Finite A → Finite B → IsForTransducer f := by
  intro A B f hf
  induction hf with
  | @base A B f h =>
      intro hA hB
      rcases h with hreg | ⟨A₀, e, e', hfe⟩
      · exact isForTransducer_of_isRegularFun hreg hA hB
      · haveI : Finite A₀ := Finite.of_equiv A e
        refine IsForTransducer.congr
          (forTransducer_comp_aux (forTransducer_comp_aux (isForTransducer_map (e : A → A₀))
            (isForTransducer_markedSquare A₀)) (isForTransducer_map (e'.symm : A₀ ⊕ A₀ → B)))
          (fun w => (hfe w).symm)
  | id A => intro hA _; exact isForTransducer_id
  | comp _ _ ihf ihg =>
      intro hA hC
      exact forTransducer_comp_aux (ihf hA ‹Finite _›) (ihg ‹Finite _› hC)

end Lax194892Proofs.Transducers
