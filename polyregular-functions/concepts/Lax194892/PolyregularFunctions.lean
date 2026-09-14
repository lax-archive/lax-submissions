import Lax765601.CompositionClosure
import Lax916827.RegularFunctions
import Lax194892.MarkedSquaring

/-!
---
title: Polyregular functions
type: definition
---
A string-to-string function is *polyregular* (Definition D.0.1 of
*Transducers*) if it can be obtained as a finite composition of functions each
of which is either regular or a marked squaring function:
$$\text{polyregular} = (\text{regular} \cup \text{marked squaring})^*.$$
The polyregular functions are the top step of the book's transducer ladder;
Part D shows that they are the functions of for-transducers and of pebble
transducers.

# Formalization notes

As for the regular functions, marked squaring appears in the family up to a
renaming of the alphabets by bijections `A ≃ A₀` and `B ≃ A₀ ⊕ A₀`;
`IsPolyregular` is the composition closure of `Lax765601.CompositionClosure`.
-/

namespace Lax194892.PolyregularFunctions

open Lax765601.CompositionClosure Lax916827.RegularFunctions Lax194892.MarkedSquaring

/-- The family of prime polyregular functions: regular functions and marked
squaring, up to a renaming of the alphabets. -/
def PolyregularFam : Family := fun A B f =>
  IsRegularFun f ∨
  (∃ (A₀ : Type) (e : A ≃ A₀) (e' : B ≃ A₀ ⊕ A₀),
      ∀ w, f w = (markedSquare A₀ (w.map e)).map e'.symm)

/-- A function is polyregular if it is a finite composition of regular functions
and marked squaring. -/
def IsPolyregular {A B : Type} (f : List A → List B) : Prop := CompClosure PolyregularFam A B f

end Lax194892.PolyregularFunctions
