import Lax765601.MapLifting
import Lax765601.CompositionClosure
import Lax132576.RationalFunctions

/-!
---
title: Regular functions
type: definition
---
The *map reverse* function is the map lifting of string reversal, applied
blockwise between separators, and the *map duplicate* function is the map
lifting of string duplication $w \mapsto ww$:
$$123\#45\#6789 \mapsto 321\#54\#9876, \qquad 123\#45\#6789 \mapsto 123123\#4545\#67896789.$$
Neither is rational. A string-to-string function is *regular* (Definition
C.0.1 of *Transducers*) if it can be obtained as a finite composition of
functions each of which is a rational function, a map reverse function or a map
duplicate function. The regular functions are the third step of the transducer
ladder; Part C shows that they are the functions of two-way transducers,
of streaming string transducers, of string-to-string mso transductions and of
regular terms.

# Formalization notes

Map reverse and map duplicate are families of functions, one for every
alphabet `A`, of type `(A + 1)* → (A + 1)*` with `Option A` for `A + 1`. In the
family `RegularFam` they appear up to renaming: `f : A* → B*` is a map reverse if
the alphabets are in bijection with some `Option A₀` and `f` is `mapReverse A₀`
transported along the bijections. `IsRegularFun` is the composition closure of
`Lax765601.CompositionClosure`.
-/

namespace Lax916827.RegularFunctions

open Lax765601.MapLifting Lax765601.CompositionClosure Lax132576.RationalFunctions

/-- The map reverse function `w₁ # ⋯ # wₙ ↦ reverse w₁ # ⋯ # reverse wₙ`. -/
def mapReverse (A : Type) : List (Option A) → List (Option A) := mapLift List.reverse

/-- The map duplicate function `w₁ # ⋯ # wₙ ↦ w₁w₁ # ⋯ # wₙwₙ`. -/
def mapDuplicate (A : Type) : List (Option A) → List (Option A) := mapLift (fun w => w ++ w)

/-- The family of prime regular functions: rational functions, and the map reverse
and map duplicate functions, up to a renaming of the alphabets. -/
def RegularFam : Family := fun A B f =>
  IsRationalFun f ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapReverse A₀ (w.map e)).map e'.symm) ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapDuplicate A₀ (w.map e)).map e'.symm)

/-- A string-to-string function is regular if it is a finite composition of
rational functions, map reverse and map duplicate. -/
def IsRegularFun {A B : Type} (f : List A → List B) : Prop := CompClosure RegularFam A B f

end Lax916827.RegularFunctions
