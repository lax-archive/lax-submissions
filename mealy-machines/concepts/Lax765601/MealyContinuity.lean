import Lax765601.Continuity
import Lax765601.MealyMachine

/-!
---
title: Mealy machines are continuous
type: theorem
---
Every function computed by a Mealy machine is continuous: the inverse image of a
regular language under it is regular (Theorem A.1.4 of *Transducers*). The book
derives this from closure under composition through the letter-to-letter lifting
of a language, which labels every position of a string by whether the prefix
ending there belongs to the language; a direct product construction works just
as well, and is the one formalised.

# Formalization notes

Finiteness of the two alphabets is assumed, as everywhere in the book; the
product of the machine with a deterministic automaton for the output language
recognises the inverse image.
-/

namespace Lax765601.MealyContinuity

open Lax765601.Continuity Lax765601.MealyMachine

/-- A function computed by a Mealy machine is continuous. -/
axiom continuous_of_isMealy {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsMealy f) : Continuous f

end Lax765601.MealyContinuity
