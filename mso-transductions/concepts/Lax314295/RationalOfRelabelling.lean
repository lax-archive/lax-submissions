import Lax132576.RationalFunctions
import Lax314295.MSORelabellings

/-!
---
title: MSO relabellings are rational
type: theorem
---
Every function definable by an mso relabelling is rational (Theorem C.4.4 of
*Transducers*, Bloem–Engelfriet, the implication from relabelling to rational).
By Claim C.4.6 the strings annotated at every position with the formula true
there form a regular language, so an automaton with output guesses the
annotation, checks it, and outputs the output map of the guessed formulas.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax314295.RationalOfRelabelling

open Lax132576.RationalFunctions Lax314295.MSORelabellings

/-- A function definable by an mso relabelling is rational. -/
axiom isRationalFun_of_isMSORelabelling {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMSORelabelling f) : IsRationalFun f

end Lax314295.RationalOfRelabelling
