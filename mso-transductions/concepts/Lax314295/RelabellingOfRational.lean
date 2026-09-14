import Lax132576.RationalFunctions
import Lax314295.MSORelabellings

/-!
---
title: Rational functions are MSO relabellings
type: theorem
---
Every rational function is definable by an mso relabelling (Theorem C.4.4 of
*Transducers*, Bloem–Engelfriet, the implication from rational to relabelling).
A rational function is computed by a bimachine; for each pair of a state of the
prefix automaton and a state of the suffix automaton there is an mso formula
selecting the positions at which the bimachine is in that pair of states
(Claim C.4.5, stated for the index of a bimachine), and the output map is the
output function of the bimachine.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax314295.RelabellingOfRational

open Lax132576.RationalFunctions Lax314295.MSORelabellings

/-- A rational function is definable by an mso relabelling. -/
axiom isMSORelabelling_of_isRationalFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) : IsMSORelabelling f

end Lax314295.RelabellingOfRational
