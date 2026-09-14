import Lax916827.RegularFunctions
import Lax314295.MSOTransductions

/-!
---
title: Regular functions are MSO transductions
type: theorem
---
Every regular function is defined by a string-to-string mso transduction
(Theorem C.4.8 of *Transducers*, Engelfriet–Hoogeboom, the implication from
regular to transduction). A regular function is computed by a two-way
transducer (Theorem C.2.9); the transduction's elements are the pairs of a
configuration of its run and an index into the output produced there, and all
its formulas — which configurations are reached, which letter is produced, which
of two configurations comes first — are regular properties of the input with
marked positions, hence mso-definable by Büchi's theorem.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax314295.MSOTransductionOfRegular

open Lax916827.RegularFunctions Lax314295.MSOTransductions

/-- A regular function is defined by an mso transduction. -/
axiom isMSOTransduction_of_isRegularFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRegularFun f) : IsMSOTransduction f

end Lax314295.MSOTransductionOfRegular
