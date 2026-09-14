import Lax132576.RationalFunctions
import Lax314295.MSORelabellings

/-!
---
title: Rational functions are exactly the MSO relabellings
type: theorem
---
A string-to-string function is rational if and only if it is definable by an
mso relabelling (Theorem C.4.4 of *Transducers*, Bloem and Engelfriet). The two
implications are the separate statements `RelabellingOfRational` and
`RationalOfRelabelling`; this statement is their conjunction.

# Formalization notes

Both alphabets are assumed finite.
-/

namespace Lax314295.RationalIffRelabelling

open Lax132576.RationalFunctions Lax314295.MSORelabellings

/-- A function is rational if and only if it is an mso relabelling. -/
axiom isRationalFun_iff_isMSORelabelling {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsRationalFun f ↔ IsMSORelabelling f

end Lax314295.RationalIffRelabelling
