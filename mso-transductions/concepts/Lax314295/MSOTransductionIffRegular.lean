import Lax916827.RegularFunctions
import Lax314295.MSOTransductions

/-!
---
title: MSO transductions define exactly the regular functions
type: theorem
---
String-to-string mso transductions define exactly the regular functions
(Theorem C.4.8 of *Transducers*, Engelfriet and Hoogeboom). The two
implications are the separate statements `RegularOfMSOTransduction` and
`MSOTransductionOfRegular`; this statement is their conjunction.

# Formalization notes

Both alphabets are assumed finite.
-/

namespace Lax314295.MSOTransductionIffRegular

open Lax916827.RegularFunctions Lax314295.MSOTransductions

/-- A function is defined by an mso transduction if and only if it is regular. -/
axiom isMSOTransduction_iff_isRegularFun {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsMSOTransduction f ↔ IsRegularFun f

end Lax314295.MSOTransductionIffRegular
