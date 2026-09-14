import Lax916827.RegularFunctions
import Lax916827.StreamingStringTransducers

/-!
---
title: Streaming string transducers compute exactly the regular functions
type: theorem
---
A string-to-string function is computed by a streaming string transducer if and
only if it is regular (Theorem C.3.2 of *Transducers*). The two implications
are the separate statements `SSTOfRegular` and `RegularOfSST`; this statement
is their conjunction.

# Formalization notes

Both alphabets are assumed finite.
-/

namespace Lax916827.SSTIffRegular

open Lax916827.RegularFunctions Lax916827.StreamingStringTransducers

/-- A function is computed by a streaming string transducer if and only if it is
regular. -/
axiom isSST_iff_isRegularFun {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSST f ↔ IsRegularFun f

end Lax916827.SSTIffRegular
