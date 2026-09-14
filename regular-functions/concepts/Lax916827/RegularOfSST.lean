import Lax916827.RegularFunctions
import Lax916827.StreamingStringTransducers

/-!
---
title: Every streaming string transducer computes a regular function
type: theorem
---
Every function computed by a streaming string transducer is regular (Theorem
C.3.2 of *Transducers*, the implication from sst to regular). The sst is first
normalised — the register update depends only on the letter read, and no
register occurs twice in a final output string — by annotating the input with
the states through a rational function; a two-way transducer then expands the
final output string depth-first, moving left to expand a register and right when
an expansion is finished, the copyless restriction making the place to resume
an expansion a function of the register and the letter returned to. Two-way
transducers compute regular functions (Theorem C.2.9).

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax916827.RegularOfSST

open Lax916827.RegularFunctions Lax916827.StreamingStringTransducers

/-- A function computed by a streaming string transducer is regular. -/
axiom isRegularFun_of_isSST {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsSST f) : IsRegularFun f

end Lax916827.RegularOfSST
