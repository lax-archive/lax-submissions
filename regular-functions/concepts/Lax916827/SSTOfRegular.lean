import Lax916827.RegularFunctions
import Lax916827.StreamingStringTransducers

/-!
---
title: Every regular function is computed by a streaming string transducer
type: theorem
---
Every regular function is computed by a streaming string transducer (Theorem
C.3.2 of *Transducers*, the implication from regular to sst). Streaming string
transducers are closed under post-composition with every prime regular
function — a rational function through the Krohn–Rhodes decomposition of its
Mealy machines, map reverse and map duplicate by keeping the register contents
as tuples indexed by the separators inside them — and the identity is an sst.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax916827.SSTOfRegular

open Lax916827.RegularFunctions Lax916827.StreamingStringTransducers

/-- A regular function is computed by a streaming string transducer. -/
axiom isSST_of_isRegularFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : IsSST f

end Lax916827.SSTOfRegular
