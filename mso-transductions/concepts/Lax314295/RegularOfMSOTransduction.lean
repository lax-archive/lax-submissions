import Lax916827.RegularFunctions
import Lax314295.MSOTransductions

/-!
---
title: MSO transductions define regular functions
type: theorem
---
Every function defined by a string-to-string mso transduction is regular
(Theorem C.4.8 of *Transducers*, Engelfriet–Hoogeboom, the implication from
transduction to regular). The transduction is normalised to one universe and
one letter formula per copy and one order formula per pair of copies (Lemma
C.4.9); the questions the formulas ask are precomputed by a letter-to-letter
rational function (Lemma C.4.10); and a two-way transducer walks through the
output order, moving to the successor of the current element by running the
automaton of the precomputed language on the infix between them.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax314295.RegularOfMSOTransduction

open Lax916827.RegularFunctions Lax314295.MSOTransductions

/-- A function defined by an mso transduction is regular. -/
axiom isRegularFun_of_isMSOTransduction {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMSOTransduction f) : IsRegularFun f

end Lax314295.RegularOfMSOTransduction
