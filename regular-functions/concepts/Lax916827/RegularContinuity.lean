import Lax765601.Continuity
import Lax916827.RegularFunctions

/-!
---
title: Regular functions are continuous
type: theorem
---
Regular functions are continuous (Theorem C.1.1 of *Transducers*, the
continuity half). Continuous functions are closed under composition and
rational functions are continuous (Theorem B.1.5), so it remains to see that
map reverse and map duplicate are continuous, which is Lemma C.1.2 (reversal
and duplication are continuous) lifted through Lemma C.1.3 (the map lifting of
a continuous function is continuous).

# Formalization notes

The finiteness hypotheses on the alphabets are those of the book; the prime
regular functions are in fact continuous over any alphabets.
-/

namespace Lax916827.RegularContinuity

open Lax765601.Continuity Lax916827.RegularFunctions

/-- A regular function is continuous. -/
axiom continuous_of_isRegularFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : Continuous f

end Lax916827.RegularContinuity
