import Lax765601.Continuity
import Lax916827.TwoWayTransducers

/-!
---
title: Two-way transducers are continuous
type: theorem
---
Every function computed by a two-way transducer is continuous (Theorem C.2.2 of
*Transducers*, Rabin–Scott and Shepherdson). The book computes the reachable
configuration graph by a rational function (Lemma C.2.3) and checks membership
of the output in a regular language on the representation (Lemma C.2.4); a
direct proof runs a deterministic automaton for the output language inside the
transducer, turning it into a two-way automaton, whose language is regular by
Shepherdson's theorem.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax916827.TwoWayContinuity

open Lax765601.Continuity Lax916827.TwoWayTransducers

/-- A function computed by a two-way transducer is continuous. -/
axiom continuous_of_isTwoWay {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : Continuous f

end Lax916827.TwoWayContinuity
