import Lax916827.RegularFunctions
import Lax916827.TwoWayTransducers

/-!
---
title: Every two-way transducer computes a regular function
type: theorem
---
Every function computed by a two-way transducer is regular, i.e. decomposes
into rational functions, map reverse and map duplicate (Theorem C.2.9 of
*Transducers*, the hard implication). The run of the transducer is described by
its *snake graph*, computed by a rational function, and the output of a snake
graph of width at most $k$ is a regular function of its representation (the
snake lemma, Lemma C.2.12), by induction on the width: a snake of width $k$ is
cut, at the record-breaking columns, into looping and progressing parts of
smaller width, whose outputs are computed by the induction hypothesis on factors
cut out by rational functions and glued back by the closure properties of
Lemma C.2.10. A run that halts visits every column at most $|Q|$ times, so the
transducer's function is its own width-$|Q|$ snake output.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax916827.RegularOfTwoWay

open Lax916827.RegularFunctions Lax916827.TwoWayTransducers

/-- A function computed by a two-way transducer is regular. -/
axiom isRegularFun_of_isTwoWay {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : IsRegularFun f

end Lax916827.RegularOfTwoWay
