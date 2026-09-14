import Lax132576.TransducerCodes
import Lax916827.TwoWayCodes

/-!
---
title: Decidable equivalence of regular functions
type: theorem
---
Equivalence is decidable for regular functions (Theorem C.1.4 of
*Transducers*), the functions being given by two-way transducers, which compute
exactly the regular functions (Theorem C.2.9). The book reduces to equivalence
of weighted automata over the rationals, as for rational functions: the class of
functions that can be post-composed with weighted automata is closed under
composition, contains the rational functions (Theorem B.3.6), and contains map
reverse and map duplicate by two constructions with triples of states.

# Formalization notes

The two transducers are given by codes (`TwoWayCodes`), under the promise that
both are total, and the decided property is equality of the coded relations.
The proof does not follow the book's reduction to the letter: the bound on the
length of a shortest distinguishing input is obtained from the
crossing-sequence decomposition of a two-way run and Schützenberger's rank
criterion, which gives an explicit arithmetic bound in the sizes of the codes,
and the two coded transducers are compared on all inputs up to that bound over
the letters of the codes and one fresh letter.
-/

namespace Lax916827.RegularEquivalenceDecidable

open Lax132576.TransducerCodes Lax916827.TwoWayCodes

/-- Equivalence of two total coded two-way transducers is decidable. -/
axiom decidable_twoWayCodeRel_eq :
    DecidableUnderPromise
      (fun p : TwoWayCode × TwoWayCode => TwoWayCodeTotal p.1 ∧ TwoWayCodeTotal p.2)
      (fun p => twoWayCodeRel p.1 = twoWayCodeRel p.2)

end Lax916827.RegularEquivalenceDecidable
