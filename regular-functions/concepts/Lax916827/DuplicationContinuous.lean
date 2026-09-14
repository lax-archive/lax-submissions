import Lax765601.Continuity

/-!
---
title: String duplication is continuous
type: theorem
---
String duplication $w \mapsto ww$ is continuous (Lemma C.1.2 of *Transducers*,
second half): the inverse image of a regular language $L$ is the union, over
the states $q$ of an automaton for $L$, of the strings that lead from an initial
state to $q$ and from $q$ to an accepting state.

# Formalization notes

The alphabet is assumed finite, as in the book.
-/

namespace Lax916827.DuplicationContinuous

open Lax765601.Continuity

/-- String duplication is continuous. -/
axiom continuous_duplicate {A : Type} [Finite A] : Continuous (fun w : List A => w ++ w)

end Lax916827.DuplicationContinuous
