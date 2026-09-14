import Lax765601.Continuity

/-!
---
title: String reversal is continuous
type: theorem
---
String reversal $w \mapsto \mathrm{reverse}(w)$ is continuous (Lemma C.1.2 of
*Transducers*, first half): the inverse image of a regular language under
reversal is recognised by the automaton with all transitions reversed and
initial and accepting states swapped.

# Formalization notes

The alphabet is assumed finite, as in the book.
-/

namespace Lax916827.ReversalContinuous

open Lax765601.Continuity

/-- String reversal is continuous. -/
axiom continuous_reverse {A : Type} [Finite A] : Continuous (List.reverse : List A → List A)

end Lax916827.ReversalContinuous
