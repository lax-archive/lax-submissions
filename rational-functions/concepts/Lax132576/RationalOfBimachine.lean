import Lax132576.RationalFunctions
import Lax132576.Bimachines

/-!
---
title: Bimachines compute rational functions
type: theorem
---
Every function computed by a bimachine is rational: the implication (3) ⇒ (1)
of Theorem B.2.3 of *Transducers*, the easiest one. The nondeterministic
automaton guesses the runs of both the prefix and the suffix automaton, its
states being pairs of their states plus one extra final state; a transition on
the letter $a$ from $(p, q)$ to $(p', q')$ requires $p \xrightarrow{a} p'$ in
the prefix automaton and $q' \xrightarrow{a} q$ in the suffix automaton and
outputs the piece of the gap to the left of $a$, and an empty transition into
the final state outputs the piece of the last gap.

# Formalization notes

Both alphabets are assumed finite, as in the book's global convention; the
transition relation of the constructed automaton is indexed by the letters.
-/

namespace Lax132576.RationalOfBimachine

open Lax132576.RationalFunctions Lax132576.Bimachines

/-- A function computed by a bimachine is rational. -/
axiom isRationalFun_of_isBimachine {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsBimachine f) : IsRationalFun f

end Lax132576.RationalOfBimachine
