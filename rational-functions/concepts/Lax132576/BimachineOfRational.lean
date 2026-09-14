import Lax132576.RationalFunctions
import Lax132576.Bimachines

/-!
---
title: Rational functions are computed by bimachines
type: theorem
---
Every rational function is computed by a bimachine: the implication (1) ⇒ (3)
of Theorem B.2.3 of *Transducers* (Eilenberg), through the unambiguous
automaton of (2). Given an unambiguous automaton whose accepting runs end with
a single empty-input transition, the bimachine's prefix automaton computes the
states reachable from an initial state on the prefix, its suffix automaton
computes the first letter of the suffix and the states that can reach
acceptance on the rest, and the output function reads off the output of the
unique transition consuming the letter at the gap — or of the final
empty-input transition at the last gap.

# Formalization notes

Both alphabets are assumed finite, as the construction of the unambiguous
automaton needs.
-/

namespace Lax132576.BimachineOfRational

open Lax132576.RationalFunctions Lax132576.Bimachines

/-- A rational function is computed by a bimachine. -/
axiom isBimachine_of_isRationalFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) : IsBimachine f

end Lax132576.BimachineOfRational
