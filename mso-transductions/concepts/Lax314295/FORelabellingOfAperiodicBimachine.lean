import Lax132576.Bimachines
import Lax314295.MSORelabellings

/-!
---
title: Aperiodic bimachines compute first-order relabellings
type: theorem
---
Every function computed by an aperiodic bimachine is a first-order
relabelling (Theorem C.4.16 of *Transducers*, the implication from bimachine to
relabelling). By Theorem C.4.11 the runs of the two aperiodic automata are
described in first-order logic: for each pair of a transition of the prefix
automaton and one of the suffix automaton there is a first-order formula
selecting the positions at which they are used, and the output map is the
output function of the bimachine.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax314295.FORelabellingOfAperiodicBimachine

open Lax132576.Bimachines Lax314295.MSORelabellings

/-- A function computed by an aperiodic bimachine is a first-order relabelling. -/
axiom isFORelabelling_of_isAperiodicBimachine {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsAperiodicBimachine f) : IsFORelabelling f

end Lax314295.FORelabellingOfAperiodicBimachine
