import Lax132576.Bimachines
import Lax314295.MSORelabellings

/-!
---
title: First-order relabellings are exactly the aperiodic bimachines
type: theorem
---
A string-to-string function is a first-order relabelling if and only if it is
computed by an aperiodic bimachine (Theorem C.4.16 of *Transducers*). The two
implications are the separate statements `AperiodicBimachineOfFORelabelling`
and `FORelabellingOfAperiodicBimachine`; this statement is their
conjunction.

# Formalization notes

Both alphabets are assumed finite.
-/

namespace Lax314295.FORelabellingIffAperiodicBimachine

open Lax132576.Bimachines Lax314295.MSORelabellings

/-- A function is a first-order relabelling if and only if an aperiodic bimachine
computes it. -/
axiom isFORelabelling_iff_isAperiodicBimachine {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsFORelabelling f ↔ IsAperiodicBimachine f

end Lax314295.FORelabellingIffAperiodicBimachine
