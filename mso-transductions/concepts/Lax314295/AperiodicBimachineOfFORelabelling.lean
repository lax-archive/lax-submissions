import Lax132576.Bimachines
import Lax314295.MSORelabellings

/-!
---
title: First-order relabellings are computed by aperiodic bimachines
type: theorem
---
Every first-order relabelling is computed by an aperiodic bimachine (Theorem
C.4.16 of *Transducers*, the implication from relabelling to bimachine). For a
first-order formula with one free variable, the prefixes and the suffixes on
which it holds at the marked position are first-order definable languages,
recognised by aperiodic automata (Theorem C.4.11), which become the prefix and
suffix automata of the bimachine.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax314295.AperiodicBimachineOfFORelabelling

open Lax132576.Bimachines Lax314295.MSORelabellings

/-- A first-order relabelling is computed by an aperiodic bimachine. -/
axiom isAperiodicBimachine_of_isFORelabelling {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsFORelabelling f) : IsAperiodicBimachine f

end Lax314295.AperiodicBimachineOfFORelabelling
