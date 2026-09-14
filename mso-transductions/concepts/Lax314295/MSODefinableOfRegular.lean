import Lax314295.MSOLogic

/-!
---
title: Regular languages are MSO-definable
type: theorem
---
Every regular language is definable in monadic second-order logic (Theorem
C.4.1 of *Transducers*, Büchi–Elgot–Trakhtenbrot, the implication from regular
to definable). The formula guesses the run of a deterministic automaton on the
input as one set variable per state, and checks that the sets partition the
positions, that the first position carries the initial state's successor, that
consecutive positions follow the transition function, and that the last
position leads to an accepting state.

# Formalization notes

The alphabet is assumed finite, as in the book.
-/

namespace Lax314295.MSODefinableOfRegular

open Lax314295.MSOLogic

/-- A regular language is definable in mso. -/
axiom msoDefinable_of_isRegular {A : Type} [Finite A] {L : Language A} (hL : L.IsRegular) :
    MSODefinable L

end Lax314295.MSODefinableOfRegular
