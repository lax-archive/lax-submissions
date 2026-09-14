import Lax314295.MSOLogic

/-!
---
title: Büchi's theorem: regular languages are the MSO-definable ones
type: theorem
---
A language $L \subseteq A^*$ is regular if and only if it is definable in
monadic second-order logic (Theorem C.4.1 of *Transducers*, Büchi, Elgot and
Trakhtenbrot). The two implications are the separate statements
`MSODefinableOfRegular` and `RegularOfMSODefinable`; this statement is their
conjunction.

# Formalization notes

The alphabet is assumed finite.
-/

namespace Lax314295.BuchiTheorem

open Lax314295.MSOLogic

/-- A language is regular if and only if it is mso-definable. -/
axiom isRegular_iff_msoDefinable {A : Type} [Finite A] (L : Language A) :
    L.IsRegular ↔ MSODefinable L

end Lax314295.BuchiTheorem
