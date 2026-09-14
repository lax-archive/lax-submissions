import Lax314295.MSOLogic

/-!
---
title: MSO-definable languages are regular
type: theorem
---
Every language definable in monadic second-order logic is regular (Theorem
C.4.1 of *Transducers*, Büchi–Elgot–Trakhtenbrot, the implication from
definable to regular). It follows from Lemma C.4.2 on formulas with free
variables, by induction on the formula: the annotated strings satisfying a
formula form a regular language, Boolean connectives are Boolean operations on
languages, and a quantifier is a projection of the annotation.

# Formalization notes

The alphabet is assumed finite, as in the book.
-/

namespace Lax314295.RegularOfMSODefinable

open Lax314295.MSOLogic

/-- An mso-definable language is regular. -/
axiom isRegular_of_msoDefinable {A : Type} [Finite A] {L : Language A} (hL : MSODefinable L) :
    L.IsRegular

end Lax314295.RegularOfMSODefinable
