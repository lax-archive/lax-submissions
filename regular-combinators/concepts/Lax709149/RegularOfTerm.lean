import Lax709149.RegularUnderRepresentation
import Lax709149.RegularTerms

/-!
---
title: Regular terms define regular functions
type: theorem
---
Every type-to-type function defined by a regular term is regular under string
representation (Theorem C.5.4 of *Transducers*, the implication from terms to
regular functions). The proof is an induction on the term: every atomic term
is computed, on representations, by a rational or a regular string-to-string
function — reading a representation with a bracket counter capped at the height
of the type — and the four combinators preserve regularity under representation,
composition by Theorem C.1.1, pairing and co-pairing through the closure
properties of Lemma C.2.10, and map through map lifting.

# Formalization notes

The converse implication of Theorem C.5.4, that every function regular under
string representation is defined by a regular term, is not formalised, and no
statement of the archive asserts it; this half is stated on its own.
-/

namespace Lax709149.RegularOfTerm

open Lax709149.Types Lax709149.RegularUnderRepresentation Lax709149.RegularTerms

/-- A function defined by a regular term is regular under string representation. -/
axiom isRegularUnderRepr_of_isRegularTermFun {A B : Ty} {f : A.Elt → B.Elt}
    (hf : IsRegularTermFun f) : IsRegularUnderRepr f

end Lax709149.RegularOfTerm
