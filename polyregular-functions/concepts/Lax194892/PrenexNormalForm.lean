import Lax194892.ForTransducers

/-!
---
title: Every for-transducer has a prenex form
type: theorem
---
Every for-transducer is equivalent to one in prenex form (Lemma D.1.3 of
*Transducers*): a block of nested loops over positions, in increasing or
decreasing order, whose body is loop-free and outputs at most one letter per
iteration, followed by a loop-free epilogue. Loops are pulled outwards one at a
time, Boolean variables recording which iterations have already been executed.

# Formalization notes

Stated over any alphabets, for every program `P`; `PrenexForm` is that of
`ForTransducers`.
-/

namespace Lax194892.PrenexNormalForm

open Lax194892.ForTransducers

/-- Every for-transducer program is equivalent to one in prenex form. -/
axiom exists_prenexForm {A B : Type} (P : ForProg A B) :
    ∃ P' : ForProg A B, P'.PrenexForm ∧ ∀ w, P'.eval w = P.eval w

end Lax194892.PrenexNormalForm
