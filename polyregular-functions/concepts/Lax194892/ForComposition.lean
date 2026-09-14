import Lax194892.ForTransducers

/-!
---
title: For-transducers are closed under composition
type: theorem
---
The functions computed by for-transducers are closed under composition
(Lemma D.1.4 of *Transducers*). The second program is run on the output of the
first, in prenex form: an output position of the first program is a tuple of
loop variables of its prenex form, so a loop of the second program over output
positions becomes a block of loops over input positions, and its tests on
output letters become the loop-free body of the first program.

# Formalization notes

Stated over any alphabets.
-/

namespace Lax194892.ForComposition

open Lax194892.ForTransducers

/-- The composition of two functions computed by for-transducers is computed by a
for-transducer. -/
axiom isForTransducer_comp {A B C : Type} {f : List A → List B} {g : List B → List C}
    (hf : IsForTransducer f) (hg : IsForTransducer g) : IsForTransducer (g ∘ f)

end Lax194892.ForComposition
