import Lax765601.MealyMachine

/-!
---
title: Mealy machines are closed under composition
type: theorem
---
If $f : A^* \to B^*$ and $g : B^* \to C^*$ are computed by Mealy machines, then
so is their composition $A^* \xrightarrow{f} B^* \xrightarrow{g} C^*$ (Theorem
A.1.3 of *Transducers*). The proof is a product construction: the composed
machine runs both machines in lockstep, feeding each output letter of the first
to the second, so its state space is the product of the two state spaces.

# Formalization notes

The book writes the composition as $f \cdot g$, first $f$ then $g$; in Lean it is
`g ∘ f`. The intermediate alphabet is required to be finite, as in the closure
under composition of `CompositionClosure`; nothing is assumed of the outer
alphabets.
-/

namespace Lax765601.MealyComposition

open Lax765601.MealyMachine

/-- The composition of two functions computed by Mealy machines is computed by a
Mealy machine. -/
axiom isMealy_comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C}
    (hf : IsMealy f) (hg : IsMealy g) : IsMealy (g ∘ f)

end Lax765601.MealyComposition
