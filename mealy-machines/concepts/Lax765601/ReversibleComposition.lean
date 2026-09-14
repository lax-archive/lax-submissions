import Lax765601.PrimeMealyMachines

/-!
---
title: Reversible Mealy machines are closed under composition
type: theorem
---
The composition of two functions computed by reversible Mealy machines is
computed by a reversible Mealy machine (Lemma A.2.6 of *Transducers*). Hence the
class $(\mathrm{Reversible})^*$ of compositions of reversible machines is just
the class of reversible machines: the product machine of the composition
(Theorem A.1.3) is reversible, since the state transformation of a letter in it
is a permutation in each coordinate.

# Formalization notes

As for closure under composition of Mealy machines, the intermediate alphabet is
assumed finite.
-/

namespace Lax765601.ReversibleComposition

open Lax765601.PrimeMealyMachines

/-- The composition of two reversible Mealy machines is a reversible Mealy
machine. -/
axiom isReversibleMealy_comp {A B C : Type} [Finite B]
    {f : List A → List B} {g : List B → List C}
    (hf : IsReversibleMealy f) (hg : IsReversibleMealy g) : IsReversibleMealy (g ∘ f)

end Lax765601.ReversibleComposition
