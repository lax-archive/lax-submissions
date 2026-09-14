import Lax765601.Continuity
import Lax132576.SubsequentialTransducers
import Lax132576.LeftDistance

/-!
---
title: Machine-independent characterisation of subsequential functions
type: theorem
---
A partial function $f : A^* \to B^*$ is subsequential if and only if it is
continuous and has bounded variation: for all $w_1, w_2$,
$$\sup_w \|f(w w_1), f(w w_2)\| < \infty,$$
$w$ ranging over the strings for which both values are defined (Theorem B.4.8
of *Transducers*, Choffrut). The construction of the transducer splits the
output after a prefix into a *branching* part, which depends on the future,
and a *non-branching* part, both of which are shown regular; the book's
Claims B.4.9–B.4.12 are the steps of that construction.

# Formalization notes

Continuity of a partial function is `PartialContinuous` of
`Lax765601.Continuity`, and bounded variation is `BoundedVariation` of
`LeftDistance`. Both alphabets are assumed finite.
-/

namespace Lax132576.SubsequentialCharacterisation

open Lax765601.Continuity Lax132576.SubsequentialTransducers Lax132576.LeftDistance

/-- A partial function is subsequential if and only if it is continuous and has
bounded variation. -/
axiom isSubsequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → Option (List B)) :
    IsSubsequential f ↔ PartialContinuous f ∧ BoundedVariation f

end Lax132576.SubsequentialCharacterisation
