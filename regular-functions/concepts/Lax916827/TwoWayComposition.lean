import Lax916827.TwoWayTransducers

/-!
---
title: Two-way transducers are closed under composition
type: theorem
---
Functions computed by two-way transducers are closed under composition
(Theorem C.2.5 of *Transducers*, Chytil and Jákl). The composed transducer
computes the reachable configuration graph of the first transducer by a
rational function (Lemma C.2.3), which two-way transducers can be pre-composed
with (Corollary C.2.7), and then simulates the second transducer on the
represented path, walking backwards along the path — which is possible because
the run of a deterministic transducer never revisits a configuration — when the
second transducer moves left.

# Formalization notes

All three alphabets are assumed finite, as in the book.
-/

namespace Lax916827.TwoWayComposition

open Lax916827.TwoWayTransducers

/-- The composition of two functions computed by two-way transducers is computed by
a two-way transducer. -/
axiom isTwoWay_comp {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C} (hf : IsTwoWay f) (hg : IsTwoWay g) :
    IsTwoWay (g ∘ f)

end Lax916827.TwoWayComposition
