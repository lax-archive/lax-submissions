import Lax765601.Continuity
import Lax132576.RationalRelations

/-!
---
title: Rational relations are continuous
type: theorem
---
If $R \subseteq A^* \times B^*$ is a rational relation and $L \subseteq B^*$
is a regular language, then the inverse image
$$\{w \in A^* \mid w\,R\,v \text{ for some } v \in L\}$$
is a regular language (Theorem B.1.5 of *Transducers*). The book deduces it
from closure under composition: rational relations with an empty output
alphabet are the regular languages over the input alphabet, and the inverse
image is the composition of $R$ with the relation $\{(w, \varepsilon) \mid w \in L\}$.
Since rational relations are input/output symmetric, forward images of regular
languages are regular too.

# Formalization notes

The conclusion is `RelContinuous R` of `Lax765601.Continuity`, continuity in
the relational form. No finiteness of the alphabets is needed.
-/

namespace Lax132576.RationalContinuity

open Lax765601.Continuity Lax132576.RationalRelations

/-- A rational relation is continuous: inverse images of regular languages are
regular. -/
axiom relContinuous_of_isRationalRel {A B : Type} {R : List A → List B → Prop}
    (hR : IsRationalRel R) : RelContinuous R

end Lax132576.RationalContinuity
