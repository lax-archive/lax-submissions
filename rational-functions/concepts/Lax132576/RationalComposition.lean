import Lax132576.RationalRelations

/-!
---
title: Rational relations are closed under composition
type: theorem
---
If $R \subseteq A^* \times B^*$ and $S \subseteq B^* \times C^*$ are rational
relations, then so is their relational composition
$$R \cdot S = \{(u, v) \in A^* \times C^* \mid u\,R\,w \text{ and } w\,S\,v \text{ for some } w \in B^*\}$$
(Theorem B.1.4 of *Transducers*). The proof is the product construction of
Theorem A.1.3, after splitting transitions so that each produces at most one
letter of input or output and adding empty transitions around every state, so
that the two runs can be synchronised on the intermediate string.

# Formalization notes

No finiteness of the alphabets is needed: the product construction only uses
the finiteness of the two state spaces.
-/

namespace Lax132576.RationalComposition

open Lax132576.RationalRelations

/-- The composition of two rational relations is rational. -/
axiom isRationalRel_comp {A B C : Type}
    {R : List A → List B → Prop} {S : List B → List C → Prop}
    (hR : IsRationalRel R) (hS : IsRationalRel S) :
    IsRationalRel (fun w v => ∃ u, R w u ∧ S u v)

end Lax132576.RationalComposition
