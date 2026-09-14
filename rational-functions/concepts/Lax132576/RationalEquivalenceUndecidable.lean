import Lax132576.TransducerCodes

/-!
---
title: Equivalence of rational relations is undecidable
type: theorem
---
The equivalence problem $R = S$ is undecidable for rational relations (Theorem
B.1.6 of *Transducers*, Griffiths). The book reduces the Post correspondence
problem to the universality problem: for two homomorphisms $g, h$, the instance
has no solution exactly when the union of the complements of $g$ and $h$ — a
rational relation by Claim B.1.7 and closure under union — is the full relation
$A^* \times B^*$.

# Formalization notes

The two relations are given by codes (`TransducerCodes`), and undecidability is
the negation of mathlib's `ComputablePred` for the equality of the two coded
relations. The proof assumes the undecidability of the Post correspondence
problem in index form, which the archive states separately
(`PostCorrespondenceIndexUndecidable` of the submission on the Post
correspondence problem).
-/

namespace Lax132576.RationalEquivalenceUndecidable

open Lax132576.TransducerCodes

/-- No algorithm decides whether two coded rational relations are equal. -/
axiom not_computablePred_codeRel_eq :
    ¬ ComputablePred (fun p : RelCode × RelCode => codeRel p.1 = codeRel p.2)

end Lax132576.RationalEquivalenceUndecidable
