import Mathlib.Computability.Halting
import Lax251941.PostCorrespondence

/-!
---
title: The Post correspondence problem in index form is undecidable
type: theorem
---
No algorithm decides, given a finite list of pairs of strings over $\mathbb{N}$,
whether some nonempty sequence of indices makes the two concatenations equal.
This is the undecidability of the Post correspondence problem in the index form
used by the book *Transducers*, where it is the source of the undecidability of
equivalence of rational relations (Theorem B.1.6). A list of dominos taken from
an instance and a list of positions in the instance carry the same information,
so the index form is the domino form `PostCorrespondenceUndecidable` restated.

# Formalization notes

`Solvable` is the index form of `PostCorrespondence`; decidability is mathlib's
`ComputablePred` on lists of pairs of lists of natural numbers.
-/

namespace Lax251941.PostCorrespondenceIndexUndecidable

open Lax251941.PostCorrespondence

/-- The Post correspondence problem in index form is undecidable. -/
axiom not_computablePred_solvable : ¬ ComputablePred Solvable

end Lax251941.PostCorrespondenceIndexUndecidable
