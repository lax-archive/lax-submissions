/-
The undecidability of the Post correspondence problem in index form, assumed
from the archive.

In the source development this module (`RequestProject/PCP/Index.lean`) proves
`Transducers.PCP.solvable_not_computablePred` by reducing the index form of the
Post correspondence problem to the domino form, whose undecidability is
established from the halting problem in the `PCP/` and `Acceptance/` folders.
That development is the submission `pcp-undecidability` (lax-251941); the
present submission does not repeat it, and takes the fact as an assumption from
the archive statement
`Lax251941.PostCorrespondenceIndexUndecidable.not_computablePred_solvable`.

The two predicates `Solvable` — the archive's
`Lax251941.PostCorrespondence.Solvable` and the source's
`Transducers.PCP.Solvable` of `Source/PartB/PCPRed.lean` — are defined by
identical terms (`Instance`, `conc`, `Solvable`), so they are definitionally
equal and the archive statement is the source statement.  The rest of Part B
(Theorem `thm:undecidable-equivalence-rational-relations` in
`Source/PartB/RationalStatements.lean`) uses it under the source's name, as it
did before.
-/
import Lax251941.PostCorrespondenceIndexUndecidable
import Lax132576Proofs.Source.PartB.PCPRed

namespace Lax132576Proofs.Transducers.PCP

/-- The Post correspondence problem in index form is undecidable — assumed from
the archive (lax-251941), see the header of this file. -/
theorem solvable_not_computablePred : ¬ ComputablePred Solvable :=
  Lax251941.PostCorrespondenceIndexUndecidable.not_computablePred_solvable

end Lax132576Proofs.Transducers.PCP
