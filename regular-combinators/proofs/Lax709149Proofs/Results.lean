import Lax709149.RegularOfTerm
import Lax709149Proofs.Bridge

/-!
The numbered result of Part C §5 of *Transducers*, transported from the ported
source development through `Lax709149Proofs.Bridge`.
-/

namespace Lax709149Proofs.Results

open Lax709149.Types Lax709149.RegularUnderRepresentation Lax709149.RegularTerms
open Lax709149Proofs.Bridge

/--
---
conclusion: Lax709149.RegularOfTerm.isRegularUnderRepr_of_isRegularTermFun
---
Every function defined by a regular term is regular under string representation
(Theorem C.5.4, the implication from terms to regular functions): induction on
the term, every atomic term being computed on representations by a rational or
regular function that parses the representation with a capped bracket counter,
and the combinators preserving regularity under representation
(`Transducers.regularTerm_isRegular`).

# Proof strategy

The concept's terms are moved to the source's by `toSrcTerm`, the elements of a
type along `eltEquiv`, and the semantics commute (`eval_toSrcTerm`), so the
transported function is defined by a source term (`isRegularTermFun_toSrc`).
The source theorem makes it regular under the source's representation, and
`isRegularUnderRepr_iff` brings it back: the representations agree up to the
renaming of the alphabets (`repr_toSrc`), and a regular function conjugated by
that renaming is regular, through Part C §1–3's bridge for the regular
functions.

# Attribution

Theorem C.5.4 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/CombStatements.lean`.
-/
theorem isRegularUnderRepr_of_isRegularTermFun {A B : Ty} {f : A.Elt → B.Elt}
    (hf : IsRegularTermFun f) : IsRegularUnderRepr f :=
  (isRegularUnderRepr_iff f).2
    (Lax709149Proofs.Transducers.regularTerm_isRegular (isRegularTermFun_toSrc hf))

end Lax709149Proofs.Results
