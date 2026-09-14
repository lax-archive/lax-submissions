import Mathlib.Computability.Halting
import Lax251941.PostCorrespondence

/-!
---
title: The Post correspondence problem is undecidable
type: theorem
---
No algorithm decides whether an instance of the Post correspondence problem has
a match (Post 1946; Sipser, Theorem 5.15). It follows from the reduction of
the acceptance problem for Turing machines to the Post correspondence problem
(`PostCorrespondenceReduction`) and the undecidability of that acceptance
problem (`TapeAcceptanceUndecidable`).

# Formalization notes

Stated for instances over the alphabet `ℕ`, in the domino form `HasMatch`, with
mathlib's `ComputablePred`. The index form the book *Transducers* uses is
`PostCorrespondenceIndexUndecidable`.
-/

namespace Lax251941.PostCorrespondenceUndecidable

open Lax251941.PostCorrespondence

/-- The Post correspondence problem over `ℕ` is undecidable. -/
axiom not_computablePred_hasMatch : ¬ ComputablePred fun P : Inst ℕ => HasMatch P

end Lax251941.PostCorrespondenceUndecidable
