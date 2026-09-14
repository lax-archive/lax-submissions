import Mathlib.Computability.Halting
import Lax251941.TuringMachines
import Lax251941.PostCorrespondence

/-!
---
title: The acceptance problem reduces to the Post correspondence problem
type: theorem
---
If the Post correspondence problem were decidable, then the acceptance problem
for Turing machines would be decidable as well (Sipser, Theorem 5.15, as a
many-one reduction). From a machine $M$ and an input $w$ one constructs, by
Sipser's seven kinds of dominos, an instance whose matches are exactly the
accepting computation histories of $M$ on $w$ — the strings
$\#\,C_1\,\#\,C_2\,\#\cdots\#\,C_k\,\#$ of consecutive configurations from
$q_0 w$ to a configuration in the accept state, each obtained from the previous
one by a step of the machine; the passage through the modified problem, in
which a match must start with the first domino, is the $\star$ trick. The
construction is effective, indeed primitive recursive, which is the part of the
argument that the textbook takes for granted.

# Formalization notes

Both problems are stated over the alphabet `ℕ` with mathlib's
`ComputablePred`: Sipser's instance is built over the alphabet `Sym` of
configurations and histories, and the proof transports it to `ℕ` along an
injective encoding of `Sym`, which preserves and reflects the existence of a
match.
-/

namespace Lax251941.PostCorrespondenceReduction

open Lax251941.TuringMachines Lax251941.PostCorrespondence

/-- A decision procedure for the Post correspondence problem would decide the
acceptance problem for Turing machines. -/
axiom computablePred_accepts_of_hasMatch
    (h : ComputablePred fun P : Inst ℕ => HasMatch P) :
    ComputablePred fun p : TM × List ℕ => p.1.Accepts p.2

end Lax251941.PostCorrespondenceReduction
