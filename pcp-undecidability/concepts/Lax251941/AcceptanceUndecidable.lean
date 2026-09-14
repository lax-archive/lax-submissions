import Lax251941.Acceptance

/-!
---
title: The acceptance problem is undecidable
type: theorem
---
No machine decides the acceptance problem $A_{TM}$ (Sipser, Theorem 4.11). The
proof is the diagonalisation argument: a decider $H$ for $A_{TM}$ would give a
machine $D$ that, on the description $\langle N\rangle$ of a machine $N$, runs
$H$ on $\langle N, \langle N\rangle\rangle$ and answers the opposite; running $D$
on its own description is then a contradiction.

# Formalization notes

The statement is `¬ TuringDecidable ATM` for the machines and the language of
`Acceptance`. It is equivalent to the membership predicate of `ATM` not being
mathlib's `ComputablePred`, decidability of a language and computability of its
membership predicate being the same thing for these machines.
-/

namespace Lax251941.AcceptanceUndecidable

open Lax251941.Acceptance

/-- Sipser's Theorem 4.11: the acceptance problem is undecidable. -/
axiom not_turingDecidable_ATM : ¬ TuringDecidable ATM

end Lax251941.AcceptanceUndecidable
