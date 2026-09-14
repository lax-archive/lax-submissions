import Lax132576.TransducerCodes
import Lax132576.WeightedCodes

/-!
---
title: Decidable zeroness of weighted automata over the rationals
type: theorem
---
The zeroness problem — does a given weighted automaton over the field of
rationals compute the constant function $0$? — is decidable (Theorem B.3.7 of
*Transducers*). It is the special case of equivalence (Theorem B.3.3) in which
the second automaton is empty, and conversely equivalence reduces to zeroness
of the difference; the book proves the zeroness criterion, Schützenberger's
bound on the length of a witness, and derives both.

# Formalization notes

The automaton is given by a valid code, and the decided property is that its
function is `0`.
-/

namespace Lax132576.WeightedZeronessDecidable

open Lax132576.TransducerCodes Lax132576.WeightedCodes

/-- Zeroness of a valid coded weighted automaton over `ℚ` is decidable. -/
axiom decidable_wcodeEval_eq_zero :
    DecidableUnderPromise WCodeValid (fun c => wcodeEval c = 0)

end Lax132576.WeightedZeronessDecidable
