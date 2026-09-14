import Lax132576.TransducerCodes

/-!
---
title: Deciding length preservation of a rational function
type: theorem
---
One can decide whether a given rational function is length preserving (Lemma
B.4.3 of *Transducers*). The book's direct argument computes the unique
candidate typing $\tau : Q \to \mathbb{Z}$ of the automaton — the difference
between output and input length of the runs reaching each state — and checks
that every transition respects it and that accepting states have type zero
(Claim B.4.4).

# Formalization notes

The decided property, that every output of the coded relation has the length
of its input, is meaningful for every code, so the decision procedure is
correct for every code; the promise that the code is functional is kept for
uniformity with the other decidability statements. The procedure of the proof
enumerates the transition sequences of length at most three times the number of
states and checks the accepting ones, a pumping argument showing the bound
sufficient.
-/

namespace Lax132576.LengthPreservingDecidable

open Lax132576.TransducerCodes

/-- Length preservation of a coded rational function is decidable. -/
axiom decidable_lengthPreserving :
    DecidableUnderPromise CodeFunctional
      (fun c => ∀ w v, codeRel c w v → v.length = w.length)

end Lax132576.LengthPreservingDecidable
