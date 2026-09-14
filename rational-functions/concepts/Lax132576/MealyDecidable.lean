import Lax765601.MealyMachine
import Lax132576.TransducerCodes

/-!
---
title: Deciding whether a rational function is a Mealy machine
type: theorem
---
One can decide whether a given rational function is computed by a Mealy
machine (Theorem B.4.2 of *Transducers*). By Theorem B.4.1 it suffices to check
the three properties of a Mealy function: continuity is automatic for a
rational function, length preservation is decided by Lemma B.4.3, and after
Lemma B.4.5 has put the automaton in a form where every transition reads and
writes one letter, prefix preservation fails exactly when two transitions with
the same input letter and different output letters start in states reachable
by a common input string.

# Formalization notes

The function is given by a functional code, and the decided property is that
some function computed by a Mealy machine agrees with the coded relation on
the code words: a code reads only the letters of its alphabet, so the
comparison is relativised to `CodeWord c` — without the relativisation the
property would be false for every code and the statement empty. The proof
reduces prefix preservation to the equality of two rational functions, decided
by Theorem B.3.4.
-/

namespace Lax132576.MealyDecidable

open Lax765601.MealyMachine Lax132576.TransducerCodes

/-- Whether a coded rational function is computed by a Mealy machine is decidable.
-/
axiom decidable_isMealy :
    DecidableUnderPromise CodeFunctional
      (fun c => ∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f)

end Lax132576.MealyDecidable
