import Lax132576.TransducerCodes
import Lax132576.WeightedCodes

/-!
---
title: Decidable equivalence of weighted automata over the rationals
type: theorem
---
Given two weighted automata over the field of rationals, it is decidable
whether they compute the same function (Theorem B.3.3 of *Transducers*,
Schützenberger). The book proves it through linear representations: the
difference of the two automata is a weighted automaton, and by Schützenberger's
rank argument it is zero on all inputs as soon as it is zero on the inputs of
length less than its dimension, a finite check. The same proof works for any
field whose elements are finitely representable and whose operations are
computable.

# Formalization notes

The automata are given by codes (`WeightedCodes`), the promise is that both
codes are valid, and the decided property is equality of the two computed
functions on all of `ℕ*`; decidability is `DecidableUnderPromise` of
`TransducerCodes`. The decision procedure combines the effective form of
Schützenberger's bound with a primitive recursive evaluation of a coded
automaton on a string, both developed in the proof package.
-/

namespace Lax132576.WeightedEquivalenceDecidable

open Lax132576.TransducerCodes Lax132576.WeightedCodes

/-- Equivalence of two valid coded weighted automata over `ℚ` is decidable. -/
axiom decidable_wcodeEval_eq :
    DecidableUnderPromise (fun p : WCode × WCode => WCodeValid p.1 ∧ WCodeValid p.2)
      (fun p => wcodeEval p.1 = wcodeEval p.2)

end Lax132576.WeightedEquivalenceDecidable
