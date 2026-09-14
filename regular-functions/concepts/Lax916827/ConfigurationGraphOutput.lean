import Mathlib.Computability.DFA
import Lax916827.ConfigurationGraphs

/-!
---
title: Checking the output of a configuration graph against a regular language
type: theorem
---
For a regular language $L$ over the output alphabet, the set of strings over
$C$ that represent a reachable configuration graph whose output string belongs
to $L$ is a regular language (Lemma C.2.4 of *Transducers*). An automaton
checks that the string is a representation and guesses a labelling of the edges
of the represented path by transitions of an automaton for $L$.

# Formalization notes

The output string of a representation is the string printed by the transducer
`pathTrans M` walking along the represented path; on the representation of the
graph of `M` on `w` it is the output of `M` on `w`. As in the book, the
transducer is assumed to compute a total function `f`, so that every
representation has an output.
-/

namespace Lax916827.ConfigurationGraphOutput

open Lax916827.TwoWayTransducers Lax916827.ConfigurationGraphs

/-- The representations of reachable configuration graphs whose output lies in a
regular language form a regular language. -/
axiom isRegular_encOutputLang {A B Q : Type} [Finite A] [Finite Q] (M : TwoWay A B Q)
    {f : List A → List B} (hM : ∀ w, M.Computes w (f w)) {L : Language B} (hL : L.IsRegular) :
    Language.IsRegular {u : List (CLet Q (TwoWay.Lab M)) |
      (∃ w, u = TwoWay.enc M w) ∧ ∃ v, (TwoWay.pathTrans M).Computes u v ∧ v ∈ L}

end Lax916827.ConfigurationGraphOutput
