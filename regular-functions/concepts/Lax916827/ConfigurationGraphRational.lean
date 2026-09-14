import Lax132576.RationalFunctions
import Lax916827.ConfigurationGraphs

/-!
---
title: Computing the reachable configuration graph is rational
type: theorem
---
The function which maps an input string to the string representation of its
reachable configuration graph is rational (Lemma C.2.3 of *Transducers*). The
main observation is that the representations of reachable configuration graphs
form a regular language — reachability is checked locally, slice by slice — so
that an automaton with output can guess the representation and verify it.

# Formalization notes

The alphabet and the state space are assumed finite, so that the alphabet `C` is
finite; the output alphabet may be arbitrary. `enc M` is the representation of
`ConfigurationGraphs`.
-/

namespace Lax916827.ConfigurationGraphRational

open Lax132576.RationalFunctions Lax916827.TwoWayTransducers Lax916827.ConfigurationGraphs

/-- The string representation of the reachable configuration graph is a rational
function of the input. -/
axiom isRationalFun_enc {A B Q : Type} [Finite A] [Finite Q] (M : TwoWay A B Q) :
    IsRationalFun (TwoWay.enc M)

end Lax916827.ConfigurationGraphRational
