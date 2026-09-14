import Lax132576.RationalFunctions
import Lax132576.WeightedAutomata

/-!
---
title: Weighted automata are closed under pre-composition with rational functions
type: theorem
---
For every semiring $\mathbb{S}$, the composition
$$A^* \xrightarrow{f} B^* \xrightarrow{h} \mathbb{S}$$
of a rational function $f$ with a function $h$ computed by a weighted automaton
is computed by a weighted automaton (Lemma B.3.5 of *Transducers*). The
automaton for $f$ is first made unambiguous and ε-free (Lemmas B.2.4 and
B.2.5), so that its unique run aligns with the runs of the automaton for $h$
in a product construction whose transitions carry, as weight, the sum of the
weights of the runs of $h$ over the output of one transition of $f$.

# Formalization notes

The semiring is arbitrary (mathlib's `Semiring`); both alphabets are assumed
finite, as the unambiguous automaton needs.
-/

namespace Lax132576.WeightedPrecomposition

open Lax132576.RationalFunctions Lax132576.WeightedAutomata

/-- Pre-composing a weighted function with a rational function gives a weighted
function. -/
axiom isWeighted_comp_of_isRationalFun {A B S : Type} [Finite A] [Finite B] [Semiring S]
    {f : List A → List B} {h : List B → S} (hf : IsRationalFun f) (hh : IsWeighted h) :
    IsWeighted (h ∘ f)

end Lax132576.WeightedPrecomposition
