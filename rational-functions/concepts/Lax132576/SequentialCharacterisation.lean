import Lax765601.Continuity
import Lax765601.ElementaryProperties
import Lax132576.SequentialTransducers

/-!
---
title: Machine-independent characterisation of sequential functions
type: theorem
---
A function $f : A^* \to B^*$ is sequential if and only if it (a) is continuous,
(b) is prefix preserving, (c) outputs $\varepsilon$ on the input $\varepsilon$,
and (d) has the *bounded increase* property: the increase of output length
caused by extending the input by one letter,
$$\sup_{w \in A^*,\, a \in A} |f(wa)| - |f(w)|,$$
is finite (Theorem B.4.6 of *Transducers*, Ginsburg and Rose). The derivative
$wa \mapsto f(w)^{-1} f(wa)$, well defined by prefix preservation and of
finite image by bounded increase, is shown to be computed by a finite
automaton — its length by continuity modulo a large enough number, and then
its value by continuity again.

# Formalization notes

Item (c) is the conjunct `f [] = []`. An earlier edition of the book omitted
it, and without it the statement is false: a sequential transducer produces no
output before reading any input, while $a^n \mapsto a^{n+1}$ has the three
other properties. Bounded increase is stated with an explicit bound `K`. Both
alphabets are assumed finite.
-/

namespace Lax132576.SequentialCharacterisation

open Lax765601.Continuity Lax765601.ElementaryProperties Lax132576.SequentialTransducers

/-- A function is sequential if and only if it maps `ε` to `ε`, is continuous,
prefix preserving, and has bounded increase. -/
axiom isSequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSequential f ↔
      f [] = [] ∧ Continuous f ∧ PrefixPreserving f ∧
        ∃ K : ℕ, ∀ (w : List A) (a : A), (f (w ++ [a])).length ≤ (f w).length + K

end Lax132576.SequentialCharacterisation
