import Mathlib.Data.Set.Finite.Basic
import Lax765601.Continuity
import Lax132576.RationalFunctions
import Lax132576.LeftDistance

/-!
---
title: Machine-independent characterisation of rational functions
type: theorem
---
A function $f : A^* \to B^*$ is rational if and only if it is continuous and
the equivalence relation
$$w_1 \sim w_2 \quad\Longleftrightarrow\quad \sup_{w \in A^*} \|f(w w_1), f(w w_2)\| < \infty$$
on input strings has finite index (Theorem B.4.13 of *Transducers*, Reutenauer
and Schützenberger). For a rational function computed by a bimachine, two
strings with the same state of the suffix automaton are equivalent, so the
index is finite; conversely the finitely many classes are used as the states of
a suffix automaton, and the output after a prefix is computed by a
subsequential transducer for each class. String reversal is not rational: all
its input strings are pairwise inequivalent.

# Formalization notes

The relation is `BoundedVarRel f` of `LeftDistance`; finite index is the
finiteness of the set of its classes `{w₂ | w₁ ∼ w₂}`, as a set of sets. Both
alphabets are assumed finite.
-/

namespace Lax132576.RationalMachineIndependent

open Lax765601.Continuity Lax132576.RationalFunctions Lax132576.LeftDistance

/-- A function is rational if and only if it is continuous and the relation of
bounded variation has finitely many classes. -/
axiom isRationalFun_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsRationalFun f ↔
      Continuous f ∧ {C : Set (List A) | ∃ w₁, C = {w₂ | BoundedVarRel f w₁ w₂}}.Finite

end Lax132576.RationalMachineIndependent
