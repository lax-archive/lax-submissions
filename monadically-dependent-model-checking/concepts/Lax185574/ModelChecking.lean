import Lax185574.Algorithms
import Lax185574.MonadicDependence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: First-order model checking on monadically dependent graph classes
type: theorem
---
There is an algorithm which solves the model checking problem for
first-order logic on graphs, that is, it decides whether a given graph
*G* satisfies a given first-order sentence φ, with the following
guarantee. For every monadically dependent graph class 𝒞 and every real
ε > 0, the algorithm runs in time O_{𝒞,φ,ε}(n^(3+ε)) on the n-vertex
graphs G ∈ 𝒞.

# Formalization notes

The algorithm is an algorithm in the sense of `Lax185574.Algorithms`, a
word RAM program together with the exponent of the word length it needs.
It comes first, before the class, the sentence and ε, and it knows none
of them. Only the constant `c` of the O-notation depends on them.

`A.Decides c (G, φ) (G ⊨ φ) T` is a statement about the encoding of the
pair `(G, φ)` of `Lax185574.Encodings`, which is the encoding of the
graph followed by the encoding of the sentence. At every word length
that is admissible for `c`, every halting run of `A` on this input
writes `1` if `G ⊨ φ` and `0` otherwise, and `A` halts within
`c · T + c` steps once this number fits into a word. Here
`T = n^(3+ε)` is the real power. The additive `c` is part of the
O-notation, and it covers small graphs, such as the graph without
vertices, where `T` vanishes. An n-vertex graph with m edges is encoded
by a word of length n + 4m + 1 ≤ 2n² + 1, so reading the input fits into
the time bound.

Every graph lies in a monadically dependent class, for instance the
class consisting of it alone. So the algorithm decides every instance
correctly at every word length that is admissible for some such class.
The time bound is claimed for members of a monadically dependent class
only.

Monadic dependence is the transduction-based definition of
`Lax185574.MonadicDependence`: the class does not transduce the class of
all graphs. It agrees with the archive's definition
`Lax710763.MonadicDependence` and with the definition of the paper, see
`Lax185574.MonadicDependence`.
-/

namespace Lax185574.ModelChecking

open Lax185574.Graphs Lax185574.FirstOrderLogic Lax185574.MonadicDependence
open Lax185574.Algorithms

/-- **First-order model checking on monadically dependent graph
classes.** There is an algorithm `A` such that for every monadically
dependent class `C`, every sentence `φ` and every `ε > 0` there is a
constant `c` such that `A` decides `G ⊨ φ` from `(G, φ)` in time
`O(n ^ (3 + ε))` with the constant `c`, for every graph `G ∈ C` on `n`
vertices. -/
axiom exists_program_modelChecking :
    ∃ A : Algorithm, ∀ C : GraphClass, MonadicallyDependent C →
      ∀ (φ : Sentence) (ε : ℝ), 0 < ε → ∃ c : ℕ,
        ∀ G ∈ C, A.Decides c (G, φ) (G ⊨ φ) ((G.n : ℝ) ^ (3 + ε))

end Lax185574.ModelChecking
