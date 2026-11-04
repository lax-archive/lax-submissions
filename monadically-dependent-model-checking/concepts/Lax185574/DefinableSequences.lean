import Lax185574.LocalDefinability
import Lax185574.ConstructionSequences
import Lax185574.MonadicDependence
import Lax185574.Algorithms
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Computing locally definable construction sequences
type: theorem
---
Let r ≥ 1 be an integer, ε > 0 a rational, and 𝒞 a monadically
dependent graph class. There is a constant δ ≥ 1 depending only on 𝒞
such that every n-vertex graph G ∈ 𝒞 has a construction sequence of G
which is radius-r definable with O(r/ε) unary predicates,
O_{𝒞,r,ε}(n^{δε}) parameters and quantifier rank 7, and has length
O_{𝒞,r,ε}(n^{1+δε}). Moreover, there is an algorithm (independent of 𝒞)
which, given r, ε and G, computes such a sequence, and runs in time
Ô_{𝒞,r,ε}(n³) whenever G ∈ 𝒞. Here Ô_k(n³) stands for a bound
O_{k,η}(n^{3+η}) for every η > 0.

# Formalization notes

The construction sequence is produced by a function `script` of r, ε
and the graph, as a script of `Lax185574.ConstructionSequences`, and
the algorithm `A` computes this function, in the sense of
`Lax185574.Algorithms`. The algorithm, the function and the absolute
constant `K` of the bound O(r/ε) on the number of predicates come first,
so none of them depends on the class. On every graph, the script gives
a construction sequence of the graph. The input of the algorithm is the
triple (r, ε, G), with the encodings of `Lax185574.Encodings`.

The constant δ of the paper is `a`. It is chosen after the class and
before r and ε. The time bound Ô_{𝒞,r,ε}(n³) is spelled out as
`n^(3+η)` for every real η > 0, with the constant `c` depending on 𝒞,
r, ε and η. The same `c` bounds the sequence. The bounds on the
sequence do not involve η, so a single η, say η = 1, gives a constant
for them. The number of unary predicates is at most `⌈K · r/ε⌉ + K`,
which is O(r/ε) in the sense of the paper, including its additive
constant.

Every graph belongs to some monadically dependent class, for instance
the class containing it alone. So the algorithm computes the script of
every graph, at every word length admissible for the constant of some
class that contains it.

Every number in the encoding of the script is at most the length of the
encoding plus n (`Script.HasSmallNumbers`). The paper does not say
this. The algorithm can ensure it by giving the vertices of the initial
partial graph the colors 0, …, n − 1, since steps only use colors that
occur.
-/

namespace Lax185574.DefinableSequences

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.Algorithms
open Lax185574.ConstructionSequences Lax185574.LocalDefinability

/-- **Locally definable construction sequences.** One algorithm
computes, from `r ≥ 1`, a rational `ε > 0` and a graph `G`, a
construction sequence of `G`, given by its script. On members of a
monadically dependent class it takes time `O(n^(3+η))` for every
`η > 0`, and the sequence has length at most `c · (n+1)^(1+aε)` and is
radius-`r` definable with `⌈K·r/ε⌉ + K` unary predicates,
`⌊c · (n+1)^(aε)⌋` parameters and quantifier rank `7`. Here `a ≥ 1`
depends only on the class, and `c` on the class, `r`, `ε` and `η`. -/
axiom exists_program_definableSequence :
    ∃ (A : Algorithm) (K : ℕ) (script : ℕ → ℚ → (G : Graph) → Script G.n),
      (∀ (r : ℕ) (ε : ℚ) (G : Graph), 1 ≤ r → 0 < ε →
        IsConstructionSequence G.toSimpleGraph (script r ε G).run ∧
          (script r ε G).HasSmallNumbers) ∧
      ∀ C : GraphClass, MonadicallyDependent C → ∃ a : ℕ, 1 ≤ a ∧
        ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε → ∀ η : ℝ, 0 < η → ∃ c : ℕ,
          ∀ G ∈ C,
            A.Computes c (r, ε, G) (script r ε G) ((G.n : ℝ) ^ (3 + η)) ∧
            ((script r ε G).run.length : ℝ) ≤ c * ((G.n : ℝ) + 1) ^ (1 + (a : ℝ) * ε) ∧
            IsRadiusDefinable G.toSimpleGraph (script r ε G).run r (⌈(K : ℚ) * r / ε⌉₊ + K)
              ⌊(c : ℝ) * ((G.n : ℝ) + 1) ^ ((a : ℝ) * ε)⌋₊ 7

end Lax185574.DefinableSequences
