import Lax185574.Width
import Lax185574.ConstructionSequences
import Lax185574.MonadicDependence
import Lax185574.Algorithms
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Construction sequences with few realized types
type: theorem
---
Let 𝒞 be a monadically dependent graph class, r, q ∈ ℕ, and let ε > 0
be a rational. There is a constant α ≥ 1 depending only on 𝒞 and q such
that every graph G ∈ 𝒞 has a construction sequence of radius-r depth-q
width O_{𝒞,r,q,ε}(n^{αε}) and length O_{𝒞,r,q,ε}(n^{1+αε}). Moreover,
there is an algorithm (independent of 𝒞) which, given r, q ∈ ℕ, a
rational ε > 0 and an n-vertex graph G ∈ 𝒞, computes such a
construction sequence in time Ô_{𝒞,r,q,ε}(n³). Here Ô_k(n³) stands for
a bound O_{k,η}(n^{3+η}) for every η > 0.

It is important that α does not depend on ε, as this makes the exponent
αε of the width as small as one likes.

# Formalization notes

The shape is that of `Lax185574.DefinableSequences`. The construction
sequence is produced by a function `script` of r, q, ε and the graph,
and the algorithm `A` computes this function. Neither depends on 𝒞. On
every graph, the script gives a construction sequence of the graph, and
the numbers in its encoding are small (`Script.HasSmallNumbers`). The
input of the algorithm is the quadruple (r, q, ε, G). The constant α of
the paper is `a`. It is chosen after the class and q, and before r and
ε. The width is the radius-r depth-q width of `Lax185574.Width`.

Every number in the encoding of the script is at most the length of the
encoding plus n. The paper does not say this. The algorithm can ensure
it by giving the vertices of the initial partial graph the colors
0, …, n − 1, since steps only use colors that occur.

The time bound Ô_{𝒞,r,q,ε}(n³) is spelled out as `n^(3+η)` for every
real η > 0, with the constant `c` depending on 𝒞, r, q, ε and η. The
same `c` bounds the sequence.
-/

namespace Lax185574.FewTypes

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.Algorithms
open Lax185574.ConstructionSequences Lax185574.Width

/-- **Construction sequences with few realized types.** One algorithm
computes, from `r`, `q`, a rational `ε > 0` and a graph `G`, a
construction sequence of `G`, given by its script. On members of a
monadically dependent class it takes time `O(n^(3+η))` for every
`η > 0`, and the sequence has length at most `c · (n+1)^(1+aε)` and
radius-`r` depth-`q` width at most `c · (n+1)^(aε)`. Here `a ≥ 1`
depends only on the class and `q`, and `c` on the class, `r`, `q`, `ε`
and `η`. -/
axiom exists_program_fewTypes :
    ∃ (A : Algorithm) (script : ℕ → ℕ → ℚ → (G : Graph) → Script G.n),
      (∀ (r q : ℕ) (ε : ℚ) (G : Graph), 0 < ε →
        IsConstructionSequence G.toSimpleGraph (script r q ε G).run ∧
          (script r q ε G).HasSmallNumbers) ∧
      ∀ C : GraphClass, MonadicallyDependent C → ∀ q : ℕ, ∃ a : ℕ, 1 ≤ a ∧
        ∀ (r : ℕ) (ε : ℚ), 0 < ε → ∀ η : ℝ, 0 < η → ∃ c : ℕ,
          ∀ G ∈ C,
            A.Computes c (r, q, ε, G) (script r q ε G) ((G.n : ℝ) ^ (3 + η)) ∧
            ((script r q ε G).run.length : ℝ) ≤ c * ((G.n : ℝ) + 1) ^ (1 + (a : ℝ) * ε) ∧
            (width r q (script r q ε G).run : ℝ) ≤ c * ((G.n : ℝ) + 1) ^ ((a : ℝ) * ε)

end Lax185574.FewTypes
