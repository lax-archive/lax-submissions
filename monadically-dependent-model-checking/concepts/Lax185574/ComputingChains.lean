import Lax185574.Chains
import Lax185574.Algorithms
import Lax185574.MonadicDependence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Computing chains of small width
type: theorem
---
There is an algorithm which, given an n-vertex graph G, a radius r ∈ ℕ
and a rational ε > 0, computes a chain of G of length O(r/ε) and radius-r
width O_{𝒞,r,ε}(n^ε), and runs in time Ô_{𝒞,r}(n³), where 𝒞 is any
monadically dependent graph class containing G. Here Ô_k(n^c) stands for
a bound O_{k,δ}(n^{c+δ}) for every δ > 0.

The paper cites this as Theorem 4.4 of the companion paper
*Monadically dependent graph classes have almost bounded merge-width*
(see `Lax185574.ChainTheorem`).

# Formalization notes

The radius is at least 1, which is the case used. The chain is
produced by a function `chain` of r, ε and the graph, and the algorithm
`A` computes this function, in the sense of `Lax185574.Algorithms`. The
algorithm and the absolute constant `K` of the length bound come first.
On every graph the output is a chain of length at most K · r/ε + K. The
algorithm does not depend on the class. For a monadically dependent
class 𝒞, a radius r and ε, the constant `c` bounds the width by
c · (n+1)^ε on the members of 𝒞. The input is the triple (r, ε, G) and
the output is the list of the sets of the chain. The chain is listed in
increasing order, ∅ = S₁ ⊆ ⋯ ⊆ S_m = V(G), as in `Lax185574.Chains`.
This is the reverse of the order of the paper.

**Deviation from the paper.** The paper claims the running time
Ô_{𝒞,r}(n³), whose constant does not depend on ε. Here the time bound
is O(n^{3+δ}) on members of 𝒞 for every δ > 0, with a constant c
depending on 𝒞, r, ε and δ, as in `Lax185574.ChainTheorem`. This is
weaker than the paper and is what `Lax185574.DefinableSequences`
needs. A caller chooses δ independently of ε, so that the time fits the
word lengths of its own statement. The statement is the companion
paper's theorem with the chain reversed. The word lengths at which the
statement speaks also depend on the class, through c, as in
`Lax185574.DefinableSequences`.
-/

namespace Lax185574.ComputingChains

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.Algorithms Lax185574.Chains

/-- **Computing chains.** One algorithm computes, from `r ≥ 1`, a
rational `ε > 0` and a graph, a chain of length at most `K · r/ε + K`. On
members of a monadically dependent class, the chain has radius-`r` width
at most `c · (n+1)^ε`, and for every `δ > 0` the algorithm takes time
`O(n^(3+δ))`, with `c` depending also on `δ`. -/
axiom exists_program_chain :
    ∃ (A : Algorithm) (K : ℕ) (chain : ℕ → ℚ → (G : Graph) → List (Finset (Fin G.n))),
      (∀ (r : ℕ) (ε : ℚ) (G : Graph), 1 ≤ r → 0 < ε →
        IsChain (chain r ε G) ∧ ((chain r ε G).length : ℚ) ≤ K * r / ε + K) ∧
      ∀ C : GraphClass, MonadicallyDependent C → ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε →
        ∀ δ : ℝ, 0 < δ → ∃ c : ℕ, ∀ G ∈ C,
          (chainWidth G.toSimpleGraph r (chain r ε G) : ℝ) ≤ c * ((G.n : ℝ) + 1) ^ (ε : ℝ) ∧
          A.Computes c (r, ε, G) (chain r ε G) ((G.n : ℝ) ^ (3 + δ))

end Lax185574.ComputingChains
