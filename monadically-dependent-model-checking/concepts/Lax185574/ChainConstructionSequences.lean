import Lax185574.Chains
import Lax185574.VCDimension
import Lax185574.ConstructionWidth
import Lax185574.LocalDefinability
import Lax185574.ConstructionSequences
import Lax185574.Algorithms

/-!
---
title: Locally definable construction sequences from chains
type: lemma
---
For every n-vertex graph G and its chain of length ℓ there is a
construction sequence G₁, …, G_λ of G such that the following properties
hold for all r ≥ 1. Let k_r denote the radius-(5r+1) width of the chain
and w_r ≔ k_r · π_G(k_r).

1. The resulting construction sequence has radius-r width at most w_r
   and length λ ≤ O(n w₁).
2. For every t ∈ [λ−1] and v ∈ V(G), the induced partial graph
   G_t[Ball^{G_{t+1}}_r(v)] is definable in some expansion of G with
   2ℓ+1 unary predicates, using formulas of quantifier rank 7 with w_r
   parameters.
3. The construction sequence can be computed in time O(ℓ n³), given G
   and its chain.

# Formalization notes

The construction sequence is produced by a function `script` of the
graph and the chain, as a script of `Lax185574.ConstructionSequences`,
and the algorithm `A` computes this function, in the sense of
`Lax185574.Algorithms`. The algorithm, the constant `c` of the time
bound O((ℓ+1) · (n+1)³) and the constant `K` of the length bound come
first, so both constants are absolute. The input is the pair (G, S),
with the encodings of `Lax185574.Encodings`. A graph has the vertices
`Fin n`, and the notions of chains and construction sequences are
applied to its `SimpleGraph`.

The width of item 1 is the radius-r width of
`Lax185574.ConstructionWidth`, which counts parts. The length bound
O(n w₁) is spelled out as K · (n+1) · (w₁+1). The number w_r is
`chainBound G S r`, with π_G the neighborhood complexity
`VCDimension.neighborhoodComplexity`. Item 2 is
`LocalDefinability.IsRadiusDefinable` with 2ℓ+1 predicates, w_r
parameters and rank 7.

Every number in the encoding of the script is at most the length of the
encoding plus n (`Script.HasSmallNumbers`). The paper does not say
this. An algorithm can ensure it by giving the vertices of the initial
partial graph the colors 0, …, n − 1. The bound is what
`Lax185574.DefinableSequences` asks of its output.
-/

namespace Lax185574.ChainConstructionSequences

open Lax185574.Graphs Lax185574.Algorithms
open Lax185574.Chains Lax185574.VCDimension
open Lax185574.ConstructionSequences Lax185574.ConstructionWidth
open Lax185574.LocalDefinability

universe z

/-- The number `w_r = k_r · π_G(k_r)`, where `k_r` is the
radius-`(5r+1)` width of the chain `S`. -/
noncomputable def chainBound {V : Type z} (G : SimpleGraph V) (S : List (Finset V)) (r : ℕ) : ℕ :=
  chainWidth G (5 * r + 1) S * neighborhoodComplexity G (chainWidth G (5 * r + 1) S)

/-- **Construction sequences from chains.** One algorithm computes, from
a graph and a chain of length `ℓ`, a construction sequence of the graph,
given by its script, in time `O((ℓ+1) · (n+1)³)`. For every `r ≥ 1`, it
has radius-`r` width at most `w_r` and length at most
`K · (n+1) · (w₁+1)`, and it is radius-`r` definable with `2ℓ+1`
predicates, `w_r` parameters and rank `7`. -/
axiom exists_constructionSequence_of_chain :
    ∃ (A : Algorithm) (c K : ℕ) (script : (G : Graph) → List (Finset (Fin G.n)) → Script G.n),
      ∀ (G : Graph) (S : List (Finset (Fin G.n))), IsChain S →
        let σ := script G S
        IsConstructionSequence G.toSimpleGraph σ.run ∧ σ.HasSmallNumbers ∧
        σ.run.length ≤ K * (G.n + 1) * (chainBound G.toSimpleGraph S 1 + 1) ∧
        (∀ r : ℕ, 1 ≤ r →
          constructionWidth r σ.run ≤ chainBound G.toSimpleGraph S r ∧
          IsRadiusDefinable G.toSimpleGraph σ.run r (2 * S.length + 1)
            (chainBound G.toSimpleGraph S r) 7) ∧
        A.Computes c (G, S) σ ((S.length + 1) * (G.n + 1) ^ 3)

end Lax185574.ChainConstructionSequences
