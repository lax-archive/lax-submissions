import Lax185574.MergeSequences
import Lax185574.Chains
import Lax185574.VCDimension
import Lax185574.Colorings
import Lax185574.FirstOrderTypes
import Lax185574.Algorithms

/-!
---
title: Merge sequences with definable stages from chains
type: lemma
---
For every graph G and chain of length ℓ there is a merge sequence
(𝒬₁, R₁), …, (𝒬_ℓ, R_ℓ) with the following properties.

1. For all r ≥ 1, the radius-r width of the merge sequence is bounded by
   k · π_G(k), where k is the radius-(5r+1) width of the given chain.
2. For each i ∈ [ℓ], the relations ≡_{𝒬_i} and R_i are definable in some
   expansion G^i of G with two unary predicates, using two fixed
   first-order formulas φ_≡(x, y) and φ_R(x, y) of quantifier rank at
   most 5.
3. The merge sequence can be computed in time O(ℓ n³), given G and its
   chain.

Here ≡_𝒬 is the equivalence relation on V(G) whose classes are the parts
of the partition 𝒬.

# Formalization notes

The two formulas come first, since they are fixed: the same formulas
serve every graph, every chain and every stage. Only the expansion G^i
depends on the stage. They are formulas of graphs with two colors, in
the language of `Lax185574.Colorings`, with the free variables x and y
of `Fin 2`. `StagesDefinable` states the second property for given
formulas.

The merge sequence is produced by a function `M` of the graph and the
chain, and the algorithm `A` computes this function, in the sense of
`Lax185574.Algorithms`. The algorithm and the constant `c` of the time
bound O((ℓ+1) · (n+1)³) come first, so the constant is absolute. The
input is the pair (G, S) and the output is the merge sequence, with
partitions encoded as in `Lax185574.Partitions`. The merge sequence has
length ℓ, the length of the chain. A graph has the vertices `Fin n`,
and the notions of merge sequences and chains are applied to its
`SimpleGraph`. The neighborhood complexity π_G is
`VCDimension.neighborhoodComplexity`.
-/

namespace Lax185574.BetterMergeSequences

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.Graphs Lax185574.Algorithms
open Lax185574.Partitions Lax185574.MergeSequences Lax185574.Chains
open Lax185574.VCDimension Lax185574.Colorings Lax185574.FirstOrderTypes

universe z

variable {V : Type z}

/-- The stages of the merge sequence `ms` are definable by the formulas
`φeq` and `φR`: for every stage there are two color sets such that, in
the expansion of `G` by them, `φeq` defines the equivalence relation of
the partition and `φR` defines the relation of the stage. -/
def StagesDefinable (G : SimpleGraph V) (ms : List (Setoid V × SimpleGraph V))
    (φeq φR : (withColors Language.graph 2).Formula (Fin 2)) : Prop :=
  ∀ (t : ℕ) (ht : t < ms.length), ∃ colors : Fin 2 → Set V, ∀ x : Fin 2 → V,
    (@Formula.Realize _ V (expansion G colors) _ φeq x ↔ ms[t].1 (x 0) (x 1)) ∧
      (@Formula.Realize _ V (expansion G colors) _ φR x ↔ ms[t].2.Adj (x 0) (x 1))

/-- **Merge sequences from chains.** Two fixed formulas of quantifier
rank at most `5` and one algorithm that computes, from a graph and a
chain of length `ℓ`, a merge sequence of length `ℓ` with the following
properties. (1) For every `r ≥ 1`, its radius-`r` width is at most
`k · π_G(k)` for the radius-`(5r+1)` width `k` of the chain. (2) The two
formulas define its stages. (3) The algorithm takes time
`O((ℓ+1) · (n+1)³)`. -/
axiom exists_mergeSequence_of_chain :
    ∃ (φeq φR : (withColors Language.graph 2).Formula (Fin 2)),
      quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
      ∃ (A : Algorithm) (c : ℕ) (M : (G : Graph) → List (Finset (Fin G.n)) →
          List (Setoid (Fin G.n) × SimpleGraph (Fin G.n))),
        ∀ (G : Graph) (S : List (Finset (Fin G.n))), IsChain S →
          IsMergeSequence G.toSimpleGraph (M G S) ∧ (M G S).length = S.length ∧
          (∀ r : ℕ, 1 ≤ r →
            mergeWidth r (M G S) ≤ chainWidth G.toSimpleGraph (5 * r + 1) S *
              neighborhoodComplexity G.toSimpleGraph (chainWidth G.toSimpleGraph (5 * r + 1) S)) ∧
          StagesDefinable G.toSimpleGraph (M G S) φeq φR ∧
          A.Computes c (G, S) (M G S) ((S.length + 1) * (G.n + 1) ^ 3)

end Lax185574.BetterMergeSequences
