import Lax185574.BetterMergeSequences
import Lax185574.ConstructionWidth
import Lax185574.LocalDefinability
import Lax185574.ConstructionSequences

/-!
---
title: From merge sequences to locally definable construction sequences
type: lemma
---
For every n-vertex graph G and merge sequence (𝒫₁, R₁), …, (𝒫_ℓ, R_ℓ) of
G, there is a construction sequence G₁, …, G_λ of G such that the
following properties hold for all r ≥ 1. Let w_r be the radius-r width
of the merge sequence.

1. The obtained construction sequence has radius-r width at most w_r,
   and has length λ ≤ O(n w₁).
2. Suppose for every i ∈ [ℓ], the relations ≡_{𝒫_i} and R_i are
   definable in some expansion of G with 2 unary predicates, using two
   fixed first-order formulas of quantifier rank 5. Then, for every
   t ∈ [λ−1] and v ∈ V(G), the induced partial graph
   G_t[Ball^{G_{t+1}}_r(v)] is definable in some expansion of G with
   2ℓ+1 unary predicates, using formulas of quantifier rank 7 with w_r
   parameters.
3. The construction sequence can be computed in time O(ℓ n²), given an
   n-vertex graph G and merge sequence of length ℓ.

# Formalization notes

The construction sequence is produced by a function `script` of the
graph and the merge sequence, as a script of
`Lax185574.ConstructionSequences`, and the algorithm `A` computes this
function, in the sense of `Lax185574.Algorithms`. The algorithm, the
constant `c` of the time bound O((ℓ+1) · (n+1)²) and the constant `K` of
the length bound come first, so both constants are absolute. The input
is the pair (G, merge sequence). A graph has the vertices `Fin n`, and
the notions of merge sequences and construction sequences are applied
to its `SimpleGraph`.

A merge sequence is one in the sense of `Lax185574.MergeSequences`, so
𝒫₁ is the partition into singletons and 𝒫_ℓ = {V(G)} by its definition.

The width of item 1 is the radius-r width of
`Lax185574.ConstructionWidth`, which counts parts. The length bound
O(n w₁) is spelled out as K · (n+1) · (w₁+1). The radius-r width of the
merge sequence is `MergeSequences.mergeWidth`. The definability
hypothesis of item 2 is `BetterMergeSequences.StagesDefinable` for some
two formulas of quantifier rank at most 5, and the conclusion is
`LocalDefinability.IsRadiusDefinable` with 2ℓ+1 predicates, w_r
parameters and rank 7.

**Deviation from the paper.** Both bounds use max(1, w_r) instead of
w_r. On a graph with one vertex the merge sequence of length 1 has width
0, the maximum over an empty range, while every construction sequence
has width 1. For n ≥ 2 the two agree, since every merge sequence has
length at least 2 and width at least 1.

Every number in the encoding of the script is at most the length of the
encoding plus n (`Script.HasSmallNumbers`). The paper does not say
this. An algorithm can ensure it by giving the vertices of the initial
partial graph the colors 0, …, n − 1. The bound lets the output be
passed on as in `Lax185574.DefinableSequences`.
-/

namespace Lax185574.MergeToConstruction

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.Graphs Lax185574.Algorithms
open Lax185574.Partitions Lax185574.MergeSequences Lax185574.BetterMergeSequences
open Lax185574.ConstructionSequences Lax185574.ConstructionWidth
open Lax185574.LocalDefinability Lax185574.FirstOrderTypes

/-- **Merge sequences to construction sequences.** One algorithm
converts a merge sequence of length `ℓ` of a graph into a construction
sequence of the same graph, given by its script, in time
`O((ℓ+1) · (n+1)²)`. For every `r ≥ 1`, the construction sequence has
radius-`r` width at most `max 1 w_r`, where `w_r` is the radius-`r`
width of the merge sequence, and length at most `K · (n+1) · (w₁+1)`. If
two formulas of quantifier rank at most `5` define the stages, it is
radius-`r` definable with `2ℓ+1` predicates, `max 1 w_r` parameters and
rank `7`. -/
axiom exists_constructionSequence_of_mergeSequence :
    ∃ (A : Algorithm) (c K : ℕ) (script : (G : Graph) →
        List (Setoid (Fin G.n) × SimpleGraph (Fin G.n)) → Script G.n),
      ∀ (G : Graph) (ms : List (Setoid (Fin G.n) × SimpleGraph (Fin G.n))),
        IsMergeSequence G.toSimpleGraph ms →
          let σ := script G ms
          IsConstructionSequence G.toSimpleGraph σ.run ∧ σ.HasSmallNumbers ∧
          σ.run.length ≤ K * (G.n + 1) * (mergeWidth 1 ms + 1) ∧
          (∀ r : ℕ, 1 ≤ r →
            constructionWidth r σ.run ≤ max 1 (mergeWidth r ms) ∧
            ((∃ φeq φR : (withColors Language.graph 2).Formula (Fin 2),
                quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
                  StagesDefinable G.toSimpleGraph ms φeq φR) →
              IsRadiusDefinable G.toSimpleGraph σ.run r (2 * ms.length + 1)
                (max 1 (mergeWidth r ms)) 7)) ∧
          A.Computes c (G, ms) σ ((ms.length + 1) * (G.n + 1) ^ 2)

end Lax185574.MergeToConstruction
