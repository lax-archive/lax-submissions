import Lax185574.PairRelation
import Lax185574.TypeSplitting
import Lax185574.MergeSequences

/-!
---
title: Splitting by a transversal gives a partition homogeneous modulo the pair relation
type: lemma
---
Fix a graph G and a partition 𝒫 of V(G), let T be a transversal of 𝒫,
and R ≔ R(G, 𝒫). Then 𝒬 ≔ 𝒫 ∧ T is *homogeneous modulo R*, that is,
for all X, Y ∈ 𝒬 either

XY ∖ R ⊆ E(G)  or  XY ∖ R ⊆ E(Ḡ).

# Formalization notes

Homogeneity modulo R is `MergeSequences.HomogeneousModulo`, the fourth
condition of a merge sequence. The graph may be infinite.
-/

namespace Lax185574.HomogeneousSplitting

open Lax185574.Partitions Lax185574.PairRelation Lax185574.TypeSplitting
open Lax185574.MergeSequences

universe z

/-- **Homogeneity modulo the pair relation.** For a transversal `T` of
`𝒫`, the partition `𝒫 ∧ T` is homogeneous modulo `R(G, 𝒫)`. -/
axiom homogeneousModulo_split {V : Type z} (G : SimpleGraph V) (P : Setoid V) (T : Set V)
    (hT : IsTransversal P T) :
    HomogeneousModulo G (split G P T) (pairRelation G P)

end Lax185574.HomogeneousSplitting
