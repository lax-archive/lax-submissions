import Lax185574.TypeSplitting

/-!
---
title: Splitting by minimal representatives preserves coarsening
type: lemma
---
Fix a graph G together with a total order < on its vertices. Let
𝒫₁ ≼ 𝒫₂ ≼ ⋯ ≼ 𝒫_m be a sequence of ever coarser partitions of V(G). Pick
representatives T₁ ⊇ T₂ ⊇ ⋯ ⊇ T_m of 𝒫₁, …, 𝒫_m by setting

T_i ≔ { min_<(P) : P ∈ 𝒫_i },

and define 𝒬_i ≔ 𝒫_i ∧ T_i. Then 𝒬₁ ≼ 𝒬₂ ≼ ⋯ ≼ 𝒬_m is also a sequence
of ever coarser partitions.

# Formalization notes

The paper uses this lemma inside the proof that the partitions of its
merge sequence get coarser.

The order is a linear order on the vertex type. The set T_i is the set
of vertices that are minimal in their part, `minimalVertices`. On a
finite vertex type every part has a minimum, so this set is a
transversal. The conclusion needs no finiteness. The sequence is a
list, and the hypothesis and the conclusion compare consecutive
entries.
-/

namespace Lax185574.SplittingMonotone

open Lax185574.TypeSplitting

universe z

variable {V : Type z}

/-- The vertices that are minimal in their part of `P`. -/
def minimalVertices [LinearOrder V] (P : Setoid V) : Set V :=
  {v | ∀ u : V, P u v → v ≤ u}

/-- **Coarsening is preserved.** Splitting ever coarser partitions
along their minimal vertices gives ever coarser partitions. -/
axiom split_minimalVertices_mono [LinearOrder V] (G : SimpleGraph V) (Ps : List (Setoid V))
    (h : ∀ (t : ℕ) (ht : t + 1 < Ps.length), Ps[t] ≤ Ps[t + 1]) :
    ∀ (t : ℕ) (ht : t + 1 < Ps.length),
      split G Ps[t] (minimalVertices Ps[t]) ≤ split G Ps[t + 1] (minimalVertices Ps[t + 1])

end Lax185574.SplittingMonotone
