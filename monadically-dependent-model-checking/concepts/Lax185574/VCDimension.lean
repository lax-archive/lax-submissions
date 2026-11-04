import Lax199508.NeighborhoodComplexity
import Mathlib.Data.ENat.Lattice

/-!
---
title: Neighborhood complexity and VC-dimension
type: definition
---
The *neighborhood complexity* of a graph G is the function π_G : ℕ → ℕ
defined by

π_G(k) ≔ max_{S ⊆ V(G), |S| ≤ k} |{ N^G(v) ∩ S : v ∈ V(G) }|,

which counts the maximum number of distinct neighborhoods of vertices of
G restricted to a set of size at most k.

The *VC-dimension* of a graph G is the maximal size of a set A ⊆ V(G)
such that { N(v) ∩ A : v ∈ V(G) } = 2^A.

# Formalization notes

The number of traces |{ N^G(v) ∩ S : v ∈ V(G) }| is `traceCount` of the
Sparsity Lectures submission (Lax199508), which is the cardinality of
the set of traces. For a finite set S the traces are subsets of S, so
there are at most 2^|S| of them and the count is exact. The maximum over
all S with |S| ≤ k is the supremum of a set of natural numbers bounded
by 2^k, so it is attained.

A set A is shattered if every subset B ⊆ A is the trace N(v) ∩ A of some
vertex v. The VC-dimension is the supremum of the sizes of the finite
shattered sets, an extended natural number. It is the maximum of the
paper whenever that exists, and ⊤ for a graph with arbitrarily large
shattered sets. "VC-dimension at most d" is `vcDim G ≤ d`.
-/

namespace Lax185574.VCDimension

open Lax199508.NeighborhoodComplexity

universe u

variable {V : Type u}

/-- The neighborhood complexity `π_G(k)`: the largest number of
neighborhood traces `N(v) ∩ S` on a set `S` of at most `k` vertices. -/
noncomputable def neighborhoodComplexity (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sSup {m | ∃ S : Finset V, S.card ≤ k ∧ m = traceCount G (S : Set V)}

/-- The neighborhoods of `G` shatter `A`: every subset of `A` is the
trace `N(v) ∩ A` of some vertex `v`. -/
def Shatters (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ B ⊆ A, ∃ v : V, ∀ a ∈ A, (G.Adj v a ↔ a ∈ B)

/-- The VC-dimension of `G`: the supremum of the sizes of the finite
vertex sets shattered by the neighborhoods. -/
noncomputable def vcDim (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (A : Finset V) (_ : Shatters G A), (A.card : ℕ∞)

end Lax185574.VCDimension
