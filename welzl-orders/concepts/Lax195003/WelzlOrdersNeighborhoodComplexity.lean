import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

/-!
---
title: Neighborhood complexity
type: definition
---
The neighborhood complexity `π_G(k)` of a finite graph *G* is the largest
number of distinct traces `N(v) ∩ A` left by vertex neighborhoods on a set
*A* of at most *k* vertices. A graph satisfies the linear bound with constant
*c* if `π_G(k) ≤ c · k` for every positive *k*. A graph class has linear
neighborhood complexity if one constant *c* ≥ 1 works uniformly for every
graph in the class.

# Formalization notes

The trace count is defined directly as the natural cardinality of the set of
traces. On the finite carrier `Fin n` this is the exact number of distinct
sets `N(v) ∩ A`. Working with `Set` keeps the trace literal and requires no
decidability instances.

The paper defines the maximum over sets of size at most `k`. On the finite
carrier `Fin n`, the natural supremum below is that maximum. The bound is
required only for positive `k`: at `k = 0`, the empty vertex set has the one
trace `∅`, so the literal inequality `π_G(0) ≤ c · 0` would be false.
-/

namespace Lax195003.WelzlOrdersNeighborhoodComplexity

/-- The number of distinct traces `N(v) ∩ A` that vertex neighborhoods leave
on the vertex set `A`. -/
noncomputable def traceCount {V : Type*} (G : SimpleGraph V)
    (A : Set V) : ℕ :=
  {S : Set V | ∃ v : V, S = G.neighborSet v ∩ A}.ncard

/-- The maximum number of distinct neighborhood traces on a vertex set of
cardinality at most `k`. -/
noncomputable def neighborhoodComplexity {n : ℕ}
    (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ :=
  sSup {q : ℕ | ∃ A : Set (Fin n),
    A.ncard ≤ k ∧ q = traceCount G A}

/-- The graph `G` has neighborhood complexity at most `c · k` for every
positive `k`. -/
def HasLinearNeighborhoodComplexityWithConstant {n : ℕ}
    (G : SimpleGraph (Fin n)) (c : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → neighborhoodComplexity G k ≤ c * k

/-- One natural constant `c ≥ 1` bounds the neighborhood complexity of every
graph satisfying the class predicate `C` by `c · k`: the class has linear
neighborhood complexity. -/
def HasLinearNeighborhoodComplexity
    (C : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      HasLinearNeighborhoodComplexityWithConstant G c

end Lax195003.WelzlOrdersNeighborhoodComplexity
