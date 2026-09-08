import Lax12.NeighborhoodComplexity
import Mathlib.Data.Nat.Lattice

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

The count of distinct traces is the endorsed
`Lax12.NeighborhoodComplexity.traceCount`; only the maximum over vertex sets
and the genuinely linear graph and class bounds are introduced here. This is
deliberately different from Lax12's class-level `HasAlmostLinearNC`, whose
bound permits an exponent `1 + ε` and a constant depending on `ε`.

The paper defines the maximum over sets of size at most `k`. On the finite
carrier `Fin n`, the natural supremum below is that maximum. The bound is
required only for positive `k`: at `k = 0`, the empty vertex set has the one
trace `∅`, so the literal inequality `π_G(0) ≤ c · 0` would be false.
-/

namespace Lax195003.WelzlOrdersNeighborhoodComplexity

open Lax12.GraphClasses
open Lax12.NeighborhoodComplexity

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
graph in the class by `c · k`: the class has linear neighborhood complexity. -/
def HasLinearNeighborhoodComplexity (C : GraphClass) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      HasLinearNeighborhoodComplexityWithConstant G c

end Lax195003.WelzlOrdersNeighborhoodComplexity
