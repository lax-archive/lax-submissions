import Lax185574.AtomicTypes
import Lax185574.DefinableFlips
import Lax185574.GraphBalls
import Lax185574.VCDimension

/-!
---
title: A definable flip separating a ball one step further
type: lemma
---
For all d, t ∈ ℕ, there is some z ∈ ℕ with the following property.

For every graph G of VC-dimension at most d, radius r ∈ ℕ, finite set
A ⊆ V(G), and arbitrary set C ⊆ V(G) satisfying

Ball^G_r[C] ∩ A = ∅  and  |ATypes^G(Ball^G_r[C]/A)| ≤ t,

there exists a z-definable flip H of G in which Ball^H_{r+1}[C] ∩ A = ∅.

# Formalization notes

The number z is chosen after d and t and before the graph and the
radius, so it does not depend on r. The graph is finite, so A is finite.
The paper also allows infinite graphs with A finite. The lemma is
applied in the proof of the closure theorem to flips of graphs of a
graph class, which are finite. The atomic types are taken in G.
-/

namespace Lax185574.BallFlip

open Lax185574.AtomicTypes Lax185574.DefinableFlips Lax185574.GraphBalls
open Lax185574.VCDimension

universe u

/-- **Ball flip.** If a ball of radius `r` around `C` avoids `A` and
realizes at most `t` atomic types over `A`, then a `z(d, t)`-definable
flip moves `A` out of the ball of radius `r + 1` around `C`. -/
axiom exists_ball_flip (d t : ℕ) :
    ∃ z : ℕ, ∀ (V : Type u) [Finite V] (G : SimpleGraph V), vcDim G ≤ d →
      ∀ (r : ℕ) (A C : Set V), Disjoint (graphBall G r C) A →
        atomicTypeCount G (graphBall G r C) A ≤ t →
        ∃ H : SimpleGraph V, IsDefinableFlip G z H ∧
          Disjoint (graphBall H (r + 1) C) A

end Lax185574.BallFlip
