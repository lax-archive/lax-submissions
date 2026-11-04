import Lax185574.PairRelation
import Lax185574.Flips
import Lax185574.GraphBalls

/-!
---
title: Balls of the pair relation lie in flip-metric balls
type: lemma
---
Fix a graph G and a partition 𝒫 of V(G), and let R ≔ R(G, 𝒫). For every
radius r ∈ ℕ and vertex v ∈ V(G),

Ball^R_r(v) ⊆ Ball^𝒫_{5r}(v).

# Formalization notes

Ball^R_r(v) is the ball in the graph R, `GraphBalls.graphBall`, around
the single vertex v. Ball^𝒫_{5r}(v) is the ball of the 𝒫-flip metric,
`Flips.flipBall`.
-/

namespace Lax185574.PairRelationBalls

open Lax185574.PairRelation Lax185574.Flips Lax185574.GraphBalls

universe z

/-- **Ball containment.** A radius-`r` ball of `R(G, 𝒫)` lies in the
radius-`5r` ball of the `𝒫`-flip metric. -/
axiom graphBall_pairRelation_subset {V : Type z} (G : SimpleGraph V) (P : Setoid V)
    (r : ℕ) (v : V) :
    graphBall (pairRelation G P) r {v} ⊆ flipBall G P (5 * r) v

end Lax185574.PairRelationBalls
