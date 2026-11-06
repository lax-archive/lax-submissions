import Lax185574.AtomicTypes
import Lax185574.DefinableFlips
import Lax185574.DpMinimality
import Lax185574.GraphBalls

/-!
---
title: Few atomic types in balls avoiding a closure
type: lemma
---
For every dp-minimal graph class 𝒞 and r, s ∈ ℕ, there are some
k, t ∈ ℕ with the following property. For every G ∈ 𝒞 and finite
set A ⊆ V(G), there is A* ⊇ A of size O_{𝒞,r,s}(|A|^k) such that, for
every s-definable flip H of G and every vertex v,

Ball^H_r[v] ∩ A* = ∅  ⟹  |ATypes^H(Ball^H_r[v]/A)| ≤ t.

Equivalently, Ball^H_r[v] intersects at most t parts of the partition of
V(H) into atomic types over A in H.

# Formalization notes

The bound O_{𝒞,r,s}(|A|^k) is spelled out as a · (|A| + 1)^k, with a
chosen together with k and t, after 𝒞, r and s. The set A* is chosen
before the flip H and the vertex v. The atomic types are taken in the
flip H, as in the paper. The parameter bound s is an input of the lemma,
not an output. The graphs of 𝒞 are finite, as in `ClosureTheorem`.
-/

namespace Lax185574.BallTypes

open Lax185574.Graphs Lax185574.DpMinimality
open Lax185574.AtomicTypes Lax185574.DefinableFlips Lax185574.GraphBalls

/-- **Few types in balls.** Every finite set `A` has a polynomial-size
superset `A*` such that, in every `s`-definable flip `H`, each ball of
radius `r` that avoids `A*` realizes at most `t` atomic types over `A`
in `H`. -/
axiom ball_types (C : GraphClass) (hC : DpMinimal C) (r s : ℕ) :
    ∃ k t a : ℕ, ∀ G ∈ C, ∀ A : Finset (Fin G.n), ∃ Astar ⊇ A,
      Astar.card ≤ a * (A.card + 1) ^ k ∧
      ∀ H : SimpleGraph (Fin G.n), IsDefinableFlip G.toSimpleGraph s H → ∀ v : Fin G.n,
        Disjoint (graphBall H r {v}) (Astar : Set (Fin G.n)) →
          atomicTypeCount H (graphBall H r {v}) (A : Set (Fin G.n)) ≤ t

end Lax185574.BallTypes
