import Lax185574.Flips
import Lax185574.GraphBalls
import Lax185574.Partitions
import Lax185574.MonadicDependence

/-!
---
title: Closure theorem
type: theorem
---
For every monadically dependent graph class 𝒞 and radius r ∈ ℕ there are
some c, s ∈ ℕ with the following property.

For every G ∈ 𝒞 and finite set A ⊆ V(G) there is a set A* ⊆ V(G) of size
O_{𝒞,r}(|A|^c) such that for every vertex v ∉ A there is a set
S(v) ⊆ A* of size at most s and an S(v)-definable flip H with

dist^H(v, A) > r.

# Formalization notes

The bound O_{𝒞,r}(|A|^c) is spelled out as a · (|A| + 1)^c, with a
chosen together with c and s, after 𝒞 and r. Since c is existentially
quantified, this is equivalent to the paper's a·|A|^c + b. An
S(v)-definable flip is an S(v)-flip, that is a flip for the partition
`Partitions.atomicTypes` of G into atomic types over S(v). These are
the flips G ⊕ (p̄, R) for the tuples p̄ listing S(v). The condition
dist^H(v, A) > r is stated as Ball^H_r[v] ∩ A = ∅.

The set A* need not contain A, as in the paper. The paper proves the
theorem for finite or infinite graphs. Here 𝒞 is a `GraphClass`, so its
members are finite, which is the case used in the model-checking
theorem. Monadic dependence is that of `Lax185574.MonadicDependence`,
by transductions, as in the paper.
-/

namespace Lax185574.ClosureTheorem

open Lax185574.Graphs Lax185574.MonadicDependence
open Lax185574.Flips Lax185574.GraphBalls Lax185574.Partitions

/-- **Closure theorem.** For a monadically dependent class and a radius
`r`, every finite parameter set `A` has a polynomial-size closure `A*`
such that each vertex outside `A` is separated from `A` at distance more
than `r` by a flip over at most `s` vertices of `A*`. -/
axiom closure_theorem (C : GraphClass) (hC : MonadicallyDependent C) (r : ℕ) :
    ∃ c s a : ℕ, ∀ G ∈ C, ∀ A : Finset (Fin G.n), ∃ Astar : Finset (Fin G.n),
      Astar.card ≤ a * (A.card + 1) ^ c ∧
      ∀ v ∉ A, ∃ S ⊆ Astar, S.card ≤ s ∧ ∃ H : SimpleGraph (Fin G.n),
        IsFlip G.toSimpleGraph (atomicTypes G.toSimpleGraph (S : Set (Fin G.n))) H ∧
        Disjoint (graphBall H r {v}) (A : Set (Fin G.n))

end Lax185574.ClosureTheorem
