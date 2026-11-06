import Lax185574.DpMinimality
import Lax185574.Flips
import Lax185574.GraphBalls

/-!
---
title: Closure theorem for tuples
type: theorem
---
For every dp-minimal graph class 𝒞, radius r ∈ ℕ, and tuple size k ∈ ℕ,
there are some c, s ∈ ℕ with the following property.

For every G ∈ 𝒞 and finite set A ⊆ V(G) there is a set ℋ of
O_{𝒞,r,k}(|A|^c) many s-flips of G such that for every tuple
v̄ ∈ (V(G) ∖ A)^k there is a flip H ∈ ℋ with

dist^H(v̄, A) > r.

# Formalization notes

The bound O_{𝒞,r,k}(|A|^c) is spelled out as a · (|A| + 1)^c, with a
chosen together with c and s, after 𝒞, r and k. The set ℋ is a finite
set of graphs on the vertex set of G, each an s-flip, that is a 𝒫-flip
for a partition 𝒫 into at most s parts. The number of parts is the
cardinality of the quotient, which is finite as the graph is finite.
The flips need not be definable. The condition dist^H(v̄, A) > r, for
the minimum distance between the entries of v̄ and A, is stated as
disjointness of A from the ball of radius r around the entries of v̄.
The graphs of 𝒞 are finite, as in `ClosureTheorem`.
-/

namespace Lax185574.ClosureTheoremTuples

open Lax185574.Graphs Lax185574.DpMinimality
open Lax185574.Flips Lax185574.GraphBalls

/-- **Closure theorem for tuples.** For a dp-minimal class, a radius `r`
and a tuple size `k`, every finite parameter set `A` has a
polynomial-size family of `s`-flips such that each `k`-tuple outside `A`
is at distance more than `r` from `A` in some member. -/
axiom closure_theorem_tuples (C : GraphClass) (hC : DpMinimal C)
    (r k : ℕ) :
    ∃ c s a : ℕ, ∀ G ∈ C, ∀ A : Finset (Fin G.n),
      ∃ family : Finset (SimpleGraph (Fin G.n)),
        family.card ≤ a * (A.card + 1) ^ c ∧
        (∀ H ∈ family, ∃ P : Setoid (Fin G.n),
          Nat.card (Quotient P) ≤ s ∧ IsFlip G.toSimpleGraph P H) ∧
        ∀ v : Fin k → Fin G.n, (∀ i, v i ∉ A) →
          ∃ H ∈ family, Disjoint (graphBall H r (Set.range v)) (A : Set (Fin G.n))

end Lax185574.ClosureTheoremTuples
