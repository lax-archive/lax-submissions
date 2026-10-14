import Lax195003.WelzlOrdersInGraphs
import Lax195003.WelzlOrdersComputation
import Lax195003.WelzlOrdersNeighborhoodComplexity
import Lax195003.WordRamRandomness
import Lax11.GraphEncoding
import Lax808846.Ram
import Mathlib.Data.Nat.Log

/-!
---
title: Refined near-linear computation of Welzl orders
type: theorem
---
For every graph with linear neighborhood complexity bounded by `c · k`,
where `c ≥ 2`, a randomized word-RAM algorithm computes an order whose
crossing number is at most a constant times
`c^5 (log₂ c)^2 log₂ n`. Its running time is linear in the encoded input
size times `log n`, and it succeeds with probability at least `2/3`.
For fixed `c`, the crossing bound is `O(log n)`.

# Formalization notes

The graph order and neighborhood-complexity predicates, the compressed-sparse-
row input encoding, and the finite-tape randomized word-RAM semantics are
imported from Lax195003 and its registered dependencies. The graph statement
uses the existing open-neighborhood convention. The paper's set-system result
implies this specialization because an undirected graph's open-neighborhood
system is self-dual.

The paper states expected running time. This statement uses a bounded-time
version: truncate an expected-time run at a sufficiently large constant
multiple of its expectation and return failure on timeout. Markov's inequality
then gives success on at least two thirds of finite tapes, with every tape
halting within the displayed bound. Repeating independent attempts until a
valid order is returned recovers expected near-linear time. The runtime
constant is existential. The displayed crossing bound uses the paper's
sampler parameter directly: `k` is rounded up as in Lemma 18, and the
reconstruction contributes at most `2k` per round.

More explicitly, Lemma 18 sets `s = ceil(64 log₂ c)` and
`k = ceil(768 c^5 (s + 1) log₂ c)`, while Theorem 20 bounds crossings by
`2k log₂ n`. Replacing each logarithm by its natural-number ceiling yields
the displayed bound, with the additive `1` accounting for rounding up `k`.

The program is existential and black-box at the concept level. Its concrete
instruction sequence and the bridges from the refined sampler to the machine
interface belong in the proof package.
-/

namespace Lax457868.RefinedWelzlOrders

open Lax11.GraphEncoding
open Lax808846.Ram
open Lax195003.WelzlOrdersInGraphs
open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax195003.WordRamRandomness

/-- A black-box word-RAM program achieves the refined crossing bound within
near-linear time, with constant success probability. -/
axiom exists_refined_randomized_welzlOrder_program :
      ∃ (p : Program) (Ktime : ℕ), 1 ≤ Ktime ∧
      ∀ (c n : ℕ) (G : SimpleGraph (Fin n)),
        2 ≤ c → 2 ≤ n →
        HasLinearNeighborhoodComplexityWithConstant G c →
        ∀ (w : ℕ) (x : List ℕ), EncodesGraph x n G →
          (∀ v ∈ c :: x, Ktime * (x.length + v + 1) ≤ 2 ^ w) →
          let T := Ktime * (x.length + 1) * (Nat.clog 2 n + 1)
          SucceedsWithProbabilityAtLeastInTime
            (2 / 3 : ℚ) w p (c :: x) T T
            (EncodesGraphWelzlOrder G 1
              (2 * (768 * c ^ 5 *
                (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1) *
                Nat.clog 2 n))

end Lax457868.RefinedWelzlOrders
