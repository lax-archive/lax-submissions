import Lax195003.WordRamRandomness
import Lax195003.WelzlOrdersInGraphs
import Lax195003.WelzlOrdersNeighborhoodComplexity
import Lax11.GraphEncoding
import Mathlib.Data.Nat.Log

/-!
---
title: Near-linear-time computation of Welzl orders
type: theorem
---
Let *G* be an *n*-vertex graph whose neighborhoods leave at most
*c* · |*A*| distinct traces on every nonempty vertex set *A*, for some
*c* ≥ 1. There is a randomized algorithm which, given *G* and *c*, runs in
`O((n+m) log n)` time and, with probability at least 2/3, returns a total
order of the vertices with crossing number at most 12*c*² log² *n*.

This is Theorem 1.3 of Dreier and Kuske, *Near-Linear Time Computation of
Welzl Orders on Graphs with Linear Neighborhood Complexity* (2026).

# Formalization notes

Linear neighborhood complexity is the separate definition
`Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexity`
in this submission, together with the per-graph predicate used below. They
define the graph's shatter function from the endorsed neighborhood trace count
of *Sparsity Lectures* (Lax12), and require the genuinely linear bound
`π_G(k) ≤ c · k`; they are not Lax12's almost-linear class predicate. The graph
is presented by the compressed sparse row encoding of Lax11, and the program
runs on the registered word RAM of Lax67 through this submission's
finite-randomness predicate.

The program and the constant `K` precede the graph, the linearity constant,
the input word and the word length, so one uniform program realizes the whole
algorithm. Its input is `c :: x` followed by the random tape. The time bound
`K · (|x|+1) · (⌈log₂ n⌉+1)` is an elementary form of
`O((n+m) log n)`: a compressed sparse row word has length `3+n+2m`, up to
any repetitions present in the representation. The added ones make the bound
meaningful for the empty and one-vertex graphs and change it only by a
constant factor.

The paper writes a real-valued base-two logarithm. Its use in the natural
crossing and time bounds is read as `Nat.clog 2 n`, the ceiling binary
logarithm; this rounds the displayed upper bound upward rather than silently
strengthening it at non-powers of two.

The word-length condition says that the input, every value in it, and a
linear amount of working memory fit into a word-addressed machine. It follows
the convention of Lax11's algorithmic statements and is separate from the
running-time bound. The random tape has the same length as the time bound;
unused trailing bits do not affect its uniform success probability.

The output is relational rather than a preselected function of the graph:
any encoded vertex order meeting the paper's explicit crossing bound for the
open radius-one neighborhood system is a successful output. Radius one is the
ordinary open-neighborhood specialization of the general `k`-neighborhood
Welzl-order definition in `Lax195003.WelzlOrdersInGraphs`. Thus the statement
preserves the mathematical content of a randomized search algorithm without
imposing an arbitrary tie-breaking rule absent from the paper.
-/

namespace Lax195003.WelzlOrdersComputation

open Lax11.GraphEncoding
open Lax67.Ram
open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax195003.WordRamRandomness Lax195003.WelzlOrdersInGraphs

/-- **Near-linear computation of graph Welzl orders** (Dreier–Kuske,
Theorem 1.3): one randomized word-RAM program, given a graph with neighborhood
complexity at most `c · k`, returns with probability at least `2/3` an order
with crossing number at most `12 · c^2 · log₂(n)^2`, within a constant
multiple of `(n+m) log n` steps. -/
axiom exists_nearLinearTime_randomized_welzlOrder_program :
    ∃ (p : Program) (K : ℕ), 1 ≤ K ∧
      ∀ (c n : ℕ) (G : SimpleGraph (Fin n)), 1 ≤ c →
        HasLinearNeighborhoodComplexityWithConstant G c →
        ∀ (w : ℕ) (x : List ℕ), EncodesGraph x n G →
          (∀ v ∈ c :: x, K * (x.length + v + 1) ≤ 2 ^ w) →
          let T := K * (x.length + 1) * (Nat.clog 2 n + 1)
          SucceedsWithProbabilityAtLeastInTime
            (2 / 3 : ℚ) w p (c :: x) T T
            (EncodesGraphWelzlOrder G
              1
              (12 * c ^ 2 * (Nat.clog 2 n) ^ 2))

end Lax195003.WelzlOrdersComputation
