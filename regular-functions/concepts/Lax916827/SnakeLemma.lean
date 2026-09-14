import Lax916827.RegularFunctions
import Lax916827.SnakeGraphs

/-!
---
title: The snake lemma: the output of a snake graph is a regular function
type: theorem
---
Let $C$ be the alphabet representing snake graphs with states $Q$ and output
alphabet $B$. For every $k$, the function mapping a string $w \in C^*$ to the
output of the snake graph it represents, if it represents a snake graph of width
at most $k$, and to $\varepsilon$ otherwise, is regular (Lemma C.2.12 of
*Transducers*, the book's *snake lemma*). The proof is an induction on the
width: a snake of width $k$ visits the *record-breaking* columns, the ones it
reaches for the first time further right than ever before; between two
consecutive record-breakers the snake consists of a *looping part* and a
*progress part*, both of width below $k$, whose outputs are given by the
induction hypothesis on factors cut out by rational functions, and the closure
properties of Lemma C.2.10 glue them together.

# Formalization notes

The function is `snakeOut k` of `SnakeGraphs`. The lemma is stated for every
`k`, not only for `k ∈ {1, …, |Q|}`, which is more general and costs nothing:
a column has at most `|Q|` vertices. The state set and the output alphabet are
assumed finite, so that the alphabet `C` is finite. The formal proof carries out
the induction for the width-`k` output function of an arbitrary two-way
transducer and reads the snake letters through the transducer that walks along a
snake graph.
-/

namespace Lax916827.SnakeLemma

open Lax916827.RegularFunctions Lax916827.SnakeGraphs

/-- The output of a snake graph of width at most `k`, read off its string
representation, is a regular function. -/
axiom isRegularFun_snakeOut {Q B : Type} [Finite Q] [Finite B] (k : ℕ) :
    IsRegularFun (snakeOut (Q := Q) (B := B) k)

end Lax916827.SnakeLemma
