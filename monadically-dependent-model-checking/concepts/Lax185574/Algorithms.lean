import Lax185574.Encodings
import Lax808846.Ram
import Mathlib.Data.Real.Basic

/-!
---
title: Algorithms and their running times
type: definition
---
An *algorithm* is a program of the word RAM of `Lax808846.Ram`. It reads
the encoding of a value and writes the encoding of a value, in the
encodings of `Lax185574.Encoding`.

The word RAM computes with words of w bits. As usual, the word length
must grow logarithmically with the input, so that a word can hold an
address of the input and each number of the input. Each algorithm states
how much it needs: an exponent e such that it works with words of
e · log₂ (N + Σ) + O(1) bits on inputs of length N whose numbers sum to
Σ.

The algorithm A *computes* b from a *in time O(T)*, with the constant c,
if the following holds for the encoding x of a, of length N, whose
numbers sum to Σ. At every word length w with c · (N + Σ + 1)^e ≤ 2^w,

1. every run of A on x that halts outputs the encoding of b, and
2. if c · T + c ≤ 2^w, then A halts on x within c · T + c steps.

A word length w with c · (N + Σ + 1)^e ≤ 2^w is called *admissible* for
c on the input x.

The algorithm A *decides* a property P of a in time O(T) if it computes
the truth value of P in time O(T).

# Formalization notes

A statement about an algorithm has the form "there is an algorithm A
such that for all parameters there is a constant c such that for all
inputs a, A computes b from a in time O(T)". The program and the
exponent e come first, so neither depends on the parameters or on the
word length. The constant c is O-notation with explicit constants. It
bounds both the running time and the additive term of the word length.

The word length bound includes the numbers of the input, since the
machine reduces every number modulo 2^w, so a number that does not fit
into a word cannot be read. The sum of the numbers dominates each of
them and also covers the empty input.

The first clause is soundness at every word length of the hypothesis.
An algorithm that calls another one runs it at word lengths fixed by its
own memory, where the running time of the callee need not fit into a
word. It can trust any output it receives. The second clause claims
halting only once the time bound fits into a word, the usual word RAM
convention that a word holds the running time. This matters when the
output is large. Its size can be polynomial of a degree that grows with
parameters fixed after e, and then at some word lengths of the
hypothesis the output cannot be written. Since the machine is
deterministic, the two clauses together say that the run is correct
whenever it halts, and that it halts in time whenever the time fits.

The time bound is a real number, so that bounds like n^(3+ε) can be
written directly. The additive c lets T vanish on small inputs, as
O-notation does. Several outputs are computed as one pair.
-/

namespace Lax185574.Algorithms

open Lax808846.Ram Lax185574.Encoding

/-- An algorithm: a word RAM program, together with the exponent `e`
such that it needs words of `e · log₂ (N + Σ) + O(1)` bits on inputs of
length `N` whose numbers sum to `Σ`. -/
structure Algorithm where
  /-- The program. -/
  program : Program
  /-- The exponent of the word length the algorithm needs. -/
  wordExponent : ℕ

/-- `A.Computes c a b T`: the algorithm `A` computes `b` from `a` in time
`O(T)`, with the constant `c`. Let `x` be the encoding of `a`. At every
word length `w` with `c · (|x| + Σx + 1)^e ≤ 2^w`, where `Σx` is the sum
of the numbers of `x`,
1. every halting run of `A` on `x` outputs the encoding of `b`, and
2. if `c · T + c ≤ 2^w`, then `A` halts on `x` within `c · T + c` steps,
   with the encoding of `b` as output. -/
def Algorithm.Computes {α β : Type*} [Encode α] [Encode β]
    (A : Algorithm) (c : ℕ) (a : α) (b : β) (T : ℝ) : Prop :=
  ∀ w : ℕ, c * ((encode a).length + (encode a).sum + 1) ^ A.wordExponent ≤ 2 ^ w →
    (∀ y t, RunsTo w A.program (encode a) y t → y = encode b) ∧
    ((c : ℝ) * T + c ≤ 2 ^ w →
      ∃ t : ℕ, (t : ℝ) ≤ c * T + c ∧ RunsTo w A.program (encode a) (encode b) t)

open Classical in
/-- `A.Decides c a P T`: the algorithm `A` computes from `a` whether `P`
holds, writing `true` (encoded as `1`) or `false` (encoded as `0`), in
time `O(T)` with the constant `c`. -/
def Algorithm.Decides {α : Type*} [Encode α] (A : Algorithm) (c : ℕ) (a : α) (P : Prop)
    (T : ℝ) : Prop :=
  A.Computes c a (decide P) T

end Lax185574.Algorithms
