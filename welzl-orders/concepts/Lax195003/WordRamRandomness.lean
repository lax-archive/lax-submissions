import Lax67.Ram
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Card

/-!
---
title: Randomized computation on the word RAM
type: definition
---
A randomized word-RAM computation is a deterministic word-RAM program whose
ordinary input is followed by a finite tape of independent uniform random
bits. Given a rational threshold *q*, it succeeds with probability at least
*q* within time *T* if every random tape makes the program halt within *T*
steps, and at least a *q* fraction of the equally likely bit strings make it
halt with an accepted output.

# Formalization notes

The machine itself is exactly the word RAM of Lax67; randomness is input, not
a new primitive instruction. A random tape of length `r` is a function
`Fin r → Bool`, encoded in index order by the words zero and one. There are
exactly `2 ^ r` such tapes. For a rational success threshold `q`, the
inequality `q · 2^r ≤ |good tapes|` states the probability bound without
introducing a measure-theoretic representation of a finite experiment. The
Welzl-order theorem instantiates `q` with `2/3`.

The definition separates total running time from success: every tape must
halt within the bound, while a bad tape may return any output. The accepting
condition is a relation on output words because a search algorithm may return
any one of many correct witnesses. Supplying more bits than a program reads
does not alter the success fraction—each used prefix has equally many
extensions—so a theorem may use its time bound itself as a uniform tape
length without exposing an implementation-specific random-bit count.
-/

namespace Lax195003.WordRamRandomness

open Lax67.Ram

/-- A bit tape as a word list, in index order, with `false` encoded by zero
and `true` by one. -/
def bitTape {r : ℕ} (ρ : Fin r → Bool) : List ℕ :=
  List.ofFn (fun i : Fin r => if ρ i then 1 else 0)

/-- The program halts within `T` steps on every `r`-bit tape, and on at least
a `successProbability` fraction of those tapes its output satisfies `Accept`. -/
noncomputable def SucceedsWithProbabilityAtLeastInTime
    (successProbability : ℚ) (w : ℕ) (p : Program)
    (input : List ℕ) (r T : ℕ)
    (Accept : List ℕ → Prop) : Prop :=
  (∀ ρ : Fin r → Bool, ∃ y : List ℕ, ∃ t ≤ T,
      RunsTo w p (input ++ bitTape ρ) y t) ∧
    successProbability * (2 ^ r : ℚ) ≤
      ({ρ : Fin r → Bool | ∃ y : List ℕ, ∃ t ≤ T,
        RunsTo w p (input ++ bitTape ρ) y t ∧ Accept y}.ncard : ℚ)

end Lax195003.WordRamRandomness
