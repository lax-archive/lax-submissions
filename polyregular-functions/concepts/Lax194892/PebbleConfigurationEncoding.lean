import Lax194892.PebbleTransducers

/-!
---
title: String representations of pebble configurations, and balanced runs
type: definition
---
Section D.2 of *Transducers* represents a configuration of a $k$-pebble
transducer on an input $w$ — a state and a stack of at most $k$ gaps of $w$ — as
a string with one letter per gap of $w$, the letter of a gap recording the
state, the input letter that follows the gap and the set of pebbles sitting in
the gap; the results on reachability speak about a *pair* of configurations at
a time, encoded together. A run between two configurations of height $\ell$ is
*balanced* if the pebble at height $\ell$ is never popped during it, although
it may be moved.

# Formalization notes

`pairEnc q₁ q₂ sts stt w` has `w.length + 1` letters, the last one being the
only one with no following input letter; `ann k st p` is the set of pebbles of
the stack `st` sitting in the gap `p`. `RestrReaches M w ℓ` is reachability
along runs all of whose configurations have height at least `ℓ`; with `ℓ = 0` it
is ordinary reachability, and for endpoints of height `ℓ` it is the book's
balanced run.
-/

namespace Lax194892.PebbleConfigurationEncoding

open Lax194892.PebbleTransducers

/-- Reachability along runs whose configurations all have height at least `ℓ`:
the topmost `ℓ` pebbles are never popped. -/
inductive RestrReaches {A B Q : Type} {k : ℕ} (M : Pebble A B Q k) (w : List A) (ℓ : ℕ) :
    PebbleCfg Q → PebbleCfg Q → Prop
  /-- The empty run. -/
  | refl (q : Q) (st : List ℕ) (h : ℓ ≤ st.length) :
      RestrReaches M w ℓ (PebbleCfg.conf q st) (PebbleCfg.conf q st)
  /-- One step from a configuration of height at least `ℓ`. -/
  | step {q : Q} {st : List ℕ} {c' c'' : PebbleCfg Q} {o : List B} (h : ℓ ≤ st.length)
      (hs : M.stepCfg w (PebbleCfg.conf q st) = some (o, c'))
      (hr : RestrReaches M w ℓ c' c'') :
      RestrReaches M w ℓ (PebbleCfg.conf q st) c''

/-- A balanced run between two configurations of height `ℓ`: the pebble at
height `ℓ` is never popped. -/
def BalancedRun {A B Q : Type} {k : ℕ} (M : Pebble A B Q k) (w : List A) (ℓ : ℕ)
    (c c' : PebbleCfg Q) : Prop :=
  RestrReaches M w ℓ c c'

/-- The pebbles of the stack `st` sitting in the gap `p`. -/
def ann (k : ℕ) (st : List ℕ) (p : ℕ) : Fin k → Bool := fun i => decide (st[(i : ℕ)]? = some p)

/-- A letter of the representation of a pair of configurations: the two states, the
input letter following the gap, and the pebbles of each configuration in the gap. -/
abbrev PairLetter (A Q : Type) (k : ℕ) := Q × Q × Option A × (Fin k → Bool) × (Fin k → Bool)

/-- The string representation of the pair of configurations `(q₁, sts)` and
`(q₂, stt)` of the input `w`: one letter per gap. -/
def pairEnc {A Q : Type} {k : ℕ} (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A) :
    List (PairLetter A Q k) :=
  (List.range (w.length + 1)).map fun p => (q₁, q₂, w[p]?, ann k sts p, ann k stt p)

end Lax194892.PebbleConfigurationEncoding
