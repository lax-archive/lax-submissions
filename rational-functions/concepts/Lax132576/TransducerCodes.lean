import Mathlib.Computability.Halting
import Lax132576.RationalRelations

/-!
---
title: Codes of automata with output, and decidability under a promise
type: definition
---
The decidability statements of the book are about algorithms whose inputs are
automata. An automaton with output whose states and letters are natural numbers
is described by a finite *code*: the list of its transitions $(p, u, v, q)$ —
from state $p$ to state $q$, reading $u$ and writing $v$ — and the lists of its
initial and final states. A code mentions only finitely many letters, its
*alphabet*; a string over that alphabet is a *code word*. A code is
*functional* if the relation it describes is a total function on the code words:
every code word has exactly one output.

A problem "given an automaton satisfying a promise, decide whether it has a
property" is decidable if there is a computable Boolean-valued function on
codes that answers correctly on every code satisfying the promise. This is the
form of Theorems B.3.4, B.4.2 and Lemma B.4.3 (and of Theorem C.1.4 in Part C).

# Formalization notes

`RelCode` is a structure with the three lists as named fields; it is
`Primcodable` through the evident bijection with a tuple, so that
computability of functions on codes is mathlib's `Computable`. `codeAut c` is
the automaton with output over the alphabet `ℕ` that the code describes, and
`codeRel c` its relation. Totality over *all* of `ℕ*` cannot be asked for — a
code reads only the letters of its alphabet, so no code describes a total
function on `ℕ*` — which is why the promise `CodeFunctional` and the decided
properties are relativised to the code words; `DecidableUnderPromise promise P`
is the existence of a computable decision procedure correct under the promise.
-/

namespace Lax132576.TransducerCodes

open Lax132576.LabelledAutomata Lax132576.RationalRelations

/-- A code of an automaton with output over the alphabet `ℕ` with states in `ℕ`:
its transitions `(p, u, v, q)` and its initial and final states. -/
structure RelCode where
  /-- The transitions `(p, u, v, q)`: from `p` to `q`, reading `u`, writing `v`. -/
  transitions : List (ℕ × List ℕ × List ℕ × ℕ)
  /-- The initial states. -/
  init : List ℕ
  /-- The final states. -/
  final : List ℕ

/-- A code is the tuple of its three lists. -/
def relCodeEquiv : RelCode ≃ List (ℕ × List ℕ × List ℕ × ℕ) × List ℕ × List ℕ where
  toFun c := (c.transitions, c.init, c.final)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv := by rintro ⟨t, i, f⟩; rfl
  right_inv := by rintro ⟨t, i, f⟩; rfl

instance : Primcodable RelCode := Primcodable.ofEquiv _ relCodeEquiv

/-- The automaton with output described by a code. -/
def codeAut (c : RelCode) : NFAO ℕ ℕ ℕ where
  init := {q | q ∈ c.init}
  final := {q | q ∈ c.final}
  δ := {t | t ∈ c.transitions}
  δ_finite := c.transitions.finite_toSet

/-- The rational relation described by a code. -/
def codeRel (c : RelCode) : List ℕ → List ℕ → Prop := (codeAut c).rel

/-- The alphabet of a code: the letters occurring in the input strings of its
transitions. -/
def codeAlphabet (c : RelCode) : List ℕ := c.transitions.flatMap (fun t => t.2.1)

/-- A string over the alphabet of the code. -/
def CodeWord (c : RelCode) (w : List ℕ) : Prop := ∀ x ∈ w, x ∈ codeAlphabet c

/-- The relation described by the code is a total function on the code words. -/
def CodeFunctional (c : RelCode) : Prop := ∀ w, CodeWord c w → ∃! v, codeRel c w v

/-- A property `P` is decidable under a promise if a computable Boolean-valued
function answers `P` correctly on every input satisfying the promise. -/
def DecidableUnderPromise {α : Type} [Primcodable α] (promise P : α → Prop) : Prop :=
  ∃ D : α → Bool, Computable D ∧ ∀ a, promise a → (D a = true ↔ P a)

end Lax132576.TransducerCodes
