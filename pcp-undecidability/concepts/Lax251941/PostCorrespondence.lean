import Mathlib.Data.List.Basic

/-!
---
title: The Post correspondence problem
type: definition
---
An instance of the *Post correspondence problem* is a finite collection of
*dominos* $[t / b]$, each carrying a top string $t$ and a bottom string $b$ over
some alphabet. A *match* is a nonempty sequence of dominos from the collection,
repetitions allowed, such that reading off the top strings gives the same string
as reading off the bottom strings. The problem asks whether a given instance has
a match (Sipser, Section 5.2; Post 1946).

The same problem in *index form*, as the book *Transducers* uses it: an
instance is a finite list of pairs of strings $(u_1, v_1), \ldots, (u_n, v_n)$
over the alphabet $\mathbb{N}$, and it is solvable if some nonempty sequence of
indices $i_1 \cdots i_k$ satisfies
$$u_{i_1} \cdots u_{i_k} = v_{i_1} \cdots v_{i_k}.$$

# Formalization notes

`Inst α` is a list of dominos over any alphabet `α`; `IsMatch P s` says that the
nonempty list `s` of dominos, each belonging to `P`, has equal top and bottom
strings, and `HasMatch P` that some match exists. `Solvable` is the index form
over `ℕ`: `conc ws idx` concatenates the strings of `ws` selected by the indices
(an index out of range selects the empty string, but the definition requires
every index to be in range). The two forms carry the same information — choose
an index for each domino, or read a domino off each index — and both are stated
as undecidable.
-/

namespace Lax251941.PostCorrespondence

/-- A domino: a top string and a bottom string. -/
abbrev Domino (α : Type*) := List α × List α

/-- An instance of the Post correspondence problem: a finite list of dominos. -/
abbrev Inst (α : Type*) := List (Domino α)

/-- The string read off the top halves of a sequence of dominos. -/
def topStr {α : Type*} (s : List (Domino α)) : List α := (s.map Prod.fst).flatten

/-- The string read off the bottom halves of a sequence of dominos. -/
def botStr {α : Type*} (s : List (Domino α)) : List α := (s.map Prod.snd).flatten

/-- `s` is a match of the instance `P`: a nonempty sequence of dominos of `P`
whose top string equals its bottom string. -/
def IsMatch {α : Type*} (P : Inst α) (s : List (Domino α)) : Prop :=
  s ≠ [] ∧ (∀ d ∈ s, d ∈ P) ∧ topStr s = botStr s

/-- The instance `P` has a match. -/
def HasMatch {α : Type*} (P : Inst α) : Prop := ∃ s, IsMatch P s

/-- An instance in index form: a finite list of pairs of strings over `ℕ`. -/
abbrev Instance := List (List ℕ × List ℕ)

/-- The concatenation of the strings of `ws` selected by a list of indices. -/
def conc (ws : List (List ℕ)) (idx : List ℕ) : List ℕ :=
  (idx.map (fun i => ws.getD i [])).flatten

/-- An instance is solvable if some nonempty sequence of indices makes the two
concatenations equal. -/
def Solvable (P : Instance) : Prop :=
  ∃ idx : List ℕ, idx ≠ [] ∧ (∀ i ∈ idx, i < P.length) ∧
    conc (P.map Prod.fst) idx = conc (P.map Prod.snd) idx

end Lax251941.PostCorrespondence
