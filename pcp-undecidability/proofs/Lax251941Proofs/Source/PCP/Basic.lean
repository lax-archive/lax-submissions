/-
# The Post Correspondence Problem: basic definitions

Following Sipser, *Introduction to the Theory of Computation* (3rd ed.), Section 5.2.

An instance of the Post Correspondence Problem (PCP) is a finite collection of *dominos*
`[t/b]`, each carrying a top string `t` and a bottom string `b` over some alphabet.
A *match* is a nonempty sequence of dominos from the collection (repetitions allowed)
such that reading off the top strings gives the same string as reading off the bottom
strings.
-/
import Mathlib

namespace Lax251941Proofs.PCP

variable {α : Type*}

/-- A domino: a pair consisting of a top string and a bottom string. -/
abbrev Domino (α : Type*) := List α × List α

/-- An instance of the Post Correspondence Problem: a finite list of dominos. -/
abbrev Inst (α : Type*) := List (Domino α)

/-- The string obtained by reading off the top strings of a sequence of dominos. -/
def topStr (s : List (Domino α)) : List α := (s.map Prod.fst).flatten

/-- The string obtained by reading off the bottom strings of a sequence of dominos. -/
def botStr (s : List (Domino α)) : List α := (s.map Prod.snd).flatten

@[simp] lemma topStr_nil : topStr ([] : List (Domino α)) = [] := rfl
@[simp] lemma botStr_nil : botStr ([] : List (Domino α)) = [] := rfl

@[simp] lemma topStr_cons (d : Domino α) (s : List (Domino α)) :
    topStr (d :: s) = d.1 ++ topStr s := rfl

@[simp] lemma botStr_cons (d : Domino α) (s : List (Domino α)) :
    botStr (d :: s) = d.2 ++ botStr s := rfl

@[simp] lemma topStr_append (s s' : List (Domino α)) :
    topStr (s ++ s') = topStr s ++ topStr s' := by
  simp [topStr]

@[simp] lemma botStr_append (s s' : List (Domino α)) :
    botStr (s ++ s') = botStr s ++ botStr s' := by
  simp [botStr]

/-- `IsMatch P s` says that the nonempty sequence of dominos `s`, all taken from the
instance `P`, is a match: the top string equals the bottom string. -/
def IsMatch (P : Inst α) (s : List (Domino α)) : Prop :=
  s ≠ [] ∧ (∀ d ∈ s, d ∈ P) ∧ topStr s = botStr s

/-- `HasMatch P`: the PCP instance `P` has a match.  This is the predicate defining the
language `PCP` of Sipser, Section 5.2. -/
def HasMatch (P : Inst α) : Prop := ∃ s, IsMatch P s

/-- `HasMatchFirst P`: the instance `P` has a match that starts with its first domino.
This is the predicate defining the language `MPCP` (the Modified Post Correspondence
Problem) of Sipser, Section 5.2. -/
def HasMatchFirst (P : Inst α) : Prop :=
  ∃ d rest, P = d :: rest ∧ ∃ s, (∀ e ∈ s, e ∈ P) ∧ topStr (d :: s) = botStr (d :: s)

end Lax251941Proofs.PCP
