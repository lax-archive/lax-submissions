import Mathlib.Computability.Halting
import Mathlib.Data.Rat.Defs
import Lax132576.WeightedAutomata

/-!
---
title: Codes of weighted automata over the rationals
type: definition
---
The decision problems of Section B.3 of *Transducers* — equivalence and
zeroness of weighted automata over the field of rationals — are about
algorithms whose inputs are weighted automata. A weighted automaton over
$\mathbb{Q}$ with states and letters in $\mathbb{N}$ is described by a finite
*code*: its transitions $(p, u, (a, b), q)$, from $p$ to $q$, reading $u$, with
weight $a / b$ given by an integer and a natural number, and its lists of
initial and final states. A code is *valid* if the automaton it describes is a
genuine weighted automaton, i.e. every input string has finitely many accepting
runs; validity is the promise under which the decision procedures of Theorems
B.3.3 and B.3.7 are correct.

# Formalization notes

`WCode` is a structure with the three lists as named fields and is
`Primcodable` through the evident bijection with a tuple. The weight of a coded
transition is the rational number `a / b`; a zero denominator gives the weight
`0`, as division by zero does in mathlib.
-/

namespace Lax132576.WeightedCodes

open Lax132576.LabelledAutomata Lax132576.WeightedAutomata

/-- A code of a weighted automaton over `ℚ`: transitions `(p, u, (a, b), q)` from
`p` to `q` reading `u` with weight `a / b`, and the initial and final states. -/
structure WCode where
  /-- The transitions `(p, u, (a, b), q)`. -/
  transitions : List (ℕ × List ℕ × (ℤ × ℕ) × ℕ)
  /-- The initial states. -/
  init : List ℕ
  /-- The final states. -/
  final : List ℕ

/-- A code is the tuple of its three lists. -/
def wcodeEquiv : WCode ≃ List (ℕ × List ℕ × (ℤ × ℕ) × ℕ) × List ℕ × List ℕ where
  toFun c := (c.transitions, c.init, c.final)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv := by rintro ⟨t, i, f⟩; rfl
  right_inv := by rintro ⟨t, i, f⟩; rfl

instance : Primcodable WCode := Primcodable.ofEquiv _ wcodeEquiv

/-- The weighted automaton over `ℚ` described by a code. -/
def wcodeAut (c : WCode) : LabAut ℕ ℚ ℕ where
  init := {q | q ∈ c.init}
  final := {q | q ∈ c.final}
  δ := {t | ∃ s ∈ c.transitions, t = (s.1, s.2.1, (s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ), s.2.2.2)}
  δ_finite := Set.Finite.ofFinset
    (c.transitions.toFinset.image
      (fun s => (s.1, s.2.1, (s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ), s.2.2.2)))
    (by intro t; simp [eq_comm])

/-- The function computed by the weighted automaton described by a code. -/
noncomputable def wcodeEval (c : WCode) : List ℕ → ℚ := wEval (wcodeAut c)

/-- A code is valid if it describes a genuine weighted automaton: every input has
finitely many accepting runs. -/
def WCodeValid (c : WCode) : Prop := FinitelyManyRuns (wcodeAut c)

end Lax132576.WeightedCodes
