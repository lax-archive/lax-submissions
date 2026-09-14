import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Basic

/-!
---
title: Monadic second-order logic on strings
type: definition
---
A string $w \in A^*$ is a structure whose universe is the set of positions of
$w$, with the order $x \le y$ on positions and, for every letter $a \in A$, the
unary predicate $a(x)$ "position $x$ carries the letter $a$". *Monadic
second-order logic* (mso) has first-order variables ranging over positions and
second-order variables ranging over sets of positions, the atomic formulas
$x \le y$, $a(x)$ and $x \in X$, Boolean connectives, and existential
quantification over both kinds of variables (Section C.4.1 of *Transducers*).
A sentence — a formula without free variables — *defines* the language of the
strings that satisfy it; the *first-order fragment* is the set of formulas that
use neither set variables nor membership. A formula with free variables is
evaluated on a string together with a valuation, which the book represents by
*annotating* the string: the string $w \otimes \{x_1\} \otimes \cdots \otimes X_\ell$
over the alphabet $A \times 2^{k + \ell}$ carries at every position the bits
saying which of the variables point to it.

# Formalization notes

Variables of both kinds are named by natural numbers, and a valuation is a pair
of functions `ℕ → ℕ` (positions of the first-order variables) and `ℕ → Set ℕ`
(sets of positions of the second-order variables); quantifiers range over
positions `p < w.length` and subsets of them. Satisfaction, the first-order
fragment, the quantifier rank and the free variables of a formula are defined
by recursion on the syntax; `MSODefinable L` asks for a formula satisfied by
exactly the strings of `L` under every valuation, which for a sentence is the
usual notion and for a formula with free variables is the same as for its
universal closure. `annotate k l w fo so` is the annotated string of a valuation
of the variables `0, …, k-1` and `0, …, l-1`, and `extFO`/`extSO` extend such a
valuation to all variables. Alphabets are arbitrary types; finiteness is a
hypothesis of the theorems.
-/

namespace Lax314295.MSOLogic

/-- Formulas of monadic second-order logic over strings with letters in `A`;
first-order and second-order variables are named by natural numbers. -/
inductive MSO (A : Type) : Type
  /-- The order test `x_i ≤ x_j`. -/
  | le : ℕ → ℕ → MSO A
  /-- The label test `a (x_i)`. -/
  | lab : A → ℕ → MSO A
  /-- The membership test `x_i ∈ X_j`. -/
  | mem : ℕ → ℕ → MSO A
  /-- Negation. -/
  | not : MSO A → MSO A
  /-- Conjunction. -/
  | and : MSO A → MSO A → MSO A
  /-- Disjunction. -/
  | or : MSO A → MSO A → MSO A
  /-- First-order existential quantification `∃ x_i`. -/
  | exFO : ℕ → MSO A → MSO A
  /-- Second-order existential quantification `∃ X_i`. -/
  | exSO : ℕ → MSO A → MSO A

namespace MSO

variable {A : Type}

/-- Satisfaction of a formula in a string under a valuation of the first-order
variables by positions and of the second-order variables by sets of positions. -/
def Sat (w : List A) : (ℕ → ℕ) → (ℕ → Set ℕ) → MSO A → Prop
  | fo, _, le i j => fo i ≤ fo j
  | fo, _, lab a i => w[fo i]? = some a
  | fo, so, mem i j => fo i ∈ so j
  | fo, so, not φ => ¬ Sat w fo so φ
  | fo, so, and φ ψ => Sat w fo so φ ∧ Sat w fo so ψ
  | fo, so, or φ ψ => Sat w fo so φ ∨ Sat w fo so ψ
  | fo, so, exFO i φ => ∃ p < w.length, Sat w (Function.update fo i p) so φ
  | fo, so, exSO i φ => ∃ S ⊆ {p | p < w.length}, Sat w fo (Function.update so i S) φ

/-- A formula is first-order if it uses neither set quantification nor membership.
-/
def IsFO : MSO A → Prop
  | le _ _ => True
  | lab _ _ => True
  | mem _ _ => False
  | not φ => IsFO φ
  | and φ ψ => IsFO φ ∧ IsFO ψ
  | or φ ψ => IsFO φ ∧ IsFO ψ
  | exFO _ φ => IsFO φ
  | exSO _ _ => False

/-- The quantifier rank: the maximal number of nested quantifiers. -/
def qrank : MSO A → ℕ
  | le _ _ => 0
  | lab _ _ => 0
  | mem _ _ => 0
  | not φ => qrank φ
  | and φ ψ => max (qrank φ) (qrank ψ)
  | or φ ψ => max (qrank φ) (qrank ψ)
  | exFO _ φ => qrank φ + 1
  | exSO _ φ => qrank φ + 1

/-- The free first-order variables of a formula. -/
def freeFO : MSO A → Set ℕ
  | le i j => {i, j}
  | lab _ i => {i}
  | mem i _ => {i}
  | not φ => freeFO φ
  | and φ ψ => freeFO φ ∪ freeFO ψ
  | or φ ψ => freeFO φ ∪ freeFO ψ
  | exFO i φ => freeFO φ \ {i}
  | exSO _ φ => freeFO φ

/-- The free second-order variables of a formula. -/
def freeSO : MSO A → Set ℕ
  | le _ _ => ∅
  | lab _ _ => ∅
  | mem _ j => {j}
  | not φ => freeSO φ
  | and φ ψ => freeSO φ ∪ freeSO ψ
  | or φ ψ => freeSO φ ∪ freeSO ψ
  | exFO _ φ => freeSO φ
  | exSO i φ => freeSO φ \ {i}

end MSO

/-- A language is definable in monadic second-order logic. -/
def MSODefinable {A : Type} (L : Language A) : Prop :=
  ∃ φ : MSO A, ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat w fo so φ ↔ w ∈ L

/-- A language is definable in first-order logic. -/
def FODefinable {A : Type} (L : Language A) : Prop :=
  ∃ φ : MSO A, φ.IsFO ∧
    ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat w fo so φ ↔ w ∈ L

open scoped Classical in
/-- The annotation `w ⊗ {x₁} ⊗ ⋯ ⊗ {x_k} ⊗ X₁ ⊗ ⋯ ⊗ X_l` of a string by the values
of `k` first-order and `l` second-order variables. -/
noncomputable def annotate {A : Type} (k l : ℕ) (w : List A)
    (fo : Fin k → ℕ) (so : Fin l → Set ℕ) : List (A × (Fin k → Bool) × (Fin l → Bool)) :=
  w.zipIdx.map (fun z => (z.1, fun i => decide (fo i = z.2), fun j => decide (z.2 ∈ so j)))

/-- Extend a valuation of the first-order variables `0, …, k-1` to all variables. -/
def extFO (k : ℕ) (fo : Fin k → ℕ) : ℕ → ℕ :=
  fun i => if h : i < k then fo ⟨i, h⟩ else 0

/-- Extend a valuation of the set variables `0, …, l-1` to all variables. -/
def extSO (l : ℕ) (so : Fin l → Set ℕ) : ℕ → Set ℕ :=
  fun j => if h : j < l then so ⟨j, h⟩ else ∅

end Lax314295.MSOLogic
