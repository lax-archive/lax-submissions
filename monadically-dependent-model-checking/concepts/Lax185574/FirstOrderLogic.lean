import Lax185574.Graphs
import Mathlib.Data.Fin.Tuple.Basic

/-!
---
title: First-order logic on colored graphs
type: definition
---
First-order formulas speak about the vertices of a graph. Their atoms
say that two vertices are adjacent, that they are equal, or that a
vertex has a color. Formulas are closed under negation, conjunction and
existential quantification over vertices. The other connectives and the
universal quantifier are expressed by these as usual.

A formula has free variables x₀, …, x_{n−1} for some n, and its
quantifier ∃ binds the next variable xₙ. A *sentence* has no free
variables and no colors, and `G ⊨ φ` says that the sentence φ holds in
the graph G.

# Formalization notes

The colors are the elements of a type `K`. Sentences use the empty type
of colors. A coloring of a graph assigns to each color the set of
vertices that have it, and the sets of different colors may overlap.

The type of a formula records how many free variables it may use, so a
formula cannot refer to a variable that is not bound or assigned.
Variables are numbered by the order in which they are introduced (de
Bruijn levels), so a variable keeps its number under a quantifier, and
`Fin.snoc a v` extends the assignment `a` of x₀, …, x_{n−1} by the vertex
`v` for xₙ.
-/

namespace Lax185574.FirstOrderLogic

open Lax185574.Graphs

/-- First-order formulas on graphs with colors from `K`, whose free
variables are among `x₀, …, x_{n-1}`. -/
inductive Formula (K : Type) : ℕ → Type
  /-- `xᵢ` and `xⱼ` are adjacent. -/
  | adj {n : ℕ} (i j : Fin n) : Formula K n
  /-- `xᵢ` and `xⱼ` are equal. -/
  | eq {n : ℕ} (i j : Fin n) : Formula K n
  /-- Negation. -/
  | not {n : ℕ} (φ : Formula K n) : Formula K n
  /-- Conjunction. -/
  | and {n : ℕ} (φ ψ : Formula K n) : Formula K n
  /-- `∃ xₙ φ`: some vertex can be assigned to `xₙ` so that `φ` holds. -/
  | ex {n : ℕ} (φ : Formula K (n + 1)) : Formula K n
  /-- `xᵢ` has the color `c`. -/
  | color {n : ℕ} (c : K) (i : Fin n) : Formula K n

/-- The formula `φ` holds in the graph `G` with the coloring `col`, when
the free variable `xᵢ` is assigned the vertex `a i`. -/
def Formula.Holds {K : Type} (G : Graph) (col : K → Set (Fin G.n)) :
    {n : ℕ} → Formula K n → (Fin n → Fin G.n) → Prop
  | _, .adj i j, a => G.Adj (a i) (a j)
  | _, .eq i j, a => a i = a j
  | _, .not φ, a => ¬ φ.Holds G col a
  | _, .and φ ψ, a => φ.Holds G col a ∧ ψ.Holds G col a
  | _, .ex φ, a => ∃ v : Fin G.n, φ.Holds G col (Fin.snoc a v)
  | _, .color c i, a => a i ∈ col c

/-- A sentence: a formula without colors and without free variables. -/
abbrev Sentence : Type := Formula Empty 0

/-- The sentence `φ` holds in the graph `G`. -/
def Models (G : Graph) (φ : Sentence) : Prop :=
  φ.Holds G Empty.elim Fin.elim0

@[inherit_doc] scoped infix:50 " ⊨ " => Models

end Lax185574.FirstOrderLogic
