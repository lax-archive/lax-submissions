import Mathlib.ModelTheory.Graph
import Mathlib.ModelTheory.Semantics

/-!
---
title: (φ, ψ)-patterns
type: definition
---
Fix first-order formulas φ(x̄, z) and ψ(ȳ, z). A *(φ, ψ)-pattern* of
order s × t in a graph G consists of tuples ā₁, …, ā_s ∈ V(G)^{|x̄|},
b̄₁, …, b̄_t ∈ V(G)^{|ȳ|}, and vertices (c_{i,j} : i ∈ [s], j ∈ [t])
such that the following holds for all i, i' ∈ [s] and j, j' ∈ [t]:

1. G ⊨ φ(āᵢ, c_{i,j}), and G ⊭ φ(ā_{i'}, c_{i,j}) if i' > i,
2. G ⊨ ψ(b̄ⱼ, c_{i,j}), and G ⊭ ψ(b̄_{j'}, c_{i,j}) if j' > j.

The set { c_{i,j} : i ∈ [s], j ∈ [t] } is the set of *grid-points* of
the pattern, and s is its *height*.

# Formalization notes

Formulas are mathlib's first-order formulas in the language of graphs,
evaluated in the structure of the graph G. A formula φ(x̄, z) has the
free variables `Fin p ⊕ Fin 1`: the left summand is the tuple x̄ of
length p, and the right summand is the single variable z. This is the
convention of `IndependenceProperty` for formulas φ(x̄, ȳ). Rows and
columns are indexed by `Fin s` and `Fin t` with their usual order. The
grid-points and the tuples need not be distinct.
-/

namespace Lax185574.PhiPsiPatterns

open FirstOrder FirstOrder.Language

universe u

variable {V : Type u}

/-- `G ⊨ φ(ā, c)` for a formula `φ(x̄, z)` of the language of graphs. -/
def Holds (G : SimpleGraph V) {p : ℕ}
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1)) (a : Fin p → V) (c : V) :
    Prop :=
  @Formula.Realize Language.graph V G.structure _ φ (Sum.elim a ![c])

/-- The tuples `a i`, `b j` and the vertices `c i j` form a
`(φ, ψ)`-pattern of order `s × t` in `G`. -/
def IsPattern (G : SimpleGraph V) {p p' : ℕ}
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) {s t : ℕ}
    (a : Fin s → Fin p → V) (b : Fin t → Fin p' → V) (c : Fin s → Fin t → V) :
    Prop :=
  ∀ i j,
    (Holds G φ (a i) (c i j) ∧ ∀ i', i < i' → ¬ Holds G φ (a i') (c i j)) ∧
    (Holds G ψ (b j) (c i j) ∧ ∀ j', j < j' → ¬ Holds G ψ (b j') (c i j))

/-- `G` contains a `(φ, ψ)`-pattern of order `s × t`. -/
def HasPattern (G : SimpleGraph V) {p p' : ℕ}
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) (s t : ℕ) : Prop :=
  ∃ (a : Fin s → Fin p → V) (b : Fin t → Fin p' → V) (c : Fin s → Fin t → V),
    IsPattern G φ ψ a b c

end Lax185574.PhiPsiPatterns
