import Lax185574.Graphs
import Lax185574.PhiPsiPatterns

/-!
---
title: Clean patterns and dp-minimal graph classes
type: definition
---
Fix first-order formulas φ(x̄, z) and ψ(ȳ, z). A *clean (φ, ψ)-pattern*
of order s × t in a graph G consists of tuples ā₁, …, ā_s ∈ V(G)^{|x̄|},
b̄₁, …, b̄_t ∈ V(G)^{|ȳ|} and vertices (c_{i,j} : i ∈ [s], j ∈ [t]) such
that the following hold for all i, i' ∈ [s] and j, j' ∈ [t]:

1. G ⊨ φ(ā_{i'}, c_{i,j}) if and only if i = i',
2. G ⊨ ψ(b̄_{j'}, c_{i,j}) if and only if j = j'.

A graph class 𝒞 is *dp-minimal* if for every two formulas φ(x̄, z) and
ψ(ȳ, z) there is some t ∈ ℕ such that no graph in 𝒞 contains a clean
(φ, ψ)-pattern of order t × t.

# Formalization notes

Formulas, their free variables and their evaluation are those of
`PhiPsiPatterns`: a formula φ(x̄, z) of the language of graphs has the
free variables `Fin p ⊕ Fin 1`, and `Holds` is G ⊨ φ(ā, c). The tuples
and the vertices c_{i,j} need not be distinct. The definition is given
for the finite graphs of a `GraphClass`.
-/

namespace Lax185574.DpMinimality

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.PhiPsiPatterns

universe u

variable {V : Type u}

/-- The tuples `a i`, `b j` and the vertices `c i j` form a clean
`(φ, ψ)`-pattern of order `s × t` in `G`. -/
def IsCleanPattern (G : SimpleGraph V) {p p' : ℕ}
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) {s t : ℕ}
    (a : Fin s → Fin p → V) (b : Fin t → Fin p' → V) (c : Fin s → Fin t → V) :
    Prop :=
  ∀ i j,
    (∀ i', Holds G φ (a i') (c i j) ↔ i' = i) ∧
    (∀ j', Holds G ψ (b j') (c i j) ↔ j' = j)

/-- `G` contains a clean `(φ, ψ)`-pattern of order `s × t`. -/
def HasCleanPattern (G : SimpleGraph V) {p p' : ℕ}
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) (s t : ℕ) : Prop :=
  ∃ (a : Fin s → Fin p → V) (b : Fin t → Fin p' → V) (c : Fin s → Fin t → V),
    IsCleanPattern G φ ψ a b c

/-- A graph class is *dp-minimal*: for every two formulas `φ(x̄, z)` and
`ψ(ȳ, z)`, some order `t × t` of clean `(φ, ψ)`-patterns occurs in no
graph of the class. -/
def DpMinimal (C : GraphClass) : Prop :=
  ∀ {p p' : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)),
    ∃ t : ℕ, ∀ G ∈ C, ¬ HasCleanPattern G.toSimpleGraph φ ψ t t

end Lax185574.DpMinimality
