import Lax185574.DpMinimality

/-!
---
title: Dp-minimality is preserved under interpretations with parameters
type: lemma
---
Let 𝒞 be a dp-minimal graph class, let α(x₁, x₂; ȳ) be a formula and let
ℓ = |ȳ|. For G ∈ 𝒞 and ū ∈ V(G)^ℓ, let α(G, ū) denote the graph with
vertex set V(G) in which distinct vertices u, v are adjacent if and only
if G ⊨ α(u, v; ū) ∨ α(v, u; ū). Then the graph class
{ α(G, ū) : G ∈ 𝒞, ū ∈ V(G)^ℓ } is dp-minimal.

# Formalization notes

A formula α(x₁, x₂; ȳ) has the free variables `Fin 2 ⊕ Fin ℓ`, as in
`DefinableFlipFormula`: the left summand is (x₁, x₂) and the right
summand is ȳ. A graph α(G, ū) is a member of the class as a graph on the
vertices of G, through `Graph.ofSimpleGraph`.
-/

namespace Lax185574.DpMinimalInterpretations

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.DpMinimality

universe u

variable {V : Type u}

/-- The graph `α(G, ū)`: distinct vertices `x`, `y` are adjacent if and
only if `G ⊨ α(x, y; ū) ∨ α(y, x; ū)`. -/
def interpretedGraph (G : SimpleGraph V) {ℓ : ℕ}
    (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ)) (u : Fin ℓ → V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y =>
    @Formula.Realize Language.graph V G.structure _ α (Sum.elim ![x, y] u)

/-- The class of all graphs `α(G, ū)` for `G ∈ C` and `ū ∈ V(G)^ℓ`. -/
def interpretationClass (C : GraphClass) {ℓ : ℕ}
    (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ)) : GraphClass :=
  {H | ∃ G ∈ C, ∃ u : Fin ℓ → Fin G.n,
    H = Graph.ofSimpleGraph (interpretedGraph G.toSimpleGraph α u)}

/-- **Interpretations preserve dp-minimality.** -/
axiom dpMinimal_interpretationClass (C : GraphClass) (hC : DpMinimal C) {ℓ : ℕ}
    (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ)) : DpMinimal (interpretationClass C α)

end Lax185574.DpMinimalInterpretations
