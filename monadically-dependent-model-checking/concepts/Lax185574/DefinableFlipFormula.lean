import Lax185574.DefinableFlips
import Mathlib.ModelTheory.Complexity

/-!
---
title: The edges of a definable flip are quantifier-free definable
type: observation
---
The edges of a definable flip can be defined in the original graph. More
precisely, for every s ∈ ℕ and symmetric relation R ⊆ Π^s × Π^s there
exists a quantifier-free formula E_{⊕R}(x, y, z̄) such that for every
graph G, tuple p̄ ∈ V(G)^s, and vertices u, v ∈ V(G),

G ⊕ (p̄, R) ⊨ E(u, v)  ⟺  G ⊨ E_{⊕R}(u, v, p̄).

# Formalization notes

The formula is in mathlib's language of graphs with the free variables
`Fin 2 ⊕ Fin s`: the left summand is (x, y) and the right summand is z̄.
Quantifier-free is mathlib's `IsQF`. The formula is chosen before the
graph, so one formula works for all graphs on all vertex types of a
fixed universe, finite or infinite. G ⊕ (p̄, R) ⊨ E(u, v) is adjacency
in `DefinableFlips.flipOver`.
-/

namespace Lax185574.DefinableFlipFormula

open FirstOrder FirstOrder.Language
open Lax185574.AtomicTypes Lax185574.DefinableFlips

universe u

/-- **Definable flips are quantifier-free definable.** For a symmetric
relation `R` on atomic types over `s`-tuples, one quantifier-free
formula `E_{⊕R}(x, y, z̄)` defines the edges of `G ⊕ (p̄, R)` in `G`, for
every graph `G` and tuple `p̄`. -/
axiom exists_isQF_flipOver_formula (s : ℕ)
    (R : (Fin s → PairType) → (Fin s → PairType) → Prop)
    (hR : ∀ P Q, R P Q → R Q P) :
    ∃ φ : Language.graph.Formula (Fin 2 ⊕ Fin s), φ.IsQF ∧
      ∀ (V : Type u) (G : SimpleGraph V) (p : Fin s → V) (x y : V),
        (flipOver G p R).Adj x y ↔
          @Formula.Realize Language.graph V G.structure _ φ (Sum.elim ![x, y] p)

end Lax185574.DefinableFlipFormula
