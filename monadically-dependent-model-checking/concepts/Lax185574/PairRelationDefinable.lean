import Lax185574.PairRelation
import Lax185574.Colorings
import Lax185574.FirstOrderTypes

/-!
---
title: The pair relation of atomic types is definable
type: lemma
---
Suppose G is a graph and 𝒫 is the partition of V(G) into atomic types
over some set S ⊆ V(G). Then the relation R ≔ R(G, 𝒫) is definable in G
expanded with one unary predicate marking S, using a fixed first-order
formula φ_R(x, y) of quantifier rank at most 5.

# Formalization notes

"Fixed" means that one formula serves all graphs and all sets S, so the
formula is chosen first. It is a formula of graphs with one color, in
the language of `Lax185574.Colorings`, with the two free variables x
and y of `Fin 2`. The expansion interprets the color by S. The graph may
be infinite.
-/

namespace Lax185574.PairRelationDefinable

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.Partitions Lax185574.PairRelation Lax185574.Colorings
open Lax185574.FirstOrderTypes

universe z

/-- **Definability of the pair relation.** One formula of quantifier
rank at most `5`, with one color marking `S`, defines `R(G, 𝒫_S)` in
every graph `G`. -/
axiom exists_formula_pairRelation :
    ∃ φ : (withColors Language.graph 1).Formula (Fin 2), quantifierRank φ ≤ 5 ∧
      ∀ {V : Type z} (G : SimpleGraph V) (S : Set V) (x : Fin 2 → V),
        @Formula.Realize _ V (expansion G fun _ => S) _ φ x ↔
          (pairRelation G (atomicTypes G S)).Adj (x 0) (x 1)

end Lax185574.PairRelationDefinable
