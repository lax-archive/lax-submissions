import Lax710763.Transductions
import Mathlib.ModelTheory.Graph

/-!
---
title: Colorings of graphs
type: definition
---
A *coloring* of a graph G is an expansion G⁺ of G by finitely many unary
predicates. With c predicates, G⁺ is a structure in the signature of
graphs expanded by c unary symbols.

# Formalization notes

The colored language and the color sets are those of
`Lax710763.Transductions`, which the archive's monadic dependence is
stated over. The c color sets are arbitrary: they may overlap and need
not cover the vertex set. The expansion is the structure of the sum
language, which interprets adjacency by `G` and the i-th color by the
i-th color set.

The main theorem, monadic dependence and the independence property use
the formulas of `Lax185574.FirstOrderLogic`, with a coloring given by
one set of vertices per color. The statements about types and
definability use the formulas of mathlib in the colored language here,
since mathlib provides the quantifier rank, parameters and the sets of
formulas that types are made of. In both, a coloring with c colors is
a family of c sets of vertices, which may overlap.
-/

namespace Lax185574.Colorings

open FirstOrder FirstOrder.Language Lax710763.Transductions

universe z

variable {V : Type z}

/-- The expansion `G⁺` of the graph `G` by the color sets `colors`. -/
@[implicit_reducible]
def expansion (G : SimpleGraph V) {c : ℕ} (colors : Fin c → Set V) :
    (withColors Language.graph c).Structure V :=
  @Language.sumStructure _ _ V G.structure (colorStructure colors)

end Lax185574.Colorings
