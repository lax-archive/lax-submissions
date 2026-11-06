import Lax185574.DpMinimality
import Lax185574.PhiPsiPatterns

/-!
---
title: Dp-minimal classes exclude large (φ, ψ)-patterns
type: lemma
---
For every dp-minimal graph class 𝒞 and formulas φ(x̄, z), ψ(ȳ, z),
there is some t ∈ ℕ such that no graph G ∈ 𝒞 contains a (φ, ψ)-pattern
of order t × t.

This is a corollary of Lemma C.1 of the cited work on ordered
twin-width. The paper includes a self-contained proof.

# Formalization notes

The paper allows infinite graphs in this part. Here the graphs are
those of a `GraphClass`, which are finite, as in every use.

The formulas are formulas of the language of graphs, without colors,
with free variables as in `PhiPsiPatterns`. The patterns are the
(φ, ψ)-patterns of `PhiPsiPatterns`, in which each condition constrains
only later rows and columns, and not the clean patterns of
`DpMinimality`. The number t is chosen after 𝒞, φ and ψ, so it depends
on these only.
-/

namespace Lax185574.ForbiddenPhiPsiPatterns

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.DpMinimality Lax185574.PhiPsiPatterns

/-- **Forbidden `(φ, ψ)`-patterns.** No graph of a dp-minimal class
contains a `(φ, ψ)`-pattern of order `t × t`, for some `t` depending on
the class, `φ` and `ψ`. -/
axiom forbidden_phiPsi_patterns (C : GraphClass) (hC : DpMinimal C)
    {p p' : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ G ∈ C, ¬ HasPattern G.toSimpleGraph φ ψ t t

end Lax185574.ForbiddenPhiPsiPatterns
