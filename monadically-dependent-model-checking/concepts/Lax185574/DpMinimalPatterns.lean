import Lax185574.DpMinimality

/-!
---
title: Dp-minimal classes exclude large (φ, ψ)-patterns
type: lemma
---
Let 𝒞 be a dp-minimal graph class, and let φ(x̄, z) and ψ(ȳ, z) be
first-order formulas. Then there is some t ∈ ℕ such that no graph G ∈ 𝒞
contains a (φ, ψ)-pattern of order t × t.

# Formalization notes

The patterns here are the (φ, ψ)-patterns of `PhiPsiPatterns`, in which
each condition constrains only later rows and columns, and not the clean
patterns of `DpMinimality`. The number t is chosen after 𝒞, φ and ψ.
-/

namespace Lax185574.DpMinimalPatterns

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.PhiPsiPatterns Lax185574.DpMinimality

/-- **Forbidden `(φ, ψ)`-patterns in dp-minimal classes.** No graph of a
dp-minimal class contains a `(φ, ψ)`-pattern of order `t × t`, for some
`t` depending on the class, `φ` and `ψ`. -/
axiom forbidden_phiPsi_patterns (C : GraphClass) (hC : DpMinimal C)
    {p p' : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ G ∈ C, ¬ HasPattern G.toSimpleGraph φ ψ t t

end Lax185574.DpMinimalPatterns
