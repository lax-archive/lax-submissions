import Lax185574.DpMinimality
import Lax185574.PhiPatterns

/-!
---
title: Dp-minimal classes exclude large φ-patterns
type: corollary
---
For every dp-minimal graph class 𝒞 and formula φ(x̄, z), there is some
t ∈ ℕ such that no graph G ∈ 𝒞 contains a φ-pattern of order t × t.

# Formalization notes

The paper allows infinite graphs in this part. Here the graphs are
those of a `GraphClass`, which are finite, as in every use.

This is the case ψ(y, z) = E(y, z) or ψ(y, z) = ¬E(y, z) of the
exclusion of (φ, ψ)-patterns. A single t excludes both kinds of
φ-patterns. The formula is a formula of the language of graphs with
free variables as in `PhiPsiPatterns`.
-/

namespace Lax185574.ForbiddenPhiPatterns

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.DpMinimality Lax185574.PhiPatterns

/-- **Forbidden `φ`-patterns.** No graph of a dp-minimal class contains
a `φ`-pattern of order `t × t`, for some `t` depending on the class and
`φ`. -/
axiom forbidden_phi_patterns (C : GraphClass) (hC : DpMinimal C)
    {p : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ G ∈ C, ¬ HasPhiPattern G.toSimpleGraph φ t t

end Lax185574.ForbiddenPhiPatterns
