import Lax185574.PhiPsiPatterns

/-!
---
title: φ-patterns
type: definition
---
For a first-order formula φ(x̄, z), a *φ-pattern* is a (φ, ψ)-pattern
with ψ(y, z) = E(y, z) or ψ(y, z) = ¬E(y, z). These are called a
*(φ, E)-pattern* and a *(φ, ¬E)-pattern*, respectively. Such a pattern
consists of tuples ā₁, …, ā_s ∈ V(G)^{|x̄|}, vertices b₁, …, b_t ∈ V(G)
and (c_{i,j} : i ∈ [s], j ∈ [t]). The tuple b̄ = (b₁, …, b_t) is the
*base* of the pattern.

# Formalization notes

The formula E(y, z) is the adjacency atom with y the single variable of
the left summand and z the variable of the right summand, as in
`PhiPsiPatterns`. A φ-pattern is a pattern for this formula or for its
negation. The base vertex bⱼ is the single entry of the tuple b̄ⱼ of
length one.
-/

namespace Lax185574.PhiPatterns

open FirstOrder FirstOrder.Language
open Lax185574.PhiPsiPatterns

universe u

variable {V : Type u}

/-- The formula `E(y, z)`. -/
def edgeFormula : Language.graph.Formula (Fin 1 ⊕ Fin 1) :=
  Relations.formula₂ Language.adj (Term.var (Sum.inl 0)) (Term.var (Sum.inr 0))

/-- `G` contains a `φ`-pattern of order `s × t`: a `(φ, E)`-pattern or a
`(φ, ¬E)`-pattern. -/
def HasPhiPattern (G : SimpleGraph V) {p : ℕ}
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1)) (s t : ℕ) : Prop :=
  HasPattern G φ edgeFormula s t ∨ HasPattern G φ edgeFormula.not s t

end Lax185574.PhiPatterns
