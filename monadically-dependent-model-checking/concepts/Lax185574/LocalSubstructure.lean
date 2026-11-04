import Lax185574.LocalFormulas

/-!
---
title: Local formulas are evaluated in any superset of the ball
type: lemma
---
Let φ(x̄) be an r-local σ-formula, let A be a σ-structure, let
ā ∈ V(A)^{|x̄|}, and let Ball^A_r(ā) ⊆ B ⊆ V(A). Then
A ⊨ φ(ā) if and only if A[B] ⊨ φ(ā).

# Formalization notes

The signature is a finite relational language, as required by the
definition of local formulas. The structure is arbitrary, possibly
infinite. The tuple is given as a tuple of B, and its image in A is its
coordinatewise image. The formula is evaluated in A[B] with the induced
structure of `GaifmanGraph.induced`, whose Gaifman graph may have fewer
edges than the restriction of the Gaifman graph of A to B.
-/

namespace Lax185574.LocalSubstructure

open FirstOrder FirstOrder.Language
open Lax185574.GaifmanGraph Lax185574.LocalFormulas

universe u v z

/-- **Local formulas and substructures.** An `r`-local formula holds of
a tuple in a structure `A` if and only if it holds of the tuple in every
induced substructure `A[B]` with `B ⊇ Ball^A_r(ā)`. -/
axiom realize_iff_realize_induced (L : Language.{u, v}) [L.IsRelational]
    [Finite (Σ l, L.Relations l)] (r k : ℕ) (φ : L.Formula (Fin k)) (hφ : IsLocal r φ)
    (V : Type z) [L.Structure V] (B : Set V) (a : Fin k → B) :
    ball L r (Subtype.val ∘ a) ⊆ B →
      (φ.Realize (Subtype.val ∘ a) ↔ @Formula.Realize L B (induced B) _ φ a)

end Lax185574.LocalSubstructure
