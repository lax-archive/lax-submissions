import Lax185574.ConstructionSequences
import Lax185574.Colorings
import Lax185574.FirstOrderTypes

/-!
---
title: Locally definable construction sequences
type: definition
---
Let A be a structure and H a partial graph with V(H) ⊆ V(A). Then H is
*definable* in A by formulas of quantifier rank q₀ with parameters from
a set S ⊆ V(A) if for every relation R of H of arity k there is a formula
φ_R(x₁, …, x_k) of quantifier rank at most q₀ with parameters from S
such that, for all v̄ ∈ V(A)^k,

A ⊨ φ_R(v̄)  ⟺  v̄ ∈ V(H)^k and H ⊨ R(v̄).

Let G be a graph and r, c, s, q₀ ∈ ℕ. A construction sequence
G₁, …, G_λ of G is *radius-r definable* with c unary predicates,
s parameters and quantifier rank q₀ if, for all t ∈ [λ−1] and
v ∈ V(G), the induced partial graph G_t[Ball^{G_{t+1}}_r(v)] is
definable in some expansion of G by c unary predicates, by formulas of
quantifier rank q₀ with parameters from a set of at most s vertices.
The expansion and the parameters may depend on t and v.

# Formalization notes

The defined partial graph is an induced partial graph H[B]. It is given
by H and the set B, so the definition needs no subtype. Its relations
are those of H restricted to B. The condition "v̄ ∈ V(H[B])^k and
H[B] ⊨ R(v̄)" therefore reads "every entry of v̄ lies in B and H ⊨ R(v̄)".
The relations are the edges, the non-edges and every color class. A
color class that misses B is defined by any false formula, so only
finitely many conditions have content. Parameters are free variables of
the right summand, as in `Lax185574.FirstOrderTypes`.
-/

namespace Lax185574.LocalDefinability

open FirstOrder FirstOrder.Language
open Lax185574.PartialGraphs Lax185574.FirstOrderTypes Lax185574.Colorings
open Lax710763.Transductions

universe u v z

variable {V : Type z}

/-- The induced partial graph `H[B]` is definable in the structure on
`V` by formulas of quantifier rank at most `q₀` with parameters from
`S`. -/
def DefinableIn {L : Language.{u, v}} [L.Structure V] (q₀ : ℕ) (S : Set V)
    (H : PartialGraph V) (B : Set V) : Prop :=
  ∀ {k : ℕ} (R : PartialGraphs.language.Relations k),
    ∃ φ : L.Formula (Fin k ⊕ S), quantifierRank φ ≤ q₀ ∧
      ∀ x : Fin k → V,
        φ.Realize (Sum.elim x Subtype.val) ↔
          (∀ i, x i ∈ B) ∧ @Structure.RelMap _ V H.structure k R x

/-- The sequence `s` is radius-`r` definable in the graph `G` with `c`
unary predicates, `s'` parameters and quantifier rank `q₀`: for every
step `t` and vertex `v`, the induced partial graph
`s[t][Ball^{s[t+1]}_r(v)]` is definable in some expansion of `G` by `c`
unary predicates, by formulas of quantifier rank at most `q₀` with at
most `s'` parameters. -/
def IsRadiusDefinable (G : SimpleGraph V) (s : List (PartialGraph V))
    (r c s' q₀ : ℕ) : Prop :=
  ∀ (t : ℕ) (ht : t + 1 < s.length) (v : V),
    ∃ (colors : Fin c → Set V) (S : Finset V), S.card ≤ s' ∧
      @DefinableIn V (withColors Language.graph c) (expansion G colors) q₀ S
        s[t] (s[t + 1].ball r v)

end Lax185574.LocalDefinability
