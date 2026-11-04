import Lax185574.FirstOrderTypes
import Lax185574.LocalFormulas

/-!
---
title: Gaifman's locality theorem with a rank bound
type: theorem
---
For all α, q, k ∈ ℕ there is a p = p(α, q, k), computable from α, q, k,
with the following property. Let σ be a finite relational signature of
arity at most α. Every σ-formula φ(x̄) of quantifier rank at most q and
with |x̄| ≤ k free variables is equivalent to a σ-formula φ^loc(x̄),
computable from φ, that is a Boolean combination of basic 7^q-local
sentences and 7^q-local formulas, each of quantifier rank at most p.

This is Gaifman's locality theorem. Gaifman's paper does not state the
bound p explicitly. An analysis of its proof shows that p depends only
on α, q and k, and not on the signature σ, as the rank-preserving locality theorems of Dreier and
Toruńczyk and of van Bergerem, Grohe and Schweikardt make explicit for
their variants of local formulas. The dependence of p on α comes from expressing the
distance predicates in plain first-order logic.

# Formalization notes

The number p is quantified before the signature, so it depends on α, q
and k only. A finite relational signature of arity at most α is a
relational language with finitely many relation symbols, none of arity
above α. The formula has exactly n free variables for some n ≤ k.

The Boolean combinations are those generated from the constituents by
falsum and implication, which give all Boolean connectives. A basic
local sentence becomes a formula with the free variables x̄ by the
evident relabelling of its (absent) free variables. Each constituent,
a 7^q-local formula or a basic 7^q-local sentence, has quantifier rank
at most p, counting the quantifiers of the dist formulas in the ball
guards. Equivalence is over all finite structures with domain in an arbitrary
universe, including the empty one. The theorem holds for all structures,
but its only use, `Lax185574.LocalToGlobal`, concerns finite ones.

The present paper asserts that p is computable from α, q, k and that
φ^loc is computable from φ. Here both only exist, since no algorithm uses them.
-/

namespace Lax185574.GaifmanLocality

open FirstOrder FirstOrder.Language
open Lax185574.FirstOrderTypes Lax185574.LocalFormulas

universe u v w z

variable {L : Language.{u, v}}

/-- `IsBooleanCombination P φ`: the formula `φ` is a Boolean combination
of formulas satisfying `P`, built by falsum and implication. -/
inductive IsBooleanCombination {α : Type w} (P : L.Formula α → Prop) :
    L.Formula α → Prop
  /-- A constituent is a Boolean combination. -/
  | atom {φ : L.Formula α} : P φ → IsBooleanCombination P φ
  /-- Falsum is a Boolean combination. -/
  | falsum : IsBooleanCombination P ⊥
  /-- Implications of Boolean combinations are Boolean combinations. -/
  | imp {φ ψ : L.Formula α} :
      IsBooleanCombination P φ → IsBooleanCombination P ψ →
        IsBooleanCombination P (φ.imp ψ)

/-- The constituents of a Gaifman normal form with radius `h` and rank
bound `p`: `h`-local formulas and basic `h`-local sentences, each of
quantifier rank at most `p`. -/
def IsLocalConstituent [Finite (Σ l, L.Relations l)] (h p : ℕ) {n : ℕ}
    (χ : L.Formula (Fin n)) : Prop :=
  (IsLocal h χ ∧ quantifierRank χ ≤ p) ∨
    ∃ ψ : L.Sentence, IsBasicLocal h ψ ∧ quantifierRank ψ ≤ p ∧
      χ = ψ.relabel Empty.elim

/-- **Gaifman's locality theorem.** For all `α, q, k` there is a rank
bound `p` such that every formula of quantifier rank at most `q` with at
most `k` free variables, over a finite relational signature of arity at
most `α`, is equivalent to a Boolean combination of `7^q`-local formulas
and basic `7^q`-local sentences of quantifier rank at most `p`. -/
axiom exists_local_equivalent (α q k : ℕ) :
    ∃ p : ℕ, ∀ (L : Language.{u, v}) [L.IsRelational] [Finite (Σ l, L.Relations l)],
      (∀ l, α < l → IsEmpty (L.Relations l)) →
      ∀ (n : ℕ), n ≤ k → ∀ φ : L.Formula (Fin n), quantifierRank φ ≤ q →
        ∃ ψ : L.Formula (Fin n), FinitelyEquivalent.{u, v, z, 0} φ ψ ∧
          IsBooleanCombination (IsLocalConstituent (7 ^ q) p) ψ

end Lax185574.GaifmanLocality
