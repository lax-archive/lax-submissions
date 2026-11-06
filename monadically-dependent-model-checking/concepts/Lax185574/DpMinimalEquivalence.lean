import Lax185574.Colorings
import Lax185574.DpMinimality
import Lax185574.FirstOrderTypes
import Lax185574.MonadicDependence

/-!
---
title: Equivalent characterizations of monadic dependence
type: corollary
---
Let 𝒞 be a graph class. The following conditions are equivalent.

1. 𝒞 is monadically dependent.
2. 𝒞 is dp-minimal.
3. For all k, q, c ∈ ℕ, every graph G ∈ 𝒞, every expansion G⁺ of G by c
   unary predicates and every subset U ⊆ V(G),

   |Types^{G⁺}_{k,q}(V(G)/U)| ≤ O_{𝒞,q,k,c}(1) · poly_{𝒞,q,k}(|U|).

# Formalization notes

The graphs are the finite graphs of a `GraphClass`. Monadic dependence
is that of `Lax185574.MonadicDependence`, by transductions, and
dp-minimality is that of `Lax185574.DpMinimality`.

Condition 3 is `HasPolynomialTypes`. The bound is spelled out as in
`Lax185574.TypeBound`: there is an exponent `a`, depending on the class,
`k` and `q`, and for each `c` a factor `F`, such that the count is at
most `F · (|U| + 1)^a`. The quantifier order puts `a` before `c`, so the
degree of the polynomial does not depend on the number c of unary
predicates.
-/

namespace Lax185574.DpMinimalEquivalence

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.DpMinimality
open Lax185574.FirstOrderTypes Lax185574.Colorings

/-- Condition 3: the number of types of quantifier rank `q` of `k`-tuples
over a parameter set `U`, in an expansion by `c` unary predicates, is at
most `F · (|U| + 1)^a`, where the exponent `a` does not depend on `c`. -/
def HasPolynomialTypes (C : GraphClass) : Prop :=
  ∀ k q : ℕ, ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ, ∀ G ∈ C,
    ∀ (colors : Fin c → Set (Fin G.n)) (U : Finset (Fin G.n)),
      typeCountOver (expansion G.toSimpleGraph colors) k q Set.univ (U : Set (Fin G.n)) ≤
        F * (U.card + 1) ^ a

/-- **Equivalent characterizations of monadic dependence.** A graph class
is monadically dependent if and only if it is dp-minimal, if and only if
it has polynomially many types over parameter sets. -/
axiom tfae_monadicallyDependent_dpMinimal_hasPolynomialTypes (C : GraphClass) :
    List.TFAE [MonadicallyDependent C, DpMinimal C, HasPolynomialTypes C]

end Lax185574.DpMinimalEquivalence
