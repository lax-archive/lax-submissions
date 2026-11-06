import Lax185574.Colorings
import Lax185574.DpMinimality
import Lax185574.FirstOrderTypes

/-!
---
title: Polynomial bound on the number of types in dp-minimal classes
type: theorem
---
Let 𝒞 be a dp-minimal graph class and k, q, c ∈ ℕ. For every graph
G ∈ 𝒞, every expansion G⁺ of G by c unary predicates and every subset
U ⊆ V(G),

|Types^{G⁺}_{k,q}(V(G)/U)| ≤ O_{𝒞,q,k,c}(1) · poly_{𝒞,q,k}(|U|).

The degree of the polynomial does not depend on the number c of unary
predicates. Only the constant factor does.

# Formalization notes

The bound is spelled out as in `Lax185574.TypeBound`: there is an
exponent `a`, depending on the class, `k` and `q`, and for each `c` a
factor `F`, such that the count is at most `F · (|U| + 1)^a`. The
quantifier order puts `a` before `c`. The statement is for the finite
graphs of a `GraphClass`.
-/

namespace Lax185574.DpMinimalTypeBound

open Lax185574.Graphs Lax185574.DpMinimality
open Lax185574.FirstOrderTypes Lax185574.Colorings

/-- **Type bound.** In a dp-minimal class, the number of types of
quantifier rank `q` of `k`-tuples over a parameter set `U`, in an
expansion by `c` unary predicates, is at most `F · (|U| + 1)^a`. The
exponent `a` does not depend on `c`. -/
axiom typeCountOver_le (C : GraphClass) (hC : DpMinimal C) (k q : ℕ) :
    ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ, ∀ G ∈ C,
      ∀ (colors : Fin c → Set (Fin G.n)) (U : Finset (Fin G.n)),
        typeCountOver (expansion G.toSimpleGraph colors) k q Set.univ (U : Set (Fin G.n)) ≤
          F * (U.card + 1) ^ a

end Lax185574.DpMinimalTypeBound
