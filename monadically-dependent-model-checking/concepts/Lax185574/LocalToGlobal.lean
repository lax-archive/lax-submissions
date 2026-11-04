import Lax185574.FirstOrderTypes
import Lax185574.GaifmanGraph

/-!
---
title: Types are determined by types in a neighborhood
type: theorem
---
For all k, q, α ∈ ℕ there is a number q' = q'(k, q, α) such that with
h ≔ 7^q the following holds. Let σ be a relational signature of arity at most
α and A a σ-structure. Then, for all ā ∈ V(A)^k and B ⊇ Ball^A_h(ā),
the type tp^A_q(ā) depends only on tp^{A[B]}_{q'}(ā).

This is a corollary of Gaifman's locality theorem. The point is that h
depends on q alone, and q' does not depend on the signature beyond its
arity. The latter matters when the signature has one unary symbol per
part of a partition with up to n parts. The paper states that h = h(q)
is computable, and its proof takes h = 7^q. The statement here names
this value, because algorithms downstream compute the radius from q.

# Formalization notes

"Depends only on" is stated pairwise. If ā with B ⊇ Ball_h(ā) and b̄ with
B' ⊇ Ball_h(b̄) have the same type of rank q' in A[B] and A[B']
respectively, then they have the same type of rank q in A. The tuples
are given as tuples of B and B', and their images in A are their
coordinates. Types without parameters are compared as sets of formulas
of one fixed language, so types in different substructures are
comparable.

The paper states the lemma for finite signatures, with h and q'
computable. Here the signature is any relational language with relation
symbols of arity at most α, possibly infinitely many. This is the
generality that the lemma is applied in, as the language of partial
graphs has a unary symbol for every natural number. For an infinite
signature the statement follows from the finite case, applied to the
finitely many symbols of each formula, since q' does not depend on the
signature. The structure is finite. The radius is h = 7^q. The rank q' only exists, as no algorithm
uses it.
-/

namespace Lax185574.LocalToGlobal

open FirstOrder FirstOrder.Language
open Lax185574.FirstOrderTypes Lax185574.GaifmanGraph

universe u v z

/-- **Local-to-global types.** For a relational structure of arity at
most `α`, the type of quantifier rank `q` of a `k`-tuple is determined
by its type of quantifier rank `q'` in any induced substructure that
contains its ball of radius `7^q`. -/
axiom rankType_eq_of_rankType_induced_eq (k q α : ℕ) :
    ∃ q' : ℕ, ∀ (L : Language.{u, v}) [L.IsRelational],
      (∀ l, α < l → IsEmpty (L.Relations l)) →
      ∀ (V : Type z) [Finite V] [L.Structure V] (B B' : Set V)
        (a : Fin k → B) (b : Fin k → B'),
        ball L (7 ^ q) (Subtype.val ∘ a) ⊆ B →
        ball L (7 ^ q) (Subtype.val ∘ b) ⊆ B' →
        @rankType L B (induced B) q' k a = @rankType L B' (induced B') q' k b →
        rankType (L := L) q (Subtype.val ∘ a) = rankType (L := L) q (Subtype.val ∘ b)

end Lax185574.LocalToGlobal
