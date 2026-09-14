import Lax314295.MSOLogic
import Lax314295.KTypes

/-!
---
title: k-types capture first-order sentences of quantifier rank k
type: theorem
---
Two strings have the same $k$-type if and only if they satisfy the same
first-order sentences of quantifier rank at most $k$ (Lemma C.4.13 of
*Transducers*). From equal types to equal satisfaction is the compositionality
of first-order logic: a position chosen on one string can be matched on the
other so that all formulas of one rank lower are preserved. Conversely the set
of strings of a given $k$-type is defined by a first-order sentence of
quantifier rank $k$, built by induction on $k$ with quantification relativised
to the two sides of a chosen position.

# Formalization notes

The book says "formulas" where it means "sentences": satisfaction of a formula
with free variables has no meaning without a valuation. The statement therefore
quantifies over first-order formulas without free first-order variables,
satisfied under every valuation — which for a sentence is just satisfaction.
The alphabet is assumed finite.
-/

namespace Lax314295.KTypesFOEquivalence

open Lax314295.MSOLogic Lax314295.KTypes

/-- Two strings have the same `k`-type if and only if they satisfy the same
first-order sentences of quantifier rank at most `k`. -/
axiom tp_eq_iff_fo_equiv {A : Type} [Finite A] (k : ℕ) (w v : List A) :
    tp k w = tp k v ↔
      ∀ φ : MSO A, φ.IsFO → φ.freeFO = ∅ → φ.qrank ≤ k →
        ((∀ fo so, MSO.Sat w fo so φ) ↔ (∀ fo so, MSO.Sat v fo so φ))

end Lax314295.KTypesFOEquivalence
