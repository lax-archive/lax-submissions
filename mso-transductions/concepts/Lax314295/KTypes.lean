import Mathlib.Data.Set.Basic

/-!
---
title: The k-type of a string
type: definition
---
The *$k$-type* of a string (Definition C.4.12 of *Transducers*) is defined by
induction on $k$: the $0$-type of every string is the same, and the
$(k+1)$-type of $w$ is the set of triples
$$\{(\text{$k$-type of } w_1,\; a,\; \text{$k$-type of } w_2) \mid w = w_1\, a\, w_2\}$$
over all factorisations of $w$ around one of its letters. Two strings have the
same $k$-type if and only if they satisfy the same first-order sentences of
quantifier rank at most $k$ (Lemma C.4.13); $k$-types refine, are a congruence
for concatenation and are aperiodic (Lemma C.4.15), which is what makes the
first-order definable languages the aperiodic ones (Theorem C.4.11).

# Formalization notes

`TpType A k` is the type of `k`-types, `Unit` for `k = 0` and sets of triples
for `k + 1`, and `tp k w` the `k`-type of `w`. Over a finite alphabet there are
finitely many `k`-types for every `k`, which is not part of the definition.
-/

namespace Lax314295.KTypes

/-- The type of `k`-types over the alphabet `A`. -/
def TpType (A : Type) : ℕ → Type
  | 0 => Unit
  | k + 1 => Set (TpType A k × A × TpType A k)

/-- The `k`-type of a string: trivial for `k = 0`, and for `k + 1` the set of
triples `(tp k w₁, a, tp k w₂)` over the factorisations `w = w₁ a w₂`. -/
def tp {A : Type} : (k : ℕ) → List A → TpType A k
  | 0, _ => ()
  | k + 1, w =>
      {t : TpType A k × A × TpType A k |
        ∃ (w₁ : List A) (a : A) (w₂ : List A), w = w₁ ++ a :: w₂ ∧ t = (tp k w₁, a, tp k w₂)}

end Lax314295.KTypes
