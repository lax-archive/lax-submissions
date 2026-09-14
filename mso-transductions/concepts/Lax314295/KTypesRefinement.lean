import Lax314295.KTypes

/-!
---
title: k-types refine each other
type: theorem
---
Strings with the same $(k+1)$-type have the same $k$-type (Lemma C.4.15 of
*Transducers*, refinement): the $k$-type of a string is determined by its
$(k+1)$-type.

# Formalization notes

Stated over any alphabet; no finiteness is needed.
-/

namespace Lax314295.KTypesRefinement

open Lax314295.KTypes

/-- Equal `(k+1)`-types have equal `k`-types. -/
axiom tp_eq_of_tp_succ_eq {A : Type} (k : ℕ) (w v : List A) (h : tp (k + 1) w = tp (k + 1) v) :
    tp k w = tp k v

end Lax314295.KTypesRefinement
