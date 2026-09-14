import Lax314295.KTypes

/-!
---
title: k-types are a congruence for concatenation
type: theorem
---
The $k$-type of a concatenation $wv$ depends only on the $k$-types of $w$
and of $v$ (Lemma C.4.15 of *Transducers*, congruence): the relation "same
$k$-type" is a congruence of the free monoid.

# Formalization notes

Stated over any alphabet; no finiteness is needed.
-/

namespace Lax314295.KTypesCongruence

open Lax314295.KTypes

/-- The `k`-type of a concatenation is determined by the `k`-types of the parts. -/
axiom tp_append_congr {A : Type} (k : ℕ) (w w' v v' : List A)
    (hw : tp k w = tp k w') (hv : tp k v = tp k v') : tp k (w ++ v) = tp k (w' ++ v')

end Lax314295.KTypesCongruence
