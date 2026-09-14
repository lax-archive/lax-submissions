import Lax765601.Aperiodicity
import Lax314295.KTypes

/-!
---
title: k-types are aperiodic
type: theorem
---
For every string $w$ and every $k$, the $k$-types of the powers
$w, w^2, w^3, \ldots$ eventually stabilise (Lemma C.4.15 of *Transducers*,
aperiodicity): all sufficiently large powers of a string have the same
$k$-type. This is what makes the automaton of $k$-types aperiodic.

# Formalization notes

`npow w n` is `wⁿ`, from `Lax765601.Aperiodicity`. Stated over any alphabet.
-/

namespace Lax314295.KTypesAperiodicity

open Lax765601.Aperiodicity Lax314295.KTypes

/-- The `k`-types of the powers of a string eventually stabilise. -/
axiom exists_tp_npow_eq {A : Type} (k : ℕ) (w : List A) :
    ∃ N : ℕ, ∀ n ≥ N, tp k (npow w n) = tp k (npow w N)

end Lax314295.KTypesAperiodicity
