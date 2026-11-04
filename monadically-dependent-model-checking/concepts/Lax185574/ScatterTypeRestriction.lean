import Lax185574.ScatterTypes

/-!
---
title: Restriction of scatter types
type: lemma
---
For every partial graph G and q ≥ 1, the function stp_{k+1,q−1} is the
restriction of stp_{k,q} to domain(stp_{k+1,q−1}).

# Formalization notes

q ≥ 1 is written as q + 1. The statement says that domain(stp_{k+1,q})
is contained in domain(stp_{k,q+1}) and that the two functions agree on
it.
-/

namespace Lax185574.ScatterTypeRestriction

open Lax185574.PartialGraphs Lax185574.ScatterTypes

/-- **Restriction of scatter types.** -/
axiom stp_restrict {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) :
    domain G (k + 1) q ⊆ domain G k (q + 1) ∧
      ∀ p ∈ domain G (k + 1) q, value G (k + 1) q p = value G k (q + 1) p

end Lax185574.ScatterTypeRestriction
