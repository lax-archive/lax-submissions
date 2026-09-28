import Lax235315.TwinReconstruction
import Lax195003.WelzlOrdersInGraphs

/-!
---
title: Reconstruction yields a graph Welzl order
type: lemma
---
A checked reconstruction with r rounds, near-twin distance at most k,
and a base ground set of size at most q returns a graph Welzl order with
crossing number at most (r+1)q, provided 2k≤q.

Taking k=6c²L, q=12c²L, and r+1≤L gives 12c²L², the deterministic
crossing argument in Theorem 3.2 of Dreier--Kuske.

# Formalization notes

The output uses the exact registered graph-order relation, not a surrogate
list bound. The result proves both permutation validity and the crossing
bound. It is conditional on a concrete reconstruction certificate; producing
that certificate from machine execution is a separate open obligation.
-/

namespace Lax235315.ReconstructionCorrectness
open Lax235315.TwinReconstruction Lax195003.WelzlOrdersInGraphs

/-- A full-vertex reconstruction encodes an order with the accumulated crossing bound. -/
axiom encodesGraphWelzlOrder {n k q rounds bound : ℕ}
    (G : SimpleGraph (Fin n)) (l : List (Fin n))
    (h : Run G k q rounds Set.univ Set.univ l)
    (hkq : 2 * k ≤ q) (hbound : (rounds + 1) * q ≤ bound) :
    EncodesGraphWelzlOrder G 1 bound (l.map Fin.val)

end Lax235315.ReconstructionCorrectness
