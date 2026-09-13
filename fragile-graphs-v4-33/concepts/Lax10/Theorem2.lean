import Lax10.ThreeConnectedAndColorable

/-!
---
title: Theorem 2
type: theorem
---
Let $m \geq 4$. If a finite simple graph has chromatic number at least
$m + 1$, then it has a $3$-connected subgraph with chromatic number at least
$m$.
-/

namespace Lax10.Theorem2

universe u

open Lax10.ThreeConnectedAndColorable

/--
If $\chi(G) \geq m + 1$, some $3$-connected subgraph of $G$ has chromatic
number at least $m$.
-/
axiom theorem2 {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hchi : ((m + 1 : Nat) : ℕ∞) ≤ G.chromaticNumber) :
    ∃ H : G.Subgraph, ThreeConnected H.coe ∧
      (m : ℕ∞) ≤ H.coe.chromaticNumber

end Lax10.Theorem2
