import Lax48.Treewidth
import Lax65.BonnetDepresGraph

/-!
---
title: Treewidth of G_t
type: lemma
---
Fix a real 0 < *ε* ≤ 1/2 and an integer *t* > 1/*ε*. Then *G*<sub>*t*</sub>
has treewidth at most *t* + 1.
-/

namespace Lax65.TreewidthOfBonnetDepres

open Lax48.Treewidth Lax65.BonnetDepresGraph

/-- `G_{t,ε}` has treewidth at most `t + 1`. -/
axiom treewidth_le (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1 / 2) (t : ℕ)
    (ht : 1 / ε < t) :
    treewidth (bonnetDepres ε t) ≤ t + 1

end Lax65.TreewidthOfBonnetDepres
