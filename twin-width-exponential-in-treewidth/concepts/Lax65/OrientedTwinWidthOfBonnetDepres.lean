import Lax65.OrientedTwinWidth
import Lax65.BonnetDepresGraph

/-!
---
title: Oriented twin-width of the Bonnet–Déprés graph
type: lemma
---
Fix a real $0 < \varepsilon \le 1/2$ and an integer $t > 1/\varepsilon$. Then the
oriented twin-width of $G_{t,\varepsilon}$ is at most $t + 1$.
-/

namespace Lax65.OrientedTwinWidthOfBonnetDepres

open Lax65.OrientedTwinWidth Lax65.BonnetDepresGraph

/-- `G_{t,ε}` has oriented twin-width at most `t + 1`. -/
axiom orientedTwinWidth_le (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1 / 2) (t : ℕ)
    (ht : 1 / ε < t) :
    orientedTwinWidth (bonnetDepres ε t) ≤ t + 1

end Lax65.OrientedTwinWidthOfBonnetDepres
