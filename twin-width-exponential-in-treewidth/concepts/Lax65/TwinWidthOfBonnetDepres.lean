import Lax48.TwinWidth
import Lax65.BonnetDepresGraph

/-!
---
title: Twin-width of the Bonnet–Déprés graph
type: lemma
---
Fix a real $0 < \varepsilon \le 1/2$ and an integer $t > 1/\varepsilon$. Then
$G_{t,\varepsilon}$ has twin-width greater than $2^{(1-\varepsilon)t}$.
-/

namespace Lax65.TwinWidthOfBonnetDepres

open Lax48.TwinWidth Lax65.BonnetDepresGraph

/-- `G_{t,ε}` has twin-width greater than `2 ^ ((1 - ε) t)`. -/
axiom two_rpow_lt_twinWidth (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1 / 2) (t : ℕ)
    (ht : 1 / ε < t) :
    (2 : ℝ) ^ ((1 - ε) * t) < twinWidth (bonnetDepres ε t)

end Lax65.TwinWidthOfBonnetDepres
