import Lax65.GridNumber
import Lax65.BonnetDepresGraph

/-!
---
title: Grid number of the Bonnet–Déprés graph
type: lemma
---
Fix a real $0 < \varepsilon \le 1/2$ and an integer $t > 1/\varepsilon$. Then the grid
number of $G_{t,\varepsilon}$ is at most $t + 2$.
-/

namespace Lax65.GridNumberOfBonnetDepres

open Lax65.GridNumber Lax65.BonnetDepresGraph

/-- `G_{t,ε}` has grid number at most `t + 2`. -/
axiom gridNumber_le (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1 / 2) (t : ℕ)
    (ht : 1 / ε < t) :
    gridNumber (bonnetDepres ε t) ≤ t + 2

end Lax65.GridNumberOfBonnetDepres
