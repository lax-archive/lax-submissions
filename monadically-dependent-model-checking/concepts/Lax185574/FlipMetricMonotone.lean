import Lax185574.Flips

/-!
---
title: Refining a partition increases the flip metric
type: observation
---
If 𝒬 refines 𝒫, then every 𝒫-flip is also a 𝒬-flip, and hence

dist_𝒬(u, v) ≥ dist_𝒫(u, v).

# Formalization notes

Refinement is 𝒬 ≤ 𝒫 for setoids. The inequality of the flip metrics is
stated through their balls: for every r, Ball^𝒬_r(v) ⊆ Ball^𝒫_r(v),
that is, dist_𝒬(u, v) ≤ r implies dist_𝒫(u, v) ≤ r. This is the
inequality for distances that may be infinite. The two parts of the
observation are two axioms. The graph may be infinite.
-/

namespace Lax185574.FlipMetricMonotone

open Lax185574.Flips

universe u

/-- If `𝒬` refines `𝒫`, every `𝒫`-flip is a `𝒬`-flip. -/
axiom isFlip_of_le {V : Type u} (G : SimpleGraph V) {P Q : Setoid V}
    (hQP : Q ≤ P) (H : SimpleGraph V) (hH : IsFlip G P H) : IsFlip G Q H

/-- If `𝒬` refines `𝒫`, then `dist_𝒬(u, v) ≥ dist_𝒫(u, v)`: every ball
of the flip metric of `𝒬` lies in the ball of the same radius of the
flip metric of `𝒫`. -/
axiom flipBall_subset_of_le {V : Type u} (G : SimpleGraph V) {P Q : Setoid V}
    (hQP : Q ≤ P) (r : ℕ) (v : V) : flipBall G Q r v ⊆ flipBall G P r v

end Lax185574.FlipMetricMonotone
