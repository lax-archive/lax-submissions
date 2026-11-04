import Lax185574.FlipMetricMonotone

namespace Lax185574Proofs.FlipMetricMonotone

open Lax185574.Flips

universe u

/--
---
conclusion: Lax185574.FlipMetricMonotone.isFlip_of_le
---
Each part of `𝒬` lies in a part of `𝒫`, so the choice between agreeing
and disagreeing made for a pair of `𝒫`-parts also serves the pair of
`𝒬`-parts inside it.
-/
theorem isFlip_of_le {V : Type u} (G : SimpleGraph V) {P Q : Setoid V}
    (hQP : Q ≤ P) (H : SimpleGraph V) (hH : IsFlip G P H) : IsFlip G Q H := by
  intro a b
  rcases hH a b with h | h
  · exact Or.inl fun x y hx hy hxy => h x y (hQP hx) (hQP hy) hxy
  · exact Or.inr fun x y hx hy hxy => h x y (hQP hx) (hQP hy) hxy

/--
---
conclusion: Lax185574.FlipMetricMonotone.flipBall_subset_of_le
---
Every `𝒫`-flip is a `𝒬`-flip, so a bound on the distance in all
`𝒬`-flips is in particular a bound in all `𝒫`-flips.
-/
theorem flipBall_subset_of_le {V : Type u} (G : SimpleGraph V) {P Q : Setoid V}
    (hQP : Q ≤ P) (r : ℕ) (v : V) : flipBall G Q r v ⊆ flipBall G P r v :=
  fun _ hu H hH => hu H (isFlip_of_le G hQP H hH)

end Lax185574Proofs.FlipMetricMonotone
